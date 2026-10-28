#!/usr/bin/python3
# -*- coding: utf-8 -*-
# @file    : 悦听吧_T3.py  (影视仓 / T3 内置 python; 同源文件 悦听吧.py 为 hipy-server T4 版)
"""
悦听吧 (yuetingba.cn) TVBox py 爬虫

站点分析 (2026-10):
- IIS + 自定义模板 (非 maccms), 页面纯服务端渲染, 结构:
  分类  /book/{cid}/{page}      cid: 1玄幻 2历史 3武侠 4都市 5科幻 6名著 7女频 8社科 9儿童 a评书
  详情  /book/detail/{uuid}/{offset}   offset 每页 200 集 (0/200/400...)
  搜索  /search?type=1&name=xx&pageIndex=N   (1书名 2作者 3演播)
  榜单  /top/latest/1  /top/recommend/1
- 广告/乱跳分析: 全站 HTML 无 window.open / popunder / adsbygoogle, 仅挂了
  Google Analytics + 百度统计 + disable-devtool(浏览器反调试), 乱跳只发生在
  浏览器 JS 层面; 本爬虫纯 HTTP 抓取、不执行任何页面 JS, 广告跳转完全无影响。
  详情页内嵌 uni-app 播放 iframe (/tingpage), 也不使用 —— 播放地址本地算法直出。

播放链 (逆向自 /tingpage/assets/pages-book-bookplay.js, 已沙箱实测 206 audio/mpeg):
1. 详情页内嵌 var assl (AES 服务端列表, 全站同一份) / var py (书代号) / var bookId / var sk (签名盐)
   assl 解密: 先 replace(sk,'') -> AES-128-CBC
   key = b64('le95G3hnFDJsBE+1/v9eYw=='), iv = b64('IvswQFEUdKYf+d1wKpYLTg==')
2. 选服务器: AsType=='1' 且 Type=='A'; bookId 第5段(-分隔)命中 BookIds 用命中项,
   否则用 BookIds 为空的项; 再筛 Ratio>0 取第一个
3. 单集 efi: GET /api/app/docs-listen/{tingId}/ting-with-efi -> {efi, creationTime}
   key/iv 派生 (AES-256-CBC): A=tingId去掉所有'-'; ct=creationTime去掉-:T.和空格后右侧补'0'到20位
   gk: 前20位 A[i]+int(ct[i]), 其后 A[i]+int(ct[i-20]);  gi: i从20递减到5, A[i]+int(ct[i-1])
   解密得真实路径, 取文件名 fname
4. 路径改写: 服务器名 _p 结尾 -> /{py}_{bookId}/{fname}
            服务器名 _b 结尾 -> /myfiles/host/listen/booksdir/{py}_{bookId}/{fname}
5. 签名: expire=floor(now/1000)+600, token=md5(fname+'|'+expire+'|'+sk)
   最终 {Scheme}://{Value}:{Port}{path}?token=&expire= (path 按段 urlencode, 支持 Range 拖动)

环境无 pycryptodome 时自动回退内置纯 Python AES 实现。
"""

import base64
import hashlib
import json
import os
import re
import sys
import tempfile
import threading
import time
from concurrent.futures import ThreadPoolExecutor

import requests as N

sys.path.append('..')
try:
    from base.spider import Spider as A          # 影视仓 / T3 内置 python
except Exception:
    try:
        from base.spider import BaseSpider as A  # hipy-server T4
    except Exception:
        try:
            from t4.base.spider import BaseSpider as A
        except Exception:
            class A(object):                     # 兜底: 独立加载不报错
                def __init__(self):
                    pass

UA = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36'
BASE = 'http://yuetingba.cn'
FLAG = '悦听吧'
# assl 全站同一份 + 签名盐 (逆向自详情页内嵌 JS, 已实测)
ASSL_KEY_B64 = 'le95G3hnFDJsBE+1/v9eYw=='
ASSL_IV_B64 = 'IvswQFEUdKYf+d1wKpYLTg=='
SK_DEFAULT = 'xMiP5W1DHBxC5PwQ5oj5QfRn0tsT5UBk'
PAGE_STEP = 200                # 详情页每页集数
CACHE_FILE = os.path.join(tempfile.gettempdir(), 'tvbox_yuetingba_cache.json')
CACHE_LOCK = threading.Lock()

CLASSES = [
    ('1', '玄幻'), ('2', '历史'), ('3', '武侠'), ('4', '都市'), ('5', '科幻'),
    ('6', '名著'), ('7', '女频'), ('8', '社科'), ('9', '儿童'), ('a', '评书'),
]


def LOG(msg):
    try:
        print('[悦听吧]', msg)
    except Exception:
        pass


# ---------------- 纯 Python AES (CBC 解密, 无 pycryptodome 依赖) ----------------
_g_SBOX = None
_g_ISBOX = None


def _gmul(a, b):
    p = 0
    for _ in range(8):
        if b & 1:
            p ^= a
        hi = a & 0x80
        a = (a << 1) & 0xFF
        if hi:
            a ^= 0x1B
        b >>= 1
    return p


def _gpow(a, n):
    r = 1
    while n:
        if n & 1:
            r = _gmul(r, a)
        a = _gmul(a, a)
        n >>= 1
    return r


def _sbox_init():
    global _g_SBOX, _g_ISBOX
    if _g_SBOX is not None:
        return
    sbox = [0] * 256
    for x in range(256):
        sbox[x] = 0 if x == 0 else _gpow(x, 254)   # GF(2^8) 乘法逆元
    out = [0] * 256
    for i in range(256):
        v = sbox[i]
        r = v
        for _ in range(4):                          # 仿射变换
            v = ((v << 1) | (v >> 7)) & 0xFF
            r ^= v
        out[i] = r ^ 0x63
    inv = [0] * 256
    for i, v in enumerate(out):
        inv[v] = i
    _g_SBOX = out
    _g_ISBOX = inv


def _aes_key_expand(key, nk):
    _sbox_init()
    nr = nk + 6
    w = [list(key[4 * i:4 * i + 4]) for i in range(nk)]
    rcon = 1
    for i in range(nk, 4 * (nr + 1)):
        t = list(w[i - 1])
        if i % nk == 0:
            t = t[1:] + t[:1]
            t = [_g_SBOX[b] for b in t]
            t[0] ^= rcon
            rcon = _gmul(rcon, 2)
        elif nk > 6 and i % nk == 4:
            t = [_g_SBOX[b] for b in t]
        w.append([w[i - nk][j] ^ t[j] for j in range(4)])
    return w, nr


def _aes_dec_block(block, w, nr):
    _sbox_init()
    s = list(block)

    def add_round_key(rnd):
        for c in range(4):
            wk = w[rnd * 4 + c]
            for r in range(4):
                s[r + 4 * c] ^= wk[r]

    def inv_shift_rows():
        old = s[:]
        for r in range(1, 4):
            for c in range(4):
                s[r + 4 * c] = old[r + 4 * ((c - r) % 4)]

    def inv_sub_bytes():
        ib = _g_ISBOX
        for i in range(16):
            s[i] = ib[s[i]]

    def inv_mix_columns():
        for c in range(4):
            i = 4 * c
            a, b, cc, d = s[i], s[i + 1], s[i + 2], s[i + 3]
            s[i] = _gmul(a, 14) ^ _gmul(b, 11) ^ _gmul(cc, 13) ^ _gmul(d, 9)
            s[i + 1] = _gmul(a, 9) ^ _gmul(b, 14) ^ _gmul(cc, 11) ^ _gmul(d, 13)
            s[i + 2] = _gmul(a, 13) ^ _gmul(b, 9) ^ _gmul(cc, 14) ^ _gmul(d, 11)
            s[i + 3] = _gmul(a, 11) ^ _gmul(b, 13) ^ _gmul(cc, 9) ^ _gmul(d, 14)

    add_round_key(nr)
    for rnd in range(nr - 1, 0, -1):
        inv_shift_rows()
        inv_sub_bytes()
        add_round_key(rnd)
        inv_mix_columns()
    inv_shift_rows()
    inv_sub_bytes()
    add_round_key(0)
    return bytes(s)


def _aes_cbc_decrypt(cipher_b64, key, iv):
    """AES-CBC 解密 (key 16/24/32 字节自动选轮数), 返回去 PKCS7 的 utf8 字符串"""
    try:
        from Crypto.Cipher import AES
        c = AES.new(key, AES.MODE_CBC, iv)
        pt = c.decrypt(base64.b64decode(cipher_b64))
    except Exception:
        nk = len(key) // 4
        w, nr = _aes_key_expand(key, nk)
        raw = base64.b64decode(cipher_b64)
        out = bytearray()
        prev = iv
        for i in range(0, len(raw), 16):
            blk = raw[i:i + 16]
            dec = _aes_dec_block(blk, w, nr)
            out.extend(bytes(x ^ y for x, y in zip(dec, prev)))
            prev = blk
        pt = bytes(out)
    if pt:
        pad = pt[-1]
        if 1 <= pad <= 16 and pt[-pad:] == bytes([pad]) * pad:
            pt = pt[:-pad]
    return pt.decode('utf-8', 'ignore')


# ---------------- 悦听吧 ----------------
class Spider(A):

    def __init__(self):
        super().__init__()
        self.name = FLAG
        self.extend = {}
        self._assl_raw = None
        self._sk = SK_DEFAULT
        self._servers = None
        self._loadDisk()

    # ---- 缓存 (assl 全站一份, 落盘复用) ----
    def _loadDisk(self):
        try:
            with open(CACHE_FILE, 'r', encoding='utf-8') as f:
                d = json.load(f)
            self._assl_raw = d.get('assl')
            self._sk = d.get('sk') or SK_DEFAULT
            self._servers = d.get('servers')
        except Exception:
            pass

    def _saveDisk(self):
        try:
            with CACHE_LOCK:
                with open(CACHE_FILE, 'w', encoding='utf-8') as f:
                    json.dump({'assl': self._assl_raw, 'sk': self._sk,
                               'servers': self._servers}, f)
        except Exception:
            pass

    def getName(self):
        return self.name

    def init(self, extend='{}'):
        try:
            self.extend = json.loads(extend) if extend else {}
            if isinstance(self.extend, dict):
                self.name = self.extend.get('name', FLAG) or FLAG
                if self.extend.get('url'):
                    self.BASE = str(self.extend['url']).rstrip('/')
        except Exception as e:
            LOG(e)
            self.extend = {}

    def _base(self):
        return getattr(self, 'BASE', None) or BASE

    # ---- 网络: 重试 + 退避 (站点限流 5次/5秒, 见响应头 x-rate-limit-limit) ----
    def _req(self, url, tries=4, timeout=15):
        last = None
        for i in range(tries):
            try:
                r = N.get(url, headers={'User-Agent': UA,
                                        'Referer': self._base() + '/'},
                          timeout=timeout)
                if r.status_code == 200 and r.text:
                    return r.text
                last = Exception('HTTP %s %s' % (r.status_code, url))
                if r.status_code == 429:
                    # 撞限流: 快速重试仍在 5s 窗口内会连续 429, 等窗口滑出再拉,
                    # 否则翻页拿到空列表 app 会误判为"没有下一页"
                    time.sleep(5.2)
                    continue
            except Exception as e:
                last = e
            time.sleep(0.3 * (i + 1))
        raise last or Exception('req fail: ' + url)

    # ---- 列表卡片解析 (分类/搜索/首页同构) ----
    def _parseCards(self, html):
        out, seen = [], set()
        for chunk in html.split('section-box-list-item')[1:]:
            mu = re.search(r'href="/book/detail/([0-9a-f-]{36})/\d+"', chunk)
            if not mu:
                continue
            uid = mu.group(1)
            if uid in seen:
                continue
            seen.add(uid)
            mt = re.search(r'box-list-item-text-title"><a[^>]*>([^<]+)</a>', chunk)
            if not mt:
                continue
            name = mt.group(1).strip()
            mp = re.search(r'<img[^>]+src=["\']([^"\']+)["\']', chunk)
            pic = mp.group(1) if mp else ''
            if pic.startswith('/'):
                pic = self._base() + pic
            ma = re.search(r'type=2&name=([^"&\s]+)', chunk)
            ms = re.search(r'type=3&name=([^"&\s]+)', chunk)
            try:
                from urllib.parse import unquote
                author = unquote(ma.group(1)) if ma else ''
                teller = unquote(ms.group(1)) if ms else ''
            except Exception:
                author = ma.group(1) if ma else ''
                teller = ms.group(1) if ms else ''
            out.append({'id': uid, 'name': name, 'pic': pic,
                        'author': author, 'teller': teller})
        return out

    def _buildVod(self, c):
        return {
            'vod_id': c['id'],
            'vod_name': c['name'],
            'vod_pic': c['pic'],
            'vod_remarks': c.get('teller') or c.get('author') or '',
            'vod_content': '',
        }

    def homeContent(self, filter):
        try:
            html = self._req(self._base() + '/')
        except Exception as e:
            LOG('home fail: %s' % e)
            return {'class': list({'type_id': c, 'type_name': n} for c, n in CLASSES),
                    'filters': {}, 'list': [], 'parse': 0, 'jx': 0}
        classes = list({'type_id': c, 'type_name': n} for c, n in CLASSES)
        try:
            nav = re.findall(r'<a[^>]*href="/book/([0-9a-zA-Z]+)/1"[^>]*>([^<]+)</a>', html)
            if nav:
                seen, cls = set(), []
                for cid, nm in nav:
                    if cid in seen:
                        continue
                    seen.add(cid)
                    cls.append({'type_id': cid, 'type_name': nm.strip()})
                classes = cls
        except Exception:
            pass
        cards = self._parseCards(html)
        return {'class': classes, 'filters': {},
                'list': [self._buildVod(c) for c in cards],
                'parse': 0, 'jx': 0}

    def homeVideoContent(self):
        try:
            html = self._req(self._base() + '/')
            cards = self._parseCards(html)
            return {'list': [self._buildVod(c) for c in cards]}
        except Exception as e:
            LOG('homeVideo fail: %s' % e)
            return {'list': []}

    def categoryContent(self, cid, page, filter, ext):
        try:
            pg = int(page or 1)
        except Exception:
            pg = 1
        if pg < 1:
            pg = 1
        S = {'page': pg, 'pagecount': pg, 'limit': 10, 'total': 0,
             'list': [], 'parse': 0, 'jx': 0}
        url = '%s/book/%s/%s' % (self._base(), cid, pg)
        try:
            html = self._req(url)
        except Exception as e:
            LOG('category fail %s: %s' % (cid, e))
            return S                          # pagecount==page => 无下一页, 停止翻页
        cards = self._parseCards(html)
        S['list'] = [self._buildVod(c) for c in cards]
        total = 0
        try:
            m = re.search(r'共(\d+)条', html)
            if m:
                total = int(m.group(1))
        except Exception:
            pass
        if total:
            # 站点给了总数: 页数精确可算; 本页满 10 条时确保 pagecount>page,
            # 让 app 判定"还有下一页"继续上滑加载
            S['total'] = total
            S['pagecount'] = max((total + 9) // 10, pg + 1 if len(cards) >= 10 else pg)
        elif len(cards) >= 10:
            S['pagecount'] = pg + 1           # 满页 => 下一页待拉
            S['total'] = (pg + 1) * 10
        else:
            S['total'] = (pg - 1) * 10 + len(cards)
        return S

    def searchContent(self, key, quick, page='1'):
        from urllib.parse import quote
        try:
            pg = int(page or 1)
        except Exception:
            pg = 1
        if pg < 1:
            pg = 1
        S = {'page': pg, 'pagecount': pg, 'limit': 10, 'total': 0,
             'list': [], 'parse': 0, 'jx': 0}
        url = '%s/search?type=1&name=%s&pageIndex=%s' % (
            self._base(), quote(str(key)), pg)
        try:
            html = self._req(url)
        except Exception as e:
            LOG('search fail: %s' % e)
            return S
        cards = self._parseCards(html)
        S['list'] = [self._buildVod(c) for c in cards]
        total = 0
        try:
            m = re.search(r'共(\d+)条', html)
            if m:
                total = int(m.group(1))
        except Exception:
            pass
        if total:
            S['total'] = total
            S['pagecount'] = max((total + 9) // 10, pg + 1 if len(cards) >= 10 else pg)
        elif len(cards) >= 10:
            S['pagecount'] = pg + 1           # 满页 => 还有下一页
            S['total'] = (pg + 1) * 10
        else:
            S['total'] = (pg - 1) * 10 + len(cards)
        return S

    # ---- 详情: 元数据 + 全量选集 (按 200/页并行拉取) ----
    def _detailMeta(self, html, uid):
        def grab(pat, default=''):
            m = re.search(pat, html, re.S)
            return m.group(1).strip() if m else default

        name = grab(r'<h1 class="hidden-xs">\s*([^<]+?)\s*</h1>')
        author = grab(r'作\s*者：</span>\s*<span class="text-desc-content">\s*(?:<a[^>]*>)?([^<]+)')
        teller = grab(r'演\s*播：</span>\s*<span class="text-desc-content">\s*(?:<a[^>]*>)?([^<]+)')
        cat = grab(r'分\s*类：</span>\s*<span class="text-desc-content">\s*([^<]+)')
        status = grab(r'状\s*态：</span>\s*<span class="text-desc-content">\s*([^<]+)')
        cnt = grab(r'集\s*数：</span>\s*<span class="text-desc-content">\s*(\d+)')
        intro = grab(r'内容简介：</h4></div>\s*<div class="col-md-12 text-desc-content">(.*?)</div>')
        intro = re.sub(r'<br\s*/?>', '\n', intro)
        intro = re.sub(r'<[^>]+>', '', intro).strip()
        mpic = re.search(r'<div class="books-detail-img">\s*<img src="([^"]+)"', html)
        pic = mpic.group(1) if mpic else ''
        assl = grab(r"var assl = '([^']+)'")
        py = grab(r"var py\s*=\s*'([^']+)'")
        book = grab(r"var bookId = '([^']+)'") or uid
        sk = grab(r"var sk = '([^']+)'")
        return {'name': name, 'author': author, 'teller': teller, 'cat': cat,
                'status': status, 'count': int(cnt) if cnt.isdigit() else 0,
                'intro': intro, 'pic': pic, 'assl': assl, 'py': py,
                'book': book, 'sk': sk}

    @staticmethod
    def _parseEps(html):
        eps = []
        for m in re.finditer(
                r'<a title="([^"]+)"[^>]*onclick="testFn\(\'([0-9a-f-]{36})\'\)"', html):
            title, tid = m.group(1).strip(), m.group(2)
            if title:
                eps.append((title, tid))
        if not eps:  # 兜底: item_ 锚点
            for m in re.finditer(
                    r'id="item_([0-9a-f-]{36})"[^>]*>.*?<a[^>]*>\s*([^<]+?)\s*</a>',
                    html, re.S):
                eps.append((m.group(2).strip(), m.group(1)))
        return eps

    def detailContent(self, did):
        uid = did[0] if isinstance(did, (list, tuple)) else str(did)
        uid = uid.split('|')[0].split('$')[0].strip()
        detail_url = '%s/book/detail/%s/0' % (self._base(), uid)
        html = None
        last = None
        for _ in range(2):                       # 整体重试 1 轮
            try:
                html = self._req(detail_url)
                if 'testFn' in html or '集  数' in html:
                    break
                html = None
                raise Exception('detail 页异常')
            except Exception as e:
                last = e
        if not html:
            LOG('detail fail %s: %s' % (uid, last))
            return {'list': []}

        meta = self._detailMeta(html, uid)
        eps = self._parseEps(html)
        offsets = []
        if meta['count'] > PAGE_STEP:
            offsets = list(range(PAGE_STEP, meta['count'], PAGE_STEP))
            found = set(int(x) for x in re.findall(
                r'/book/detail/%s/(\d+)' % re.escape(uid), html))
            offsets = [o for o in offsets if o in found] or offsets

        if offsets:
            def fetch(off):
                try:
                    return self._req('%s/book/detail/%s/%s' % (self._base(), uid, off))
                except Exception as e:
                    LOG('detail page %s fail: %s' % (off, e))
                    return ''
            with ThreadPoolExecutor(max_workers=5) as ex:
                for h in ex.map(fetch, offsets):
                    if h:
                        eps.extend(self._parseEps(h))

        seen, eplist = set(), []
        for title, tid in eps:
            if tid in seen:
                continue
            seen.add(tid)
            eplist.append((title, tid))

        if meta['assl']:
            self._assl_raw = meta['assl']
        if meta['sk']:
            self._sk = meta['sk']
        if meta['py'] and meta['book']:
            # py/book 落盘, 进程重启后 playerContent 仍可直出
            try:
                with CACHE_LOCK:
                    d = {}
                    try:
                        with open(CACHE_FILE, 'r', encoding='utf-8') as f:
                            d = json.load(f)
                    except Exception:
                        pass
                    books = d.get('books') or {}
                    books[meta['book']] = meta['py']
                    d.update({'assl': self._assl_raw, 'sk': self._sk,
                              'servers': self._servers, 'books': books})
                    with open(CACHE_FILE, 'w', encoding='utf-8') as f:
                        json.dump(d, f)
            except Exception:
                pass

        play = '#'.join('%s$%s@%s@%s' % (t, tid, meta['book'], meta['py'])
                        for t, tid in eplist)
        vod = {
            'vod_id': uid,
            'vod_name': meta['name'],
            'vod_pic': meta['pic'],
            'vod_remarks': meta['status'] or ('%s集' % meta['count'] if meta['count'] else ''),
            'vod_actor': meta['teller'],
            'vod_director': meta['author'],
            'vod_area': meta['cat'],
            'vod_content': meta['intro'],
            'vod_play_from': FLAG,
            'vod_play_url': play,
        }
        return {'list': [vod]}

    # ---- 服务器列表 (assl 解密, 全站一份, 内存+落盘缓存) ----
    def _getServers(self, book=''):
        if self._servers:
            return self._servers
        assl, sk = self._assl_raw, self._sk
        if not assl and book:
            try:
                html = self._req('%s/book/detail/%s/0' % (self._base(), book))
                meta = self._detailMeta(html, book)
                assl, py = meta['assl'], meta['py']
                if meta['sk']:
                    sk = meta['sk']
                if py and book:
                    with CACHE_LOCK:
                        d = {}
                        try:
                            with open(CACHE_FILE, 'r', encoding='utf-8') as f:
                                d = json.load(f)
                        except Exception:
                            pass
                        books = d.get('books') or {}
                        books[book] = py
                        d['books'] = books
                        with open(CACHE_FILE, 'w', encoding='utf-8') as f:
                            json.dump(d, f)
            except Exception as e:
                LOG('assl fetch fail: %s' % e)
        if not assl:
            raise Exception('assl 不可用')
        raw = assl.replace(sk or SK_DEFAULT, '', 1)
        dec = _aes_cbc_decrypt(raw,
                               base64.b64decode(ASSL_KEY_B64),
                               base64.b64decode(ASSL_IV_B64))
        servers = json.loads(dec)
        if not isinstance(servers, list) or not servers:
            raise Exception('assl 解密结果异常')
        self._assl_raw, self._sk = assl, sk or SK_DEFAULT
        self._servers = servers
        self._saveDisk()
        return servers

    @staticmethod
    def _pickServer(servers, book):
        pool = [s for s in servers if str(s.get('AsType')) == '1'] or list(servers)
        ap = [s for s in pool if s.get('Type') == 'A'] or pool
        part = ''
        try:
            seg = str(book).split('-')
            if len(seg) > 4:
                part = seg[4]
        except Exception:
            pass
        if part:
            hit = [s for s in ap if part in json.dumps(s.get('BookIds') or '',
                                                       ensure_ascii=False)]
            if hit:
                ap = hit
            else:
                empty = [s for s in ap if not s.get('BookIds')]
                if empty:
                    ap = empty
        ratio = [s for s in ap if (s.get('Ratio') or 0) > 0]
        return (ratio or ap)[0]

    @staticmethod
    def _deriveKeys(ting_id, creation_time):
        A = ting_id.replace('-', '')
        ct = (creation_time.replace('-', '').replace(':', '')
              .replace('T', '').replace('.', '').replace(' ', ''))
        ct = ct.ljust(20, '0')[:20]
        key = bytes(ord(A[i]) + int(ct[i]) for i in range(20))
        key += bytes(ord(A[i]) + int(ct[i - 20]) for i in range(20, len(A)))
        iv = bytes(ord(A[i]) + int(ct[i - 1]) for i in range(20, 4, -1))
        return key, iv

    @staticmethod
    def _encPath(path):
        try:
            from urllib.parse import quote
            return '/'.join(quote(seg) for seg in path.split('/'))
        except Exception:
            return path

    def playerContent(self, flag, pid, vipFlags):
        out = {'parse': 0, 'jx': 0, 'url': '', 'header': {'User-Agent': UA}}
        try:
            parts = str(pid).split('@')
            ting = parts[0].strip()
            book = parts[1].strip() if len(parts) > 1 else ''
            py = parts[2].strip() if len(parts) > 2 else ''
            if not ting:
                return out

            # 1) efi 接口
            j = None
            for i in range(3):
                try:
                    j = json.loads(self._req(
                        '%s/api/app/docs-listen/%s/ting-with-efi' % (self._base(), ting)))
                    if j.get('efi'):
                        break
                    j = None
                except Exception as e:
                    j = None
                    last = e
                time.sleep(0.3 * (i + 1))
            if not j:
                LOG('efi fail %s' % ting)
                return out
            book = book or j.get('bookId') or ''

            # 2) 服务器列表 + 解密 efi
            servers = self._getServers(book)
            srv = self._pickServer(servers, book)
            key, iv = self._deriveKeys(ting, j.get('creationTime') or '')
            path = _aes_cbc_decrypt(j['efi'], key, iv).strip()
            if not path:
                LOG('efi 解密为空')
                return out

            # 3) 路径改写
            try:
                from urllib.parse import unquote
                fname = unquote(path.rstrip('/').split('/')[-1])
            except Exception:
                fname = path.rstrip('/').split('/')[-1]
            name = str(srv.get('Name') or '')
            if name.endswith('_p'):
                final = '/%s_%s/%s' % (py, book, fname)
            elif name.endswith('_b'):
                final = '/myfiles/host/listen/booksdir/%s_%s/%s' % (py, book, fname)
            else:
                final = path

            # 4) token 签名
            sk = self._sk or SK_DEFAULT
            expire = int(time.time()) + 600
            token = hashlib.md5(
                ('%s|%s|%s' % (fname, expire, sk)).encode('utf-8')).hexdigest()

            # 5) 拼最终地址
            scheme = srv.get('Scheme') or 'http'
            value = srv.get('Value') or ''
            port = srv.get('Port') or 80
            base = '%s://%s:%s' % (scheme, value, port)
            play = '%s%s?token=%s&expire=%s' % (
                base, self._encPath(final), token, expire)

            # 6) 轻量探活 (失败换下一个可用服务器重试一次)
            try:
                chk = N.get(play, headers={'User-Agent': UA, 'Referer': self._base() + '/'},
                            timeout=8, stream=True)
                code = chk.status_code
                chk.close()
                if code in (200, 206):
                    out['url'] = play
                    return out
                LOG('探活 HTTP %s, 换服务器重试' % code)
                others = [s for s in servers if s is not srv]
                for alt in others[:3]:
                    srv2 = self._pickServer([alt], book)
                    name2 = str(srv2.get('Name') or '')
                    if name2.endswith('_p'):
                        final2 = '/%s_%s/%s' % (py, book, fname)
                    elif name2.endswith('_b'):
                        final2 = '/myfiles/host/listen/booksdir/%s_%s/%s' % (py, book, fname)
                    else:
                        final2 = path
                    play2 = '%s://%s:%s%s?token=%s&expire=%s' % (
                        srv2.get('Scheme') or 'http', srv2.get('Value'),
                        srv2.get('Port') or 80, self._encPath(final2), token, expire)
                    try:
                        c2 = N.get(play2, headers={'User-Agent': UA,
                                                   'Referer': self._base() + '/'},
                                   timeout=8, stream=True)
                        ok = c2.status_code in (200, 206)
                        c2.close()
                        if ok:
                            out['url'] = play2
                            return out
                    except Exception:
                        continue
            except Exception:
                out['url'] = play   # 探活网络异常时仍给出地址
            if not out['url']:
                out['url'] = play
        except Exception as e:
            LOG('player fail %s: %s' % (pid, e))
        return out

    def localProxy(self, params):
        return None

    def isVideoFormat(self, url):
        return bool(re.search(r'\.(mp3|m4a|aac|mp4|m3u8)(\?|$)', str(url), re.I))

    def manualVideoCheck(self):
        return False

    def destroy(self):
        pass


if __name__ == '__main__':
    pass
