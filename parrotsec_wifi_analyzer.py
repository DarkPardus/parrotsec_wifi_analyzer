#!/usr/bin/env python3
"""
ParrotSec Wi-Fi Analyzer v1.0 - KDE Plasma / Parrot için canlı Wi-Fi analiz aracı (Python3 + PyQt5)
Proje: https://github.com/DarkPardus/ParrotSec-Wi-Fi-Analyzer

PASİF analiz aracıdır: çevredeki erişim noktalarının yayınlarını (beacon) okur. Paket enjeksiyonu,
deauth, el sıkışma yakalama ya da parola kırma YOKTUR. Yalnızca yetkili olduğunuz ortamlarda kullanın.

Özellikler
  * Canlı AP listesi: SSID, BSSID, sinyal çubuğu (dBm), kanal, bant, genişlik, güvenlik, Wi-Fi standardı,
    üretici (OUI), bağlı istemci sayısı ve kanal doluluğu (BSS Load), tahmini mesafe
  * Sinyal Ölçer: analog kadran + Geiger tarzı sesli bulucu (sinyal güçlendikçe sıklaşır, incelir)
  * Kanal Grafiği: 2.4 / 5 / 6 GHz, kanal genişliğine göre örtüşen parabolalar (fareyle seç)
  * Zaman Grafiği: seçili / sabitlenmiş / en güçlü ağların sinyali, son 3 dakika
  * Kanal Önerisi: girişim puanı + yıldız, en iyi kanal (DFS ayrımıyla)
  * Güvenlik Denetimi: Açık/WEP/TKIP/WPS/PMF bulguları ve düzeltme önerileri (savunma amaçlı)
  * Sahte AP / Evil Twin tespiti: aynı SSID'de güvenlik düşüşü, "güvendiğim ağ" listesine uymayan BSSID
  * Olay günlüğü: yeni / kaybolan ağ, tepsi bildirimi, CSV / JSON / Markdown rapor dışa aktarma
  * --demo ile Wi-Fi kartı olmadan deneme

Kurulum : sudo apt install python3-pyqt5 iw network-manager ieee-data
          (isteğe bağlı: python3-pyqt5.qtmultimedia → Geiger sesi için)
Çalıştır: python3 parrotsec_wifi_analyzer.py            (root gerekmez; NetworkManager ile tarama tetiklenir)
          python3 parrotsec_wifi_analyzer.py --demo     (sahte ağlarla dene)
          python3 parrotsec_wifi_analyzer.py --iface wlan0 --interval 3
Not: Arayüz "managed" modda olmalıdır (monitor modda tarama listesi alınamaz).
Ayarlar: ~/.config/parrotsec-wifi-analyzer/config.json
"""
import argparse
import fcntl
import html
import json
import os
import shutil
import signal
import socket
import struct
import subprocess
import sys
import tempfile
import threading
import time
from pathlib import Path

from PyQt5.QtCore import QByteArray, QObject, QPointF, QRectF, QSize, Qt, QTimer, QUrl, pyqtSignal
from PyQt5.QtGui import (QBrush, QColor, QFont, QIcon, QLinearGradient, QPainter, QPen, QPixmap,
                         QPolygonF)
from PyQt5.QtWidgets import (QAbstractItemView, QAction, QApplication, QCheckBox, QComboBox, QFileDialog,
                             QHBoxLayout, QHeaderView, QLabel, QLineEdit, QListWidget, QListWidgetItem,
                             QMainWindow, QMenu, QMessageBox, QPushButton, QSpinBox, QSplitter, QStyle,
                             QStyledItemDelegate, QSystemTrayIcon, QTableWidget, QTableWidgetItem,
                             QTabWidget, QToolTip, QVBoxLayout, QWidget)

CONFIG_DIR = Path(os.environ.get("XDG_CONFIG_HOME", Path.home() / ".config")) / "parrotsec-wifi-analyzer"
CONFIG_FILE = CONFIG_DIR / "config.json"

# --- PURE START -------------------------------------------------------------
# Bu bölüm Qt gerektirmez; ayrıştırıcılar, analizler ve grafik geometrisi burada.
import csv
import io
import json
import math
import os
import re
import struct
import time
import wave
from collections import defaultdict, deque
from dataclasses import asdict, dataclass, field
from typing import List, Optional

APP_NAME = "ParrotSec Wi-Fi Analyzer"
APP_VERSION = "v1.0"
APP_URL = "https://github.com/DarkPardus/ParrotSec-Wi-Fi-Analyzer"
ACCENT = "#15E0ED"

BAND_NAMES = {"2.4": "2.4 GHz", "5": "5 GHz", "6": "6 GHz"}
STD_NAMES = {"b": "802.11b", "g": "802.11g", "a": "802.11a", "n": "Wi-Fi 4 (n)", "ac": "Wi-Fi 5 (ac)",
             "ax": "Wi-Fi 6 (ax)", "be": "Wi-Fi 7 (be)"}
RISK_NAMES = ["Güçlü", "İyi", "Dikkat", "Zayıf", "Kritik"]
RISK_COLORS = ["#3ddc84", "#9be564", "#ffd60a", "#ff9f0a", "#ff453a"]


# ------------------------------------------------------------ frekans / kanal
def freq_to_channel(f):
    f = int(round(f))
    if f == 2484:
        return 14
    if 2400 <= f < 2484:
        return (f - 2407) // 5
    if 5150 <= f <= 5895:
        return (f - 5000) // 5
    if 5925 <= f <= 7125:
        return 2 if f == 5935 else (f - 5950) // 5
    return 0


def band_of(f):
    f = int(round(f))
    if 2400 <= f < 2500:
        return "2.4"
    if 5150 <= f < 5925:
        return "5"
    if 5925 <= f <= 7125:
        return "6"
    return "?"


def channel_to_freq(ch, band):
    if band == "2.4":
        return 2484 if ch == 14 else 2407 + 5 * ch
    if band == "5":
        return 5000 + 5 * ch
    if band == "6":
        return 5935 if ch == 2 else 5950 + 5 * ch
    return 0


CH24 = list(range(1, 14))
CH5 = [36, 40, 44, 48, 52, 56, 60, 64, 100, 104, 108, 112, 116, 120, 124, 128, 132, 136, 140, 144,
       149, 153, 157, 161, 165]
CH6 = list(range(1, 234, 4))
DFS5 = set(range(52, 145, 4))
BAND_CHANNELS = {"2.4": CH24, "5": CH5, "6": CH6}
BAND_RANGE = {"2.4": (2397.0, 2497.0), "5": (5165.0, 5835.0), "6": (5935.0, 7135.0)}


# ------------------------------------------------------------ model
@dataclass
class AP:
    bssid: str
    ssid: str = ""
    hidden: bool = False
    freq: int = 0
    channel: int = 0
    band: str = "?"
    signal: float = -100.0
    width: int = 20
    center: int = 0
    security: str = "Açık"
    risk: int = 4
    tkip: bool = False
    pmf: int = 0                 # 0 yok, 1 destekli (MFPC), 2 zorunlu (MFPR)
    wps: bool = False
    wps_locked: bool = False
    std: str = ""
    vendor: str = ""
    stations: Optional[int] = None
    util: Optional[float] = None  # kanal doluluğu 0-100 (BSS Load)
    country: str = ""
    age_ms: Optional[int] = None
    associated: bool = False
    beacon: int = 0


def decode_ssid(raw):
    """iw \\xHH kaçışlarını çözer. -> (ssid, gizli_mi)"""
    if raw is None:
        return "", True
    bs = raw.encode("utf-8", "replace")
    bs = re.sub(rb"\\x([0-9a-fA-F]{2})", lambda m: bytes([int(m.group(1), 16)]), bs)
    s = bs.decode("utf-8", "replace")
    s = re.sub(r"[\x00-\x1f\x7f]", "", s)
    return s.strip(), s.strip() == ""


def classify_security(rsn, wpa, privacy):
    """-> (etiket, risk 0-4, tkip_var_mi)"""
    def has(d, key, word):
        return word in (d or {}).get(key, "").upper()

    if rsn:
        akm = rsn.get("akm", "").upper()
        pair = rsn.get("pairwise", "").upper()
        tkip_only = "TKIP" in pair and "CCMP" not in pair and "GCMP" not in pair
        tkip = "TKIP" in pair
        if "OWE" in akm:
            return "OWE", 2, False
        if "SAE" in akm and "PSK" in akm:
            return "WPA2/WPA3", 0, tkip
        if "SAE" in akm:
            return "WPA3-SAE", 0, tkip
        if "802.1X" in akm or "EAP" in akm:
            return ("WPA3-Enterprise" if "SUITE" in akm or "SHA-384" in akm else "WPA2-Enterprise"), 0, tkip
        if tkip_only:
            return "WPA2-TKIP", 2, True
        return "WPA2-PSK", 1, tkip
    if wpa:
        return "WPA (TKIP)", 3, True
    if privacy:
        return "WEP", 4, False
    return "Açık", 4, False


def channel_span(freq, ht_sec, ht_width_any, vht_mhz, c1, c2):
    """(merkez_MHz, genişlik_MHz) - kapladığı frekans aralığı."""
    width, center = 20, int(freq)
    if ht_sec in ("above", "below") and ht_width_any:
        width, center = 40, freq + (10 if ht_sec == "above" else -10)
    if vht_mhz in (80, 160) or (vht_mhz == 80 and c1):
        if vht_mhz == 160 and c1:
            width, center = 160, 5000 + 5 * c1
        elif c1:
            if c2 and abs(c2 - c1) == 8:
                width, center = 160, 5000 + 5 * c2
            else:
                width, center = 80, 5000 + 5 * c1
    return int(center), int(width)


def detect_standard(raw, band):
    if raw.get("eht"):
        return "be"
    if raw.get("he"):
        return "ax"
    if raw.get("vht"):
        return "ac"
    if raw.get("ht"):
        return "n"
    if band in ("5", "6"):
        return "a"
    return "g" if raw.get("erp") else "b"


def _finalize(raw):
    ssid, hidden = decode_ssid(raw.get("ssid_raw"))
    freq = int(round(raw.get("freq", 0)))
    band = band_of(freq)
    ch = freq_to_channel(freq) or raw.get("ds_channel") or raw.get("ht_primary") or 0
    sec, risk, tkip = classify_security(raw.get("rsn"), raw.get("wpa"), raw.get("privacy"))
    center, width = channel_span(freq, raw.get("ht_sec"), raw.get("ht_width_any"), raw.get("vht_mhz"),
                                 raw.get("vht_c1"), raw.get("vht_c2"))
    pmf = 0
    caps = (raw.get("rsn") or {}).get("caps", "")
    if "MFPR" in caps:
        pmf = 2
    elif "MFPC" in caps:
        pmf = 1
    wps = raw.get("wps")
    util = raw.get("load_util")
    return AP(bssid=raw["bssid"].lower(), ssid=ssid, hidden=hidden, freq=freq, channel=ch, band=band,
              signal=raw.get("signal", -100.0), width=width, center=center, security=sec, risk=risk,
              tkip=tkip, pmf=pmf, wps=bool(wps), wps_locked=bool(wps and wps.get("locked")),
              std=detect_standard(raw, band), stations=raw.get("load_sta"),
              util=None if util is None else round(util, 1), country=raw.get("country", ""),
              age_ms=raw.get("age_ms"), associated=raw.get("associated", False),
              beacon=raw.get("beacon", 0))


# ------------------------------------------------------------ iw çıktısı ayrıştırma
def parse_iw_scan(text):
    """`iw dev X scan [dump]` çıktısı -> [AP]"""
    out, cur, section = [], None, ""

    def flush():
        if cur is not None and cur.get("freq"):
            out.append(_finalize(cur))

    def sub(sec, line):
        line = line.lstrip("* ").strip()
        key, _, val = line.partition(":")
        key, val = key.strip().lower(), val.strip()
        if sec in ("RSN", "WPA"):
            d = cur.setdefault("rsn" if sec == "RSN" else "wpa", {})
            if key == "group cipher":
                d["group"] = val
            elif key == "pairwise ciphers":
                d["pairwise"] = val
            elif key == "authentication suites":
                d["akm"] = val
            elif key == "capabilities":
                d["caps"] = val
        elif sec == "WPS":
            d = cur.setdefault("wps", {})
            if key == "ap setup locked":
                d["locked"] = val not in ("0x00", "0", "")
        elif sec == "HT operation":
            if key == "primary channel" and val.isdigit():
                cur["ht_primary"] = int(val)
            elif key == "secondary channel offset":
                cur["ht_sec"] = "above" if "above" in val else "below" if "below" in val else None
            elif key == "sta channel width":
                cur["ht_width_any"] = val.lower().startswith("any")
        elif sec in ("VHT operation", "HE operation", "EHT operation"):
            if key == "channel width":
                m = re.search(r"\((\d+)", val)
                if m:
                    cur["vht_mhz"] = int(m.group(1))
            elif key == "center freq segment 1" and val.isdigit():
                cur["vht_c1"] = int(val)
            elif key == "center freq segment 2" and val.isdigit():
                cur["vht_c2"] = int(val)
        elif sec == "BSS Load":
            if key == "station count" and val.isdigit():
                cur["load_sta"] = int(val)
            elif key.startswith("channel utili"):
                m = re.match(r"(\d+)\s*/\s*(\d+)", val)
                if m and int(m.group(2)):
                    cur["load_util"] = 100.0 * int(m.group(1)) / int(m.group(2))

    for raw in text.splitlines():
        if raw.startswith("BSS "):
            flush()
            m = re.match(r"BSS ([0-9a-fA-F:]{17})", raw)
            cur = {"bssid": m.group(1)} if m else None
            if cur is not None:
                cur["associated"] = "associated" in raw
            section = ""
            continue
        if cur is None or not raw.strip():
            continue
        indent = len(raw) - len(raw.lstrip("\t"))
        line = raw.strip()
        if indent <= 1:
            key, _, rest = line.partition(":")
            key, rest = key.strip(), rest.strip()
            section = key
            if key == "freq":
                try:
                    cur["freq"] = float(rest)
                except ValueError:
                    pass
            elif key == "signal":
                m = re.match(r"(-?\d+(?:\.\d+)?)\s*dBm", rest)
                if m:
                    cur["signal"] = float(m.group(1))
                else:
                    m = re.match(r"(\d+)\s*/\s*100", rest)
                    if m:
                        cur["signal"] = int(m.group(1)) / 2.0 - 100.0
            elif key == "last seen" and "ms ago" in rest:
                m = re.match(r"(\d+)", rest)
                if m:
                    cur["age_ms"] = int(m.group(1))
            elif key == "capability":
                cur["privacy"] = "Privacy" in rest
            elif key == "beacon interval":
                m = re.match(r"(\d+)", rest)
                if m:
                    cur["beacon"] = int(m.group(1))
            elif key == "SSID":
                cur["ssid_raw"] = rest
            elif key == "DS Parameter set":
                m = re.search(r"channel (\d+)", rest)
                if m:
                    cur["ds_channel"] = int(m.group(1))
            elif key == "Country":
                cur["country"] = rest[:2]
            elif key == "HT capabilities":
                cur["ht"] = True
            elif key == "VHT capabilities":
                cur["vht"] = True
            elif key == "HE capabilities":
                cur["he"] = True
            elif key == "EHT capabilities":
                cur["eht"] = True
            elif key == "ERP":
                cur["erp"] = True
            elif key == "RSN":
                cur["rsn"] = {}
            elif key == "WPA":
                cur["wpa"] = {}
            elif key == "WPS":
                cur["wps"] = {}
            if rest.startswith("*"):
                sub(section, rest)
        else:
            sub(section, line)
    flush()
    return out


def parse_iw_link(text):
    """`iw dev X link` -> {bssid, ssid, freq, signal, tx, rx} ya da {}"""
    m = re.search(r"Connected to ([0-9a-fA-F:]{17})", text)
    if not m:
        return {}
    d = {"bssid": m.group(1).lower()}
    for key, pat in (("ssid", r"SSID: (.*)"), ("freq", r"freq: (\d+)"), ("signal", r"signal: (-?\d+)"),
                     ("tx", r"tx bitrate: ([\d.]+)"), ("rx", r"rx bitrate: ([\d.]+)")):
        mm = re.search(pat, text)
        if mm:
            d[key] = mm.group(1).strip()
    return d


def parse_iw_dev(text):
    """`iw dev` -> [(arayüz, tür)]"""
    res, name = [], None
    for line in text.splitlines():
        m = re.match(r"\s*Interface (\S+)", line)
        if m:
            name = m.group(1)
            res.append([name, ""])
            continue
        m = re.match(r"\s*type (\S+)", line)
        if m and res:
            res[-1][1] = m.group(1)
    return [tuple(r) for r in res]


# ------------------------------------------------------------ nmcli (yedek kaynak)
def split_terse(line):
    """nmcli -t satırını kaçışlı ':' dikkate alarak böl."""
    out, cur, esc = [], [], False
    for ch in line:
        if esc:
            cur.append(ch)
            esc = False
        elif ch == "\\":
            esc = True
        elif ch == ":":
            out.append("".join(cur))
            cur = []
        else:
            cur.append(ch)
    out.append("".join(cur))
    return out


def parse_nmcli(text, with_bw=True):
    """nmcli -t -f IN-USE,BSSID,SSID,MODE,CHAN,FREQ,RATE,[BANDWIDTH,]SIGNAL,SECURITY dev wifi list"""
    aps = []
    for line in text.splitlines():
        f = split_terse(line)
        need = 10 if with_bw else 9
        if len(f) < need or not re.match(r"[0-9A-Fa-f:]{17}$", f[1]):
            continue
        if with_bw:
            inuse, bssid, ssid, mode, chan, freq, rate, bw, sig, sec = f[:10]
        else:
            inuse, bssid, ssid, mode, chan, freq, rate, sig, sec = f[:9]
            bw = ""
        try:
            fr = int(re.match(r"\d+", freq).group(0))
            quality = int(sig)
        except (AttributeError, ValueError):
            continue
        sec_u = sec.upper()
        if sec.strip() in ("", "--"):
            label, risk, tkip = "Açık", 4, False
        elif "802.1X" in sec_u:
            label, risk, tkip = "WPA2-Enterprise", 0, False
        elif "WPA3" in sec_u and "WPA2" in sec_u:
            label, risk, tkip = "WPA2/WPA3", 0, False
        elif "WPA3" in sec_u:
            label, risk, tkip = "WPA3-SAE", 0, False
        elif "OWE" in sec_u:
            label, risk, tkip = "OWE", 2, False
        elif "WPA2" in sec_u:
            label, risk, tkip = "WPA2-PSK", 1, False
        elif "WPA1" in sec_u or "WPA" in sec_u:
            label, risk, tkip = "WPA (TKIP)", 3, True
        else:
            label, risk, tkip = "WEP", 4, False
        ssid_d, hidden = decode_ssid(ssid)
        m = re.match(r"(\d+)", bw)
        width = int(m.group(1)) if m else 20
        center = fr + (10 if width == 40 else 0) if width <= 40 else fr
        aps.append(AP(bssid=bssid.lower(), ssid=ssid_d, hidden=hidden, freq=fr, channel=freq_to_channel(fr),
                      band=band_of(fr), signal=quality / 2.0 - 100.0, width=width, center=fr,
                      security=label, risk=risk, tkip=tkip, associated=(inuse.strip() == "*")))
    return aps


# ------------------------------------------------------------ üretici (OUI)
_VENDOR_NOISE = re.compile(r"\b(Corporation|Corp\.?|Inc\.?|Co\.?|Ltd\.?|Limited|Technologies|Technology|GmbH|"
                           r"plc|S\.?A\.?|LLC)\b[,.]?|\band subsidiaries\b", re.I)


def short_vendor(v):
    s = _VENDOR_NOISE.sub("", v or "")
    s = re.sub(r"\s{2,}", " ", s).strip(" ,.")
    return s or (v or "")


class OuiDb:
    PATHS = ["/usr/share/ieee-data/oui.txt", "/var/lib/ieee-data/oui.txt", "/usr/share/misc/oui.txt",
             "/usr/share/nmap/nmap-mac-prefixes", "/usr/share/wireshark/manuf", "/usr/share/ieee-data/oui.csv"]

    def __init__(self, paths=None):
        self.map, self.loaded_from = {}, ""
        for p in (paths or self.PATHS):
            if os.path.exists(p):
                try:
                    self._load(p)
                except OSError:
                    continue
                if self.map:
                    self.loaded_from = p
                    break

    def _load(self, path):
        m = self.map
        with open(path, encoding="utf-8", errors="replace") as f:
            for line in f:
                if line.startswith("#") or "(base 16)" in line:     # ieee oui.txt'te her kayıt 2 satır
                    continue
                r = re.match(r"^([0-9A-Fa-f]{2})-([0-9A-Fa-f]{2})-([0-9A-Fa-f]{2})\s+\(hex\)\s+(.+)$", line)
                if r:                                                       # ieee oui.txt
                    m["".join(r.group(i) for i in (1, 2, 3)).upper()] = r.group(4).strip()
                    continue
                r = re.match(r"^([0-9A-Fa-f]{6})\s+(.+)$", line)
                if r:                                                       # nmap-mac-prefixes
                    m[r.group(1).upper()] = r.group(2).strip()
                    continue
                r = re.match(r"^([0-9A-Fa-f]{2}):([0-9A-Fa-f]{2}):([0-9A-Fa-f]{2})\t(\S+)(?:\t(.*))?$", line)
                if r and "/" not in line.split("\t")[0]:                   # wireshark manuf
                    m["".join(r.group(i) for i in (1, 2, 3)).upper()] = (r.group(5) or r.group(4)).strip()
                    continue
                r = re.match(r"^MA-L,([0-9A-Fa-f]{6}),\"?([^\",]+)", line)  # ieee oui.csv
                if r:
                    m[r.group(1).upper()] = r.group(2).strip()

    def lookup(self, mac):
        h = re.sub(r"[^0-9A-Fa-f]", "", mac or "")
        if len(h) < 6:
            return ""
        if int(h[0:2], 16) & 2:
            return "Rastgele/yerel MAC"
        return short_vendor(self.map.get(h[:6].upper(), "")) or "Bilinmiyor"


# ------------------------------------------------------------ metrikler
def quality_pct(dbm):
    return max(0, min(100, int(round(2 * (dbm + 100)))))


def signal_color(dbm):
    if dbm >= -55:
        return "#3ddc84"
    if dbm >= -67:
        return "#9be564"
    if dbm >= -75:
        return "#ffd60a"
    if dbm >= -85:
        return "#ff9f0a"
    return "#ff453a"


def signal_label(dbm):
    return ("Mükemmel" if dbm >= -55 else "İyi" if dbm >= -67 else "Orta" if dbm >= -75
            else "Zayıf" if dbm >= -85 else "Çok zayıf")


def est_distance(dbm, freq_mhz):
    """Serbest uzay yayılımıyla kaba mesafe (m). Duvar/engel varsa gerçek mesafe daha kısadır."""
    if not freq_mhz:
        return 0.0
    return 10 ** ((27.55 - 20 * math.log10(freq_mhz) + abs(dbm)) / 20.0)


def ap_color(bssid):
    """BSSID'den kararlı, ayırt edilebilir renk (#rrggbb)."""
    import colorsys
    h = 0
    for ch in bssid.lower():
        h = (h * 131 + ord(ch)) & 0xFFFFFF
    hue = (h * 0.61803398875) % 1.0
    r, g, b = colorsys.hsv_to_rgb(hue, 0.62 + (h % 3) * 0.1, 0.95)
    return "#%02x%02x%02x" % (int(r * 255), int(g * 255), int(b * 255))


# ------------------------------------------------------------ kanal analizi
def ap_interval(ap):
    c = ap.center or ap.freq
    w = ap.width + (2 if ap.band == "2.4" else 0)
    return c - w / 2.0, c + w / 2.0


def signal_weight(dbm, util=None):
    w = max(0.0, min(1.0, (dbm + 95.0) / 55.0)) ** 1.5
    if util is not None:
        w *= 0.7 + 0.6 * util / 100.0
    return w


def rate_channels(aps, band):
    """Her aday 20 MHz kanal için girişim puanı + yıldız. -> {rows, best, best_nodfs}"""
    chans = BAND_CHANNELS.get(band, [])
    members = [a for a in aps if a.band == band]
    rows = []
    for ch in chans:
        f = channel_to_freq(ch, band)
        half = 11.0 if band == "2.4" else 10.0
        lo, hi = f - half, f + half
        score, count = 0.0, 0
        for a in members:
            alo, ahi = ap_interval(a)
            ov = max(0.0, min(hi, ahi) - max(lo, alo)) / (hi - lo)
            if ov > 0:
                score += ov * signal_weight(a.signal, a.util)
                count += 1
        stars = 5 if score < 0.15 else 4 if score < 0.5 else 3 if score < 1.2 else 2 if score < 2.5 else 1
        rows.append({"ch": ch, "freq": f, "score": round(score, 3), "stars": stars, "count": count,
                     "dfs": band == "5" and ch in DFS5})
    pool = [r for r in rows if band != "2.4" or r["ch"] in (1, 6, 11)]
    best = min(pool, key=lambda r: (r["score"], r["dfs"], r["ch"])) if pool else None
    nodfs = [r for r in pool if not r["dfs"]]
    best_nodfs = min(nodfs, key=lambda r: (r["score"], r["ch"])) if nodfs else None
    return {"rows": rows, "best": best, "best_nodfs": best_nodfs}


# ------------------------------------------------------------ güvenlik denetimi
_DEFAULT_SSID = re.compile(
    r"^(TP-?LINK_[0-9A-F]{4,6}(_5G)?|Tenda_[0-9A-F]{6}|NETGEAR\d*|Netcore\d*|D-?Link.*|HUAWEI-.*|Huawei-.*|"
    r"TTNET_.*|TurkTelekom_.*|SUPERONLINE.*|ZTE.*|FRITZ!Box.*|ASUS(_[0-9A-F]{2})?|Linksys\d*|MERCUSYS_.*|AP\d+)$", re.I)


def audit_ap(ap):
    """-> [(seviye 'crit|high|med|low|ok', bulgu, öneri)]  (yalnızca savunma amaçlı değerlendirme)"""
    f = []
    s = ap.security
    if s == "Açık":
        f.append(("crit", "Şifresiz ağ: trafik şifrelenmediği için yakındaki herkes tarafından okunabilir.",
                  "WPA2/WPA3 parolası ekleyin; açık ağda mutlaka VPN kullanın."))
    elif s == "WEP":
        f.append(("crit", "WEP eski ve kırılmış bir şifreleme; dakikalar içinde çözülebilir.",
                  "Cihazı WPA2-AES (CCMP) veya WPA3'e geçirin."))
    elif s == "WPA (TKIP)":
        f.append(("high", "WPA1/TKIP zayıf kabul edilir.", "WPA2-AES (CCMP) ya da WPA3 kullanın."))
    elif s == "WPA2-TKIP":
        f.append(("med", "WPA2 ama yalnızca TKIP şifreleme: zayıf.", "Şifrelemeyi AES (CCMP) olarak değiştirin."))
    elif s == "OWE":
        f.append(("low", "OWE: şifreli ama kimlik doğrulamasız (sahte AP'ye karşı koruma yok).",
                  "Mümkünse WPA3-SAE kullanın."))
    elif s == "WPA2-PSK":
        f.append(("ok", "WPA2-PSK: yeterli; parola gücü belirleyicidir.", "Uzun (12+ karakter) rastgele parola; mümkünse WPA3."))
    elif s in ("WPA3-SAE", "WPA2/WPA3", "WPA2-Enterprise", "WPA3-Enterprise"):
        f.append(("ok", f"{s}: güçlü güvenlik.", ""))
    if ap.tkip and s not in ("WPA (TKIP)", "WPA2-TKIP", "Açık", "WEP"):
        f.append(("low", "TKIP uyumluluk modu açık.", "Tüm cihazlar destekliyorsa yalnızca AES bırakın."))
    if ap.wps and not ap.wps_locked and s not in ("Açık",):
        f.append(("med", "WPS etkin ve kilitsiz: PIN yöntemi zayıflık barındırabilir.", "Yönetim panelinden WPS'yi kapatın."))
    if s in ("WPA2-PSK", "WPA2-TKIP", "WPA (TKIP)") and ap.pmf == 0:
        f.append(("low", "Yönetim çerçeveleri korunmuyor (PMF/802.11w yok).", "Yönlendiricide PMF'yi 'destekli/zorunlu' yapın."))
    if ap.hidden:
        f.append(("low", "Gizli SSID: güvenlik sağlamaz, istemciler adı sürekli yayınlar.", "Gizlemek yerine güçlü şifreleme kullanın."))
    if ap.ssid and _DEFAULT_SSID.match(ap.ssid):
        f.append(("low", "Üretici varsayılanına benzeyen SSID adı.", "Yönetici parolasını ve SSID'yi değiştirin."))
    return f


SEV_RANK = {"crit": 4, "high": 3, "med": 2, "low": 1, "ok": 0}
SEV_COLOR = {"crit": "#ff453a", "high": "#ff9f0a", "med": "#ffd60a", "low": "#8ab4f8", "ok": "#3ddc84"}
SEV_NAME = {"crit": "KRİTİK", "high": "YÜKSEK", "med": "ORTA", "low": "DÜŞÜK", "ok": "İYİ"}


def analyze_rogue(aps, trusted):
    """Evil Twin / sahte AP şüphesi. trusted: {ssid: [bssid,...]} -> [(key, seviye, bssids, metin)]"""
    by = defaultdict(list)
    for a in aps:
        if a.ssid and not a.hidden:
            by[a.ssid].append(a)
    out = []
    for ssid, lst in by.items():
        weak = [a for a in lst if a.risk >= 3]
        strong = [a for a in lst if a.risk <= 1]
        if weak and strong:
            out.append((f"twin:{ssid}", "crit", [a.bssid for a in weak],
                        f"'{ssid}' adı hem korumalı hem '{weak[0].security}' olarak yayınlanıyor: "
                        f"Evil Twin (sahte AP) şüphesi"))
        tb = {b.lower() for b in trusted.get(ssid, [])}
        if tb:
            for a in lst:
                if a.bssid not in tb:
                    out.append((f"unk:{ssid}:{a.bssid}", "crit", [a.bssid],
                                f"Güvendiğiniz '{ssid}' ağını taklit eden bilinmeyen BSSID: {a.bssid} "
                                f"({a.vendor or '?'}, kanal {a.channel})"))
    return out


# ------------------------------------------------------------ izleyici (yeni/kayıp ağ, geçmiş, olaylar)
@dataclass
class Event:
    t: float
    level: str       # info | warn | crit
    text: str
    key: str = ""


class Rec:
    def __init__(self, ap, now):
        self.ap = ap
        self.first = self.last = now
        self.hist = deque(maxlen=1800)
        self.ema = ap.signal
        self.mn = self.mx = ap.signal
        self.alive = True
        self.n = 0
        self.last_t = 0.0


class Tracker:
    LOST_AFTER = 20.0
    STALE_MS = 30000

    def __init__(self, trusted=None):
        self.recs = {}
        self.trusted = trusted if trusted is not None else {}
        self._reported = set()
        self.findings = []
        self.first_scan = True

    def alive(self):
        return [r for r in self.recs.values() if r.alive]

    def update(self, aps, now, interval=5.0):
        ev, seen = [], set()
        fresh_ms = max(interval * 1500.0, 4000.0)
        for ap in aps:
            if ap.age_ms is not None and ap.age_ms > self.STALE_MS:
                continue
            seen.add(ap.bssid)
            rec = self.recs.get(ap.bssid)
            if rec is None:
                rec = self.recs[ap.bssid] = Rec(ap, now)
                if not self.first_scan:
                    lvl = "warn" if ap.risk >= 4 else "info"
                    name = ap.ssid or "(gizli)"
                    ev.append(Event(now, lvl, f"Yeni ağ: {name} · {ap.bssid} · kn {ap.channel} · "
                                              f"{ap.signal:.0f} dBm · {ap.security}", f"new:{ap.bssid}"))
            else:
                rec.ap = ap
                if not rec.alive:
                    rec.alive = True
                    ev.append(Event(now, "info", f"Yeniden göründü: {ap.ssid or '(gizli)'} · {ap.bssid}",
                                    f"back:{ap.bssid}"))
            rec.last = now
            if ap.age_ms is None or ap.age_ms <= fresh_ms:
                t = now - (ap.age_ms or 0) / 1000.0
                if t > rec.last_t:
                    rec.hist.append((t, ap.signal))
                    rec.last_t = t
                    rec.ema = ap.signal if rec.n == 0 else rec.ema * 0.6 + ap.signal * 0.4
                    rec.mn, rec.mx = min(rec.mn, ap.signal), max(rec.mx, ap.signal)
                    rec.n += 1
        for b, rec in self.recs.items():
            if rec.alive and b not in seen and now - rec.last > self.LOST_AFTER:
                rec.alive = False
                ev.append(Event(now, "info", f"Ağ kayboldu: {rec.ap.ssid or '(gizli)'} · {b}", f"lost:{b}"))
        self.findings = analyze_rogue([r.ap for r in self.alive()], self.trusted)
        for key, lvl, bssids, text in self.findings:
            if key not in self._reported:
                self._reported.add(key)
                ev.append(Event(now, lvl, text, key))
        self.first_scan = False
        return ev


# ------------------------------------------------------------ filtre / sıralama
SORT_KEYS = {
    "signal": lambda r: r.ema,
    "ssid": lambda r: (r.ap.ssid.lower() or "\uffff", -r.ema),
    "channel": lambda r: (r.ap.band, r.ap.channel, -r.ema),
    "risk": lambda r: (r.ap.risk, r.ema),
    "vendor": lambda r: (r.ap.vendor.lower(), -r.ema),
    "bssid": lambda r: r.ap.bssid,
    "clients": lambda r: r.ap.stations if r.ap.stations is not None else -1,
}


def filter_sort(recs, text="", band="", weak_only=False, hidden_only=False, key="signal", desc=True):
    t = text.strip().lower()
    res = []
    for r in recs:
        a = r.ap
        if band and a.band != band:
            continue
        if weak_only and a.risk < 3:
            continue
        if hidden_only and not a.hidden:
            continue
        if t and t not in (a.ssid.lower() + " " + a.bssid + " " + a.vendor.lower() + " " + a.security.lower()):
            continue
        res.append(r)
    res.sort(key=SORT_KEYS.get(key, SORT_KEYS["signal"]), reverse=desc)
    return res


# ------------------------------------------------------------ dışa aktarma
EXPORT_COLS = ["ssid", "bssid", "signal", "quality", "channel", "freq", "band", "width", "security", "std",
               "vendor", "stations", "util", "wps", "hidden", "country", "distance_m"]


def ap_row(a):
    return {"ssid": a.ssid or "(gizli)", "bssid": a.bssid, "signal": round(a.signal, 1),
            "quality": quality_pct(a.signal), "channel": a.channel, "freq": a.freq, "band": a.band,
            "width": a.width, "security": a.security, "std": STD_NAMES.get(a.std, a.std), "vendor": a.vendor,
            "stations": "" if a.stations is None else a.stations, "util": "" if a.util is None else a.util,
            "wps": a.wps, "hidden": a.hidden, "country": a.country,
            "distance_m": round(est_distance(a.signal, a.freq), 1)}


def export_csv(aps):
    buf = io.StringIO()
    w = csv.DictWriter(buf, fieldnames=EXPORT_COLS)
    w.writeheader()
    for a in sorted(aps, key=lambda x: -x.signal):
        w.writerow(ap_row(a))
    return buf.getvalue()


def export_json(aps):
    return json.dumps({"app": f"{APP_NAME} {APP_VERSION}", "time": time.strftime("%Y-%m-%d %H:%M:%S"),
                       "networks": [ap_row(a) for a in sorted(aps, key=lambda x: -x.signal)]},
                      ensure_ascii=False, indent=2)


def export_markdown(aps, findings, iface=""):
    lines = [f"# Kablosuz Ortam Raporu — {APP_NAME} {APP_VERSION}", "",
             f"- Tarih: {time.strftime('%Y-%m-%d %H:%M:%S')}", f"- Arayüz: {iface or '-'}",
             f"- Ağ sayısı: {len(aps)}", ""]
    for b in ("2.4", "5", "6"):
        n = sum(1 for a in aps if a.band == b)
        if n:
            lines.append(f"- {BAND_NAMES[b]}: {n} ağ")
            res = rate_channels(aps, b)
            if res["best"]:
                lines.append(f"  - Önerilen kanal: **{res['best']['ch']}** (girişim puanı {res['best']['score']})")
    lines += ["", "## Ağlar", "", "| SSID | BSSID | dBm | Kn | Bant | Güvenlik | Üretici |", "|---|---|---|---|---|---|---|"]
    for a in sorted(aps, key=lambda x: -x.signal):
        lines.append(f"| {a.ssid or '(gizli)'} | {a.bssid} | {a.signal:.0f} | {a.channel} | "
                     f"{BAND_NAMES.get(a.band, a.band)} | {a.security} | {a.vendor} |")
    lines += ["", "## Güvenlik bulguları", ""]
    any_f = False
    for a in sorted(aps, key=lambda x: -x.risk):
        for sev, text, advice in audit_ap(a):
            if sev in ("crit", "high", "med"):
                any_f = True
                lines.append(f"- **{SEV_NAME[sev]}** · {a.ssid or '(gizli)'} ({a.bssid}): {text}"
                             + (f" _Öneri: {advice}_" if advice else ""))
    if not any_f:
        lines.append("- Önemli bulgu yok.")
    if findings:
        lines += ["", "## Sahte AP / Evil Twin şüpheleri", ""]
        lines += [f"- **{SEV_NAME.get(lvl, lvl)}**: {text}" for _k, lvl, _b, text in findings]
    return "\n".join(lines) + "\n"


# ------------------------------------------------------------ Geiger (sesli bulucu)
def geiger_interval_ms(dbm):
    t = max(0.0, min(1.0, (dbm + 100.0) / 60.0))
    return int(70 + 1100 * (1 - t) ** 1.3)


def geiger_pitch_index(dbm, n=5):
    t = max(0.0, min(1.0, (dbm + 100.0) / 60.0))
    return min(n - 1, int(t * n))


def write_click_wav(path, freq, ms=45, rate=44100):
    n = int(rate * ms / 1000)
    frames = bytearray()
    for i in range(n):
        env = math.exp(-5.0 * i / n)
        frames += struct.pack("<h", int(14000 * env * math.sin(2 * math.pi * freq * i / rate)))
    with wave.open(path, "wb") as w:
        w.setnchannels(1)
        w.setsampwidth(2)
        w.setframerate(rate)
        w.writeframes(bytes(frames))


# ------------------------------------------------------------ grafik geometrisi (Qt'siz → test edilebilir)
GAUGE_MIN, GAUGE_MAX = -100.0, -40.0
GAUGE_SEGMENTS = [(-100.0, -90.0, "#8b949e"), (-90.0, -67.0, "#ffd60a"), (-67.0, -40.0, "#3ddc84")]


def gauge_angle(dbm):
    v = max(GAUGE_MIN, min(GAUGE_MAX, dbm))
    return 180.0 * (1.0 - (v - GAUGE_MIN) / (GAUGE_MAX - GAUGE_MIN))


def gauge_geometry(w, h, dbm):
    """Yarım daire kadran (pivot altta ortada). Açılar matematiksel: 180°=sol(-100), 0°=sağ(-40)."""
    cy = h - 84.0
    r = max(40.0, min(w / 2.0 - 40.0, cy - 36.0))
    cx = w / 2.0
    thick = r * 0.15
    segs, bright = [], []
    for v0, v1, col in GAUGE_SEGMENTS:
        a0, a1 = gauge_angle(v0), gauge_angle(v1)
        segs.append({"start": a1, "span": a0 - a1, "color": col})
        top = min(v1, dbm)
        if top > v0:
            b1 = gauge_angle(top)
            bright.append({"start": b1, "span": a0 - b1, "color": col})
    ticks = []
    for v in range(-100, -39, 10):
        a = math.radians(gauge_angle(v))
        ticks.append({"v": v, "x1": cx + (r + 3) * math.cos(a), "y1": cy - (r + 3) * math.sin(a),
                      "x2": cx + (r + 10) * math.cos(a), "y2": cy - (r + 10) * math.sin(a),
                      "lx": cx + (r + 24) * math.cos(a), "ly": cy - (r + 24) * math.sin(a)})
    na = math.radians(gauge_angle(dbm))
    L = (r - thick) * 0.96
    return {"cx": cx, "cy": cy, "r": r, "thick": thick, "segs": segs, "bright": bright, "ticks": ticks,
            "needle": (cx, cy, cx + L * math.cos(na), cy - L * math.sin(na)), "text_y": cy + 20.0}


def _nice_labels(items, width_px, min_gap=26):
    """items: [(x, label)] → sığmayanları ele."""
    out, last = [], -1e9
    for x, lab in items:
        if x - last >= min_gap:
            out.append((x, lab))
            last = x
    return out


YMIN, YMAX = -100.0, -20.0


def point_in_poly(x, y, poly):
    inside = False
    n = len(poly)
    j = n - 1
    for i in range(n):
        xi, yi = poly[i]
        xj, yj = poly[j]
        if (yi > y) != (yj > y) and x < (xj - xi) * (y - yi) / (yj - yi + 1e-12) + xi:
            inside = not inside
        j = i
    return inside


def channel_graph_geometry(w, h, aps, band, selected=None):
    L, R, T, B = 52.0, 16.0, 16.0, 38.0
    pw, ph = w - L - R, h - T - B
    lo, hi = BAND_RANGE[band]

    def X(f):
        return L + (f - lo) / (hi - lo) * pw

    def Y(d):
        return T + (YMAX - d) / (YMAX - YMIN) * ph

    ygrid = [(Y(v), f"{v}") for v in range(-100, -19, 10)]
    ticks = [(X(channel_to_freq(c, band)), str(c)) for c in BAND_CHANNELS[band]]
    xticks = _nice_labels(ticks, pw, 24 if band != "6" else 30)
    curves, placed = [], []
    members = sorted([a for a in aps if a.band == band], key=lambda a: a.signal)
    for a in members:
        c = a.center or a.freq
        hw = max(a.width, 20) / 2.0 + (1.0 if band == "2.4" else 0.0)
        poly, N = [], 28
        for i in range(N + 1):
            t = -1 + 2.0 * i / N
            dbm = YMIN + (a.signal - YMIN) * (1 - t * t)
            poly.append((X(c + t * hw), Y(dbm)))
        poly = [(X(c - hw), Y(YMIN))] + poly + [(X(c + hw), Y(YMIN))]
        apex = (X(c), Y(a.signal))
        curves.append({"bssid": a.bssid, "color": ap_color(a.bssid), "poly": poly, "apex": apex,
                       "label": a.ssid or "(gizli)", "selected": a.bssid == selected, "signal": a.signal})
    for cv in sorted(curves, key=lambda c: c["apex"][1]):               # etiket çakışmasını önle
        tw = len(cv["label"]) * 6.4 + 6
        x0, y0 = cv["apex"][0] - tw / 2, cv["apex"][1] - 16
        for _ in range(7):
            if any(x0 < px + pw_ and px < x0 + tw and y0 < py + 13 and py < y0 + 13 for px, py, pw_ in placed):
                y0 -= 13
            else:
                break
        y0 = max(y0, T)
        placed.append((x0, y0, tw))
        cv["label_pos"] = (cv["apex"][0], y0 + 11)
    return {"plot": (L, T, pw, ph), "ygrid": ygrid, "xticks": xticks, "curves": curves,
            "x_label_y": T + ph + 24}


def time_graph_geometry(w, h, series, now, window=180.0, selected=None):
    """series: {bssid: (etiket, renk, [(t, dbm)...])}"""
    L, R, T, B = 52.0, 16.0, 16.0, 30.0
    pw, ph = w - L - R, h - T - B

    def X(t):
        return L + (1.0 - (now - t) / window) * pw

    def Y(d):
        return T + (YMAX - d) / (YMAX - YMIN) * ph

    lines = []
    for b, (label, color, pts) in series.items():
        poly = [(X(t), Y(max(YMIN, min(YMAX, d)))) for t, d in pts if now - t <= window]
        if poly:
            lines.append({"bssid": b, "label": label, "color": color, "poly": poly, "selected": b == selected})
    xt = [(X(now - s), "şimdi" if s == 0 else f"-{s // 60}:{s % 60:02d}") for s in range(0, int(window) + 1, 30)]
    return {"plot": (L, T, pw, ph), "ygrid": [(Y(v), f"{v}") for v in range(-100, -19, 10)], "xticks": xt,
            "lines": lines}


# ------------------------------------------------------------ demo (gerçek Wi-Fi olmadan deneme)
class DemoWorld:
    """Ekran görüntüsündekine benzer, sinyali dalgalanan sahte ağlar."""
    SPEC = [
        ("home", "00:22:b0:77:7f:6a", 2462, -52, "WPA2-PSK", 40, 3, 52, True),
        ("Netcore1", "08:10:76:27:26:3c", 2437, -55, "WPA2-PSK", 20, 1, 30, False),
        ("TP-LINK_44C950", "40:16:9f:44:c9:50", 2437, -81, "WPA2-PSK", 20, 0, 12, False),
        ("Tenda_597638", "c8:3a:35:59:76:38", 2427, -79, "WPA2-PSK", 20, 2, 22, False),
        ("TP-LINK_5F476C", "38:83:45:5f:47:6c", 2412, -81, "WPA2-PSK", 20, 0, 9, False),
        ("waowaozhenzhen77", "5c:63:bf:ab:aa:70", 2437, -86, "WPA2-TKIP", 20, 0, 5, False),
        ("cll", "08:10:76:14:e9:68", 2442, -88, "WPA2-PSK", 20, 0, 6, False),
        ("Kafe_Misafir", "f4:f2:6d:11:22:33", 2462, -66, "Açık", 20, 4, 40, False),
        ("home", "02:de:ad:be:ef:01", 2412, -61, "Açık", 20, None, None, False),     # demo: sahte ikiz
        ("Ofis-5G", "9c:5c:8e:aa:10:01", 5180, -58, "WPA3-SAE", 80, 7, 34, False),
        ("Ofis-5G", "9c:5c:8e:aa:10:02", 5745, -64, "WPA3-SAE", 80, 4, 21, False),
        ("DIRECT-roku", "ae:5c:8e:00:10:44", 5220, -72, "WPA2-PSK", 40, 1, 15, False),
        ("", "70:4f:57:12:34:56", 5500, -77, "WPA2-PSK", 20, 0, 8, False),
        ("Evim_Mesh", "b0:be:76:21:cd:09", 5805, -70, "WPA2/WPA3", 80, 2, 18, False),
    ]

    def __init__(self, seed=7):
        import random
        self.rnd = random.Random(seed)
        self.phase = {s[1]: self.rnd.uniform(0, 6.28) for s in self.SPEC}
        self.t0 = time.time()

    def poll(self):
        t = time.time() - self.t0
        out = []
        for ssid, bssid, f, sig, sec, width, sta, util, assoc in self.SPEC:
            wob = 3.2 * math.sin(t / 3.0 + self.phase[bssid]) + self.rnd.uniform(-1.2, 1.2)
            band = band_of(f)
            center = f
            if width == 40:
                center = f - 10 if (band == "2.4" and f >= 2452) else f + 10   # kn 9-13 → ikincil kanal altta
            elif width == 80:
                center = {5180: 5210, 5745: 5775, 5805: 5775}.get(f, f)
            risk = {"Açık": 4, "WEP": 4, "WPA (TKIP)": 3, "WPA2-TKIP": 2, "WPA2-PSK": 1}.get(sec, 0)
            out.append(AP(bssid=bssid, ssid=ssid, hidden=(ssid == ""), freq=f, channel=freq_to_channel(f),
                          band=band, signal=round(sig + wob, 1), width=width, center=center, security=sec,
                          risk=risk, tkip=("TKIP" in sec), pmf=1 if sec.startswith("WPA3") else 0,
                          wps=(ssid in ("home", "TP-LINK_44C950")), std="ax" if band == "5" and width == 80
                          else "n" if width >= 40 else "g" if band == "2.4" else "ac",
                          stations=sta, util=None if util is None else float(util), country="TR",
                          age_ms=self.rnd.randint(50, 900), associated=assoc, beacon=100))
        return out
# --- PURE END ---------------------------------------------------------------


# ------------------------------------------------------------------ Parrot logosu
# parrotsec-logo.svg'den birebir (QtSvg gerekmez; 175x175 tasarım alanı)
_LOGO_CIRCLE = (87.5, 87.5, 87.5, "#15E0ED")
_LOGO_GRAD = (61.3272, 97.5719, 167.614, 91.5736)
_LOGO_STOPS = [
    (0, "#000000", 0.9),
    (0.0856376, "#000909", 0.8229),
    (0.2278, "#002023", 0.695),
    (0.4089, "#00464C", 0.532),
    (0.6218, "#007A85", 0.3404),
    (0.8587, "#00BCCD", 0.1271),
    (1, "#00E7FC", 0),
]
_LOGO_SHADOW = [
    (60.6, 31.7), (141.9, 19), (146.8, 23.2), (149.4, 25.6), (153.4, 30),
    (156.3, 33.5), (159.3, 37.5), (162, 41.6), (164.4, 45.8), (166.2, 49.3),
    (168.2, 53.7), (169.9, 58.1), (171.5, 62.8), (172.9, 68.6), (174, 73.9),
    (174.5, 78.4), (175, 83.7), (175, 89.9), (174.7, 94.3), (174.1, 100),
    (173.4, 104.4), (171.9, 110.6), (170, 116.7), (168.5, 120.8), (166.7, 124.7),
    (164.9, 128.3), (162.7, 132.2), (160.3, 136.1), (156.8, 141), (154.4, 143.9),
    (150.4, 148.3), (146.2, 152.4), (141.1, 156.7), (135.8, 160.4), (132.8, 162.4),
    (128.3, 164.9), (121.7, 168.2), (116.6, 162.4), (80.6, 122.1), (54.6, 61.3),
]
_LOGO_BIRD = [
    (80.6, 122.1), (116.6, 162.4), (104.6, 137.2), (115.8, 148.9), (79.3, 83),
    (95, 63.4), (153.7, 39.1), (95, 40.4), (133.2, 20.3), (60.6, 31.7),
    (54.6, 61.3), (25.3, 63.2), (20.2, 88.3), (34.9, 76.3),
]


def paint_logo(p, x, y, size):
    p.save()
    p.setRenderHint(QPainter.Antialiasing)
    p.translate(x, y)
    p.scale(size / 175.0, size / 175.0)
    p.setPen(Qt.NoPen)
    cx, cy, r, col = _LOGO_CIRCLE
    p.setBrush(QColor(col))
    p.drawEllipse(QPointF(cx, cy), r, r)
    gx1, gy1, gx2, gy2 = _LOGO_GRAD
    g = QLinearGradient(gx1, gy1, gx2, gy2)
    for off, hexcol, alpha in _LOGO_STOPS:
        cc = QColor(hexcol)
        cc.setAlphaF(alpha)
        g.setColorAt(off, cc)
    p.setBrush(QBrush(g))
    p.drawPolygon(QPolygonF([QPointF(a, b) for a, b in _LOGO_SHADOW]))
    p.setBrush(QColor("#000000"))
    p.drawPolygon(QPolygonF([QPointF(a, b) for a, b in _LOGO_BIRD]))
    p.restore()


def logo_pixmap(size, dpr=2.0):
    pm = QPixmap(int(size * dpr), int(size * dpr))
    pm.fill(Qt.transparent)
    pm.setDevicePixelRatio(dpr)
    p = QPainter(pm)
    paint_logo(p, 0, 0, size)
    p.end()
    return pm


def logo_icon():
    ic = QIcon()
    for s in (16, 24, 32, 48, 64, 128):
        ic.addPixmap(logo_pixmap(s, 1.0))
    return ic


# ------------------------------------------------------------------ tarama (iş parçacığı)
def run_cmd(args, timeout=8):
    try:
        r = subprocess.run(args, capture_output=True, text=True, errors="replace", timeout=timeout,
                           env={**os.environ, "LC_ALL": "C", "LANG": "C"})
        return r.returncode, r.stdout, r.stderr
    except FileNotFoundError:
        return 127, "", "bulunamadı"
    except subprocess.TimeoutExpired:
        return 124, "", "zaman aşımı"


def list_wifi_ifaces():
    """[(ad, tür)] - önce `iw dev`, olmazsa /sys."""
    rc, out, _ = run_cmd(["iw", "dev"], 4)
    ifs = parse_iw_dev(out) if rc == 0 else []
    if not ifs:
        try:
            for n in sorted(os.listdir("/sys/class/net")):
                if os.path.isdir(f"/sys/class/net/{n}/wireless") or os.path.isdir(f"/sys/class/net/{n}/phy80211"):
                    ifs.append((n, "managed"))
        except OSError:
            pass
    return ifs


class ScanWorker(QObject):
    """Arka planda döngüyle tarar; sonucu `result` sinyaliyle ana iş parçacığına yollar."""
    result = pyqtSignal(object)

    def __init__(self, iface="", interval=5.0, demo=False):
        super().__init__()
        self.iface, self.interval, self.demo = iface, float(interval), demo
        self.world = DemoWorld() if demo else None
        self.paused = False
        self._stop = threading.Event()
        self._wake = threading.Event()
        self._thread = None

    def start(self):
        self._thread = threading.Thread(target=self._loop, daemon=True)
        self._thread.start()

    def stop(self):
        self._stop.set()
        self._wake.set()

    def scan_now(self):
        self._wake.set()

    def set_demo(self, on):
        self.demo = bool(on)
        self.world = DemoWorld() if on else None
        self._wake.set()

    def _loop(self):
        while not self._stop.is_set():
            if not self.paused:
                try:
                    self.result.emit(self.cycle())
                except Exception as e:                       # tarama hatası arayüzü düşürmesin
                    self.result.emit({"aps": [], "source": "", "link": {}, "iface": self.iface,
                                      "error": f"Tarama hatası: {e}", "time": time.time()})
            self._wake.wait(self.interval)
            self._wake.clear()

    def cycle(self):
        res = {"aps": [], "source": "", "link": {}, "iface": self.iface, "error": "", "time": time.time()}
        if self.demo:
            aps = self.world.poll()
            res.update(aps=aps, source="demo", iface="demo0")
            for a in aps:
                if a.associated:
                    res["link"] = {"bssid": a.bssid, "ssid": a.ssid, "signal": str(int(a.signal)), "tx": "72.2"}
            return res
        iface = self.iface
        if not iface:
            ifs = [i for i in list_wifi_ifaces() if i[1] != "monitor"] or list_wifi_ifaces()
            if not ifs:
                res["error"] = "Wi-Fi arayüzü bulunamadı"
                return res
            iface = ifs[0][0]
        res["iface"] = iface
        for n, t in list_wifi_ifaces():
            if n == iface and t == "monitor":
                res["error"] = f"{iface} monitor modunda: listeleme için 'managed' mod gerekir"
                return res
        text, source = "", ""
        if os.geteuid() == 0:                                           # root: taze, bloklayan tarama
            rc, out, _ = run_cmd(["iw", "dev", iface, "scan"], 20)
            if rc == 0 and "BSS " in out:
                text, source = out, "iw scan (root)"
        if not text:
            if shutil.which("nmcli"):                                   # yetkisiz: NetworkManager'dan tarama iste
                run_cmd(["nmcli", "device", "wifi", "rescan", "ifname", iface], 5)
            rc, out, _ = run_cmd(["iw", "dev", iface, "scan", "dump"], 8)
            if rc == 127:
                res["error"] = "iw bulunamadı (sudo apt install iw)"
            elif "BSS " in out:
                text, source = out, "iw dump"
        aps = parse_iw_scan(text) if text else []
        if not aps and shutil.which("nmcli"):
            base = ["nmcli", "-t", "-f"]
            tail = ["dev", "wifi", "list", "ifname", iface, "--rescan", "no"]
            rc, out, _ = run_cmd(base + ["IN-USE,BSSID,SSID,MODE,CHAN,FREQ,RATE,BANDWIDTH,SIGNAL,SECURITY"] + tail, 8)
            with_bw = True
            if rc != 0 or not out.strip():
                rc, out, _ = run_cmd(base + ["IN-USE,BSSID,SSID,MODE,CHAN,FREQ,RATE,SIGNAL,SECURITY"] + tail, 8)
                with_bw = False
            aps = parse_nmcli(out, with_bw)
            source = "nmcli" if aps else source
        if not aps and not res["error"]:
            res["error"] = "Ağ bulunamadı (arayüz kapalı mı? Wi-Fi etkin mi?)"
        res["aps"], res["source"] = aps, source
        rc, out, _ = run_cmd(["iw", "dev", iface, "link"], 4)
        res["link"] = parse_iw_link(out) if rc == 0 else {}
        return res


# ------------------------------------------------------------------ Geiger (sesli bulucu)
class ClickPlayer:
    FREQS = (650, 850, 1100, 1400, 1800)

    def __init__(self):
        self.dir = tempfile.mkdtemp(prefix="pwsn-")
        self.paths = []
        for i, f in enumerate(self.FREQS):
            p = os.path.join(self.dir, f"c{i}.wav")
            write_click_wav(p, f)
            self.paths.append(p)
        self.effects = []
        try:
            from PyQt5.QtMultimedia import QSoundEffect
            for p in self.paths:
                e = QSoundEffect()
                e.setSource(QUrl.fromLocalFile(p))
                e.setVolume(0.7)
                self.effects.append(e)
        except Exception:
            self.effects = []
        self.ext = None if self.effects else (shutil.which("paplay") or shutil.which("pw-play") or shutil.which("aplay"))
        self._last = 0.0

    def play(self, idx):
        if self.effects:
            self.effects[idx].play()
        elif self.ext:
            now = time.monotonic()
            if now - self._last < 0.09:                                 # süreç başlatmayı sınırla
                return
            self._last = now
            try:
                subprocess.Popen([self.ext, self.paths[idx]], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
            except OSError:
                pass
        else:
            QApplication.beep()

    def cleanup(self):
        shutil.rmtree(self.dir, ignore_errors=True)


class Geiger(QObject):
    def __init__(self):
        super().__init__()
        self.player = None
        self.dbm = None
        self.on = False
        self.timer = QTimer(self)
        self.timer.setSingleShot(True)
        self.timer.timeout.connect(self._tick)

    def set_enabled(self, on):
        self.on = bool(on)
        if self.on:
            if self.player is None:
                self.player = ClickPlayer()
            self.timer.start(50)
        else:
            self.timer.stop()

    def set_level(self, dbm):
        self.dbm = dbm

    def _tick(self):
        if not self.on:
            return
        if self.dbm is not None:
            self.player.play(geiger_pitch_index(self.dbm, len(ClickPlayer.FREQS)))
            self.timer.start(geiger_interval_ms(self.dbm))
        else:
            self.timer.start(400)

    def shutdown(self):
        self.timer.stop()
        if self.player:
            self.player.cleanup()


# ------------------------------------------------------------------ çizim bileşenleri
def _font(px, bold=False):
    f = QFont()
    try:
        f.setFamilies(["Arial", "Liberation Sans", "Arimo", "Helvetica", "DejaVu Sans"])
    except AttributeError:
        f.setFamily("Arial")
    f.setPixelSize(px)
    f.setBold(bold)
    return f


def _qc(hexcol, alpha=255):
    c = QColor(hexcol)
    c.setAlpha(alpha)
    return c


class SignalBarDelegate(QStyledItemDelegate):
    """Tablodaki sinyal sütunu: renkli çubuk + dBm."""

    def paint(self, painter, option, index):
        dbm = index.data(Qt.UserRole)
        if dbm is None:
            return super().paint(painter, option, index)
        painter.save()
        painter.setRenderHint(QPainter.Antialiasing)
        if option.state & QStyle.State_Selected:
            painter.fillRect(option.rect, option.palette.highlight())
        r = QRectF(option.rect.adjusted(4, 5, -4, -5))
        painter.setPen(Qt.NoPen)
        painter.setBrush(QColor(255, 255, 255, 22))
        painter.drawRoundedRect(r, 3, 3)
        w = max(4.0, r.width() * quality_pct(dbm) / 100.0)
        painter.setBrush(QColor(signal_color(dbm)))
        painter.drawRoundedRect(QRectF(r.x(), r.y(), w, r.height()), 3, 3)
        painter.setPen(QColor("#f0f6fc"))
        painter.setFont(_font(11, True))
        painter.drawText(r.adjusted(6, 0, 0, 0), Qt.AlignVCenter | Qt.AlignLeft, f"{round(dbm)} dBm")
        painter.restore()

    def sizeHint(self, option, index):
        return QSize(120, 26)


class Card(QWidget):
    """Koyu zeminli, yuvarlak çerçeveli çizim alanı tabanı."""

    def paintBackground(self, p):
        p.setRenderHint(QPainter.Antialiasing)
        p.setPen(QPen(QColor(255, 255, 255, 28), 1))
        p.setBrush(QColor("#0b0f14"))
        p.drawRoundedRect(QRectF(0.5, 0.5, self.width() - 1, self.height() - 1), 10, 10)


class GaugeWidget(Card):
    """Analog sinyal ölçer (yarım daire, -100…-40 dBm)."""

    def __init__(self):
        super().__init__()
        self.setMinimumSize(300, 230)
        self.target, self.shown = None, -100.0
        self.title, self.sub = "AP seçilmedi", ""
        self.timer = QTimer(self)
        self.timer.timeout.connect(self._anim)
        self.timer.start(33)

    def set_value(self, dbm, title, sub=""):
        self.target, self.title, self.sub = dbm, title, sub

    def _anim(self):
        goal = -100.0 if self.target is None else self.target
        d = goal - self.shown
        if abs(d) > 0.04:
            self.shown += d * 0.22
            self.update()

    def paintEvent(self, _):
        p = QPainter(self)
        self.paintBackground(p)
        g = gauge_geometry(self.width(), self.height(), self.shown)
        cx, cy, r, th = g["cx"], g["cy"], g["r"], g["thick"]
        rm = r - th / 2.0
        box = QRectF(cx - rm, cy - rm, 2 * rm, 2 * rm)
        for seg, alpha in [(s, 70) for s in g["segs"]] + [(s, 255) for s in g["bright"]]:
            pen = QPen(_qc(seg["color"], alpha), th, Qt.SolidLine, Qt.FlatCap)
            p.setPen(pen)
            p.setBrush(Qt.NoBrush)
            p.drawArc(box, int(seg["start"] * 16), int(seg["span"] * 16))
        p.setFont(_font(11))
        for t in g["ticks"]:
            p.setPen(QPen(QColor("#8b949e"), 2))
            p.drawLine(QPointF(t["x1"], t["y1"]), QPointF(t["x2"], t["y2"]))
            p.setPen(QColor("#c9d1d9"))
            p.drawText(QRectF(t["lx"] - 18, t["ly"] - 8, 36, 16), Qt.AlignCenter, str(t["v"]))
        x1, y1, x2, y2 = g["needle"]
        p.setPen(QPen(QColor("#f0f6fc"), 3, Qt.SolidLine, Qt.RoundCap))
        p.drawLine(QPointF(x1, y1), QPointF(x2, y2))
        p.setPen(Qt.NoPen)
        p.setBrush(QColor("#f0f6fc"))
        p.drawEllipse(QPointF(x1, y1), 7, 7)
        if self.target is not None:
            p.setPen(QColor(signal_color(self.target)))
            p.setFont(_font(30, True))
            p.drawText(QRectF(0, g["text_y"], self.width(), 38), Qt.AlignCenter, f"{round(self.target)} dBm")
            p.setPen(QColor("#8b949e"))
            p.setFont(_font(12))
            p.drawText(QRectF(0, g["text_y"] + 38, self.width(), 18), Qt.AlignCenter,
                       f"{signal_label(self.target)}  ·  %{quality_pct(self.target)}")
        # ağ adı kutusu (ekran görüntüsündeki gibi)
        p.setFont(_font(12))
        tw = min(self.width() - 24, max(120, len(self.title) * 7 + 24))
        pill = QRectF((self.width() - tw) / 2.0, self.height() - 30, tw, 22)
        p.setPen(QPen(QColor(255, 255, 255, 70), 1))
        p.setBrush(QColor(255, 255, 255, 14))
        p.drawRoundedRect(pill, 6, 6)
        p.setPen(QColor("#e6edf3"))
        p.drawText(pill, Qt.AlignCenter, p.fontMetrics().elidedText(self.title, Qt.ElideMiddle, int(tw - 12)))
        p.end()


class ChannelCanvas(Card):
    apClicked = pyqtSignal(str)

    def __init__(self):
        super().__init__()
        self.setMinimumHeight(220)
        self.setMouseTracking(True)
        self.aps, self.band, self.selected, self.geo = [], "2.4", None, None

    def set_data(self, aps, band, selected):
        self.aps, self.band, self.selected = aps, band, selected
        self.update()

    def paintEvent(self, _):
        w, h = self.width(), self.height()
        g = self.geo = channel_graph_geometry(w, h, self.aps, self.band, self.selected)
        p = QPainter(self)
        self.paintBackground(p)
        L, T, pw, ph = g["plot"]
        p.setFont(_font(10))
        for y, lab in g["ygrid"]:
            p.setPen(QPen(QColor(255, 255, 255, 26), 1))
            p.drawLine(QPointF(L, y), QPointF(L + pw, y))
            p.setPen(QColor("#8b949e"))
            p.drawText(QRectF(0, y - 8, L - 6, 16), Qt.AlignRight | Qt.AlignVCenter, lab)
        for x, lab in g["xticks"]:
            p.setPen(QPen(QColor(255, 255, 255, 14), 1))
            p.drawLine(QPointF(x, T), QPointF(x, T + ph))
            p.setPen(QColor("#8b949e"))
            p.drawText(QRectF(x - 16, T + ph + 4, 32, 14), Qt.AlignCenter, lab)
        p.setPen(QColor("#8b949e"))
        p.drawText(QRectF(L, g["x_label_y"] - 8, pw, 16), Qt.AlignCenter, f"Wi-Fi kanalları — {BAND_NAMES[self.band]}")
        p.save()
        p.translate(14, T + ph / 2.0)
        p.rotate(-90)
        p.drawText(QRectF(-60, -8, 120, 16), Qt.AlignCenter, "Sinyal (dBm)")
        p.restore()
        p.setRenderHint(QPainter.Antialiasing)
        for cv in g["curves"]:
            col = QColor(cv["color"])
            fill = QColor(col)
            fill.setAlpha(110 if cv["selected"] else 42)
            p.setPen(Qt.NoPen)
            p.setBrush(fill)
            p.drawPolygon(QPolygonF([QPointF(x, y) for x, y in cv["poly"]]))
            p.setPen(QPen(col, 3 if cv["selected"] else 1.8))
            p.setBrush(Qt.NoBrush)
            p.drawPolyline(QPolygonF([QPointF(x, y) for x, y in cv["poly"][1:-1]]))
        for cv in g["curves"]:
            p.setFont(_font(11, cv["selected"]))
            p.setPen(QColor(cv["color"]))
            lx, ly = cv["label_pos"]
            p.drawText(QRectF(lx - 90, ly - 12, 180, 14), Qt.AlignCenter, cv["label"])
        if not g["curves"]:
            p.setPen(QColor("#8b949e"))
            p.setFont(_font(13))
            p.drawText(QRectF(L, T, pw, ph), Qt.AlignCenter, f"{BAND_NAMES[self.band]} bandında ağ yok")
        p.end()

    def _hit(self, x, y):
        if not self.geo:
            return None
        for cv in reversed(self.geo["curves"]):                           # üstteki önce
            if point_in_poly(x, y, cv["poly"]):
                return cv
        return None

    def mouseMoveEvent(self, e):
        cv = self._hit(e.x(), e.y())
        if cv:
            QToolTip.showText(e.globalPos(), f"{cv['label']}\n{cv['bssid']}\n{cv['signal']:.0f} dBm", self)
        else:
            QToolTip.hideText()

    def mousePressEvent(self, e):
        cv = self._hit(e.x(), e.y())
        if cv:
            self.apClicked.emit(cv["bssid"])


class TimeCanvas(Card):
    def __init__(self):
        super().__init__()
        self.setMinimumHeight(200)
        self.series, self.selected = {}, None

    def set_data(self, series, selected):
        self.series, self.selected = series, selected
        self.update()

    def paintEvent(self, _):
        g = time_graph_geometry(self.width(), self.height(), self.series, time.time(), 180.0, self.selected)
        p = QPainter(self)
        self.paintBackground(p)
        L, T, pw, ph = g["plot"]
        p.setFont(_font(10))
        for y, lab in g["ygrid"]:
            p.setPen(QPen(QColor(255, 255, 255, 26), 1))
            p.drawLine(QPointF(L, y), QPointF(L + pw, y))
            p.setPen(QColor("#8b949e"))
            p.drawText(QRectF(0, y - 8, L - 6, 16), Qt.AlignRight | Qt.AlignVCenter, lab)
        for x, lab in g["xticks"]:
            p.setPen(QColor("#8b949e"))
            p.drawText(QRectF(x - 24, T + ph + 6, 48, 14), Qt.AlignCenter, lab)
        p.setRenderHint(QPainter.Antialiasing)
        for ln in g["lines"]:
            p.setPen(QPen(QColor(ln["color"]), 3 if ln["selected"] else 1.8))
            p.drawPolyline(QPolygonF([QPointF(x, y) for x, y in ln["poly"]]))
        y = T + 6
        for ln in g["lines"]:                                             # gösterge
            p.setPen(Qt.NoPen)
            p.setBrush(QColor(ln["color"]))
            p.drawRoundedRect(QRectF(L + 8, y + 2, 10, 10), 2, 2)
            p.setPen(QColor("#c9d1d9"))
            p.drawText(QRectF(L + 24, y, 220, 14), Qt.AlignLeft | Qt.AlignVCenter, ln["label"])
            y += 16
        if not g["lines"]:
            p.setPen(QColor("#8b949e"))
            p.setFont(_font(13))
            p.drawText(QRectF(L, T, pw, ph), Qt.AlignCenter, "Veri toplanıyor…")
        p.end()


STAR_COLORS = {5: "#3ddc84", 4: "#9be564", 3: "#ffd60a", 2: "#ff9f0a", 1: "#ff453a"}


class RatingCanvas(Card):
    """Kanal başına girişim çubukları + yıldızlar."""

    def __init__(self):
        super().__init__()
        self.setMinimumHeight(220)
        self.res, self.band = None, "2.4"

    def set_data(self, res, band):
        self.res, self.band = res, band
        self.update()

    def paintEvent(self, _):
        p = QPainter(self)
        self.paintBackground(p)
        p.setRenderHint(QPainter.Antialiasing)
        w, h = self.width(), self.height()
        if not self.res or not self.res["rows"]:
            return
        rows = self.res["rows"]
        L, R, T, B = 20.0, 20.0, 46.0, 52.0
        pw, ph = w - L - R, h - T - B
        best = self.res["best"]
        p.setFont(_font(13, True))
        p.setPen(QColor(ACCENT))
        txt = f"En iyi kanal ({BAND_NAMES[self.band]}): {best['ch']}" if best else ""
        nd = self.res["best_nodfs"]
        if best and nd and nd["ch"] != best["ch"]:
            txt += f"   ·   DFS dışı en iyi: {nd['ch']}"
        p.drawText(QRectF(L, 10, pw, 22), Qt.AlignLeft | Qt.AlignVCenter, txt)
        n = len(rows)
        slot = pw / n
        bw = min(34.0, slot * 0.62)
        p.setFont(_font(10))
        for i, r in enumerate(rows):
            x = L + i * slot + (slot - bw) / 2.0
            frac = min(1.0, r["score"] / 3.0)
            bh = max(3.0, frac * ph)
            col = QColor(STAR_COLORS[r["stars"]])
            if best and r["ch"] == best["ch"]:
                p.setPen(QPen(QColor(ACCENT), 2))
            else:
                p.setPen(Qt.NoPen)
            col.setAlpha(210)
            p.setBrush(col)
            p.drawRoundedRect(QRectF(x, T + ph - bh, bw, bh), 3, 3)
            p.setPen(QColor("#c9d1d9"))
            lab = str(r["ch"]) + ("*" if r["dfs"] else "")
            p.drawText(QRectF(x - 8, T + ph + 4, bw + 16, 14), Qt.AlignCenter, lab)
            p.setPen(QColor(STAR_COLORS[r["stars"]]))
            p.drawText(QRectF(x - 8, T + ph + 18, bw + 16, 14), Qt.AlignCenter, "★" * r["stars"] if bw > 20 else str(r["stars"]))
            if r["count"]:
                p.setPen(QColor("#8b949e"))
                p.drawText(QRectF(x - 8, T + ph - bh - 16, bw + 16, 14), Qt.AlignCenter, f"{r['count']} ağ")
        p.setPen(QColor("#6e7681"))
        p.setFont(_font(10))
        extra = "  (* = DFS kanalı)" if self.band == "5" else ""
        p.drawText(QRectF(L, h - 18, pw, 14), Qt.AlignLeft | Qt.AlignVCenter,
                   "Çubuk yüksekliği = girişim (düşük iyi) · yıldız = kalite" + extra)
        p.end()


# ------------------------------------------------------------------ ayarlar
DEFAULT_CFG = {"iface": "", "interval": 5, "notify": True, "trusted": {}, "pinned": [],
               "hidden_cols": [6, 8, 10, 11, 12, 13], "sort": "signal", "desc": True, "band": "",
               "geometry": "", "splitter": [], "tab": 0}


def load_config():
    cfg = json.loads(json.dumps(DEFAULT_CFG))
    try:
        cfg.update(json.loads(CONFIG_FILE.read_text()))
    except (OSError, ValueError):
        pass
    if not isinstance(cfg.get("trusted"), dict):
        cfg["trusted"] = {}
    return cfg


def save_config(cfg):
    try:
        CONFIG_DIR.mkdir(parents=True, exist_ok=True)
        CONFIG_FILE.write_text(json.dumps(cfg, ensure_ascii=False, indent=1))
    except OSError:
        pass


def read_ip(iface):
    s = None
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        r = fcntl.ioctl(s.fileno(), 0x8915, struct.pack("256s", iface[:15].encode()))   # SIOCGIFADDR
        return socket.inet_ntoa(r[20:24])
    except OSError:
        return ""
    finally:
        if s:
            s.close()


STYLE = """
QMainWindow, QWidget { background:#0d1117; color:#c9d1d9; font-size:12px; }
QLabel { background:transparent; }
QTableWidget { background:#0b0f14; alternate-background-color:#10161d; border:1px solid #21262d;
               selection-background-color:#12353a; selection-color:#ffffff; outline:0; }
QHeaderView::section { background:#161b22; color:#8b949e; border:none; border-right:1px solid #0d1117; padding:5px 6px; }
QTabWidget::pane { border:1px solid #21262d; border-radius:6px; top:-1px; }
QTabBar::tab { background:#161b22; padding:7px 14px; margin-right:2px; color:#8b949e;
               border-top-left-radius:6px; border-top-right-radius:6px; }
QTabBar::tab:selected { background:#0d1117; color:#15E0ED; border-bottom:2px solid #15E0ED; }
QLineEdit, QComboBox, QSpinBox { background:#161b22; border:1px solid #30363d; border-radius:5px; padding:3px 6px; }
QComboBox QAbstractItemView { background:#161b22; selection-background-color:#12353a; }
QPushButton { background:#161b22; border:1px solid #30363d; border-radius:6px; padding:5px 12px; }
QPushButton:hover { border-color:#15E0ED; }
QPushButton:checked { background:#0e4a52; border-color:#15E0ED; color:#ffffff; }
QListWidget { background:#0b0f14; border:1px solid #21262d; }
QMenu { background:#161b22; border:1px solid #30363d; }
QMenu::item:selected { background:#12353a; }
QMenuBar { background:#0d1117; } QMenuBar::item:selected { background:#12353a; }
QStatusBar { background:#0b0f14; color:#8b949e; }
QCheckBox { spacing:6px; }
QSplitter::handle { background:#21262d; }
"""

COLS = [("", 22), ("SSID", 170), ("BSSID", 128), ("Sinyal", 125), ("Kn", 42), ("Bant", 62), ("Genişlik", 72),
        ("Güvenlik", 112), ("Standart", 104), ("Üretici", 150), ("İst.", 44), ("Yük", 52), ("Mesafe", 66),
        ("Görülme", 72)]
COL_SORT = {1: "ssid", 2: "bssid", 3: "signal", 4: "channel", 7: "risk", 9: "vendor", 10: "clients"}
SEV_ORDER = ["crit", "high", "med", "low"]


class MainWindow(QMainWindow):
    def __init__(self, cfg, args):
        super().__init__()
        self.cfg, self.args = cfg, args
        self.oui = OuiDb()
        self.tracker = Tracker(cfg["trusted"])
        self.selected = None
        self.link, self.source, self.error, self.iface_shown = {}, "", "", ""
        self.last_scan = 0.0
        self.chan_band = cfg.get("band") or ""
        self._offered_demo = False
        self.geiger = Geiger()
        self.worker = ScanWorker(cfg["iface"], cfg["interval"], demo=args.demo)
        self.worker.result.connect(self.on_scan)
        self.setWindowTitle(f"{APP_NAME} {APP_VERSION}")
        self.setWindowIcon(logo_icon())
        self.resize(1360, 800)
        self.build_ui()
        self.build_menu()
        self.build_tray()
        if cfg.get("geometry"):
            try:
                self.restoreGeometry(QByteArray.fromHex(cfg["geometry"].encode()))
            except Exception:
                pass
        self.worker.start()

    # ---------------------------------------------------------------- arayüz
    def build_ui(self):
        root = QWidget()
        self.setCentralWidget(root)
        v = QVBoxLayout(root)
        v.setContentsMargins(10, 8, 10, 4)
        v.setSpacing(8)

        # başlık: logo + isim + bağlantı bilgisi
        hl = QHBoxLayout()
        logo = QLabel()
        logo.setPixmap(logo_pixmap(34))
        logo.setFixedSize(34, 34)
        hl.addWidget(logo)
        title = QLabel(f'<span style="color:#f0f6fc;font-size:17px;font-weight:600">{APP_NAME}</span> '
                       f'<span style="color:{ACCENT};font-size:11px;font-weight:600">{APP_VERSION}</span>')
        title.setTextFormat(Qt.RichText)
        hl.addWidget(title)
        hl.addStretch(1)
        self.conn_lbl = QLabel()
        self.conn_lbl.setTextFormat(Qt.RichText)
        self.conn_lbl.setAlignment(Qt.AlignRight | Qt.AlignVCenter)
        hl.addWidget(self.conn_lbl)
        v.addLayout(hl)

        # kontroller
        cl = QHBoxLayout()
        cl.addWidget(QLabel("Arayüz:"))
        self.iface_box = QComboBox()
        self.iface_box.setMinimumWidth(130)
        self.fill_ifaces()
        self.iface_box.currentIndexChanged.connect(self.on_iface_changed)
        cl.addWidget(self.iface_box)
        cl.addWidget(QLabel("Tarama aralığı:"))
        self.interval = QSpinBox()
        self.interval.setRange(2, 60)
        self.interval.setSuffix(" sn")
        self.interval.setValue(int(self.cfg["interval"]))
        self.interval.valueChanged.connect(self.on_interval)
        cl.addWidget(self.interval)
        self.pause_btn = QPushButton("⏸ Duraklat")
        self.pause_btn.setCheckable(True)
        self.pause_btn.toggled.connect(self.on_pause)
        cl.addWidget(self.pause_btn)
        scan_btn = QPushButton("⟳ Şimdi tara")
        scan_btn.clicked.connect(self.worker.scan_now)
        cl.addWidget(scan_btn)
        self.demo_chk = QCheckBox("Demo modu")
        self.demo_chk.setChecked(self.args.demo)
        self.demo_chk.toggled.connect(self.on_demo)
        cl.addWidget(self.demo_chk)
        cl.addStretch(1)
        self.count_lbl = QLabel()
        cl.addWidget(self.count_lbl)
        v.addLayout(cl)

        # orta: sol tablo, sağ sekmeler
        self.split = QSplitter(Qt.Horizontal)
        v.addWidget(self.split, 1)
        left = QWidget()
        ll = QVBoxLayout(left)
        ll.setContentsMargins(0, 0, 0, 0)
        fl = QHBoxLayout()
        self.search = QLineEdit()
        self.search.setPlaceholderText("Ara: SSID, BSSID, üretici, güvenlik…")
        self.search.setClearButtonEnabled(True)
        self.search.textChanged.connect(self.refresh_table)
        fl.addWidget(self.search, 1)
        self.band_filter = QComboBox()
        for lab, key in (("Tüm bantlar", ""), ("2.4 GHz", "2.4"), ("5 GHz", "5"), ("6 GHz", "6")):
            self.band_filter.addItem(lab, key)
        self.band_filter.currentIndexChanged.connect(self.refresh_table)
        fl.addWidget(self.band_filter)
        self.weak_chk = QCheckBox("Zayıf güvenlik")
        self.weak_chk.toggled.connect(self.refresh_table)
        fl.addWidget(self.weak_chk)
        self.hid_chk = QCheckBox("Gizli")
        self.hid_chk.toggled.connect(self.refresh_table)
        fl.addWidget(self.hid_chk)
        ll.addLayout(fl)

        self.table = QTableWidget(0, len(COLS))
        self.table.setHorizontalHeaderLabels([c[0] for c in COLS])
        for i, (_n, w) in enumerate(COLS):
            self.table.setColumnWidth(i, w)
        for c in self.cfg["hidden_cols"]:
            if 0 <= c < len(COLS):
                self.table.setColumnHidden(c, True)
        self.table.setEditTriggers(QAbstractItemView.NoEditTriggers)
        self.table.setSelectionBehavior(QAbstractItemView.SelectRows)
        self.table.setSelectionMode(QAbstractItemView.SingleSelection)
        self.table.setAlternatingRowColors(True)
        self.table.setShowGrid(False)
        self.table.verticalHeader().setVisible(False)
        self.table.verticalHeader().setDefaultSectionSize(27)
        self.table.setItemDelegateForColumn(3, SignalBarDelegate(self.table))
        hh = self.table.horizontalHeader()
        hh.sectionClicked.connect(self.on_header_click)
        hh.setContextMenuPolicy(Qt.CustomContextMenu)
        hh.customContextMenuRequested.connect(self.header_menu)
        self.table.itemSelectionChanged.connect(self.on_table_select)
        self.table.setContextMenuPolicy(Qt.CustomContextMenu)
        self.table.customContextMenuRequested.connect(self.row_menu)
        self.table.cellDoubleClicked.connect(lambda *_: self.tabs.setCurrentIndex(0))
        ll.addWidget(self.table, 1)
        self.split.addWidget(left)

        self.tabs = QTabWidget()
        self.split.addWidget(self.tabs)
        self.split.setStretchFactor(0, 5)
        self.split.setStretchFactor(1, 4)
        self.split.setSizes(self.cfg.get("splitter") or [780, 560])

        # 1) sinyal ölçer
        t1 = QWidget()
        l1 = QVBoxLayout(t1)
        self.gauge = GaugeWidget()
        l1.addWidget(self.gauge, 3)
        sl = QHBoxLayout()
        self.sound_btn = QPushButton("🔊 Sesli bulucu: KAPALI")
        self.sound_btn.setCheckable(True)
        self.sound_btn.toggled.connect(self.on_sound)
        sl.addWidget(self.sound_btn)
        hint = QLabel("Sinyal güçlendikçe tıklama sıklaşır ve incelir: ağın konumunu bulmak / kapsama haritası için.")
        hint.setStyleSheet("color:#8b949e")
        hint.setWordWrap(True)
        sl.addWidget(hint, 1)
        l1.addLayout(sl)
        self.details = QLabel()
        self.details.setTextFormat(Qt.RichText)
        self.details.setAlignment(Qt.AlignTop | Qt.AlignLeft)
        self.details.setTextInteractionFlags(Qt.TextSelectableByMouse)
        self.details.setWordWrap(True)
        l1.addWidget(self.details, 2)
        self.tabs.addTab(t1, "Sinyal Ölçer")

        # 2) kanal grafiği
        t2 = QWidget()
        l2 = QVBoxLayout(t2)
        self.band_btns = []
        l2.addLayout(self.make_band_row())
        self.chan_canvas = ChannelCanvas()
        self.chan_canvas.apClicked.connect(self.select_bssid)
        l2.addWidget(self.chan_canvas, 1)
        self.tabs.addTab(t2, "Kanal Grafiği")

        # 3) zaman grafiği
        t3 = QWidget()
        l3 = QVBoxLayout(t3)
        info = QLabel("Seçili, sabitlenmiş (sağ tık → İzle) ve en güçlü ağların son 3 dakikalık sinyali.")
        info.setStyleSheet("color:#8b949e")
        l3.addWidget(info)
        self.time_canvas = TimeCanvas()
        l3.addWidget(self.time_canvas, 1)
        self.tabs.addTab(t3, "Zaman Grafiği")

        # 4) kanal önerisi
        t4 = QWidget()
        l4 = QVBoxLayout(t4)
        l4.addLayout(self.make_band_row())
        self.rating = RatingCanvas()
        l4.addWidget(self.rating, 1)
        self.rating_lbl = QLabel()
        self.rating_lbl.setTextFormat(Qt.RichText)
        self.rating_lbl.setWordWrap(True)
        l4.addWidget(self.rating_lbl)
        self.tabs.addTab(t4, "Kanal Önerisi")

        # 5) güvenlik
        t5 = QWidget()
        l5 = QVBoxLayout(t5)
        self.sec_summary = QLabel()
        self.sec_summary.setTextFormat(Qt.RichText)
        l5.addWidget(self.sec_summary)
        self.sec_table = QTableWidget(0, 6)
        self.sec_table.setHorizontalHeaderLabels(["Seviye", "SSID", "BSSID", "Güvenlik", "Bulgu", "Öneri"])
        for i, w in enumerate((70, 130, 125, 100, 330, 260)):
            self.sec_table.setColumnWidth(i, w)
        self.sec_table.horizontalHeader().setStretchLastSection(True)
        self.sec_table.setEditTriggers(QAbstractItemView.NoEditTriggers)
        self.sec_table.setSelectionBehavior(QAbstractItemView.SelectRows)
        self.sec_table.verticalHeader().setVisible(False)
        self.sec_table.setAlternatingRowColors(True)
        self.sec_table.setShowGrid(False)
        self.sec_table.setWordWrap(True)
        self.sec_table.cellClicked.connect(self.on_sec_click)
        l5.addWidget(self.sec_table, 1)
        self.tabs.addTab(t5, "Güvenlik Denetimi")

        # 6) olaylar
        self.events = QListWidget()
        self.tabs.addTab(self.events, "Olaylar")
        self.tabs.setCurrentIndex(int(self.cfg.get("tab", 0)))

        self.err_lbl = QLabel()
        self.err_lbl.setStyleSheet("color:#ff9f0a")
        self.statusBar().addPermanentWidget(self.err_lbl)
        self.statusBar().showMessage("İlk tarama yapılıyor…")
        self.refresh_selected_views()

    def make_band_row(self):
        row = QHBoxLayout()
        btns = {}
        for b in ("2.4", "5", "6"):
            btn = QPushButton(BAND_NAMES[b])
            btn.setCheckable(True)
            btn.clicked.connect(lambda _c=False, bb=b: self.set_chan_band(bb))
            row.addWidget(btn)
            btns[b] = btn
        row.addStretch(1)
        self.band_btns.append(btns)
        return row

    def build_menu(self):
        mb = self.menuBar()
        m = mb.addMenu("&Dosya")
        for label, kind in (("CSV olarak dışa aktar…", "csv"), ("JSON olarak dışa aktar…", "json"),
                            ("Rapor (Markdown) kaydet…", "md")):
            m.addAction(label, lambda *_, k=kind: self.export(k))
        m.addSeparator()
        m.addAction("Çıkış", self.close)
        m = mb.addMenu("&Tarama")
        a = QAction("Şimdi tara", self)
        a.setShortcut("F5")
        a.triggered.connect(self.worker.scan_now)
        m.addAction(a)
        a = QAction("Duraklat / devam", self)
        a.setShortcut("Space")
        a.triggered.connect(lambda *_: self.pause_btn.toggle())
        m.addAction(a)
        m = mb.addMenu("&Görünüm")
        cm = m.addMenu("Tablo sütunları")
        for i, (name, _w) in enumerate(COLS):
            if not name:
                continue
            a = QAction(name, cm, checkable=True)
            a.setChecked(not self.table.isColumnHidden(i))
            a.toggled.connect(lambda on, c=i: self.set_col_visible(c, on))
            cm.addAction(a)
        m = mb.addMenu("&Yardım")
        m.addAction("Hakkında", self.about)
        m.addAction("Kurulum / gereksinimler", self.setup_help)

    def build_tray(self):
        self.tray = None
        if QSystemTrayIcon.isSystemTrayAvailable():
            self.tray = QSystemTrayIcon(logo_icon(), self)
            self.tray.setToolTip(f"{APP_NAME} {APP_VERSION}")
            menu = QMenu()
            menu.addAction("Göster / gizle", lambda *_: self.setVisible(not self.isVisible()))
            menu.addAction("Çıkış", self.close)
            self.tray.setContextMenu(menu)
            self.tray.show()

    # ---------------------------------------------------------------- kontroller
    def fill_ifaces(self):
        self.iface_box.blockSignals(True)
        self.iface_box.clear()
        self.iface_box.addItem("Otomatik", "")
        for n, t in list_wifi_ifaces():
            self.iface_box.addItem(f"{n} ({t})" if t else n, n)
        idx = self.iface_box.findData(self.cfg["iface"])
        self.iface_box.setCurrentIndex(max(0, idx))
        self.iface_box.blockSignals(False)

    def on_iface_changed(self, _i):
        self.cfg["iface"] = self.iface_box.currentData() or ""
        self.worker.iface = self.cfg["iface"]
        self.worker.scan_now()

    def on_interval(self, v):
        self.cfg["interval"] = v
        self.worker.interval = float(v)

    def on_pause(self, on):
        self.worker.paused = on
        self.pause_btn.setText("▶ Devam" if on else "⏸ Duraklat")
        if not on:
            self.worker.scan_now()

    def on_demo(self, on):
        self.worker.set_demo(on)
        self.tracker = Tracker(self.cfg["trusted"])       # gerçek/sahte veri karışmasın
        self.selected = None
        self.events.clear()

    def on_sound(self, on):
        self.sound_btn.setText("🔊 Sesli bulucu: AÇIK" if on else "🔊 Sesli bulucu: KAPALI")
        self.geiger.set_enabled(on)

    def set_col_visible(self, c, on):
        self.table.setColumnHidden(c, not on)
        hid = set(self.cfg["hidden_cols"])
        (hid.discard if on else hid.add)(c)
        self.cfg["hidden_cols"] = sorted(hid)

    def header_menu(self, pos):
        menu = QMenu(self)
        for i, (name, _w) in enumerate(COLS):
            if not name:
                continue
            a = QAction(name, menu, checkable=True)
            a.setChecked(not self.table.isColumnHidden(i))
            a.toggled.connect(lambda on, c=i: self.set_col_visible(c, on))
            menu.addAction(a)
        menu.exec_(self.table.horizontalHeader().mapToGlobal(pos))

    def on_header_click(self, col):
        key = COL_SORT.get(col)
        if not key:
            return
        if self.cfg["sort"] == key:
            self.cfg["desc"] = not self.cfg["desc"]
        else:
            self.cfg["sort"], self.cfg["desc"] = key, key == "signal"
        self.refresh_table()

    def set_chan_band(self, b):
        self.chan_band = b
        self.cfg["band"] = b
        self.refresh_graphs()

    def select_bssid(self, bssid):
        self.selected = bssid
        self.refresh_table()
        self.refresh_selected_views()
        self.refresh_graphs()

    def on_table_select(self):
        rows = self.table.selectionModel().selectedRows()
        if not rows:
            return
        it = self.table.item(rows[0].row(), 0)
        if it:
            self.selected = it.data(Qt.UserRole)
            self.refresh_selected_views()
            self.refresh_graphs()

    def on_sec_click(self, row, _col):
        it = self.sec_table.item(row, 2)
        if it and it.text() in self.tracker.recs:
            self.select_bssid(it.text())

    # ---------------------------------------------------------------- tarama sonucu
    def on_scan(self, res):
        aps = res["aps"]
        link_b = (res.get("link") or {}).get("bssid")
        for a in aps:
            a.vendor = self.oui.lookup(a.bssid)
            if link_b and a.bssid == link_b:
                a.associated = True
        self.link, self.source, self.error = res.get("link") or {}, res["source"], res["error"]
        self.iface_shown, self.last_scan = res["iface"], res["time"]
        if res["error"] == "Wi-Fi arayüzü bulunamadı" and not self.worker.demo and not self._offered_demo:
            self._offered_demo = True
            if QMessageBox.question(self, APP_NAME, "Wi-Fi arayüzü bulunamadı.\nDemo modunu (sahte ağlar) açayım mı?") \
                    == QMessageBox.Yes:
                self.demo_chk.setChecked(True)
                return
        for ev in self.tracker.update(aps, res["time"], float(self.cfg["interval"])):
            self.add_event(ev)
        alive = self.tracker.alive()
        if not (self.selected and self.selected in self.tracker.recs and self.tracker.recs[self.selected].alive) and alive:
            conn = [r for r in alive if r.ap.associated]
            self.selected = (conn or sorted(alive, key=lambda r: -r.ema))[0].ap.bssid
        if not self.chan_band and alive:
            self.chan_band = self.tracker.recs[self.selected].ap.band if self.selected in self.tracker.recs else "2.4"
        self.refresh_all()

    def add_event(self, ev):
        colors = {"crit": "#ff453a", "warn": "#ff9f0a", "info": "#8ab4f8"}
        it = QListWidgetItem(f"{time.strftime('%H:%M:%S', time.localtime(ev.t))}   {ev.text}")
        it.setForeground(QColor(colors.get(ev.level, "#c9d1d9")))
        self.events.insertItem(0, it)
        while self.events.count() > 600:
            self.events.takeItem(self.events.count() - 1)
        if ev.level == "crit" and self.cfg.get("notify") and self.tray:
            self.tray.showMessage(APP_NAME, ev.text, QSystemTrayIcon.Critical, 8000)

    # ---------------------------------------------------------------- yenileme
    def refresh_all(self):
        self.refresh_header()
        self.refresh_table()
        self.refresh_selected_views()
        self.refresh_graphs()
        self.refresh_security()
        self.refresh_status()

    def refresh_header(self):
        l = self.link
        if l.get("bssid"):
            ip = read_ip(self.iface_shown) if self.iface_shown and not self.worker.demo else "192.168.0.104"
            tx = f" · {l['tx']} Mb/s" if l.get("tx") else ""
            sg = f" · {l['signal']} dBm" if l.get("signal") else ""
            self.conn_lbl.setText(f'<span style="color:#3ddc84;font-size:15px">✔</span> Bağlı: '
                                  f'<b>{html.escape(l.get("ssid", ""))}</b> ({l["bssid"]}) · IP {ip or "-"}{tx}{sg}')
        else:
            self.conn_lbl.setText('<span style="color:#8b949e">○ Bir ağa bağlı değil</span>')

    def cell(self, text, fg=None, data=None, bold=False, center=False, tip=None, bg=None):
        it = QTableWidgetItem(text)
        if fg:
            it.setForeground(QColor(fg))
        if data is not None:
            it.setData(Qt.UserRole, data)
        if bold:
            f = it.font()
            f.setBold(True)
            it.setFont(f)
        if center:
            it.setTextAlignment(Qt.AlignCenter)
        if tip:
            it.setToolTip(tip)
        if bg:
            it.setBackground(QColor(bg))
        return it

    def trusted_set(self, ssid):
        return {b.lower() for b in self.cfg["trusted"].get(ssid, [])}

    def refresh_table(self, *_):
        recs = filter_sort(self.tracker.alive(), self.search.text(), self.band_filter.currentData() or "",
                           self.weak_chk.isChecked(), self.hid_chk.isChecked(), self.cfg["sort"], self.cfg["desc"])
        t = self.table
        now = time.time()
        link_b = self.link.get("bssid")
        vs = t.verticalScrollBar().value()
        t.blockSignals(True)
        t.setUpdatesEnabled(False)
        t.setRowCount(len(recs))
        sel_row = -1
        pinned = set(self.cfg["pinned"])
        for row, r in enumerate(recs):
            a = r.ap
            conn = a.associated or a.bssid == link_b
            bg = "#0f2a1a" if conn else None
            mark = ("✔ " if conn else "") + ("★ " if a.bssid in self.trusted_set(a.ssid) else "") + \
                   ("◉ " if a.bssid in pinned else "")
            name = a.ssid or "(gizli)"
            sw = self.cell("", data=a.bssid, tip=a.bssid, bg=ap_color(a.bssid))
            vals = [
                sw,
                self.cell(mark + name, fg="#8b949e" if a.hidden else None, bold=conn, bg=bg),
                self.cell(a.bssid, fg="#8b949e", bg=bg),
                self.cell("", data=r.ema, bg=bg, tip=f"anlık {a.signal:.0f} dBm · ort {r.ema:.0f} · "
                                                    f"en iyi {r.mx:.0f} · en kötü {r.mn:.0f}"),
                self.cell(str(a.channel), center=True, bg=bg),
                self.cell(BAND_NAMES.get(a.band, a.band), bg=bg),
                self.cell(f"{a.width} MHz", bg=bg),
                self.cell(a.security, fg=RISK_COLORS[a.risk], bold=a.risk >= 3, bg=bg,
                          tip=f"Risk: {RISK_NAMES[a.risk]}"),
                self.cell(STD_NAMES.get(a.std, "-"), bg=bg),
                self.cell(a.vendor, bg=bg),
                self.cell("-" if a.stations is None else str(a.stations), center=True, bg=bg),
                self.cell("-" if a.util is None else f"%{a.util:.0f}", center=True, bg=bg),
                self.cell(f"~{est_distance(r.ema, a.freq):.0f} m", bg=bg, tip="Kaba tahmin (serbest uzay yayılımı)"),
                self.cell(f"{int(now - r.last)} sn", fg="#8b949e", bg=bg),
            ]
            for c, it in enumerate(vals):
                t.setItem(row, c, it)
            if a.bssid == self.selected:
                sel_row = row
        if sel_row >= 0:
            t.selectRow(sel_row)
        else:
            t.clearSelection()
        t.setUpdatesEnabled(True)
        t.blockSignals(False)
        t.verticalScrollBar().setValue(vs)

    def details_html(self, rec):
        a = rec.ap
        now = time.time()
        rows = [
            ("SSID", html.escape(a.ssid) if a.ssid else "<i>(gizli ağ)</i>"),
            ("BSSID", f"{a.bssid}  ·  <span style='color:#8b949e'>{html.escape(a.vendor)}</span>"),
            ("Kanal", f"{a.channel}  ·  {a.freq} MHz  ·  {BAND_NAMES.get(a.band, a.band)}"),
            ("Genişlik", f"{a.width} MHz  <span style='color:#8b949e'>(merkez {a.center or a.freq} MHz)</span>"),
            ("Standart", STD_NAMES.get(a.std, "-")),
            ("Güvenlik", f"<b style='color:{RISK_COLORS[a.risk]}'>{a.security}</b>  "
                         f"<span style='color:#8b949e'>({RISK_NAMES[a.risk]})</span>"),
            ("WPS", "Etkin" + (" (kilitli)" if a.wps_locked else "") if a.wps else "Yok"),
            ("PMF (802.11w)", {0: "Yok", 1: "Destekli", 2: "Zorunlu"}[a.pmf]),
            ("Bağlı istemci", "-" if a.stations is None else str(a.stations)),
            ("Kanal doluluğu", "-" if a.util is None else f"%{a.util:.0f}"),
            ("Ülke", a.country or "-"),
            ("Tahmini mesafe", f"~{est_distance(rec.ema, a.freq):.0f} m  <span style='color:#8b949e'>(kaba; duvarlar yanıltır)</span>"),
            ("Sinyal", f"anlık {a.signal:.0f} · ort {rec.ema:.0f} · en iyi {rec.mx:.0f} · en kötü {rec.mn:.0f} dBm"),
            ("İzlenme süresi", f"{int(now - rec.first)} sn"),
            ("Güvenilir ağ", "★ evet" if a.bssid in self.trusted_set(a.ssid) else "hayır"),
        ]
        body = "".join(f"<tr><td style='color:#8b949e;padding:2px 14px 2px 0'>{k}</td><td>{v}</td></tr>" for k, v in rows)
        return f"<table>{body}</table>"

    def refresh_selected_views(self):
        rec = self.tracker.recs.get(self.selected) if self.selected else None
        if rec and rec.alive:
            a = rec.ap
            self.gauge.set_value(rec.ema, f"{a.ssid or '(gizli)'}  ({a.bssid})")
            self.geiger.set_level(rec.ema)
            self.details.setText(self.details_html(rec))
        else:
            self.gauge.set_value(None, "AP seçilmedi")
            self.geiger.set_level(None)
            self.details.setText("<span style='color:#8b949e'>Soldaki listeden bir ağ seçin.</span>")

    def time_series(self):
        alive = {r.ap.bssid: r for r in self.tracker.alive()}
        ids = []
        if self.selected in alive:
            ids.append(self.selected)
        ids += [b for b in self.cfg["pinned"] if b in alive and b not in ids]
        for r in sorted(alive.values(), key=lambda r: -r.ema):
            if len(ids) >= 8:
                break
            if r.ap.bssid not in ids:
                ids.append(r.ap.bssid)
        pinned = set(self.cfg["pinned"])
        return {b: ((alive[b].ap.ssid or "(gizli)") + (" ◉" if b in pinned else ""), ap_color(b),
                    list(alive[b].hist)) for b in ids}

    def refresh_graphs(self):
        aps = [r.ap for r in self.tracker.alive()]
        band = self.chan_band or "2.4"
        self.chan_canvas.set_data(aps, band, self.selected)
        self.time_canvas.set_data(self.time_series(), self.selected)
        res = rate_channels(aps, band)
        self.rating.set_data(res, band)
        counts = {b: sum(1 for a in aps if a.band == b) for b in BAND_NAMES}
        for btns in self.band_btns:
            for b, btn in btns.items():
                btn.setChecked(b == band)
                btn.setText(f"{BAND_NAMES[b]} ({counts[b]})")
        parts = []
        for b in ("2.4", "5", "6"):
            if counts[b]:
                r = rate_channels(aps, b)
                if r["best"]:
                    parts.append(f"<b>{BAND_NAMES[b]}</b>: en iyi kanal <b style='color:{ACCENT}'>{r['best']['ch']}</b> "
                                 f"({'★' * r['best']['stars']}, {counts[b]} ağ)")
        self.rating_lbl.setText(" &nbsp;·&nbsp; ".join(parts) or "<span style='color:#8b949e'>Veri yok</span>")

    def refresh_security(self):
        rows = []
        for r in self.tracker.alive():
            for sev, text, adv in audit_ap(r.ap):
                if sev != "ok":
                    rows.append((sev, r.ap, text, adv))
        for key, lvl, bssids, text in self.tracker.findings:
            for b in bssids:
                rec = self.tracker.recs.get(b)
                if rec:
                    rows.append(("crit", rec.ap, "SAHTE AP ŞÜPHESİ: " + text, "Bu AP'ye bağlanmayın; yönlendirici sahibine/ağ yöneticisine bildirin."))
        rows.sort(key=lambda x: (-SEV_RANK[x[0]], -x[1].signal))
        t = self.sec_table
        t.setUpdatesEnabled(False)
        t.setRowCount(len(rows))
        for i, (sev, a, text, adv) in enumerate(rows):
            vals = [SEV_NAME[sev], a.ssid or "(gizli)", a.bssid, a.security, text, adv]
            for c, v in enumerate(vals):
                it = QTableWidgetItem(v)
                if c == 0:
                    it.setForeground(QColor(SEV_COLOR[sev]))
                    f = it.font()
                    f.setBold(True)
                    it.setFont(f)
                t.setItem(i, c, it)
            t.setRowHeight(i, 34)
        t.setUpdatesEnabled(True)
        alive = self.tracker.alive()
        cnt = {s: sum(1 for x in rows if x[0] == s) for s in SEV_ORDER}
        strong = sum(1 for r in alive if r.ap.risk == 0)
        self.sec_summary.setText(
            f"<b>{len(alive)}</b> ağ  ·  <span style='color:{SEV_COLOR['crit']}'>{cnt['crit']} kritik</span>  ·  "
            f"<span style='color:{SEV_COLOR['high']}'>{cnt['high']} yüksek</span>  ·  "
            f"<span style='color:{SEV_COLOR['med']}'>{cnt['med']} orta</span>  ·  "
            f"<span style='color:{SEV_COLOR['low']}'>{cnt['low']} düşük</span>  ·  "
            f"<span style='color:{SEV_COLOR['ok']}'>{strong} güçlü korumalı</span>")

    def refresh_status(self):
        alive = self.tracker.alive()
        c = {b: sum(1 for r in alive if r.ap.band == b) for b in BAND_NAMES}
        weak = sum(1 for r in alive if r.ap.risk >= 3)
        self.count_lbl.setText(f"{len(alive)} ağ  ·  2.4G: {c['2.4']}  5G: {c['5']}  6G: {c['6']}  ·  zayıf güvenlik: {weak}")
        self.statusBar().showMessage(f"arayüz: {self.iface_shown or '-'}  ·  kaynak: {self.source or '-'}  ·  "
                                     f"son tarama: {time.strftime('%H:%M:%S', time.localtime(self.last_scan))}  ·  "
                                     f"OUI: {'yüklü' if self.oui.map else 'yok (sudo apt install ieee-data)'}")
        self.err_lbl.setText(("⚠ " + self.error) if self.error else "")

    # ---------------------------------------------------------------- bağlam menüsü
    def row_menu(self, pos):
        it = self.table.itemAt(pos)
        if not it:
            return
        bssid = self.table.item(it.row(), 0).data(Qt.UserRole)
        rec = self.tracker.recs.get(bssid)
        if not rec:
            return
        a = rec.ap
        menu = QMenu(self)
        menu.addAction("Seç ve sesli bul (Geiger)", lambda *_: self.find_with_sound(bssid))
        pinned = bssid in self.cfg["pinned"]
        menu.addAction("Zaman grafiğinde izlemeyi bırak" if pinned else "Zaman grafiğinde izle (sabitle)",
                       lambda *_: self.toggle_pin(bssid))
        if a.ssid:
            trusted = bssid in self.trusted_set(a.ssid)
            menu.addAction(f"'{a.ssid}' güvenilir ağım değil" if trusted else
                           f"'{a.ssid}' güvenilir ağım (görünen tüm BSSID'ler)",
                           lambda *_: self.toggle_trust(a.ssid))
        menu.addSeparator()
        menu.addAction("BSSID kopyala", lambda *_: QApplication.clipboard().setText(a.bssid))
        if a.ssid:
            menu.addAction("SSID kopyala", lambda *_: QApplication.clipboard().setText(a.ssid))
        menu.exec_(self.table.viewport().mapToGlobal(pos))

    def find_with_sound(self, bssid):
        self.select_bssid(bssid)
        self.tabs.setCurrentIndex(0)
        self.sound_btn.setChecked(True)

    def toggle_pin(self, bssid):
        p = self.cfg["pinned"]
        (p.remove if bssid in p else p.append)(bssid)
        self.refresh_table()
        self.refresh_graphs()

    def toggle_trust(self, ssid):
        tr = self.cfg["trusted"]
        if ssid in tr:
            tr.pop(ssid)
            msg = f"'{ssid}' güvenilir listesinden çıkarıldı"
        else:
            tr[ssid] = sorted({r.ap.bssid for r in self.tracker.alive() if r.ap.ssid == ssid})
            msg = f"'{ssid}' güvenilir olarak işaretlendi ({len(tr[ssid])} BSSID). Bilinmeyen yeni BSSID uyarı verir."
        self.add_event(Event(time.time(), "info", msg))
        save_config(self.cfg)
        self.refresh_all()

    # ---------------------------------------------------------------- dışa aktarma / yardım
    def export(self, kind):
        aps = [r.ap for r in self.tracker.alive()]
        if not aps:
            QMessageBox.information(self, APP_NAME, "Dışa aktarılacak ağ yok.")
            return
        ext = {"csv": "csv", "json": "json", "md": "md"}[kind]
        name = f"wifi-{time.strftime('%Y%m%d-%H%M%S')}.{ext}"
        path, _ = QFileDialog.getSaveFileName(self, "Kaydet", str(Path.home() / name))
        if not path:
            return
        data = {"csv": lambda: export_csv(aps), "json": lambda: export_json(aps),
                "md": lambda: export_markdown(aps, self.tracker.findings, self.iface_shown)}[kind]()
        try:
            Path(path).write_text(data, encoding="utf-8")
            self.statusBar().showMessage(f"Kaydedildi: {path}", 6000)
        except OSError as e:
            QMessageBox.warning(self, APP_NAME, f"Kaydedilemedi: {e}")

    def about(self):
        QMessageBox.about(self, "Hakkında", (
            f"<h3>{APP_NAME} {APP_VERSION}</h3>"
            "<p>Parrot / KDE Plasma için canlı Wi-Fi analiz aracı.</p>"
            f"<p><a href=\"{APP_URL}\">{APP_URL}</a></p>"
            "<p><b>Yalnızca pasif analiz</b> yapar: çevredeki erişim noktalarının yayınlarını okur. "
            "Paket enjeksiyonu, deauth, el sıkışma yakalama ve parola kırma içermez.</p>"
            "<p>Yalnızca sahibi olduğunuz veya yetkili olduğunuz ortamlarda kullanın. Mesafe tahmini kabadır; "
            "güvenlik bulguları genel kurallara dayanır, bir sızma testi yerine geçmez.</p>"))

    def setup_help(self):
        QMessageBox.information(self, "Kurulum", (
            "sudo apt install python3-pyqt5 iw network-manager ieee-data\n"
            "(Geiger sesi için: python3-pyqt5.qtmultimedia veya pulseaudio-utils)\n\n"
            "• root gerekmez: tarama NetworkManager'dan tetiklenir, sonuç 'iw scan dump' ile okunur.\n"
            "• Root ile çalıştırırsanız taze (bloklayan) tarama yapılır.\n"
            "• Arayüz 'managed' modda olmalıdır; monitor modda liste alınamaz.\n"
            "• Üretici adları için ieee-data (OUI) paketi gerekir."))

    def closeEvent(self, ev):
        self.cfg["geometry"] = bytes(self.saveGeometry().toHex()).decode()
        self.cfg["splitter"] = self.split.sizes()
        self.cfg["tab"] = self.tabs.currentIndex()
        save_config(self.cfg)
        self.worker.stop()
        self.geiger.shutdown()
        if self.tray:
            self.tray.hide()
        ev.accept()
        QApplication.quit()


def main():
    ap = argparse.ArgumentParser(description=f"{APP_NAME} {APP_VERSION} - pasif Wi-Fi analizi")
    ap.add_argument("--demo", action="store_true", help="sahte ağlarla dene (Wi-Fi kartı gerekmez)")
    ap.add_argument("--iface", help="Wi-Fi arayüzü (varsayılan: otomatik)")
    ap.add_argument("--interval", type=int, help="tarama aralığı (sn)")
    args = ap.parse_args()
    cfg = load_config()
    if args.iface:
        cfg["iface"] = args.iface
    if args.interval:
        cfg["interval"] = max(2, min(60, args.interval))
    app = QApplication(sys.argv[:1])
    app.setApplicationName("parrotsec-wifi-analyzer")
    app.setWindowIcon(logo_icon())
    app.setStyle("Fusion")
    app.setStyleSheet(STYLE)
    try:
        f = app.font()
        f.setFamilies(["Arial", "Liberation Sans", "Arimo", "Helvetica", "DejaVu Sans"])
        app.setFont(f)
    except AttributeError:
        pass
    win = MainWindow(cfg, args)
    win.show()
    signal.signal(signal.SIGINT, lambda *_: win.close())        # Ctrl+C
    keep = QTimer()
    keep.timeout.connect(lambda: None)                          # Python sinyallerini işlet
    keep.start(250)
    sys.exit(app.exec_())


if __name__ == "__main__":
    main()
