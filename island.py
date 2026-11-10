"""
PC Island — une "Dynamic Island" façon iPhone pour Windows.
Lit la musique en cours via Windows (SMTC : Spotify, Apple Music, Deezer,
YouTube dans le navigateur...), affiche pochette, contrôles et paroles
synchronisées (LRCLIB).
Onglets en bas de l'île dépliée : Musique, WhatsApp (favoris, appels entrants),
Prières (horaires d'Alger).

Lancer :  .venv\\Scripts\\pythonw.exe island.py
"""
import sys, os, re, time, math, asyncio, threading, ctypes, datetime, traceback, winreg, queue
from ctypes import wintypes

import json
from urllib.parse import urlencode, quote
from PySide6.QtCore import Qt, QTimer, QRectF, QPointF, QObject, Signal, QRect, QSettings
from PySide6.QtGui import (QPainter, QColor, QPainterPath, QFont, QFontMetrics, QPixmap,
                           QImage, QCursor, QRegion, QLinearGradient, QIcon, QAction, QPen)
from PySide6.QtWidgets import (QApplication, QWidget, QMenu, QSystemTrayIcon, QDialog, QVBoxLayout,
                               QHBoxLayout, QListWidget, QLineEdit, QPushButton, QLabel)

from winrt.windows.media.control import (
    GlobalSystemMediaTransportControlsSessionManager as SessionManager,
    GlobalSystemMediaTransportControlsSessionPlaybackStatus as PlaybackStatus,
)
from winrt.windows.storage.streams import Buffer, InputStreamOptions, DataReader
from winrt.windows.web.http import HttpClient
from winrt.windows.foundation import Uri
from pycaw.pycaw import AudioUtilities

# ---------------------------------------------------------------- réglages
WIN_W, WIN_H = 800, 262          # taille de la fenêtre transparente
TOP = 0                          # collée au bord haut (encoche)
SHOULDER = 11                    # « épaules » courbes qui fondent l'encoche dans le bord
COMPACT = (300, 38)              # pilule repliée
PEEK = (440, 40)                 # pilule allongée au changement de musique
HANDLE = (150, 6)                # mode discret : fine barre collée en haut
HOTKEY_MODS = 0x0001 | 0x0002   # Alt + Ctrl
HOTKEY_VK = ord("C")             # Ctrl+Alt+C = basculer pilule / barre fine
HOTKEY_ID = 1
HOVER_DELAY = 0.3           # secondes de survol avant ouverture
EXP_FULL = (720, 184)            # dépliée avec paroles
EXP_SMALL = (380, 184)           # dépliée sans paroles
LEFT_W = 370                     # largeur du panneau lecteur
EXP_EMPTY = (340, 104)           # onglet musique sans musique
WA_SIZE = (470, 184)             # onglet WhatsApp
PR_SIZE = (560, 184)             # onglet prières
CALL_SIZE = (430, 78)            # appel entrant
IDLE = (250, 36)                 # pilule repliée sans musique (prochaine prière)
TAB_H = 30                       # barre d'onglets en bas
TABS = [("music", "Musique", ""), ("wa", "WhatsApp", ""), ("prayer", "Prières", "")]
RADIUS = 34
FONTS = ["Segoe UI Variable Display", "Segoe UI"]
ICON_FONTS = ["Segoe Fluent Icons", "Segoe MDL2 Assets"]
APP_NAME = "PC Island"
VERSION = "2.0.0"
REPO = "Kesanoyl/pc-island"     # versions publiées sur GitHub (bouton « Mettre à jour »)
DATA_DIR = os.path.join(os.environ.get("APPDATA", os.path.expanduser("~")), "PCIsland")
GOLD = QColor(240, 200, 120)
WA_GREEN = QColor(37, 211, 102)


def font(size, bold=False):
    f = QFont()
    f.setFamilies(FONTS)
    f.setPointSizeF(size)
    f.setWeight(QFont.DemiBold if bold else QFont.Normal)
    return f


def icon_font(size):
    f = QFont()
    f.setFamilies(ICON_FONTS)
    f.setPointSizeF(size)
    return f


def initials(name):
    parts = [w for w in re.split(r"\s+", name.strip()) if w]
    return ("".join(w[0] for w in parts[:2]) or "?").upper()


def avatar_color(name):
    h = sum(ord(c) * (i + 7) for i, c in enumerate(name)) % 360
    return QColor.fromHsv(h, 120, 175)


def fmt(t):
    t = max(0, int(t))
    return f"{t // 60:02d}:{t % 60:02d}"


class Spring:
    """Ressort amorti : donne le petit rebond façon iOS."""
    def __init__(self, x, k=190.0, d=21.0):
        self.x, self.v, self.t, self.k, self.d = x, 0.0, x, k, d

    def step(self, dt):
        a = self.k * (self.t - self.x) - self.d * self.v
        self.v += a * dt
        self.x += self.v * dt


def notch_path(r, rad, s=SHOULDER):
    """Forme d'encoche : bord haut plat collé à l'écran, épaules concaves qui
    se fondent dans le bord, coins arrondis seulement en bas."""
    x0, x1, y0, y1 = r.left(), r.right(), r.top(), r.bottom()
    rad = max(0.0, min(rad, (y1 - y0) / 2, (x1 - x0) / 2))
    s = min(s, (y1 - y0) * 0.5)
    p = QPainterPath()
    p.moveTo(x0 - s, y0)
    p.quadTo(x0, y0, x0, y0 + s)
    p.lineTo(x0, y1 - rad)
    p.arcTo(QRectF(x0, y1 - 2 * rad, 2 * rad, 2 * rad), 180, 90)
    p.lineTo(x1 - rad, y1)
    p.arcTo(QRectF(x1 - 2 * rad, y1 - 2 * rad, 2 * rad, 2 * rad), 270, 90)
    p.lineTo(x1, y0 + s)
    p.quadTo(x1, y0, x1 + s, y0)
    p.closeSubpath()
    return p


# ---------------------------------------------------------------- média Windows
async def read_thumbnail(ref):
    stream = await ref.open_read_async()
    size = int(stream.size)
    if size <= 0:
        return None
    buf = Buffer(size)
    res = await stream.read_async(buf, size, InputStreamOptions.READ_AHEAD)
    try:
        return bytes(memoryview(res))
    except TypeError:
        reader = DataReader.from_buffer(res)
        data = bytearray(res.length)
        reader.read_bytes(data)
        return bytes(data)


class MediaWorker(QObject):
    updated = Signal(dict)

    def __init__(self):
        super().__init__()
        self.loop = asyncio.new_event_loop()
        self.session = None
        self.key = None
        self.key_time = 0.0
        self.thumb_hash = None
        self.thumb_next = 0.0

    def start(self):
        threading.Thread(target=self._run, daemon=True).start()

    def _run(self):
        asyncio.set_event_loop(self.loop)
        self.loop.run_until_complete(self._main())

    async def _main(self):
        mgr = await SessionManager.request_async()
        while True:
            try:
                await self._poll(mgr)
            except Exception:
                traceback.print_exc()
            await asyncio.sleep(0.4)

    def _pick(self, mgr):
        cur = mgr.get_current_session()
        if cur and cur.get_playback_info().playback_status == PlaybackStatus.PLAYING:
            return cur
        for s in mgr.get_sessions():
            if s.get_playback_info().playback_status == PlaybackStatus.PLAYING:
                return s
        return cur

    async def _poll(self, mgr):
        s = self._pick(mgr)
        self.session = s
        if s is None:
            self.key = None
            self.updated.emit({"has": False})
            return
        props = await s.try_get_media_properties_async()
        title = props.title or ""
        if not title:
            self.updated.emit({"has": False})
            return
        artist = props.artist or props.album_artist or ""
        album = props.album_title or ""
        key = f"{s.source_app_user_model_id}|{title}|{artist}"

        tl = s.get_timeline_properties()
        playing = s.get_playback_info().playback_status == PlaybackStatus.PLAYING
        dur = max(0.0, (tl.end_time - tl.start_time).total_seconds())
        pos = tl.position.total_seconds()
        if playing:
            try:
                delta = (datetime.datetime.now(datetime.timezone.utc) - tl.last_updated_time).total_seconds()
                if 0 <= delta < max(dur, 1):
                    pos += delta
            except Exception:
                pass
        if dur > 0:
            pos = min(pos, dur)

        d = {"has": True, "key": key, "title": title, "artist": artist, "album": album,
             "playing": playing, "pos": pos, "dur": dur, "app": s.source_app_user_model_id}

        now = time.monotonic()
        if key != self.key:
            self.key, self.key_time, self.thumb_next = key, now, 0.0
        # Chrome envoie d'abord son logo puis la vraie pochette : on relit la
        # miniature souvent juste après un changement, puis de temps en temps.
        if props.thumbnail is not None and now >= self.thumb_next:
            self.thumb_next = now + (0.8 if now - self.key_time < 10 else 4.0)
            try:
                data = await read_thumbnail(props.thumbnail)
                if data and hash(data) != self.thumb_hash:
                    self.thumb_hash = hash(data)
                    d["thumb"] = data
            except Exception:
                traceback.print_exc()
        self.updated.emit(d)

    def command(self, name, arg=None):
        asyncio.run_coroutine_threadsafe(self._cmd(name, arg), self.loop)

    async def _cmd(self, name, arg):
        s = self.session
        if not s:
            return
        if name == "toggle":
            await s.try_toggle_play_pause_async()
        elif name == "next":
            await s.try_skip_next_async()
        elif name == "prev":
            await s.try_skip_previous_async()
        elif name == "seek":
            await s.try_change_playback_position_async(int(arg * 10_000_000))


# ---------------------------------------------------------------- paroles (LRCLIB)
LRC_TAG = re.compile(r"\[(\d+):(\d+(?:\.\d+)?)\]")


def http_json(url, params, timeout=8):
    """GET JSON via la pile HTTP de Windows (pas besoin d'OpenSSL dans l'exe)."""
    async def go():
        c = HttpClient()
        c.default_request_headers.user_agent.try_parse_add("PC-Island/1.0")
        r = await c.get_async(Uri(url + "?" + urlencode(params)))
        if not r.is_success_status_code:
            return None
        return json.loads(await r.content.read_as_string_async())
    try:
        return asyncio.run(asyncio.wait_for(go(), timeout))
    except Exception:
        return None


def clean_title(t):
    t = re.sub(r"\s*[\(\[](official|lyrics?|audio|video|clip|hd|4k|visuali[sz]er|live)[^\)\]]*[\)\]]", "", t, flags=re.I)
    t = re.sub(r"\s*[\(\[]\s*(feat|ft)\.?[^\)\]]*[\)\]]", "", t, flags=re.I)
    t = re.sub(r"\s+-\s+.*(remaster|version|edit|mix).*$", "", t, flags=re.I)
    return t.strip()


def clean_artist(a):
    a = re.sub(r"(VEVO|\s*-\s*Topic)$", "", a, flags=re.I)
    return re.split(r",|&| feat\.? | ft\.? | x ", a, flags=re.I)[0].strip()


def parse_lrc(text):
    out = []
    for line in text.splitlines():
        tags = LRC_TAG.findall(line)
        if not tags:
            continue
        lyric = LRC_TAG.sub("", line).strip()
        for m, s in tags:
            out.append((int(m) * 60 + float(s), lyric))
    out.sort(key=lambda x: x[0])
    return out


def fetch_lyrics(title, artist, album, dur):
    """Renvoie ('synced', [(t, ligne)]) / ('plain', [lignes]) / ('missing', None)."""
    # YouTube : "Artiste - Titre" dans le titre
    if " - " in title and (not artist or artist.lower() in ("", "youtube")):
        artist, title = title.split(" - ", 1)
    t, a = clean_title(title), clean_artist(artist)
    candidates = []
    try:
        params = {"track_name": t, "artist_name": a}
        if album:
            params["album_name"] = album
        if dur > 0:
            params["duration"] = round(dur)
        j = http_json("https://lrclib.net/api/get", params)
        if j:
            candidates.append(j)
    except Exception:
        pass
    if not any(c.get("syncedLyrics") for c in candidates):
        try:
            res = http_json("https://lrclib.net/api/search", {"track_name": t, "artist_name": a})
            if res:
                if dur > 0:
                    res.sort(key=lambda c: abs((c.get("duration") or 0) - dur))
                candidates += res
        except Exception:
            pass
    for c in candidates:
        if c.get("syncedLyrics"):
            lines = parse_lrc(c["syncedLyrics"])
            if lines:
                return "synced", lines
    for c in candidates:
        if c.get("plainLyrics"):
            return "plain", [l for l in c["plainLyrics"].splitlines() if l.strip()]
    return "missing", None


class LyricsFetcher(QObject):
    ready = Signal(str, str, object)

    def fetch(self, key, title, artist, album, dur):
        def job():
            kind, data = fetch_lyrics(title, artist, album, dur)
            self.ready.emit(key, kind, data)
        threading.Thread(target=job, daemon=True).start()


# ---------------------------------------------------------------- détection plein écran
user32 = ctypes.windll.user32
user32.GetForegroundWindow.restype = wintypes.HWND
user32.MonitorFromWindow.restype = wintypes.HMONITOR
user32.MonitorFromWindow.argtypes = [wintypes.HWND, wintypes.DWORD]
user32.RegisterHotKey.argtypes = [wintypes.HWND, ctypes.c_int, wintypes.UINT, wintypes.UINT]


class MONITORINFO(ctypes.Structure):
    _fields_ = [("cbSize", wintypes.DWORD), ("rcMonitor", wintypes.RECT),
                ("rcWork", wintypes.RECT), ("dwFlags", wintypes.DWORD)]


def foreground_state(own_hwnd, island_x):
    """'fullscreen' si l'appli au premier plan est en plein écran,
    'top' si elle touche le haut de l'écran sous l'île (navigateur agrandi :
    les onglets sont là), sinon None."""
    hwnd = user32.GetForegroundWindow()
    if not hwnd or hwnd == own_hwnd:
        return None
    buf = ctypes.create_unicode_buffer(64)
    user32.GetClassNameW(hwnd, buf, 64)
    if buf.value in ("Progman", "WorkerW", "Shell_TrayWnd"):
        return None
    r = wintypes.RECT()
    user32.GetWindowRect(hwnd, ctypes.byref(r))
    mi = MONITORINFO()
    mi.cbSize = ctypes.sizeof(mi)
    user32.GetMonitorInfoW(user32.MonitorFromWindow(hwnd, 2), ctypes.byref(mi))
    m, wk = mi.rcMonitor, mi.rcWork
    if r.left <= m.left and r.top <= m.top and r.right >= m.right and r.bottom >= m.bottom:
        return "fullscreen"
    if r.top <= wk.top + 10 and r.left < island_x < r.right and m.left <= island_x < m.right:
        return "top"
    return None


# ---------------------------------------------------------------- volume Windows
class Volume:
    """Volume principal de Windows (pycaw). Re-prend le périphérique par défaut
    toutes les 3 s pour suivre un changement casque / haut-parleurs."""
    def __init__(self):
        self.ev, self.t = None, 0.0

    def _ep(self):
        now = time.monotonic()
        if self.ev is None or now - self.t > 3:
            try:
                self.ev, self.t = AudioUtilities.GetSpeakers().EndpointVolume, now
            except Exception:
                self.ev = None
        return self.ev

    def get(self):
        ev = self._ep()
        try:
            return 0.0 if (ev is None or ev.GetMute()) else float(ev.GetMasterVolumeLevelScalar())
        except Exception:
            return 0.0

    def set(self, v):
        ev = self._ep()
        if ev is None:
            return
        try:
            ev.SetMasterVolumeLevelScalar(max(0.0, min(1.0, v)), None)
            ev.SetMute(1 if v <= 0.001 else 0, None)
        except Exception:
            traceback.print_exc()


# ---------------------------------------------------------------- démarrage auto
RUN_KEY = r"Software\Microsoft\Windows\CurrentVersion\Run"


def autostart_cmd():
    if getattr(sys, "frozen", False):          # version .exe
        return f'"{sys.executable}"'
    exe = sys.executable.replace("python.exe", "pythonw.exe")
    return f'"{exe}" "{os.path.abspath(__file__)}"'


def autostart_enabled():
    try:
        with winreg.OpenKey(winreg.HKEY_CURRENT_USER, RUN_KEY) as k:
            winreg.QueryValueEx(k, APP_NAME)
            return True
    except OSError:
        return False


def set_autostart(on):
    with winreg.OpenKey(winreg.HKEY_CURRENT_USER, RUN_KEY, 0, winreg.KEY_SET_VALUE) as k:
        if on:
            winreg.SetValueEx(k, APP_NAME, 0, winreg.REG_SZ, autostart_cmd())
        else:
            try:
                winreg.DeleteValue(k, APP_NAME)
            except OSError:
                pass


# ---------------------------------------------------------------- prières (Alger)
ALGIERS = datetime.timezone(datetime.timedelta(hours=1))     # Algérie : UTC+1, jamais d'heure d'été
ALG_LAT, ALG_LON = 36.7538, 3.0588
PR_NAMES = [("Fajr", "الفجر"), ("Chourouk", "الشروق"), ("Dhuhr", "الظهر"),
            ("Asr", "العصر"), ("Maghrib", "المغرب"), ("Isha", "العشاء")]
PR_KEYS = ["Fajr", "Sunrise", "Dhuhr", "Asr", "Maghrib", "Isha"]
SALAT = [0, 2, 3, 4, 5]          # Chourouk n'est pas une prière
HIJRI_FR = ["Mouharram", "Safar", "Rabi al-Awwal", "Rabi ath-Thani", "Joumada al-Oula",
            "Joumada ath-Thania", "Rajab", "Chaabane", "Ramadan", "Chawwal", "Dhou al-Qi'da", "Dhou al-Hijja"]
JOURS = ["lundi", "mardi", "mercredi", "jeudi", "vendredi", "samedi", "dimanche"]
MOIS = ["janvier", "février", "mars", "avril", "mai", "juin", "juillet", "août",
        "septembre", "octobre", "novembre", "décembre"]
SKY = {   # dégradé de fond de l'onglet prières selon le moment de la journée
    "night": ((24, 30, 78), (6, 6, 18)),
    "dawn": ((80, 56, 120), (160, 96, 92)),
    "day": ((40, 100, 170), (16, 40, 84)),
    "afternoon": ((160, 108, 52), (62, 40, 74)),
    "dusk": ((120, 52, 96), (30, 22, 66)),
}


def calc_times(day):
    """Calcul astronomique de secours (hors ligne) : Fajr 18°, Isha 17°, Asr chaféite,
    comme la méthode du ministère algérien. Écart ≤ 1 min avec Aladhan."""
    rad, deg = math.radians, math.degrees
    D = (day - datetime.date(2000, 1, 1)).days
    g = rad((357.529 + 0.98560028 * D) % 360)
    q = (280.459 + 0.98564736 * D) % 360
    L = rad((q + 1.915 * math.sin(g) + 0.020 * math.sin(2 * g)) % 360)
    e = rad(23.439 - 0.00000036 * D)
    ra = deg(math.atan2(math.cos(e) * math.sin(L), math.cos(L))) / 15 % 24
    decl = math.asin(math.sin(e) * math.sin(L))
    eqt = (q / 15 - ra + 12) % 24 - 12
    lat = rad(ALG_LAT)
    noon = 12 + 1 - ALG_LON / 15 - eqt

    def T(alt):
        c = (math.sin(alt) - math.sin(decl) * math.sin(lat)) / (math.cos(decl) * math.cos(lat))
        return deg(math.acos(max(-1.0, min(1.0, c)))) / 15
    asr = math.atan(1 / (1 + math.tan(abs(lat - decl))))
    hrs = [noon - T(rad(-18)), noon - T(rad(-0.833)), noon, noon + T(asr),
           noon + T(rad(-0.833)), noon + T(rad(-17))]
    out = []
    for h in hrs:
        m = int(round(h * 60)) % 1440
        out.append(f"{m // 60:02d}:{m % 60:02d}")
    return out


class PrayerTimes(QObject):
    """Horaires d'Alger : mois entier depuis Aladhan (méthode 19 = Algérie), gardé
    en cache sur le disque ; calcul local si pas de réseau."""
    fetched = Signal(dict)

    def __init__(self):
        super().__init__()
        self.path = os.path.join(DATA_DIR, "prieres.json")
        try:
            with open(self.path, encoding="utf-8") as f:
                self.cache = json.load(f)
        except Exception:
            self.cache = {}
        self._tried = {}
        self.fetched.connect(self._merge)

    def day(self, date):
        """-> (6 datetimes à l'heure d'Alger, date hégirienne)"""
        e = self.cache.get(date.isoformat())
        if e:
            hhmm, hijri = e["t"], e.get("h", "")
        else:
            self._fetch_month(date.year, date.month)
            hhmm, hijri = calc_times(date), ""
        return [datetime.datetime.combine(date, datetime.time(int(s[:2]), int(s[3:5])), ALGIERS)
                for s in hhmm], hijri

    def _fetch_month(self, y, m):
        now = time.monotonic()
        if now - self._tried.get((y, m), -1e9) < 600:      # un essai toutes les 10 min max
            return
        self._tried[(y, m)] = now

        def job():
            j = http_json(f"https://api.aladhan.com/v1/calendarByCity/{y}/{m}",
                          {"city": "Algiers", "country": "Algeria", "method": 19}, timeout=15)
            out = {}
            try:
                for d in j["data"]:
                    dd, mm, yy = d["date"]["gregorian"]["date"].split("-")
                    h = d["date"]["hijri"]
                    out[f"{yy}-{mm}-{dd}"] = {
                        "t": [d["timings"][k][:5] for k in PR_KEYS],
                        "h": f'{int(h["day"])} {HIJRI_FR[int(h["month"]["number"]) - 1]} {h["year"]}'}
            except Exception:
                return
            if out:
                self.fetched.emit(out)
        threading.Thread(target=job, daemon=True).start()

    def _merge(self, data):
        self.cache.update(data)
        try:
            os.makedirs(DATA_DIR, exist_ok=True)
            with open(self.path, "w", encoding="utf-8") as f:
                json.dump(self.cache, f, ensure_ascii=False)
        except Exception:
            traceback.print_exc()


# ---------------------------------------------------------------- WhatsApp
WA_APP = r"shell:AppsFolder\5319275A.WhatsAppDesktop_cv1g1gvanyjgm!App"
CALL_WORDS = ("incoming", "calling", "voice call", "video call", "audio call", "appel entrant",
              "vous appelle", "appel vocal", "appel vidéo", "appel audio")
MISSED = ("missed", "manqué", "manque")
ACCEPT_NAMES = ["Accept", "Answer", "Accept call", "Answer call", "Accepter", "Répondre", "Décrocher"]
DECLINE_NAMES = ["Decline", "Reject", "Decline call", "Ignore", "Refuser", "Rejeter", "Ignorer"]
VOICE_NAMES = ["Voice call", "Audio call", "Appel vocal", "Appel audio"]
VIDEO_NAMES = ["Video call", "Appel vidéo"]

_WNDENUMPROC = ctypes.WINFUNCTYPE(ctypes.c_bool, wintypes.HWND, wintypes.LPARAM)


def proc_name(pid):
    h = ctypes.windll.kernel32.OpenProcess(0x1000, False, pid)   # QUERY_LIMITED_INFORMATION
    if not h:
        return ""
    try:
        buf = ctypes.create_unicode_buffer(520)
        n = wintypes.DWORD(520)
        if ctypes.windll.kernel32.QueryFullProcessImageNameW(h, 0, buf, ctypes.byref(n)):
            return os.path.basename(buf.value).lower()
        return ""
    finally:
        ctypes.windll.kernel32.CloseHandle(h)


def top_windows():
    """Fenêtres visibles : [(hwnd, titre, classe, exe)]"""
    out, names = [], {}

    def cb(h, _):
        if user32.IsWindowVisible(h):
            pid = wintypes.DWORD()
            user32.GetWindowThreadProcessId(h, ctypes.byref(pid))
            if pid.value not in names:
                names[pid.value] = proc_name(pid.value)
            t = ctypes.create_unicode_buffer(256)
            user32.GetWindowTextW(h, t, 256)
            c = ctypes.create_unicode_buffer(256)
            user32.GetClassNameW(h, c, 256)
            out.append((h, t.value, c.value, names[pid.value]))
        return True
    user32.EnumWindows(_WNDENUMPROC(cb), 0)
    return out


def wa_windows():
    """(fenêtre principale de WhatsApp, autres fenêtres WhatsApp)"""
    main, others = None, []
    for w in top_windows():
        if "whatsapp" not in w[3]:
            continue
        if main is None and w[2] == "WinUIDesktopWin32WindowClass" and w[1].endswith("WhatsApp"):
            main = w
        else:
            others.append(w)
    return main, others


def toast_windows():
    return [w for w in top_windows() if w[3] == "shellexperiencehost.exe"
            or (w[2] == "Windows.UI.Core.CoreWindow" and "notif" in w[1].lower())]


class UIAWorker:
    """Toute l'UI Automation (cliquer dans WhatsApp) tourne dans ce thread COM."""
    def __init__(self):
        self.q = queue.Queue()
        threading.Thread(target=self._run, daemon=True).start()

    def submit(self, fn):
        self.q.put(fn)

    def _run(self):
        import comtypes, comtypes.client
        comtypes.CoInitialize()
        comtypes.client.GetModule("UIAutomationCore.dll")
        from comtypes.gen import UIAutomationClient as U
        self.U = U
        self.uia = comtypes.client.CreateObject(U.CUIAutomation, interface=U.IUIAutomation)
        while True:
            fn = self.q.get()
            try:
                fn()
            except Exception:
                traceback.print_exc()

    def find(self, hwnd, names, button=True):
        U, uia = self.U, self.uia
        el = uia.ElementFromHandle(hwnd)
        c = None
        for n in names:
            x = uia.CreatePropertyCondition(U.UIA_NamePropertyId, n)
            c = x if c is None else uia.CreateOrCondition(c, x)
        if button:
            c = uia.CreateAndCondition(c, uia.CreatePropertyCondition(U.UIA_ControlTypePropertyId,
                                                                      U.UIA_ButtonControlTypeId))
        r = el.FindFirst(U.TreeScope_Descendants, c)
        try:
            r.CurrentName
            return r
        except Exception:
            return None

    def buttons(self, hwnd, limit=400):
        U, uia = self.U, self.uia
        el = uia.ElementFromHandle(hwnd)
        res = el.FindAll(U.TreeScope_Descendants, uia.CreatePropertyCondition(
            U.UIA_ControlTypePropertyId, U.UIA_ButtonControlTypeId))
        out = []
        for i in range(min(res.Length, limit)):
            try:
                out.append(res.GetElement(i).CurrentName or "")
            except Exception:
                pass
        return out

    @staticmethod
    def runtime_id(el):
        try:
            return tuple(el.GetRuntimeId())
        except Exception:
            return None

    def invoke(self, el):
        U = self.U
        try:
            el.GetCurrentPattern(U.UIA_InvokePatternId).QueryInterface(U.IUIAutomationInvokePattern).Invoke()
            return
        except Exception:
            pass
        r = el.CurrentBoundingRectangle           # pas de motif Invoke : vrai clic
        old = wintypes.POINT()
        user32.GetCursorPos(ctypes.byref(old))
        user32.SetCursorPos((r.left + r.right) // 2, (r.top + r.bottom) // 2)
        user32.mouse_event(0x0002, 0, 0, 0, 0)
        user32.mouse_event(0x0004, 0, 0, 0, 0)
        user32.SetCursorPos(old.x, old.y)


class WhatsApp(QObject):
    """Favoris, ouverture de discussion / appel, détection des appels entrants
    (notifications Windows) et décrocher / refuser via UI Automation."""
    call_changed = Signal(object)          # dict de l'appel entrant, ou None
    status = Signal(str)

    def __init__(self, settings):
        super().__init__()
        self.settings = settings
        try:
            self.favorites = json.loads(settings.value("wa_favorites", "[]"))
        except Exception:
            self.favorites = []
        self.uia = UIAWorker()
        self.call_id = None
        self.seen = set()
        self.listener_ok = None
        self.log_path = os.path.join(DATA_DIR, "whatsapp_debug.log")

    def save(self):
        self.settings.setValue("wa_favorites", json.dumps(self.favorites, ensure_ascii=False))

    # ---------------- appels entrants
    def start(self):
        threading.Thread(target=lambda: asyncio.run(self._main()), daemon=True).start()

    async def _main(self):
        try:
            from winrt.windows.ui.notifications.management import (
                UserNotificationListener, UserNotificationListenerAccessStatus)
            lst = UserNotificationListener.current
            ok = await lst.request_access_async() == UserNotificationListenerAccessStatus.ALLOWED
        except Exception:
            traceback.print_exc()
            lst, ok = None, False
        self.listener_ok = ok
        while True:
            try:
                await self._poll(lst if ok else None)
            except Exception:
                traceback.print_exc()
            await asyncio.sleep(1.0)

    async def _poll(self, lst):
        found = None
        if lst is not None:
            from winrt.windows.ui.notifications import NotificationKinds, KnownNotificationBindings
            now = datetime.datetime.now(datetime.timezone.utc)
            for n in await lst.get_notifications_async(NotificationKinds.TOAST):
                try:
                    if "whatsapp" not in n.app_info.display_info.display_name.lower():
                        continue
                    if (now - n.creation_time).total_seconds() > 60:
                        continue
                    b = n.notification.visual.get_binding(KnownNotificationBindings.toast_generic)
                    texts = [t.text for t in b.get_text_elements()] if b else []
                except Exception:
                    continue
                low = " ".join(texts).lower()
                if any(m in low for m in MISSED) or not any(w in low for w in CALL_WORDS):
                    continue
                name = next((t for t in texts if t.strip() and not any(w in t.lower() for w in CALL_WORDS)),
                            "WhatsApp")
                found = {"id": f"n{n.id}", "name": name, "video": "vid" in low, "texts": texts}
                break
        if found is None:
            # pas de notification (WhatsApp au premier plan) : fenêtre d'appel séparée ?
            _, others = wa_windows()
            for h, title, cls, _ in others:
                low = title.lower()
                if any(w in low for w in ("call", "appel")) and not any(m in low for m in MISSED):
                    found = {"id": f"w{h}", "name": title, "video": "vid" in low, "texts": [title]}
                    break
        fid = found["id"] if found else None
        if fid != self.call_id:
            self.call_id = fid
            self.call_changed.emit(found)
            if found and fid not in self.seen:
                self.seen.add(fid)
                self._log([f"--- {datetime.datetime.now():%Y-%m-%d %H:%M:%S} appel détecté : {found['texts']}"])

    def _log(self, lines):
        try:
            os.makedirs(DATA_DIR, exist_ok=True)
            with open(self.log_path, "a", encoding="utf-8") as f:
                f.write("\n".join(lines) + "\n")
        except Exception:
            traceback.print_exc()

    def _diag(self, call):
        """Journal pour régler la détection : noms des fenêtres et boutons au moment d'un appel."""
        try:
            main, others = wa_windows()
            lines = [f"--- {datetime.datetime.now():%Y-%m-%d %H:%M:%S} {call['texts']}"]
            for h, t, c, exe in others + toast_windows():
                lines.append(f"  fenêtre {exe} {c!r} {t!r} boutons={self.uia.buttons(h, 60)}")
            if main:
                keep = [b for b in self.uia.buttons(main[0]) if re.search(r"call|appel|accept|decl|answer|refus", b, re.I)
                        and len(b) < 40]
                lines.append(f"  principale : {keep}")
            self._log(lines)
        except Exception:
            traceback.print_exc()

    def answer(self):
        self.uia.submit(lambda: self._press(ACCEPT_NAMES, "Appel décroché", "Réponds dans WhatsApp"))

    def decline(self):
        self.uia.submit(lambda: self._press(DECLINE_NAMES, "Appel refusé", "Refuse dans WhatsApp"))

    def _press(self, names, ok, fail):
        main, others = wa_windows()
        for w in toast_windows() + others + ([main] if main else []):
            b = self.uia.find(w[0], names)
            if b:
                self.uia.invoke(b)
                self.status.emit(ok)
                return
        self.open_app()
        self.status.emit(fail)
        self._diag({"texts": [f"bouton introuvable : {names[0]}"]})     # noms réels pour corriger

    # ---------------- favoris
    def open_app(self):
        try:
            os.startfile(WA_APP)
        except Exception:
            os.startfile("whatsapp:")

    def open_chat(self, phone):
        os.startfile(f"whatsapp://send?phone={phone}")

    def send(self, fav, text):
        self.status.emit(f"Envoi à {fav['name']}…")
        self.uia.submit(lambda: self._send(fav, text))

    def _send(self, fav, text):
        """Le lien officiel ouvre LA bonne discussion avec le texte déjà écrit,
        puis on appuie sur Entrée dans WhatsApp. Si la discussion ne s'est pas
        ouverte, Entrée dans une zone vide n'envoie rien."""
        os.startfile(f"whatsapp://send?phone={fav['phone']}&text={quote(text)}")
        t0 = time.monotonic()
        while time.monotonic() - t0 < 10:
            main, _ = wa_windows()
            if main and user32.GetForegroundWindow() == main[0]:
                break
            time.sleep(0.2)
        else:
            self.status.emit("WhatsApp ne s'est pas ouvert : message non envoyé")
            return
        time.sleep(1.8)                       # le temps que la discussion et le texte se chargent
        main, _ = wa_windows()
        if not main or user32.GetForegroundWindow() != main[0]:
            self.status.emit("Message prêt dans WhatsApp : appuie sur Entrée")
            return
        press_key(0x0D)
        self.status.emit(f"Message envoyé à {fav['name']}")

    def call(self, fav, video=False):
        self.status.emit(f"Ouverture de la discussion avec {fav['name']}…")
        self.uia.submit(lambda: self._call(fav, video))

    def _call(self, fav, video):
        """Pas de lien direct pour appeler : on ouvre la discussion puis on clique
        sur le bouton d'appel de l'en-tête. On attend que l'en-tête change pour ne
        jamais appeler la personne de la discussion précédente."""
        names = VIDEO_NAMES if video else VOICE_NAMES
        menu_names = ["Call", "Appeler"]                      # bouton « Appeler » + menu
        main, _ = wa_windows()

        def ids(hwnd):
            out = []
            for n in (names, menu_names):
                b = self.uia.find(hwnd, n)
                out.append(self.uia.runtime_id(b) if b else None)
            return out
        before = ids(main[0]) if main else [None, None]
        self.open_chat(fav["phone"])
        t0 = time.monotonic()
        time.sleep(1.2)
        while time.monotonic() - t0 < 12:
            main, _ = wa_windows()
            if main:
                # un bouton n'est utilisé que s'il est NOUVEAU (en-tête de la nouvelle discussion)
                b = self.uia.find(main[0], names)
                if b and self.uia.runtime_id(b) != before[0]:
                    time.sleep(0.3)
                    self.uia.invoke(b)
                    self.status.emit(f"J'appelle {fav['name']}…")
                    return
                c = self.uia.find(main[0], menu_names)
                if c and self.uia.runtime_id(c) != before[1]:
                    self.uia.invoke(c)
                    time.sleep(0.7)
                    m = self.uia.find(main[0], names, button=False)
                    if m:
                        self.uia.invoke(m)
                        self.status.emit(f"J'appelle {fav['name']}…")
                        return
            time.sleep(0.4)
        self.status.emit("Discussion ouverte : clique sur l'icône d'appel")
        if main:
            self._diag({"texts": [f"appel sortant raté ({'vidéo' if video else 'vocal'})"]})


def normalize_phone(s):
    s = s.strip()
    digits = re.sub(r"\D", "", s)
    if s.startswith("00"):
        digits = digits[2:]
    elif not s.startswith("+") and digits.startswith("0"):
        return None                         # numéro local : il faut l'indicatif du pays
    return digits if 8 <= len(digits) <= 15 else None


class FavDialog(QDialog):
    """Fenêtre pour gérer les contacts WhatsApp favoris (l'île ne prend pas le clavier)."""
    def __init__(self, wa, on_change):
        super().__init__(None, Qt.WindowStaysOnTopHint | Qt.WindowCloseButtonHint)
        self.wa, self.on_change = wa, on_change
        self.setWindowTitle("Contacts WhatsApp — PC Island")
        self.setMinimumWidth(420)
        self.setStyleSheet("""
            QDialog { background: #121216; color: #eee; font-family: 'Segoe UI'; font-size: 10pt; }
            QLabel#hint { color: #9a9aa2; }
            QLabel#err { color: #ff6b6b; }
            QListWidget { background: #1c1c22; border: 1px solid #2a2a33; border-radius: 10px; padding: 4px; }
            QListWidget::item { padding: 7px; border-radius: 6px; }
            QListWidget::item:selected { background: #25d366; color: #0b0b0b; }
            QLineEdit { background: #1c1c22; border: 1px solid #2a2a33; border-radius: 8px; padding: 7px; color: #eee; }
            QLineEdit:focus { border-color: #25d366; }
            QPushButton { background: #2a2a33; border: none; border-radius: 8px; padding: 7px 14px; color: #eee; }
            QPushButton:hover { background: #363642; }
            QPushButton#add { background: #25d366; color: #0b0b0b; font-weight: 600; }
        """)
        lay = QVBoxLayout(self)
        hint = QLabel("Les 5 premiers contacts s'affichent dans l'onglet WhatsApp de l'île.")
        hint.setObjectName("hint")
        hint.setWordWrap(True)
        lay.addWidget(hint)
        self.list = QListWidget()
        lay.addWidget(self.list)
        row = QHBoxLayout()
        self.name = QLineEdit(placeholderText="Nom (ex. Papa)")
        self.phone = QLineEdit(placeholderText="Numéro (ex. +213 555 12 34 56)")
        row.addWidget(self.name, 2)
        row.addWidget(self.phone, 3)
        lay.addLayout(row)
        self.err = QLabel("")
        self.err.setObjectName("err")
        lay.addWidget(self.err)
        btns = QHBoxLayout()
        add = QPushButton("Ajouter")
        add.setObjectName("add")
        add.clicked.connect(self.add)
        self.phone.returnPressed.connect(self.add)
        up = QPushButton("Monter")
        up.clicked.connect(self.up)
        rm = QPushButton("Supprimer")
        rm.clicked.connect(self.remove)
        close = QPushButton("Fermer")
        close.clicked.connect(self.close)
        for b in (add, up, rm):
            btns.addWidget(b)
        btns.addStretch(1)
        btns.addWidget(close)
        lay.addLayout(btns)
        self.refresh()

    def refresh(self):
        self.list.clear()
        for f in self.wa.favorites:
            self.list.addItem(f"{f['name']}    +{f['phone']}")

    def changed(self):
        self.wa.save()
        self.refresh()
        self.on_change()

    def add(self):
        name, phone = self.name.text().strip(), normalize_phone(self.phone.text())
        if not name:
            self.err.setText("Mets un nom.")
            return
        if not phone:
            self.err.setText("Numéro invalide : mets l'indicatif du pays (ex. +213…).")
            return
        self.err.setText("")
        self.wa.favorites.append({"name": name, "phone": phone})
        self.name.clear()
        self.phone.clear()
        self.name.setFocus()
        self.changed()

    def remove(self):
        i = self.list.currentRow()
        if 0 <= i < len(self.wa.favorites):
            del self.wa.favorites[i]
            self.changed()

    def up(self):
        i = self.list.currentRow()
        if 0 < i < len(self.wa.favorites):
            f = self.wa.favorites
            f[i - 1], f[i] = f[i], f[i - 1]
            self.changed()
            self.list.setCurrentRow(i - 1)


def press_key(vk):
    """Appuie / relâche une touche (keybd_event)."""
    user32.keybd_event(vk, 0, 0, 0)
    time.sleep(0.03)
    user32.keybd_event(vk, 0, 0x0002, 0)


class ComposeDialog(QDialog):
    """Petite fenêtre « écrire un message » sous l'île (l'île ne prend pas le clavier)."""
    def __init__(self, wa, fav):
        super().__init__(None, Qt.FramelessWindowHint | Qt.WindowStaysOnTopHint | Qt.Tool)
        self.wa, self.fav = wa, fav
        self.setAttribute(Qt.WA_DeleteOnClose)
        self.setStyleSheet("""
            QDialog { background: #0b0b0d; border: 1px solid #26262c; border-radius: 16px; }
            QLabel { color: #f0f0f0; font-family: 'Segoe UI'; font-size: 10.5pt; font-weight: 600; }
            QLabel#sub { color: #8d8d96; font-size: 8.5pt; font-weight: 400; }
            QLineEdit { background: #1b1b21; border: 1px solid #2a2a33; border-radius: 12px; padding: 9px 12px;
                        color: #f0f0f0; font-family: 'Segoe UI'; font-size: 10.5pt; }
            QLineEdit:focus { border-color: #25d366; }
            QPushButton { background: #25d366; color: #0b0b0b; border: none; border-radius: 12px; padding: 9px 16px;
                          font-family: 'Segoe UI'; font-weight: 600; }
            QPushButton:hover { background: #3be07c; }
            QPushButton#ghost { background: transparent; color: #8d8d96; padding: 4px 8px; }
            QPushButton#ghost:hover { color: #f0f0f0; }
        """)
        lay = QVBoxLayout(self)
        lay.setContentsMargins(16, 14, 16, 14)
        top = QHBoxLayout()
        top.addWidget(QLabel(f"Message à {fav['name']}"))
        top.addStretch(1)
        op = QPushButton("Ouvrir la discussion")
        op.setObjectName("ghost")
        op.clicked.connect(lambda: (wa.open_chat(fav["phone"]), self.close()))
        top.addWidget(op)
        x = QPushButton("✕")
        x.setObjectName("ghost")
        x.clicked.connect(self.close)
        top.addWidget(x)
        lay.addLayout(top)
        row = QHBoxLayout()
        self.text = QLineEdit(placeholderText="Écris ton message…")
        self.text.setMinimumWidth(340)
        self.text.returnPressed.connect(self.send)
        row.addWidget(self.text)
        b = QPushButton("Envoyer")
        b.clicked.connect(self.send)
        row.addWidget(b)
        lay.addLayout(row)
        sub = QLabel("Entrée pour envoyer · Échap pour fermer")
        sub.setObjectName("sub")
        lay.addWidget(sub)

    def send(self):
        txt = self.text.text().strip()
        if txt:
            self.wa.send(self.fav, txt)
            self.close()


# ---------------------------------------------------------------- mises à jour (GitHub)
def http_bytes(url, timeout=180):
    async def go():
        c = HttpClient()
        c.default_request_headers.user_agent.try_parse_add("PC-Island/" + VERSION)
        r = await c.get_async(Uri(url))
        if not r.is_success_status_code:
            return None
        buf = await r.content.read_as_buffer_async()
        try:
            return bytes(memoryview(buf))
        except TypeError:
            reader = DataReader.from_buffer(buf)
            data = bytearray(buf.length)
            reader.read_bytes(data)
            return bytes(data)
    try:
        return asyncio.run(asyncio.wait_for(go(), timeout))
    except Exception:
        traceback.print_exc()
        return None


def vtuple(v):
    return tuple(int(x) for x in re.findall(r"\d+", v)[:3])


UPDATE_BAT = """@echo off
chcp 65001 >nul
:wait
tasklist /FI "PID eq {pid}" | find "{pid}" >nul && (timeout /t 1 /nobreak >nul & goto wait)
robocopy "{src}" "{dst}" /E /R:5 /W:1 /NFL /NDL /NJH /NJS >nul
start "" "{exe}"
"""


class Updater(QObject):
    """Regarde la dernière version publiée sur GitHub ; si elle est plus récente,
    l'île affiche « Mettre à jour ». Installer = télécharger le .zip, remplacer
    les fichiers après la fermeture, puis relancer."""
    available = Signal(dict)
    progress = Signal(str)
    quit_now = Signal()

    def __init__(self):
        super().__init__()
        self.busy = False
        self.timer = QTimer(self)
        self.timer.timeout.connect(self.check)
        self.quit_now.connect(QApplication.quit)

    def start(self):
        QTimer.singleShot(15_000, self.check)
        self.timer.start(3 * 3600 * 1000)

    def check(self):
        def job():
            j = http_json(f"https://api.github.com/repos/{REPO}/releases/latest", {}, timeout=15)
            if not j or not j.get("tag_name") or vtuple(j["tag_name"]) <= vtuple(VERSION):
                return
            asset = next((a for a in j.get("assets", []) if a["name"].lower().endswith(".zip")), None)
            if asset:
                self.available.emit({"version": j["tag_name"].lstrip("v"), "title": j.get("name") or "",
                                     "notes": j.get("body") or "", "url": asset["browser_download_url"]})
        threading.Thread(target=job, daemon=True).start()

    def install(self, info):
        if not getattr(sys, "frozen", False):
            self.progress.emit("Version script : mise à jour via le code, pas le bouton")
            return
        self.busy = True
        self.progress.emit("Téléchargement de la mise à jour…")

        def job():
            import zipfile, io, subprocess, shutil
            data = http_bytes(info["url"])
            if not data:
                self.busy = False
                self.progress.emit("Échec du téléchargement, réessaie plus tard")
                return
            tmp = os.path.join(os.environ.get("TEMP", DATA_DIR), "pcisland_update")
            src = os.path.join(tmp, "new")
            try:
                shutil.rmtree(tmp, ignore_errors=True)
                with zipfile.ZipFile(io.BytesIO(data)) as z:
                    z.extractall(src)
            except Exception:
                traceback.print_exc()
                self.busy = False
                self.progress.emit("Fichier de mise à jour abîmé")
                return
            if os.path.isdir(os.path.join(src, "PC Island")):      # le zip contient un dossier « PC Island »
                src = os.path.join(src, "PC Island")
            dst = os.path.dirname(sys.executable)
            bat = os.path.join(tmp, "maj.bat")
            with open(bat, "w", encoding="utf-8") as f:
                f.write(UPDATE_BAT.format(pid=os.getpid(), src=src, dst=dst, exe=sys.executable))
            subprocess.Popen(["cmd", "/c", bat], creationflags=0x08000000 | 0x00000200, close_fds=True)
            self.progress.emit("Mise à jour : redémarrage…")
            time.sleep(0.8)
            self.quit_now.emit()
        threading.Thread(target=job, daemon=True).start()


# ---------------------------------------------------------------- l'île
class Island(QWidget):
    def __init__(self, media: MediaWorker, wa: WhatsApp):
        super().__init__()
        self.media = media
        self.wa = wa
        self.setWindowFlags(Qt.FramelessWindowHint | Qt.WindowStaysOnTopHint | Qt.Tool
                            | Qt.WindowDoesNotAcceptFocus)
        self.setAttribute(Qt.WA_TranslucentBackground)
        self.setAttribute(Qt.WA_ShowWithoutActivating)
        self.resize(WIN_W, WIN_H)
        self._place()

        self.w, self.h = Spring(COMPACT[0]), Spring(COMPACT[1])
        self.e = Spring(0.0, k=170, d=24)           # 0 = replié, 1 = déplié
        self.top = Spring(float(TOP))
        self.disc = Spring(0.0, k=170, d=26)        # 1 = mode discret (barre fine)
        self.settings = QSettings("PCIsland", "PCIsland")
        self.discreet = self.settings.value("discreet", False, type=bool)
        self._register_hotkey()
        self.alpha = 0.0
        self.lyr_scroll = Spring(0.0, k=110, d=21)

        self.has = False
        self.missing_since = None
        self.key = None
        self.title = self.artist = self.album = ""
        self.playing = False
        self.pos = self.dur = 0.0
        self.art = None
        self.prev_art = None
        self.art_time = 0.0
        self.accent = QColor(120, 160, 255)
        self.show_lyrics = True
        self.lyr_kind, self.lyr, self.lyr_offsets, self.lyr_heights = "none", [], [], []

        self.bg = None                 # pochette floutée pour le fond
        self.vol = Volume()
        self.vol_level, self.vol_until = 0.0, 0.0
        self.lyr_hits = []
        self.peeking = False

        self.last_hover = 0.0
        self.hover_start = None
        self.peek_until = 0.0        # pilule allongée (titre) après un changement
        self.pin_until = 0.0           # dépliée après un clic
        self.fullscreen = False
        self._fs_check = 0.0
        self.bars = [3.0] * 4
        self.hits = {}
        self._mask_rect = None
        self._last = time.monotonic()

        # onglets
        self.tab = self.settings.value("tab", "music")
        if self.tab not in [t[0] for t in TABS]:
            self.tab = "music"
        self.tab_time = 0.0
        self.tab_x = Spring(float([t[0] for t in TABS].index(self.tab)), k=210, d=24)
        self.mus = Spring(1.0 if self.tab == "music" else 0.0, k=170, d=26)
        self.pray = Spring(1.0 if self.tab == "prayer" else 0.0, k=170, d=26)
        self.cm = Spring(0.0, k=190, d=24)          # 1 = carte d'appel entrant
        self._was_expanded = False
        # prières
        self.prayers = PrayerTimes()
        self.pr = None
        self._pr_check = 0.0
        self._pr_last = None
        self.alert, self.alert_until = None, 0.0
        # WhatsApp
        self.call = None
        self.call_dismissed = None
        self.wa_status, self.wa_status_until = "", 0.0
        self._fav_dlg = None
        wa.call_changed.connect(self.on_call)
        wa.status.connect(self.on_wa_status)
        self._compose = None
        self.upd = None
        self.upd_peek_until = 0.0
        self.upd_status = ""
        self.updater = Updater()
        self.updater.available.connect(self.on_update)
        self.updater.progress.connect(lambda t: (setattr(self, "upd_status", t), self.on_wa_status(t)))
        self.updater.start()
        self.update_prayer()

        self.lyrics = LyricsFetcher()
        self.lyrics.ready.connect(self.on_lyrics)
        media.updated.connect(self.on_media)

        self.timer = QTimer(self)
        self.timer.timeout.connect(self.tick)
        self.timer.start(16)

    def _place(self):
        geo = QApplication.primaryScreen().geometry()
        self.move(geo.center().x() - WIN_W // 2, geo.top())

    # -------------------------------------------------- données
    def on_media(self, d):
        now = time.monotonic()
        if not d.get("has"):
            # au changement de musique la session disparaît une fraction de
            # seconde : on attend 2,5 s avant de cacher l'île
            if self.missing_since is None:
                self.missing_since = now
            elif now - self.missing_since > 2.5:
                self.has = False
            return
        self.missing_since = None
        self.has = True
        if d["key"] != self.key:
            self.key = d["key"]
            self.title, self.artist, self.album = d["title"], d["artist"], d["album"]
            self.pos = d["pos"]   # on garde l'ancienne pochette jusqu'à la nouvelle
            self.lyr_kind, self.lyr = "loading", []
            self.lyr_scroll.x = self.lyr_scroll.t = 0
            self.peek_until = now + 3.5
            self.lyrics.fetch(self.key, self.title, self.artist, self.album, d["dur"])
        self.playing, self.dur = d["playing"], d["dur"]
        if not self.playing or abs(d["pos"] - self.pos) > 1.2:
            self.pos = d["pos"]
        if "thumb" in d:
            img = QImage.fromData(d["thumb"])
            if not img.isNull() and not self.is_app_icon(img):
                self.prev_art, self.art_time = self.art, now
                self.art =QPixmap.fromImage(img).scaled(160, 160, Qt.KeepAspectRatioByExpanding,
                                                          Qt.SmoothTransformation)
                # fond flou : on réduit à 16 px puis on ré-agrandit en lissant
                small = img.scaled(16, 16, Qt.IgnoreAspectRatio, Qt.SmoothTransformation)
                small = small.scaled(64, 32, Qt.IgnoreAspectRatio, Qt.SmoothTransformation)
                self.bg = QPixmap.fromImage(small.scaled(EXP_FULL[0], EXP_FULL[1], Qt.IgnoreAspectRatio,
                                                         Qt.SmoothTransformation))
                c = img.scaled(1, 1, Qt.IgnoreAspectRatio, Qt.SmoothTransformation).pixelColor(0, 0)
                h, s, v, _ = c.getHsv()
                self.accent = QColor.fromHsv(max(h, 0), max(s, 110), max(v, 210))

    @staticmethod
    def is_app_icon(img):
        """Logo d'appli (Chrome, Edge…) = PNG aux coins transparents. Une vraie pochette n'en a pas."""
        if not img.hasAlphaChannel():
            return False
        w, h = img.width() - 1, img.height() - 1
        corners = [img.pixelColor(x, y).alpha() for x, y in ((0, 0), (w, 0), (0, h), (w, h))]
        return max(corners) < 30

    def on_lyrics(self, key, kind, data):
        if key != self.key:
            return
        self.lyr_kind = kind
        if kind == "synced":
            self.lyr = [(t, txt or "♪") for t, txt in data]
        elif kind == "plain":
            self.lyr = [(0.0, txt) for txt in data]
        else:
            self.lyr = []
        fm = QFontMetrics(font(13.5, True))
        width = EXP_FULL[0] - LEFT_W - 44
        self.lyr_heights, self.lyr_offsets, y = [], [], 0
        for _, txt in self.lyr:
            h = fm.boundingRect(QRect(0, 0, width, 2000), Qt.TextWordWrap, txt).height()
            self.lyr_offsets.append(y)
            self.lyr_heights.append(h)
            y += h + 10

    def current_line(self):
        if not self.lyr:
            return -1
        if self.lyr_kind == "plain":
            return min(len(self.lyr) - 1, int(self.pos / self.dur * len(self.lyr))) if self.dur else 0
        idx = -1
        for i, (t, _) in enumerate(self.lyr):
            if t <= self.pos + 0.2:
                idx = i
            else:
                break
        return idx

    # -------------------------------------------------- WhatsApp / prières / onglets
    def on_call(self, d):
        if d and d["id"] == self.call_dismissed:
            return
        self.call = d
        self._set_interval(16)

    def on_wa_status(self, txt):
        self.wa_status, self.wa_status_until = txt, time.monotonic() + 5

    def open_compose(self, fav):
        if self._compose is not None:
            self._compose.close()
        self._compose = ComposeDialog(self.wa, fav)
        g = self.mapToGlobal(self.pill_rect().center().toPoint())
        self._compose.adjustSize()
        self._compose.move(g.x() - self._compose.width() // 2, self.mapToGlobal(self.pill_rect().bottomLeft().toPoint()).y() + 16)
        self._compose.show()
        self._compose.raise_()
        self._compose.activateWindow()
        self._compose.text.setFocus()

    # -------------------------------------------------- mises à jour
    def on_update(self, info):
        self.upd = info
        self.alert = None
        self.upd_peek_until = time.monotonic() + 8
        self.peek_until = max(self.peek_until, self.upd_peek_until)
        self._set_interval(16)

    def start_update(self):
        if self.upd and not self.updater.busy:
            self.updater.install(self.upd)

    def open_favorites(self):
        if self._fav_dlg is None:
            self._fav_dlg = FavDialog(self.wa, self.update)
        self._fav_dlg.refresh()
        self._fav_dlg.show()
        self._fav_dlg.raise_()
        self._fav_dlg.activateWindow()

    def set_tab(self, key, save=True):
        if key != self.tab:
            self.tab, self.tab_time = key, time.monotonic()
        if save:
            self.settings.setValue("tab", key)
        self._set_interval(16)

    def exp_size(self):
        if self.tab == "music":
            if not self.has:
                w, h = EXP_EMPTY
            else:
                w, h = EXP_FULL if (self.show_lyrics and self.lyr) else EXP_SMALL
        else:
            w, h = WA_SIZE if self.tab == "wa" else PR_SIZE
        return w, h + TAB_H

    def update_prayer(self):
        now = datetime.datetime.now(ALGIERS)
        today = now.date()
        times, hijri = self.prayers.day(today)
        nxt = next((i for i in SALAT if times[i] > now), None)
        if nxt is None:                      # après Isha : on montre demain
            shown, _ = self.prayers.day(today + datetime.timedelta(days=1))
            nidx, ndt, tomorrow = 0, shown[0], True
        else:
            shown, nidx, ndt, tomorrow = times, nxt, times[nxt], False
        passed = [i for i in SALAT if times[i] <= now]
        pdt = times[passed[-1]] if passed else times[5] - datetime.timedelta(days=1)
        if now < times[0] or now >= times[5]:
            phase = "night"
        elif now < times[1]:
            phase = "dawn"
        elif now < times[3]:
            phase = "day"
        elif now < times[4]:
            phase = "afternoon"
        else:
            phase = "dusk"
        name = PR_NAMES[nidx][0]
        # adhan : la prière attendue vient de passer → petite alerte dans la pilule
        if self._pr_last and self._pr_last[1] != ndt and self._pr_last[1] <= now \
                and (now - self._pr_last[1]).total_seconds() < 120:
            self.alert = self._pr_last
            self.alert_until = time.monotonic() + 15
            self.peek_until = max(self.peek_until, self.alert_until)
        self._pr_last = (name, ndt)
        self.pr = {"now": now, "shown": shown, "hijri": hijri, "next_idx": nidx, "next_name": name,
                   "next_dt": ndt, "prev_dt": pdt, "tomorrow": tomorrow, "phase": phase}

    @staticmethod
    def countdown(sec, long=False):
        sec = max(0, int(sec))
        h, m, s = sec // 3600, sec % 3600 // 60, sec % 60
        if long:
            return f"{h}:{m:02d}:{s:02d}" if h else f"{m:02d}:{s:02d}"
        if h:
            return f"{h} h {m:02d}"
        return f"{m} min" if m else "< 1 min"

    # -------------------------------------------------- animation
    def pill_rect(self):
        return QRectF((WIN_W - self.w.x) / 2, self.top.x, self.w.x, self.h.x)

    def tick(self):
        now = time.monotonic()
        real_dt = now - self._last
        dt = min(real_dt, 0.033)
        self._last = now

        if self.playing and self.dur > 0:
            self.pos = min(self.pos + real_dt, self.dur)

        if now - self._fs_check > 0.3:
            self._fs_check = now
            try:
                st = foreground_state(int(self.winId()), self.mapToGlobal(self.rect().center()).x())
            except Exception:
                st = None
            self.fullscreen = st == "fullscreen"
            # le mode réduit (fine barre) se bascule avec Ctrl+Alt+C
            if self.isVisible() and not self.fullscreen:
                # toujours au-dessus : une autre fenêtre « topmost » (terminal…) ne doit pas passer devant
                user32.SetWindowPos(wintypes.HWND(int(self.winId())), wintypes.HWND(-1), 0, 0, 0, 0,
                                    0x0001 | 0x0002 | 0x0010 | 0x0200)   # NOSIZE|NOMOVE|NOACTIVATE|NOOWNERZORDER
        if now - self._pr_check > 1.0:
            self._pr_check = now
            self.update_prayer()

        r = self.pill_rect().translated(self.pos_global_offset())
        handle = self.disc.x > 0.5 and self.e.x < 0.3
        margin = r.adjusted(-4, 0, 4, 2) if handle else r.adjusted(-6, -6, 6, 6)
        if margin.contains(QPointF(QCursor.pos())) and self.isVisible():
            if self.hover_start is None:
                self.hover_start = now
            self.last_hover = now
        elif now - self.last_hover > 0.35:
            self.hover_start = None
        # il faut rester 0,5 s sur l'île pour l'ouvrir (un simple passage ne l'ouvre pas)
        hover_open = self.hover_start is not None and now - self.hover_start >= HOVER_DELAY
        calling = self.call is not None
        expanded = (hover_open or now < self.pin_until) and not calling
        if expanded and not self._was_expanded and self.tab == "music" and not self.has:
            self.set_tab("prayer", save=False)        # rien ne joue : on montre les prières
        self._was_expanded = expanded
        self.peeking = not expanded and not calling and now < self.peek_until

        if calling:
            self.w.t, self.h.t = CALL_SIZE
        elif expanded:
            # panneau paroles seulement s'il y a des paroles
            self.w.t, self.h.t = self.exp_size()
        elif self.peeking:
            self.w.t, self.h.t = PEEK
        elif self.discreet:
            self.w.t, self.h.t = HANDLE
        else:
            self.w.t, self.h.t = COMPACT if self.has else IDLE
        self.e.t = 1.0 if expanded else 0.0
        self.cm.t = 1.0 if calling else 0.0
        handle_mode = self.discreet and not expanded and not self.peeking and not calling
        self.disc.t = 1.0 if handle_mode else 0.0
        self.top.t = 0.0 if handle_mode else float(TOP)
        self.tab_x.t = float([t[0] for t in TABS].index(self.tab))
        self.mus.t = 1.0 if (self.tab == "music" and self.has) else 0.0
        self.pray.t = 1.0 if self.tab == "prayer" else 0.0

        idx = self.current_line()
        if 0 <= idx < len(self.lyr_offsets):
            self.lyr_scroll.t = self.lyr_offsets[idx]

        for s in (self.w, self.h, self.e, self.lyr_scroll, self.top, self.disc,
                  self.tab_x, self.mus, self.pray, self.cm):
            s.step(dt)
        self.h.x = max(self.h.x, 2.0)

        # l'île reste visible même sans musique (prières, WhatsApp) ;
        # un appel entrant s'affiche même par-dessus un jeu en plein écran
        target_alpha = 1.0 if (not self.fullscreen or calling) else 0.0
        self.alpha += (target_alpha - self.alpha) * (1 - math.exp(-dt * 10))

        # barres d'égaliseur
        t = now
        for i in range(4):
            tgt = 4 + 11 * abs(math.sin(t * (5.1 + i * 1.7) + i * 1.3)) if self.playing else 3
            self.bars[i] += (tgt - self.bars[i]) * 0.35

        if target_alpha > 0 and not self.isVisible():
            self.show()
        elif self.alpha < 0.01 and target_alpha == 0 and self.isVisible():
            self.hide()
        if not self.isVisible():
            self._set_interval(250)
            return

        mr = self.pill_rect().toAlignedRect().adjusted(-SHOULDER - 10, 0, SHOULDER + 10, 12)   # + épaules et ombre
        if mr != self._mask_rect:
            self._mask_rect = mr
            self.setMask(QRegion(mr))

        # économie : 60 i/s seulement pendant les animations
        moving = (any(abs(s.v) > 0.3 or abs(s.t - s.x) > 0.3 for s in (self.w, self.h, self.lyr_scroll, self.top))
                  or any(abs(s.t - s.x) > 0.005 for s in (self.disc, self.tab_x, self.mus, self.pray, self.cm))
                  or abs(self.e.v) > 0.01 or abs(self.e.t - self.e.x) > 0.005
                  or abs(target_alpha - self.alpha) > 0.01
                  or now - self.art_time < 0.5 or now < self.vol_until
                  or now - self.last_hover < 0.5 or now - self.tab_time < 0.4
                  or calling or (self.e.x > 0.5 and self.tab == "prayer"))
        self._set_interval(16 if moving else 33 if self.playing else 100)
        self.update()

    def _set_interval(self, ms):
        if self.timer.interval() != ms:
            self.timer.setInterval(ms)

    # -------------------------------------------------- raccourci clavier global
    def _register_hotkey(self):
        ok = user32.RegisterHotKey(wintypes.HWND(int(self.winId())), HOTKEY_ID,
                                   HOTKEY_MODS | 0x4000, HOTKEY_VK)   # 0x4000 = pas de répétition
        if not ok:
            print("Raccourci Ctrl+Alt+C déjà pris par une autre appli", file=sys.stderr)

    def nativeEvent(self, event_type, message):
        msg = wintypes.MSG.from_address(int(message))
        if msg.message == 0x0312 and msg.wParam == HOTKEY_ID:     # WM_HOTKEY
            self.toggle_discreet()
            return True, 0
        return super().nativeEvent(event_type, message)

    def toggle_discreet(self, on=None):
        self.discreet = (not self.discreet) if on is None else bool(on)
        self.settings.setValue("discreet", self.discreet)
        self._set_interval(16)

    def enterEvent(self, _):
        self._set_interval(16)          # réaction immédiate au survol

    def pos_global_offset(self):
        g = self.mapToGlobal(self.rect().topLeft())
        return QPointF(g.x(), g.y())

    # -------------------------------------------------- dessin
    def paintEvent(self, _):
        p = QPainter(self)
        p.setRenderHints(QPainter.Antialiasing | QPainter.SmoothPixmapTransform | QPainter.TextAntialiasing)
        p.setOpacity(self.alpha)
        r = self.pill_rect()
        e = max(0.0, min(1.0, self.e.x))

        rad = min(r.height() / 2, RADIUS)
        path = notch_path(r, rad)
        # ombre douce sous l'encoche
        p.setPen(Qt.NoPen)
        for i in range(1, 7):
            p.fillPath(notch_path(r.adjusted(-i * 0.6, 0, i * 0.6, i * 1.4), rad + i), QColor(0, 0, 0, 9))
        g = QLinearGradient(r.topLeft(), r.bottomLeft())
        g.setColorAt(0, QColor(0, 0, 0, 255))
        bottom = QColor(6, 6, 8, 255)
        mix = QColor(int(28 + self.accent.red() * 0.10), int(30 + self.accent.green() * 0.10),
                     int(34 + self.accent.blue() * 0.10), 255)
        g.setColorAt(1, QColor(
            int(bottom.red() + (mix.red() - bottom.red()) * e),
            int(bottom.green() + (mix.green() - bottom.green()) * e),
            int(bottom.blue() + (mix.blue() - bottom.blue()) * e), 255))
        p.fillPath(path, g)
        p.setClipPath(path)
        me = e * max(0.0, min(1.0, self.mus.x))
        if self.bg and me > 0:          # pochette floutée en fond (façon Apple Music)
            p.setOpacity(self.alpha * me * 0.75)
            p.drawPixmap(QRectF(r.left(), r.top(), EXP_FULL[0], r.height()).toRect(), self.bg)
            p.setOpacity(self.alpha)
            shade = QLinearGradient(r.topLeft(), r.bottomLeft())
            shade.setColorAt(0, QColor(0, 0, 0, int(150 * me)))
            shade.setColorAt(1, QColor(0, 0, 0, int(90 * me)))
            p.fillPath(path, shade)
        pe = e * max(0.0, min(1.0, self.pray.x))
        if pe > 0 and self.pr:          # ciel selon le moment de la journée
            top_c, bot_c = SKY[self.pr["phase"]]
            sky = QLinearGradient(r.topLeft(), r.bottomLeft())
            sky.setColorAt(0, QColor(*top_c, 150))
            sky.setColorAt(1, QColor(*bot_c, 60))
            p.setOpacity(self.alpha * pe * 0.6)
            p.fillPath(path, sky)
        p.setOpacity(self.alpha)
        p.setPen(QColor(255, 255, 255, 22))
        p.drawPath(path)

        d = max(0.0, min(1.0, self.disc.x))
        cm = max(0.0, min(1.0, self.cm.x))
        ca = max(0.0, 1 - e * 2.5) * max(0.0, 1 - d * 2.5) * max(0.0, 1 - cm * 2.5)
        if ca > 0 and r.height() > 20:
            p.setOpacity(self.alpha * ca)
            self.draw_compact(p, r)
        if d > 0.5:                     # barre fine : progression de la musique (ou vers la prochaine prière)
            p.setOpacity(self.alpha * (d - 0.5) * 2)
            if self.has:
                frac, col = (self.pos / self.dur if self.dur else 0), self.accent
            else:
                frac, col = self.prayer_frac(), GOLD
            p.setPen(Qt.NoPen)
            p.setBrush(col)
            p.drawRect(QRectF(r.left(), r.top(), r.width() * frac, r.height()))
            p.setOpacity(self.alpha)
        ea = max(0.0, (e - 0.4) / 0.6)
        self.hits = {}
        self.lyr_hits = []
        if ea > 0:
            p.setOpacity(self.alpha * ea)
            self.draw_expanded(p, r, interactive=ea > 0.8)
        ka = max(0.0, (cm - 0.4) / 0.6)
        if ka > 0 and self.call:
            p.setOpacity(self.alpha * ka)
            self.draw_call(p, r, interactive=ka > 0.8)
        p.end()

    def prayer_frac(self):
        if not self.pr:
            return 0.0
        now = datetime.datetime.now(ALGIERS)
        span = (self.pr["next_dt"] - self.pr["prev_dt"]).total_seconds()
        return max(0.0, min(1.0, (now - self.pr["prev_dt"]).total_seconds() / span)) if span > 0 else 0.0

    def draw_art(self, p, rect, radius):
        p.save()
        clip = QPainterPath()
        clip.addRoundedRect(rect, radius, radius)
        p.setClipPath(clip, Qt.IntersectClip)
        if self.art:
            fade = min(1.0, (time.monotonic() - self.art_time) / 0.4)   # fondu entre pochettes
            op = p.opacity()
            if self.prev_art and fade < 1:
                p.drawPixmap(rect.toRect(), self.prev_art)
                p.setOpacity(op * fade)
            p.drawPixmap(rect.toRect(), self.art)
            p.setOpacity(op)
        else:
            p.fillRect(rect, QColor(45, 45, 50))
            p.setPen(QColor(255, 255, 255, 120))
            p.setFont(font(rect.height() * 0.3))
            p.drawText(rect, Qt.AlignCenter, "♪")
        p.restore()

    def draw_compact(self, p, r):
        if time.monotonic() < self.upd_peek_until and self.upd:
            p.setPen(QColor(120, 170, 255))
            p.setFont(icon_font(10))
            p.drawText(QRectF(r.left() + 12, r.top(), 20, r.height()), Qt.AlignCenter, "\uE896")
            f = font(9.5, True)
            p.setFont(f)
            p.setPen(QColor(255, 255, 255, 230))
            tr = QRectF(r.left() + 36, r.top(), r.width() - 52, r.height())
            title = self.upd.get("title") or "Nouvelle version"
            p.drawText(tr, Qt.AlignVCenter | Qt.AlignHCenter, QFontMetrics(f).elidedText(
                f"v{self.upd['version']} dispo · {title}", Qt.ElideRight, int(tr.width())))
            return
        if time.monotonic() < self.alert_until and self.alert:
            self.draw_prayer_pill(p, r, alert=True)
            return
        if not self.has:
            self.draw_prayer_pill(p, r)
            return
        s = r.height() - 12
        self.draw_art(p, QRectF(r.left() + 7, r.top() + 6, s, s), 7)
        # égaliseur
        bx = r.right() - 14 - 4 * 3 - 3 * 3
        cy = r.center().y()
        p.setPen(Qt.NoPen)
        p.setBrush(self.accent)
        for i, h in enumerate(self.bars):
            p.drawRoundedRect(QRectF(bx + i * 6, cy - h / 2, 3, h), 1.5, 1.5)
        tr = QRectF(r.left() + s + 18, r.top(), bx - (r.left() + s + 18) - 10, r.height())
        if time.monotonic() < self.vol_until:          # jauge de volume
            self.draw_volume_row(p, QRectF(tr.left() + 18, r.center().y() - 2, tr.width() - 58, 4), small=True)
            return
        # titre (au changement de musique) ou ligne de paroles
        idx = self.current_line()
        title = f"{self.title}  —  {self.artist}" if self.artist else self.title
        if self.peeking or not (self.lyr_kind == "synced" and 0 <= idx < len(self.lyr)):
            txt = title
        else:
            txt = self.lyr[idx][1]
        f = font(9.5, True)
        p.setFont(f)
        p.setPen(QColor(255, 255, 255, 215))
        p.drawText(tr, Qt.AlignVCenter | Qt.AlignHCenter,
                   QFontMetrics(f).elidedText(txt, Qt.ElideRight, int(tr.width())))

    def draw_prayer_pill(self, p, r, alert=False):
        """Pilule repliée sans musique : prochaine prière + compte à rebours.
        alert=True : « C'est l'heure de … » à l'adhan."""
        if not self.pr:
            return
        p.setPen(GOLD)
        p.setFont(icon_font(10))
        p.drawText(QRectF(r.left() + 12, r.top(), 20, r.height()), Qt.AlignCenter, "")
        if alert:
            name, dt = self.alert
            f = font(9.5, True)
            p.setFont(f)
            p.setPen(QColor(255, 255, 255, 230))
            tr = QRectF(r.left() + 36, r.top(), r.width() - 52, r.height())
            p.drawText(tr, Qt.AlignVCenter | Qt.AlignHCenter, QFontMetrics(f).elidedText(
                f"C'est l'heure de {name}  ·  {dt:%H:%M}", Qt.ElideRight, int(tr.width())))
            return
        rem = (self.pr["next_dt"] - datetime.datetime.now(ALGIERS)).total_seconds()
        f = font(9.5, True)
        p.setFont(f)
        p.setPen(QColor(255, 255, 255, 220))
        p.drawText(QRectF(r.left() + 38, r.top(), r.width() - 50, r.height()), Qt.AlignVCenter | Qt.AlignLeft,
                   f"{self.pr['next_name']}  {self.pr['next_dt']:%H:%M}")
        p.setFont(font(9))
        p.setPen(QColor(255, 255, 255, 135))
        p.drawText(QRectF(r.left(), r.top(), r.width() - 16, r.height()), Qt.AlignVCenter | Qt.AlignRight,
                   f"dans {self.countdown(rem)}")

    def draw_expanded(self, p, r, interactive):
        c = QRectF(r.left(), r.top(), r.width(), r.height() - TAB_H)    # zone au-dessus des onglets
        tf = min(1.0, (time.monotonic() - self.tab_time) / 0.25)        # fondu au changement d'onglet
        op = p.opacity()
        p.setOpacity(op * tf)
        if self.tab == "music":
            if self.has:
                self.draw_music(p, c, interactive)
            else:
                self.draw_music_empty(p, c)
        elif self.tab == "wa":
            self.draw_wa(p, c, interactive)
        else:
            self.draw_prayer(p, c)
        p.setOpacity(op)
        self.draw_tabs(p, r, interactive)

    def draw_tabs(self, p, r, interactive):
        y0 = r.bottom() - TAB_H
        p.setPen(QColor(255, 255, 255, 16))
        p.drawLine(QPointF(r.left() + 26, y0), QPointF(r.right() - 26, y0))
        tw = 96
        x0 = r.center().x() - tw * len(TABS) / 2
        p.setPen(Qt.NoPen)
        p.setBrush(QColor(255, 255, 255, 18))
        p.drawRoundedRect(QRectF(x0 + self.tab_x.x * tw + 10, y0 + 6, tw - 20, TAB_H - 11), 9, 9)
        cur = QPointF(self.mapFromGlobal(QCursor.pos()))
        tint = {"music": self.accent, "wa": WA_GREEN, "prayer": GOLD}
        for i, (key, label, glyph) in enumerate(TABS):
            rect = QRectF(x0 + i * tw, y0 + 2, tw, TAB_H - 4)
            active = key == self.tab
            hov = rect.contains(cur)
            col = QColor(255, 255, 255, 230 if active else 150 if hov else 90)
            fl = font(8.5, active)
            lw = QFontMetrics(fl).horizontalAdvance(label)
            sx = rect.center().x() - (12 + 5 + lw) / 2
            p.setFont(icon_font(8))
            p.setPen(tint[key] if active else col)
            p.drawText(QRectF(sx, rect.top(), 12, rect.height()), Qt.AlignCenter, glyph)
            p.setFont(fl)
            p.setPen(col)
            p.drawText(QRectF(sx + 17, rect.top(), lw + 2, rect.height()), Qt.AlignVCenter | Qt.AlignLeft, label)
            if interactive:
                self.hits["tab:" + key] = rect
        if self.upd:                                   # pastille « Mettre à jour » à droite
            room = r.right() - (x0 + tw * len(TABS)) - 22
            wide = room >= 104
            bw = 98 if wide else 24
            b = QRectF(r.right() - 22 - bw, y0 + 6, bw, TAB_H - 11)
            hov = b.contains(cur)
            p.setPen(Qt.NoPen)
            p.setBrush(QColor(90, 150, 255, 255 if hov else 210))
            p.drawRoundedRect(b, 9, 9)
            p.setPen(QColor(255, 255, 255))
            if wide:
                p.setFont(icon_font(7.5))
                p.drawText(QRectF(b.left() + 8, b.top(), 12, b.height()), Qt.AlignCenter, "")
                p.setFont(font(8, True))
                p.drawText(QRectF(b.left() + 22, b.top(), b.width() - 26, b.height()), Qt.AlignCenter,
                           "Mettre à jour" if not self.updater.busy else "…")
            else:
                p.setFont(icon_font(7.5))
                p.drawText(b, Qt.AlignCenter, "")
            if interactive:
                self.hits["upd"] = b

    def draw_music_empty(self, p, c):
        p.setPen(QColor(255, 255, 255, 90))
        p.setFont(icon_font(18))
        p.drawText(QRectF(c.left(), c.top() + 14, c.width(), 34), Qt.AlignCenter, "")
        p.setFont(font(10.5, True))
        p.setPen(QColor(255, 255, 255, 210))
        p.drawText(QRectF(c.left(), c.top() + 50, c.width(), 22), Qt.AlignCenter, "Aucune musique en cours")
        p.setFont(font(9))
        p.setPen(QColor(255, 255, 255, 120))
        p.drawText(QRectF(c.left(), c.top() + 72, c.width(), 18), Qt.AlignCenter,
                   "Spotify, YouTube, Deezer… s'affichent ici")

    def draw_prayer(self, p, c):
        st = self.pr
        if not st:
            return
        W = PR_SIZE[0]
        x, y = c.center().x() - W / 2, c.top()
        now = datetime.datetime.now(ALGIERS)
        white = lambda a: QColor(255, 255, 255, a)
        # en-tête : ville + dates
        p.setFont(font(13, True))
        p.setPen(white(245))
        p.drawText(QPointF(x + 26, y + 36), "Alger")
        aw = QFontMetrics(font(13, True)).horizontalAdvance("Alger")
        p.setFont(font(8.5))
        p.setPen(white(110))
        p.drawText(QPointF(x + 26 + aw + 8, y + 36), "heure d'Alger")
        date = f"{JOURS[now.weekday()].capitalize()} {now.day} {MOIS[now.month - 1]}"
        if st["hijri"]:
            date += f"   ·   {st['hijri']}"
        p.setFont(font(9.5))
        p.setPen(white(150))
        p.drawText(QPointF(x + 26, y + 57), date)
        # compte à rebours
        rem = (st["next_dt"] - now).total_seconds()
        p.setFont(font(9))
        p.setPen(white(150))
        p.drawText(QRectF(x, y + 16, W - 26, 18), Qt.AlignRight | Qt.AlignVCenter,
                   f"{st['next_name']}{' demain' if st['tomorrow'] else ''} dans")
        p.setFont(font(17, True))
        p.setPen(GOLD)
        p.drawText(QRectF(x, y + 33, W - 26, 30), Qt.AlignRight | Qt.AlignVCenter, self.countdown(rem, long=True))

        # frise de la journée
        times = st["shown"]
        n = len(times)
        cw = (W - 40) / n
        cxs = [x + 20 + cw * (i + 0.5) for i in range(n)]
        ly = y + 82
        p.setPen(QPen(white(34), 2))
        p.drawLine(QPointF(cxs[0], ly), QPointF(cxs[-1], ly))
        if st["tomorrow"] or now <= times[0]:
            px = None
        elif now >= times[-1]:
            px = cxs[-1]
        else:
            i = max(k for k in range(n) if times[k] <= now)
            frac = (now - times[i]).total_seconds() / max(1, (times[i + 1] - times[i]).total_seconds())
            px = cxs[i] + (cxs[i + 1] - cxs[i]) * frac
        if px is not None:
            gl = QLinearGradient(QPointF(cxs[0], ly), QPointF(px, ly))
            gl.setColorAt(0, QColor(GOLD.red(), GOLD.green(), GOLD.blue(), 60))
            gl.setColorAt(1, QColor(GOLD.red(), GOLD.green(), GOLD.blue(), 220))
            p.setPen(QPen(gl, 2.4))
            p.drawLine(QPointF(cxs[0], ly), QPointF(px, ly))
        nidx = st["next_idx"]
        p.setPen(Qt.NoPen)
        for i, cx in enumerate(cxs):
            passed = not st["tomorrow"] and times[i] <= now
            if i == nidx:
                p.setBrush(Qt.NoBrush)
                p.setPen(QPen(GOLD, 1.6))
                p.drawEllipse(QPointF(cx, ly), 5, 5)
                p.setPen(Qt.NoPen)
            else:
                p.setBrush(GOLD if passed else white(70))
                p.drawEllipse(QPointF(cx, ly), 3, 3)
        if px is not None:                      # « maintenant » qui respire
            pulse = 0.5 + 0.5 * math.sin(time.monotonic() * 2.4)
            p.setBrush(QColor(GOLD.red(), GOLD.green(), GOLD.blue(), int(40 + 40 * pulse)))
            p.drawEllipse(QPointF(px, ly), 8 + 3 * pulse, 8 + 3 * pulse)
            p.setBrush(QColor(255, 244, 220))
            p.drawEllipse(QPointF(px, ly), 4, 4)

        # colonnes
        for i, cx in enumerate(cxs):
            name, ar = PR_NAMES[i]
            passed = not st["tomorrow"] and times[i] <= now
            is_next = i == nidx
            sunrise = i == 1
            card = QRectF(cx - cw / 2 + 4, y + 96, cw - 8, 78)
            if is_next:
                p.setBrush(QColor(GOLD.red(), GOLD.green(), GOLD.blue(), 34))
                p.setPen(QPen(QColor(GOLD.red(), GOLD.green(), GOLD.blue(), 110), 1))
                p.drawRoundedRect(card, 14, 14)
            a_name = 245 if is_next else 105 if passed else 200
            a_time = 120 if passed else 235
            if sunrise:
                a_name, a_time = int(a_name * 0.75), int(a_time * 0.75)
            p.setFont(font(10, True))
            p.setPen(white(a_name))
            p.drawText(QRectF(card.left(), card.top() + 6, card.width(), 18), Qt.AlignCenter, name)
            p.setFont(font(9))
            p.setPen(white(int(a_name * 0.55)))
            p.drawText(QRectF(card.left(), card.top() + 24, card.width(), 18), Qt.AlignCenter, ar)
            p.setFont(font(12 if sunrise else 14, True))
            p.setPen(GOLD if is_next else white(a_time))
            p.drawText(QRectF(card.left(), card.top() + 44, card.width(), 26), Qt.AlignCenter, f"{times[i]:%H:%M}")

    def draw_wa(self, p, c, interactive):
        W = WA_SIZE[0]
        x, y = c.center().x() - W / 2, c.top()
        cur = QPointF(self.mapFromGlobal(QCursor.pos()))
        white = lambda a: QColor(255, 255, 255, a)
        # en-tête
        p.setPen(Qt.NoPen)
        p.setBrush(WA_GREEN)
        p.drawEllipse(QRectF(x + 24, y + 19, 24, 24))
        p.setPen(white(255))
        p.setFont(icon_font(9))
        p.drawText(QRectF(x + 24, y + 19, 24, 24), Qt.AlignCenter, "")
        p.setFont(font(12.5, True))
        p.drawText(QPointF(x + 58, y + 37), "WhatsApp")
        ob = QRectF(x + W - 24 - 104, y + 18, 104, 26)
        p.setPen(Qt.NoPen)
        p.setBrush(white(40 if ob.contains(cur) else 22))
        p.drawRoundedRect(ob, 13, 13)
        p.setFont(font(9, True))
        p.setPen(white(220))
        p.drawText(ob, Qt.AlignCenter, "Ouvrir l'appli")
        if interactive:
            self.hits["wa:open"] = ob

        favs = self.wa.favorites[:5]
        slots = favs + ([None] if len(favs) < 5 else [])
        sw = (W - 40) / 5
        sx0 = x + 20 if not favs else c.center().x() - sw * len(slots) / 2   # contacts centrés
        for i, f in enumerate(slots):
            cx = sx0 + sw * (i + 0.5)
            av = QRectF(cx - 23, y + 56, 46, 46)
            if f is None:                       # « + » pour ajouter
                hov = av.contains(cur)
                p.setBrush(white(20 if hov else 8))
                pen = QPen(white(110 if hov else 70), 1.4, Qt.DashLine)
                p.setPen(pen)
                p.drawEllipse(av)
                p.setFont(icon_font(12))
                p.setPen(white(200))
                p.drawText(av, Qt.AlignCenter, "")
                p.setFont(font(9))
                p.setPen(white(130))
                p.drawText(QRectF(cx - sw / 2, y + 106, sw, 18), Qt.AlignCenter, "Ajouter")
                if interactive:
                    self.hits["wa:add"] = av.adjusted(-4, -4, 4, 22)
                continue
            p.setPen(Qt.NoPen)
            p.setBrush(avatar_color(f["name"]))
            p.drawEllipse(av)
            p.setFont(font(12.5, True))
            p.setPen(white(250))
            p.drawText(av, Qt.AlignCenter, initials(f["name"]))
            fn = font(9.5, True)
            p.setFont(fn)
            p.setPen(white(225))
            p.drawText(QRectF(cx - sw / 2, y + 106, sw, 18), Qt.AlignCenter,
                       QFontMetrics(fn).elidedText(f["name"], Qt.ElideRight, int(sw - 6)))
            for kind, glyph, dx in (("chat", "", -16), ("call", "", 16)):
                b = QRectF(cx + dx - 13, y + 130, 26, 26)
                hov = b.contains(cur)
                p.setPen(Qt.NoPen)
                if kind == "call":
                    p.setBrush(QColor(WA_GREEN.red(), WA_GREEN.green(), WA_GREEN.blue(), 255 if hov else 200))
                else:
                    p.setBrush(white(55 if hov else 28))
                p.drawEllipse(b)
                p.setFont(icon_font(8.5))
                p.setPen(white(250))
                p.drawText(b, Qt.AlignCenter, glyph)
                if interactive:
                    self.hits[f"wa:{kind}:{i}"] = b.adjusted(-3, -3, 3, 3)
            if interactive:
                self.hits[f"wa:chat:{i}:av"] = av
        if not favs:
            p.setFont(font(9.5))
            p.setPen(white(130))
            p.drawText(QRectF(x + 20 + sw + 6, y + 56, W - 40 - sw - 12, 50),
                       Qt.AlignVCenter | Qt.AlignLeft | Qt.TextWordWrap,
                       "Ajoute tes contacts favoris : un clic pour leur écrire ou les appeler.")
        if time.monotonic() < self.wa_status_until:
            p.setFont(font(9))
            p.setPen(white(160))
            p.drawText(QRectF(x, y + 160, W, 18), Qt.AlignCenter, self.wa_status)
        elif self.wa.listener_ok is False:
            p.setFont(font(8.5))
            p.setPen(white(110))
            p.drawText(QRectF(x, y + 160, W, 18), Qt.AlignCenter,
                       "Appels entrants : autorise l'accès aux notifications dans Windows")

    def draw_call(self, p, r, interactive):
        call = self.call
        W = CALL_SIZE[0]
        x, y = r.center().x() - W / 2, r.top()
        t = time.monotonic()
        av = QRectF(x + 16, y + 14, 50, 50)
        for k in range(2):                       # ondes autour de l'avatar
            ph = (t * 0.8 + k * 0.5) % 1
            rr = 25 + ph * 9
            p.setBrush(Qt.NoBrush)
            p.setPen(QPen(QColor(WA_GREEN.red(), WA_GREEN.green(), WA_GREEN.blue(), int((1 - ph) * 170)), 2))
            p.drawEllipse(av.center(), rr, rr)
        p.setPen(Qt.NoPen)
        p.setBrush(avatar_color(call["name"]))
        p.drawEllipse(av)
        p.setFont(font(13, True))
        p.setPen(QColor(255, 255, 255))
        p.drawText(av, Qt.AlignCenter, initials(call["name"]))
        p.setFont(font(9))
        p.setPen(QColor(255, 255, 255, 150))
        p.drawText(QPointF(x + 82, y + 33), f"WhatsApp · {'Appel vidéo' if call['video'] else 'Appel vocal'}")
        fn = font(14, True)
        p.setFont(fn)
        p.setPen(QColor(255, 255, 255))
        p.drawText(QPointF(x + 82, y + 56), QFontMetrics(fn).elidedText(call["name"], Qt.ElideRight, W - 82 - 130))
        cur = QPointF(self.mapFromGlobal(QCursor.pos()))
        for key, rect, col, glyph in (("decline", QRectF(x + W - 122, y + 17, 44, 44), QColor(255, 59, 48), ""),
                                      ("accept", QRectF(x + W - 64, y + 17, 44, 44), QColor(52, 199, 89), "")):
            if rect.contains(cur):
                col = col.lighter(115)
            p.setPen(Qt.NoPen)
            p.setBrush(col)
            p.drawEllipse(rect)
            p.setFont(icon_font(13))
            p.setPen(QColor(255, 255, 255))
            p.drawText(rect, Qt.AlignCenter, glyph)
            if interactive:
                self.hits["call:" + key] = rect

    def draw_music(self, p, r, interactive):
        x, y = r.left(), r.top()
        pad = 20
        art = QRectF(x + pad, y + pad, 76, 76)
        self.draw_art(p, art, 14)

        tx = art.right() + 16
        tw = int(x + LEFT_W - 18 - tx)
        ft, fa = font(14, True), font(10.5)
        p.setFont(ft)
        p.setPen(QColor(255, 255, 255))
        p.drawText(QPointF(tx, y + pad + 32), QFontMetrics(ft).elidedText(self.title, Qt.ElideRight, tw))
        p.setFont(fa)
        p.setPen(QColor(255, 255, 255, 140))
        sub = self.artist + (f" — {self.album}" if self.album else "")
        p.drawText(QPointF(tx, y + pad + 54), QFontMetrics(fa).elidedText(sub, Qt.ElideRight, tw))

        # barre de progression (ou jauge de volume pendant un réglage)
        py = y + 118
        bar = QRectF(x + pad + 54, py - 2.5, LEFT_W - 2 * pad - 54 - 62, 5)
        vol_mode = time.monotonic() < self.vol_until
        if vol_mode:
            self.draw_volume_row(p, bar)
        else:
            fm = font(11)
            p.setFont(fm)
            p.setPen(QColor(255, 255, 255, 230))
            p.drawText(QRectF(x + pad, py - 12, 50, 24), Qt.AlignVCenter | Qt.AlignLeft, fmt(self.pos))
            p.drawText(QRectF(x + LEFT_W - pad - 56, py - 12, 56, 24), Qt.AlignVCenter | Qt.AlignRight,
                       f"-{fmt(self.dur - self.pos)}" if self.dur else "--:--")
            p.setPen(Qt.NoPen)
            p.setBrush(QColor(255, 255, 255, 55))
            p.drawRoundedRect(bar, 2.5, 2.5)
            frac = self.pos / self.dur if self.dur else 0
            p.setBrush(QColor(255, 255, 255, 235))
            p.drawRoundedRect(QRectF(bar.left(), bar.top(), bar.width() * frac, bar.height()), 2.5, 2.5)

        # boutons
        cy, cx = y + 154, x + LEFT_W / 2
        btns = {"lyr": cx - 96, "prev": cx - 32, "play": cx + 32, "next": cx + 96}
        for name, bx in btns.items():
            self.draw_icon(p, name, QPointF(bx, cy))
        if interactive:
            self.hits = {n: QRectF(bx - 20, cy - 18, 40, 36) for n, bx in btns.items()}
            self.hits["volbar" if vol_mode else "bar"] = bar.adjusted(0, -9, 0, 9)

        self.lyr_hits = []
        if not self.show_lyrics or not self.lyr or r.width() < LEFT_W + 60:
            return
        p.setPen(QColor(255, 255, 255, 28))
        p.drawLine(QPointF(x + LEFT_W, y + 24), QPointF(x + LEFT_W, r.bottom() - 24))
        self.draw_lyrics(p, QRectF(x + LEFT_W + 22, y + 16, EXP_FULL[0] - LEFT_W - 44, r.height() - 32),
                         interactive)

    def draw_volume_row(self, p, bar, small=False):
        """Haut-parleur + jauge + pourcentage, à la place de la barre de progression."""
        lvl = self.vol_level
        p.save()
        p.setPen(Qt.NoPen)
        p.setBrush(QColor(255, 255, 255, 235))
        # icône haut-parleur à gauche de la jauge
        sx, cy = bar.left() - (18 if small else 34), bar.center().y()
        k = 0.75 if small else 1.0
        spk = QPainterPath()
        spk.moveTo(sx, cy - 3 * k); spk.lineTo(sx + 4 * k, cy - 3 * k); spk.lineTo(sx + 9 * k, cy - 7 * k)
        spk.lineTo(sx + 9 * k, cy + 7 * k); spk.lineTo(sx + 4 * k, cy + 3 * k); spk.lineTo(sx, cy + 3 * k)
        spk.closeSubpath()
        p.drawPath(spk)
        p.setBrush(Qt.NoBrush)
        pen = QColor(255, 255, 255, 235)
        for i in range(3 if lvl > 0.66 else 2 if lvl > 0.33 else 1 if lvl > 0 else 0):
            p.setPen(QPen(pen, 1.6 * k))
            rr = (4 + i * 4) * k
            p.drawArc(QRectF(sx + 9 * k - rr + 3, cy - rr, rr * 2, rr * 2), -45 * 16, 90 * 16)
        p.setPen(Qt.NoPen)
        h = bar.height()
        p.setBrush(QColor(255, 255, 255, 55))
        p.drawRoundedRect(bar, h / 2, h / 2)
        p.setBrush(self.accent if small else QColor(255, 255, 255, 235))
        p.drawRoundedRect(QRectF(bar.left(), bar.top(), bar.width() * lvl, h), h / 2, h / 2)
        f = font(8.5 if small else 11, small)
        p.setFont(f)
        p.setPen(QColor(255, 255, 255, 230))
        p.drawText(QRectF(bar.right() + 6, cy - 12, 50, 24), Qt.AlignVCenter | Qt.AlignLeft,
                   f"{round(lvl * 100)}%")
        p.restore()

    def draw_lyrics(self, p, lr, interactive=False):
        p.save()
        p.setClipRect(lr, Qt.IntersectClip)
        f = font(13.5, True)
        p.setFont(f)
        if not self.lyr:
            msg = {"loading": "Recherche des paroles…", "missing": "Pas de paroles trouvées",
                   "none": ""}.get(self.lyr_kind, "")
            p.setPen(QColor(255, 255, 255, 110))
            p.drawText(lr, Qt.AlignVCenter | Qt.AlignLeft | Qt.TextWordWrap, msg)
            p.restore()
            return
        idx = self.current_line()
        base = lr.top() + 14 - self.lyr_scroll.x
        op = p.opacity()
        cur = QPointF(self.mapFromGlobal(QCursor.pos()))
        clickable = interactive and self.lyr_kind == "synced"
        for i, (t, txt) in enumerate(self.lyr):
            ly = base + self.lyr_offsets[i]
            lh = self.lyr_heights[i]
            if ly + lh < lr.top() or ly > lr.bottom():
                continue
            fade = 1.0
            if ly < lr.top() + 8:
                fade = max(0.0, 1 - (lr.top() + 8 - ly) / 30)
            if ly + lh > lr.bottom() - 34:
                fade = min(fade, max(0.15, (lr.bottom() - ly) / 60))
            line_rect = QRectF(lr.left(), ly, lr.width(), lh + 4)
            hovered = clickable and line_rect.contains(cur) and lr.contains(cur)
            if clickable:
                # clic sur une ligne = aller à ce moment de la musique
                self.lyr_hits.append((line_rect.intersected(lr), t))
            p.setOpacity(op * fade)
            p.setPen(QColor(255, 255, 255, 255 if i == idx else 170 if hovered else 75))
            p.drawText(line_rect, Qt.TextWordWrap | Qt.AlignLeft, txt)
        p.setOpacity(op)
        p.restore()

    def draw_icon(self, p, name, c):
        p.save()
        p.setPen(Qt.NoPen)
        white = QColor(255, 255, 255, 235)
        p.setBrush(white)

        def tri(cx, dirn, s=9.0):
            path = QPainterPath()
            path.moveTo(cx - dirn * s * 0.5, c.y() - s * 0.6)
            path.lineTo(cx + dirn * s * 0.6, c.y())
            path.lineTo(cx - dirn * s * 0.5, c.y() + s * 0.6)
            path.closeSubpath()
            p.drawPath(path)

        if name == "play":
            if self.playing:
                p.drawRoundedRect(QRectF(c.x() - 7, c.y() - 10, 5, 20), 1.5, 1.5)
                p.drawRoundedRect(QRectF(c.x() + 2, c.y() - 10, 5, 20), 1.5, 1.5)
            else:
                tri(c.x() + 1, 1, 17)
        elif name == "next":
            tri(c.x() - 5, 1, 12); tri(c.x() + 5, 1, 12)
        elif name == "prev":
            tri(c.x() + 5, -1, 12); tri(c.x() - 5, -1, 12)
        elif name == "lyr":
            if not self.show_lyrics:
                p.setBrush(QColor(255, 255, 255, 110))
            bubble = QPainterPath()
            bubble.addRoundedRect(QRectF(c.x() - 10, c.y() - 8, 20, 14), 4, 4)
            bubble.moveTo(c.x() - 5, c.y() + 5)
            bubble.lineTo(c.x() - 7, c.y() + 10)
            bubble.lineTo(c.x(), c.y() + 5)
            p.drawPath(bubble)
            p.setBrush(QColor(20, 20, 24))
            p.drawEllipse(QPointF(c.x() - 4, c.y() - 1), 2.2, 2.2)
            p.drawEllipse(QPointF(c.x() + 4, c.y() - 1), 2.2, 2.2)
        p.restore()

    # -------------------------------------------------- souris
    def mousePressEvent(self, ev):
        pt = ev.position()
        if ev.button() == Qt.RightButton:
            m = self.menu()
            for name, rect in self.hits.items():
                if name.startswith("wa:") and name.count(":") >= 2 and rect.contains(pt):
                    i = int(name.split(":")[2])
                    if i < len(self.wa.favorites):
                        f = self.wa.favorites[i]
                        m.insertSeparator(m.actions()[0])
                        first = m.actions()[0]
                        m.insertAction(first, self._act(m, f"Appel vidéo — {f['name']}", lambda: self.wa.call(f, True)))
                        m.insertAction(first, self._act(m, f"Retirer {f['name']} des favoris",
                                                        lambda: self._remove_fav(i)))
                    break
            m.exec(ev.globalPosition().toPoint())
            return
        for name, rect in self.hits.items():
            if rect.contains(pt):
                frac = max(0.0, min(1.0, (pt.x() - rect.left()) / rect.width()))
                if name.startswith("tab:"):
                    self.set_tab(name[4:])
                elif name.startswith("call:"):
                    if self.call:
                        self.call_dismissed = self.call["id"]
                        (self.wa.answer if name == "call:accept" else self.wa.decline)()
                        self.call = None
                elif name == "wa:open":
                    self.wa.open_app()
                elif name == "wa:add":
                    self.open_favorites()
                elif name.startswith("wa:"):
                    parts = name.split(":")
                    f = self.wa.favorites[int(parts[2])]
                    if parts[1] == "call":
                        self.wa.call(f)
                    elif len(parts) > 3:                  # clic sur l'avatar : ouvrir la discussion
                        self.wa.open_chat(f["phone"])
                        self.on_wa_status(f"Discussion avec {f['name']}")
                    else:                                 # bulle : écrire un message
                        self.open_compose(f)
                elif name == "upd":
                    self.start_update()
                elif name == "bar":
                    if self.dur:
                        self.pos = frac * self.dur
                        self.media.command("seek", self.pos)
                elif name == "volbar":
                    self.vol_level = frac
                    self.vol.set(frac)
                    self.vol_until = time.monotonic() + 1.6
                elif name == "lyr":
                    self.show_lyrics = not self.show_lyrics
                elif name == "play":
                    self.playing = not self.playing
                    self.media.command("toggle")
                else:
                    self.media.command(name)
                return
        for rect, t in self.lyr_hits:
            if rect.contains(pt):
                self.pos = t
                self.media.command("seek", t)
                return
        if self.e.x < 0.5:          # clic sur la pilule repliée → déplier 4 s
            self.pin_until = time.monotonic() + 4.0

    @staticmethod
    def _act(menu, text, fn):
        a = QAction(text, menu)
        a.triggered.connect(fn)
        return a

    def _remove_fav(self, i):
        if 0 <= i < len(self.wa.favorites):
            del self.wa.favorites[i]
            self.wa.save()

    def wheelEvent(self, ev):
        """Pavé tactile : glisser 2 doigts haut/bas sur l'île = volume."""
        if self.e.x > 0.5 and self.tab != "music":
            return
        dy = ev.angleDelta().y()
        if dy == 0:
            dy = ev.pixelDelta().y() * 2
        if dy == 0:
            return
        now = time.monotonic()
        if now >= self.vol_until:
            self.vol_level = self.vol.get()
        self.vol_level = max(0.0, min(1.0, self.vol_level + dy / 120 * 0.04))
        self.vol.set(self.vol_level)
        self.vol_until = now + 1.6
        self._set_interval(16)
        ev.accept()

    def menu(self):
        m = QMenu()
        a = QAction("Afficher les paroles", m, checkable=True, checked=self.show_lyrics)
        a.toggled.connect(lambda v: setattr(self, "show_lyrics", v))
        m.addAction(a)
        b = QAction("Lancer au démarrage de Windows", m, checkable=True, checked=autostart_enabled())
        b.toggled.connect(set_autostart)
        m.addAction(b)
        m.addAction("Contacts WhatsApp…", self.open_favorites)
        m.addSeparator()
        m.addAction("Quitter", QApplication.quit)
        return m


def tray_icon(size=64):
    pm = QPixmap(size, size)
    pm.fill(Qt.transparent)
    p = QPainter(pm)
    p.setRenderHint(QPainter.Antialiasing)
    p.scale(size / 64, size / 64)
    p.setBrush(QColor(10, 10, 12))
    p.setPen(QColor(255, 255, 255, 80))
    p.drawRoundedRect(QRectF(2, 20, 60, 24), 12, 12)
    p.setBrush(QColor(120, 170, 255))
    p.setPen(Qt.NoPen)
    for i, h in enumerate((8, 14, 10)):
        p.drawRoundedRect(QRectF(38 + i * 6, 32 - h / 2, 3.5, h), 1.5, 1.5)
    p.end()
    return QIcon(pm)


def main():
    # une seule île à la fois (si on relance l'exe, la 2e copie s'arrête)
    kernel32 = ctypes.windll.kernel32
    kernel32.CreateMutexW.restype = wintypes.HANDLE
    _mutex = kernel32.CreateMutexW(None, False, "PCIsland_single_instance")
    if kernel32.GetLastError() == 183:          # ERROR_ALREADY_EXISTS
        return
    app = QApplication(sys.argv)
    app.setWindowIcon(tray_icon())
    app.setQuitOnLastWindowClosed(False)
    media = MediaWorker()
    wa = WhatsApp(QSettings("PCIsland", "PCIsland"))
    island = Island(media, wa)
    media.start()
    wa.start()

    tray = QSystemTrayIcon(tray_icon(), app)
    tray.setToolTip(APP_NAME)
    menu = QMenu()
    a_lyr = menu.addAction("Afficher les paroles")
    a_lyr.setCheckable(True)
    a_lyr.toggled.connect(lambda v: setattr(island, "show_lyrics", v))
    a_disc = menu.addAction("Mode réduit (Ctrl+Alt+C)")
    a_disc.setCheckable(True)
    a_disc.toggled.connect(island.toggle_discreet)
    a_auto = menu.addAction("Lancer au démarrage de Windows")
    a_auto.setCheckable(True)
    a_auto.toggled.connect(set_autostart)
    menu.addAction("Contacts WhatsApp…", island.open_favorites)
    a_upd = menu.addAction("Mettre à jour")
    a_upd.triggered.connect(island.start_update)
    a_ver = menu.addAction(f"PC Island v{VERSION}")
    a_ver.setEnabled(False)
    menu.addSeparator()
    menu.addAction("Quitter", app.quit)

    def refresh():
        for act, val in ((a_lyr, island.show_lyrics), (a_disc, island.discreet),
                         (a_auto, autostart_enabled())):
            act.blockSignals(True); act.setChecked(val); act.blockSignals(False)
    menu.aboutToShow.connect(refresh)
    menu.aboutToShow.connect(lambda: (a_upd.setVisible(island.upd is not None),
                                      a_upd.setText(f"Mettre à jour → v{island.upd['version']}" if island.upd else "")))
    tray.setContextMenu(menu)
    tray.show()
    island._tray = tray
    sys.exit(app.exec())


if __name__ == "__main__":
    main()
