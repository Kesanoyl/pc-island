# Build léger : pyinstaller island.spec
from PyInstaller.utils.hooks import collect_all, collect_submodules

datas, binaries, hiddenimports = collect_all("winrt")
hiddenimports += collect_submodules("pycaw") + collect_submodules("comtypes", filter=lambda n: ".test" not in n)

a = Analysis(
    ["island.py"],
    datas=datas,
    binaries=binaries,
    hiddenimports=hiddenimports,
    excludes=["tkinter", "unittest", "pydoc", "doctest", "PySide6.QtNetwork", "PySide6.QtQml",
              "PySide6.QtQuick", "PySide6.QtPdf", "PySide6.QtOpenGL", "PySide6.QtSvg",
              "numpy", "PIL", "setuptools", "pkg_resources", "multiprocessing", "packaging", "_pyrepl", "_pydecimal", "pydoc_data", "lib2to3",
              "ssl", "_ssl", "requests", "urllib3", "brotli", "_brotli", "backports", "zstandard",
              "idna", "charset_normalizer", "certifi", "comtypes.test", "http.server", "xmlrpc"],
)

# Qt embarque plein de choses inutiles ici : on les retire
DROP = ("opengl32sw", "Qt6Quick", "Qt6Qml", "Qt6Pdf", "Qt6Network", "Qt6OpenGL", "Qt6Svg",
        "Qt6VirtualKeyboard", "qdirect2d", "qtiff", "qsvg", "qpdf", "qicns", "qtga", "qwbmp",
        "qnetworklistmanager", "qtuiotouchplugin", "qcertonlybackend", "qschannelbackend",
        "qopensslbackend", "QtNetwork.pyd", "translations",
        "libcrypto", "libssl", "_ssl.pyd", "_brotli", "_zstd")
keep = lambda name: not any(d.lower() in name.lower() for d in DROP)
a.binaries = [b for b in a.binaries if keep(b[0])]
a.datas = [d for d in a.datas if keep(d[0])]

pyz = PYZ(a.pure)
exe = EXE(pyz, a.scripts, [], exclude_binaries=True, name="PC Island", icon="island.ico",
          console=False, upx=False)
coll = COLLECT(exe, a.binaries, a.datas, name="PC Island", upx=False)
