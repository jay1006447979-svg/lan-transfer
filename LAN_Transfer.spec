# -*- mode: python ; coding: utf-8 -*-
"""
LAN Transfer 打包配置（PyInstaller）

打包命令：
    pyinstaller --clean --noconfirm LAN_Transfer.spec

产物：dist/LAN Transfer.exe
  - 单文件模式（onefile），双击即用
  - 带控制台窗口（用于显示使用说明与服务日志）
  - 不打包 shared_files 里的任何用户数据
"""

block_cipher = None

a = Analysis(
    ['launcher.py'],
    pathex=[],
    binaries=[],
    datas=[],
    hiddenimports=[
        # server 是通过 import server 动态加载的，且内部用到这些标准库，
        # 显式声明可避免打包器静态分析漏掉。
        # 注意：v2.2 起不再使用 cgi 模块（Python 3.13 已移除它），
        # 上传请求体是原始二进制直接落盘。
        'server',
        'http.server',
        'sqlite3',
        'zipfile',
        'zlib',
        'mimetypes',
        'hashlib',
        'hmac',
        'socket',
        'threading',
        'secrets',
        'uuid',
        'json',
        'struct',
        'urllib.parse',
        # http.server / zipfile 的间接依赖，必须显式带上
        'email',
        'email.parser',
        'email.message',
        'email.feedparser',
        'email.utils',
        'email.errors',
        'xml',
        'xml.etree.ElementTree',
        'http.client',
        'http.cookies',
        'collections',
        'html',
        'html.entities',
        'shutil',
        'tempfile',
        'webbrowser',
        'argparse',
    ],
    hookspath=[],
    hooksconfig={},
    runtime_hooks=[],
    # 显式排除体积大又用不到的东西，显著减小 EXE。
    # 注意：cgi / http.server / zipfile 会间接依赖 email、xml、urllib 等，
    # 这些**不能**排除，否则运行时报 No module named 'email'。
    excludes=[
        'tkinter', 'unittest', 'pydoc', 'doctest', 'test',
        'numpy', 'PIL', 'psutil', 'setuptools', 'pip',
        'pdb', 'lib2to3', 'distutils', 'multiprocessing',
        'asyncio', 'concurrent', 'ctypes.test', 'ssl', 'socket.test',
    ],
    win_no_prefer_redirects=False,
    win_private_assemblies=False,
    cipher=block_cipher,
    noarchive=False,
)

pyz = PYZ(a.pure, a.zipped_data, cipher=block_cipher)

exe = EXE(
    pyz,
    a.scripts,
    a.binaries,
    a.zipfiles,
    a.datas,
    [],
    name='LAN Transfer',
    debug=False,
    bootloader_ignore_signals=False,
    strip=False,
    upx=True,
    upx_exclude=[],
    runtime_tmpdir=None,
    console=True,          # 需要控制台来显示使用说明
    disable_windowed_traceback=False,
    argv_emulation=False,
    target_arch=None,
    codesign_identity=None,
    entitlements_file=None,
)
