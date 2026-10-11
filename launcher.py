#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
LAN Transfer - EXE 启动器

双击 EXE 时的入口：打印使用说明 → 冻结/打包环境下的默认参数处理
→ 拉起 server.main()。

之所以单独一个文件：
  - 打包成 EXE 后 `__file__` 指向临时解包目录（_MEIPASS），
    共享目录必须落在 EXE 自身所在的文件夹，所以在这里统一改写 sys.argv。
  - 使用说明放在这里，方便单独维护文案。
"""

from __future__ import annotations

import os
import sys
import time


APP_TITLE = "LAN Transfer 2.0"
LINE = "=" * 64


def _is_frozen() -> bool:
    """是否由 PyInstaller 打包运行。"""
    return getattr(sys, "frozen", False)


def _exe_dir() -> str:
    """
    返回程序所在目录：
      - 打包后 → EXE 文件所在目录（不是临时解包目录）
      - 源码运行 → 脚本所在目录
    """
    if _is_frozen():
        return os.path.dirname(os.path.abspath(sys.executable))
    return os.path.dirname(os.path.abspath(__file__))


def print_usage(argv: list) -> None:
    """打印使用说明。"""
    exe = os.path.basename(sys.executable if _is_frozen() else __file__)
    share = "shared_files（本程序同目录）"

    print()
    print(LINE)
    print(f"  {APP_TITLE}  -  局域网文件 / 文字传输工具")
    print(LINE)
    print()
    print("  【这是什么】")
    print("    把手机、平板、其它电脑和本机连在同一个 Wi-Fi / 局域网里，")
    print(f"    用浏览器互相传文件和文字。对方不需要安装任何软件。")
    print()
    print("  【怎么用】")
    print("    1. 启动后，下面会列出几个网址（形如 http://192.168.x.x:9876）")
    print("    2. 在另一台设备（手机等）的浏览器里输入那个网址")
    print("    3. 打开网页后：")
    print("         · 「文字」页  → 发文字、读剪贴板、看最新内容")
    print("         · 「文件」页  → 上传 / 下载 / 删除文件与文件夹")
    print("         · 「记录」页  → 查看文字历史")
    print()
    print("  【共享目录】")
    print(f"    {share}")
    print("    放到这个文件夹里的东西，手机都能看到并下载；")
    print("    手机上传的文件也会存到这里。")
    print()
    print("  【上传大文件】")
    print("    自动分块 + 断点续传。中途断网、锁屏、关掉网页都不要紧，")
    print("    重新选择同一个文件会接着传，不用从头再来。")
    print()
    print("  【手机上选不了文件夹？】")
    print("    这是手机浏览器的限制（桌面浏览器才支持选目录）。")
    print("    手机上请先把文件夹压缩成 zip 再上传，或改用多选文件。")
    print()
    print("  【关闭服务】")
    print("    在本窗口按 Ctrl + C 即可停止。")
    print()
    print("  【常用参数】")
    print(f"    {exe} -p 8080              指定端口（默认 9876）")
    print(f"    {exe} -d D:\\share          指定共享目录")
    print(f"    {exe} --read-only          只读模式（别人只能下载）")
    print(f"    {exe} --token 密码          启用访问令牌")
    print(f"    {exe} --open               启动后自动打开本机网页")
    print(f"    {exe} -h                   查看全部参数")
    print()
    print("  【注意】")
    print("    这是局域网明文 HTTP 工具，请不要在公网直接暴露。")
    print("    能访问该网址的人都能查看 / 下载 / 删除共享目录里的文件。")
    print()
    print(LINE)
    print()


def _strip_own_args(argv: list) -> list:
    # --no-pause 由打包器（如某些启动脚本）注入，避免无控制台时挂起
    return [a for a in argv if a != "--no-pause"]


def main() -> int:
    argv = _strip_own_args(sys.argv[1:])

    # -h / --help 交给 server 的 argparse 处理，不打印长说明
    wants_help = any(a in ("-h", "--help") for a in argv)

    if not wants_help:
        print_usage(argv)
        # 打包运行时暂停一下，方便用户看清说明；源码运行也保留，体验一致
        try:
            input("  按回车键启动服务……")
        except (EOFError, KeyboardInterrupt):
            print("\n  已取消。\n")
            return 0

    # 打包运行时，默认共享目录 = EXE 同目录下的 shared_files
    has_dir = any(a in ("-d", "--dir") or a.startswith("--dir=") for a in argv)
    if not has_dir:
        default_share = os.path.join(_exe_dir(), "shared_files")
        argv += ["-d", default_share]

    # 让 server 的 argparse 看到我们构造好的参数
    sys.argv = [sys.argv[0]] + argv

    try:
        import server
    except Exception as e:  # pragma: no cover
        print(f"\n  [错误] 无法加载服务模块：{e}")
        try:
            input("\n  按回车键退出……")
        except Exception:
            pass
        return 1

    try:
        server.main()
    except SystemExit:
        raise
    except KeyboardInterrupt:
        pass
    except Exception as e:  # pragma: no cover
        print(f"\n  [错误] 服务异常退出：{e}")
        import traceback
        traceback.print_exc()
        try:
            input("\n  按回车键退出……")
        except Exception:
            pass
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
