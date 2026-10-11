@echo off
chcp 65001 >nul
title LAN Transfer 2.0
cd /d "%~dp0"

set PY=
if exist "%USERPROFILE%\.workbuddy\binaries\python\envs\py39\Scripts\python.exe" set PY=%USERPROFILE%\.workbuddy\binaries\python\envs\py39\Scripts\python.exe
if "%PY%"=="" (where python >nul 2>nul && set PY=python)
if "%PY%"=="" (where py >nul 2>nul && set PY=py)
if "%PY%"=="" (
  echo [错误] 没有找到 Python，请先安装 Python 3.8 或以上版本。
  pause
  exit /b 1
)

"%PY%" server.py --open %*
echo.
pause
