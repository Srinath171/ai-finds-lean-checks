@echo off
setlocal
set "TEAM_NO_PAUSE="
if "%~1"=="" goto run
if /I not "%~1"=="--no-pause" goto usage
if not "%~2"=="" goto usage
set "TEAM_NO_PAUSE=1"
:run
"%SystemRoot%\System32\WindowsPowerShell\v1.0\powershell.exe" -NoLogo -NoProfile -File "%~dp0proof-lab\continuation\team\Research-Team.ps1" -Action Start
set "TEAM_EXIT=%ERRORLEVEL%"
if not defined TEAM_NO_PAUSE pause
exit /b %TEAM_EXIT%
:usage
echo Usage: START-RESEARCH.cmd [--no-pause]
exit /b 2
