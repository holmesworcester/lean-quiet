$ErrorActionPreference='Stop'
$app='C:\QuietVM\lean-quiet-windows\app\LeanQuiet.exe'
$shortcut=(New-Object -ComObject WScript.Shell).CreateShortcut("$([Environment]::GetFolderPath('Desktop'))\Lean Quiet.lnk")
$shortcut.TargetPath=$app
$shortcut.WorkingDirectory=Split-Path $app
$shortcut.Save()
Start-Process $app -WorkingDirectory (Split-Path $app)
