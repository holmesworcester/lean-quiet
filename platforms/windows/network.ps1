$ErrorActionPreference='Stop'
$b='C:\QuietVM\lean-quiet-windows'
$out="$b\network"; New-Item -ItemType Directory -Force $out | Out-Null
$rules=@()
try {
 foreach($suite in @(@('JoinTcp','sources-jointcp.txt'),@('Restart','sources-restart.txt'))) {
  & '\\host.lan\Data\lean-quiet-windows\stage\windows\build.ps1' -Sources $suite[1] -Name $suite[0] -Console
  $name=$suite[0]
  $rule="LeanQuiet-test-$name-$([Guid]::NewGuid().ToString('N'))"
  # Windows exempts loopback. Block external access to these test-only listeners
  # and suppress the asynchronous firewall consent dialog during UI automation.
  New-NetFirewallRule -Name $rule -DisplayName $rule -Program "$b\app\$name.exe" -Direction Inbound -Action Block -Protocol TCP -Profile Any | Out-Null
  $rules+=$rule
  $p=Start-Process "$b\app\$name.exe" -ArgumentList "$out\join" -WorkingDirectory "$b\app" -PassThru -RedirectStandardOutput "$out\$name.log" -RedirectStandardError "$out\$name.err.log"
  $null=$p.Handle
  if(!$p.WaitForExit(240000)) {$p.Kill();$p.WaitForExit();throw "$name timed out"}
  Get-Content "$out\$name.log"
  if($p.ExitCode -ne 0) {Get-Content "$out\$name.err.log";throw "$name exited $($p.ExitCode)"}
 }
 @{passed=$true;suites=@('tests.engine.JoinTcp','tests.engine.Restart')} | ConvertTo-Json | Set-Content "$out\network-report.json"
} finally {
 foreach($rule in $rules) { Remove-NetFirewallRule -Name $rule }
 & robocopy $out '\\host.lan\Data\lean-quiet-windows\results' /E /NFL /NDL /NJH /NJS /NP | Out-Null
 if($LASTEXITCODE -ge 8) {throw 'Network artifacts copy failed'}
}
