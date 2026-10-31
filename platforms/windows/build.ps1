param([string]$Stage='\\host.lan\Data\lean-quiet-windows\stage', [string]$Build='C:\QuietVM\lean-quiet-windows', [string]$Toolchain='\\host.lan\Data\lean-quiet-windows\toolchain', [string]$Sources='sources.txt', [string]$Name='LeanQuiet', [switch]$Console)
$ErrorActionPreference='Stop'
function Sync-Tree($from,$to) {
    & robocopy $from $to /E /NFL /NDL /NJH /NJS /NP | Out-Null
    if ($LASTEXITCODE -ge 8) { throw "Copy failed: $from" }
}
New-Item -ItemType Directory -Force $Build | Out-Null
Sync-Tree $Stage "$Build\stage"
Sync-Tree $Toolchain "$Build\lean"
$st="$Build\stage"; $tc="$Build\lean"; $obj="$Build\objects"; $app="$Build\app"
New-Item -ItemType Directory -Force $obj,$app | Out-Null
$env:PATH="$tc\bin;$env:PATH"
$cc="$tc\bin\leanc.exe"
$flags=@('-O2','-w','-I',"$st\sqlite",'-I',"$tc\include")
$sourceFiles=@(Get-Content "$st\$Sources")
$objects=@("$st\native\glue.o", "$st\native\crypto.o", "$st\native\sqlite.o", "$st\native\shell.o")
if($Sources -eq 'sources-restart.txt') { $objects += "$st\native\listener_fixture.o" }
$compilerHash=(Get-FileHash "$tc\bin\clang.exe" -Algorithm SHA256).Hash
$headerHash=(Get-FileHash "$tc\include\lean\lean.h" -Algorithm SHA256).Hash
foreach($src in $sourceFiles) {
    $inputFile=Join-Path $st $src
    $outputFile=Join-Path $obj (($src -replace '[/\\]','_')+'.o')
    $hash=(Get-FileHash $inputFile -Algorithm SHA256).Hash
    $hash += $compilerHash + $headerHash + ($flags -join " ")
    $objects+=$outputFile
    if((Test-Path $outputFile) -and (Test-Path "$outputFile.sha") -and (Get-Content "$outputFile.sha" -Raw).Trim() -eq $hash) { continue }
    Write-Output "Compile $src"
    & $cc @flags '-c' $inputFile '-o' $outputFile
    if($LASTEXITCODE) { throw "Compilation failed: $src" }
    Set-Content "$outputFile.sha" $hash
}
# A response file avoids Windows' command-line length limit. Only closure members link.
$link=@($objects)+@("$st\glue\liblq_crypto.a",'-luser32','-lgdi32','-lws2_32','-lbcrypt',"$st\glue\libntdll.a",'-luserenv','-o',"$app\$Name.exe")
if(!$Console) { $link += '-Wl,--subsystem,windows' }
($link | ForEach-Object { '"'+($_ -replace '\\','/')+'"' }) | Set-Content -Encoding ASCII "$Build\link.rsp"
& $cc "@$Build\link.rsp"
if($LASTEXITCODE) { throw 'Link failed' }
Sync-Tree "$st\assets" "$app\assets"
# The linked executable imports only Windows system DLLs (Windows 11 x64).
# Do not ship the compiler's unrelated DLLs with the application.
if($Name -eq 'LeanQuiet') {
    $archive="$Build\LeanQuiet-windows-x64.zip"
    Compress-Archive -Path "$app\LeanQuiet.exe","$app\assets" -DestinationPath $archive -Force
    Copy-Item $archive '\\host.lan\Data\lean-quiet-windows\results\LeanQuiet-windows-x64.zip' -Force
}
Write-Output "Built $app\$Name.exe"
