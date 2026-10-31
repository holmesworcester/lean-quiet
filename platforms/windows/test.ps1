param([string]$Build='C:\QuietVM\lean-quiet-windows')
$ErrorActionPreference='Stop'
Add-Type -AssemblyName System.Windows.Forms,System.Drawing
Add-Type @'
using System;
using System.Runtime.InteropServices;
public static class Win {
 [StructLayout(LayoutKind.Sequential)] public struct Point {public int x,y;}
 [StructLayout(LayoutKind.Sequential)] public struct Rect {public int l,t,r,b;}
 [DllImport("user32.dll")] public static extern IntPtr GetForegroundWindow();
 [DllImport("user32.dll")] public static extern bool SetWindowPos(IntPtr h,IntPtr after,int x,int y,int w,int height,uint flags);
 [DllImport("user32.dll")] public static extern bool SetForegroundWindow(IntPtr h);
 [DllImport("user32.dll")] public static extern bool GetClientRect(IntPtr h,out Rect r);
 [DllImport("user32.dll")] public static extern bool GetWindowRect(IntPtr h,out Rect r);
 [DllImport("user32.dll")] public static extern bool ClientToScreen(IntPtr h,ref Point p);
 [StructLayout(LayoutKind.Sequential)] public struct MouseInput {public int dx,dy; public uint data,flags,time;public UIntPtr extra;}
 [StructLayout(LayoutKind.Sequential)] public struct Input {public uint type;public MouseInput mouse;}
 [DllImport("user32.dll",SetLastError=true)] static extern uint SendInput(uint n,Input[] inputs,int size);
 [DllImport("user32.dll")] public static extern int GetSystemMetrics(int index);
 [DllImport("user32.dll")] public static extern bool GetCursorPos(out Point p);
 static Input Move(int x,int y) {return new Input {mouse=new MouseInput {dx=(x-GetSystemMetrics(76))*65535/(GetSystemMetrics(78)-1),dy=(y-GetSystemMetrics(77))*65535/(GetSystemMetrics(79)-1),flags=0xC001}};}
 static void Send(Input[] inputs) {if(SendInput((uint)inputs.Length,inputs,Marshal.SizeOf(typeof(Input)))!=inputs.Length) throw new System.ComponentModel.Win32Exception(Marshal.GetLastWin32Error());}
 public static void ClickScreen(int x,int y) {Send(new Input[]{Move(x,y),new Input {mouse=new MouseInput {flags=2}},new Input {mouse=new MouseInput {flags=4}}});}
 public static void WheelScreen(int x,int y,int delta) {Send(new Input[]{Move(x,y),new Input {mouse=new MouseInput {flags=0x800,data=unchecked((uint)delta)}}});}
 [DllImport("user32.dll")] public static extern bool SetCursorPos(int x,int y);
 [DllImport("user32.dll")] public static extern void mouse_event(uint f,uint x,uint y,int data,UIntPtr extra);
 [DllImport("user32.dll")] public static extern bool MoveWindow(IntPtr h,int x,int y,int w,int hh,bool repaint);
 [DllImport("user32.dll")] public static extern bool PostMessage(IntPtr h,uint m,IntPtr w,IntPtr l);
}
'@
$out="$Build\test"; New-Item -ItemType Directory -Force $out | Out-Null
# Exercise the distributable, with no compiler/runtime DLLs beside it.
$portable="$out\portable-$([Guid]::NewGuid().ToString('N'))"
Expand-Archive "$Build\LeanQuiet-windows-x64.zip" -DestinationPath $portable
$env:QUIET_DB="$out\quiet-$([Guid]::NewGuid().ToString('N')).db"
$env:QUIET_STATE="$out\state.txt"
$env:QUIET_INPUT_TRACE="1"
$script:checks=0; $script:proc=$null; $script:hwnd=[IntPtr]::Zero
function Lines { if(Test-Path $env:QUIET_STATE) { return @(Get-Content -Encoding UTF8 $env:QUIET_STATE) }; return @() }
function Wait-For([scriptblock]$test,[string]$label) {
 $end=(Get-Date).AddSeconds(45)
 do { if($script:proc -and $script:proc.HasExited) {throw "App exited: $($script:proc.ExitCode): $label"}; if(& $test) {return}; Start-Sleep -Milliseconds 100 } while((Get-Date) -lt $end)
 throw "Timed out: $label; state: $((Lines) -join '|')"
}
function Check($ok,[string]$label) {if(!$ok){throw $label}; $script:checks++; Write-Output "ok $label"}
function Click([int]$x,[int]$y) {
 if([Win]::GetForegroundWindow() -ne $script:hwnd) { throw "App lost foreground before native input" }
 $p=New-Object Win+Point; $p.x=$x;$p.y=$y; [void][Win]::ClientToScreen($script:hwnd,[ref]$p)
 [Win]::ClickScreen($p.x,$p.y)
 Start-Sleep -Milliseconds 100
 $actual=New-Object Win+Point;[void][Win]::GetCursorPos([ref]$actual)
 Write-Output "click client $x,$y screen $($p.x),$($p.y) actual $($actual.x),$($actual.y) desktop $([Win]::GetSystemMetrics(78)),$([Win]::GetSystemMetrics(79))"
}
function Keys([string]$s) { [System.Windows.Forms.SendKeys]::SendWait($s); Start-Sleep -Milliseconds 100 }
function Paste([string]$s) { [System.Windows.Forms.Clipboard]::SetText($s); Keys '^v' }
function Resize([int]$w,[int]$h) {
 $r=New-Object Win+Rect;$c=New-Object Win+Rect
 [void][Win]::GetWindowRect($script:hwnd,[ref]$r);[void][Win]::GetClientRect($script:hwnd,[ref]$c)
 [void][Win]::MoveWindow($script:hwnd,20,20,$w+$r.r-$r.l-$c.r,$h+$r.b-$r.t-$c.b,$true)
 Wait-For { (Lines)[0] -eq "$w $h" } "resize $w $h"
}
function Shot([string]$name) {
 Start-Sleep -Milliseconds 300
 $r=New-Object Win+Rect;[void][Win]::GetClientRect($script:hwnd,[ref]$r)
 $p=New-Object Win+Point;[void][Win]::ClientToScreen($script:hwnd,[ref]$p)
 $bmp=New-Object Drawing.Bitmap($r.r,$r.b);$g=[Drawing.Graphics]::FromImage($bmp)
 $g.CopyFromScreen($p.x,$p.y,0,0,$bmp.Size);$g.Dispose();$bmp.Save("$out\$name.png");return $bmp
}
function Start-App($arguments,[string]$ready='App.PageId.chat') {
 Remove-Item $env:QUIET_STATE -ErrorAction SilentlyContinue
 $script:proc=Start-Process "$portable\LeanQuiet.exe" -ArgumentList $arguments -WorkingDirectory $portable -PassThru -RedirectStandardOutput "$out\app.log" -RedirectStandardError "$out\app.err.log"
 $null=$script:proc.Handle
 Wait-For { (Lines).Count -ge 8 -and (Lines)[3] -eq $ready } 'chat ready'
 $script:proc.Refresh();$script:hwnd=$script:proc.MainWindowHandle
 [void][Win]::SetWindowPos($script:hwnd,[IntPtr](-1),0,0,0,0,0x43)
 $r=New-Object Win+Rect; [void][Win]::GetWindowRect($script:hwnd,[ref]$r)
 [Win]::ClickScreen($r.l+100,$r.t+15)
 [void][Win]::SetForegroundWindow($script:hwnd); Start-Sleep -Milliseconds 400
 Wait-For { [Win]::GetForegroundWindow() -eq $script:hwnd } "native app foreground"
}
function Page-Click([string]$action) {
 Wait-For { @(Lines | Where-Object {$_ -like "action Pages.Act.$action *"}).Count -gt 0 } "page action $action"
 $row=(@(Lines | Where-Object {$_ -like "action Pages.Act.$action *"})[0] -split ' ')
 Click ([int]$row[-2]) ([int]$row[-1])
}
function Stop-App {
 if(![Win]::PostMessage($script:hwnd,16,[IntPtr]::Zero,[IntPtr]::Zero)) { throw "WM_CLOSE delivery failed" }
 if(!$script:proc.WaitForExit(15000)) {throw 'Window close did not exit'}
 Check ($script:proc.ExitCode -eq 0) "clean window close and writer drain (exit $($script:proc.ExitCode))"
 $script:proc=$null
}
try {
 Start-App @('--demo','--scroll-fixture')
 Resize 1000 760
 $systemDark=(Get-ItemProperty 'HKCU:\Software\Microsoft\Windows\CurrentVersion\Themes\Personalize' -Name AppsUseLightTheme -ErrorAction SilentlyContinue).AppsUseLightTheme -eq 0
 $rgb=if($systemDark){@(47,25,61)}else{@(118,71,199)}
 $im=Shot 'chat'; $c=$im.GetPixel(2,140); Check ($c.R -eq $rgb[0] -and $c.G -eq $rgb[1] -and $c.B -eq $rgb[2]) 'real Lean RGBA follows Windows system appearance';$im.Dispose()
 Check ([int](Lines)[5] -ge 42) 'shared demo and scroll history persisted'
 $ed=((Lines | Where-Object {$_ -like 'editor *'}) -split ' ')
 Click ([int]$ed[1]+20) ([int]$ed[2]+4)
 Keys 'Windows keyboard'
 Wait-For { (Lines)[4] -eq 'Windows keyboard' } 'native keyboard composer'
 Keys '^a';Keys '^c';Keys '{END}';Keys '^v'
 Wait-For {(Lines)[4] -eq 'Windows keyboardWindows keyboard'} 'copy and paste'
 Check $true 'native keyboard selection and clipboard roundtrip'
 Keys '^a'
 $unicode='Windows: '+[char]0x00E9+' '+[char]0x05E9+[char]0x05DC+[char]0x05D5+[char]0x05DD+' '+[char]0x65E5+[char]0x672C+' '+[char]::ConvertFromUtf32(0x1F642)
 Paste $unicode
 Wait-For {(Lines)[4] -eq $unicode} 'Unicode clipboard and surrogate pairs'
 Keys '^a'; Keys '^c'; Check ([Windows.Forms.Clipboard]::GetText() -eq $unicode) 'non-Latin and emoji clipboard survives exact roundtrip'
 Keys '{END}';Keys '+{ENTER}';Keys 'second line'
 Wait-For {((Lines) -join "`n").Contains("$unicode`nsecond line")} 'Shift Enter newline'
 Keys '^a';Paste $unicode
 Wait-For {(Lines)[4] -eq $unicode} 'replace multiline selection'
 $before=[int](Lines)[5];Keys '{ENTER}'
 Wait-For {(Lines)[4] -eq '' -and [int](Lines)[5] -gt $before} 'message sent'
 Check $true 'Return writes Unicode message through real engine'
 $im=Shot 'unicode-message';$im.Dispose()
 Keys '^0';Keys '^='
 Wait-For { (Lines) -contains 'zoom 110 dpi 176 cell 19' -or ((Lines | Where-Object {$_ -like 'zoom 110 *'}).Count -gt 0) } 'zoom in'
 Check $true 'shared zoom from Windows shortcut'
 Keys '^0'; Wait-For {((Lines | Where-Object {$_ -like 'zoom 100 *'}).Count -gt 0)} 'zoom reset'
 $old=(Lines)[7]
 $p=New-Object Win+Point;$p.x=700;$p.y=300;[void][Win]::ClientToScreen($script:hwnd,[ref]$p)
 [Win]::WheelScreen($p.x,$p.y,120)
 Wait-For {(Lines)[7] -ne $old} 'wheel scroll'
 Check $true 'wheel reaches older history'
 $im=Shot 'scrolled';$im.Dispose()
 Resize 390 760
 $im=Shot 'narrow';Check ($im.Width -eq 390 -and $im.GetPixel(100,140).R -eq 247) 'responsive narrow layout removes the desktop sidebar';$im.Dispose()
 Resize 1100 760
 for($i=0;$i -lt 10;$i++) {
  Resize 390 760
  Resize 1100 760
  Click 90 28
  Wait-For { @(Lines | Where-Object {$_ -like 'switch *'}).Count -gt 0 } "resize/menu cycle $i"
  Keys '{ESC}'
  Wait-For { @(Lines | Where-Object {$_ -like 'switch *'}).Count -eq 0 } 'menu closed'
 }
 Check $true 'ten consecutive native resize and menu cycles'
 Click 90 28
 Wait-For {((Lines | Where-Object {$_ -like 'switch *'}).Count -gt 0)} 'community menu'
 $choice=((@(Lines | Where-Object {$_ -match '^switch \d+ 0 '})[0]) -split ' ')
 Click ([int]$choice[3]) ([int]$choice[4])
 Wait-For {((Lines | Where-Object {$_ -like 'switch *'}).Count -eq 0)} 'switch choice'
 Wait-For { (Lines)[1] -eq 'Garden' -and [int](Lines)[5] -eq 0 } 'different community selected'
 Check $true 'native pointer switches community'
 Click 90 730
 Wait-For {(Lines) -contains 'Desktop.Context.settings'} 'settings'
 $a=((Lines | Where-Object {$_ -like 'appearance *'}) -split ' ');Click ([int]$a[1]) ([int]$a[2])
 Wait-For {(Lines) -contains 'drawer App.PageId.appearance'} 'appearance settings'
 $a=((Lines | Where-Object {$_ -like 'choice dark *'}) -split ' ');Click ([int]$a[2]) ([int]$a[3])
 Wait-For {(Lines) -contains 'theme dark'} 'dark theme'
 $im=Shot 'dark';$c=$im.GetPixel(2,140);Check ($c.R -eq 47 -and $c.G -eq 25 -and $c.B -eq 61) 'shared theme repaints native window';$im.Dispose()
 Stop-App
 Start-App @('--offline')
 Wait-For {(Lines) -contains 'theme dark'} 'persisted theme'
 Check $true 'database reopens with theme and communities'
 $im=Shot 'reopened';$im.Dispose()
 Stop-App
 # Exercise a system-menu close as well as ordinary WM_CLOSE.
 Start-App @('--offline')
 Keys '% ' # Alt+Space opens Windows' real system menu.
 Stop-App
 Check $true 'close exits the native system menu without stranding the Lean loop'
 $env:QUIET_DB="$out\onboarding-$([Guid]::NewGuid().ToString('N')).db"
 Start-App @('--offline') 'App.PageId.getStarted'
 Page-Click 'createCommunity'
 Wait-For {(Lines)[3] -eq 'App.PageId.create'} 'create form'
 Paste 'Windows UI'
 Wait-For {(Lines) -contains 'field Windows UI'} 'community name editor'
 Page-Click 'continue_'
 Wait-For {(Lines)[3] -eq 'App.PageId.createName'} 'display name form'
 Paste 'WinTester'
 Wait-For {(Lines) -contains 'field WinTester'} 'display name editor'
 Page-Click 'continue_'
 Wait-For {(Lines)[3] -eq 'App.PageId.chat' -and (Lines)[1] -eq 'Windows UI'} 'community founded from Windows UI'
 $ed=((Lines | Where-Object {$_ -like 'editor *'}) -split ' ')
 Click ([int]$ed[1]+20) ([int]$ed[2]+4)
 Keys 'Created and sent from Windows.'; Keys '{ENTER}'
 Wait-For {[int](Lines)[5] -eq 1} 'first onboarding message'
 $im=Shot 'onboarding';$im.Dispose()
 Check $true 'fresh onboarding and first message use actual native forms'
 Stop-App
 Start-App @('--offline')
 Wait-For {(Lines)[1] -eq 'Windows UI' -and [int](Lines)[5] -eq 1} 'onboarding persistence'
 Check $true 'new community and its message survive process restart'
 Stop-App
 @{checks=$script:checks;passed=$true;database=$env:QUIET_DB} | ConvertTo-Json | Set-Content "$out\report.json"
} catch {
 if($script:hwnd -ne [IntPtr]::Zero) {try {$im=Shot 'failure';$im.Dispose()}catch{}}
 throw
} finally {
 if($script:proc -and !$script:proc.HasExited) {$script:proc.Kill();$script:proc.WaitForExit()}
 & robocopy $out '\\host.lan\Data\lean-quiet-windows\results' /E /NFL /NDL /NJH /NJS /NP | Out-Null
 if($LASTEXITCODE -ge 8) {throw 'Artifact copy failed'}
}
