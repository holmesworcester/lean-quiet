# Windows desktop

The Win32 shell runs `platforms.desktop.Main`, the same Lean application,
renderer, queries and TCP engine as Linux and macOS. It presents Lean's pixels
with GDI and uses a native Unicode editor for keyboard input, selection and
clipboard. System appearance follows Windows’ app-theme setting and updates on
Windows theme notifications. Community creation/join/approval, messages, received pictures,
reactions, community switching, settings, themes and zoom stay in shared Lean.

The shell supports resizing to the narrow layout, mouse wheel and the shared
scrollbar, hover/right-click actions, Ctrl+A/C/X/V, Enter to send, Shift+Enter,
Ctrl+plus/minus and Ctrl+0. Unicode scalar selections cross the UTF-16/CRLF
boundary explicitly. Windows per-monitor DPI and user zoom are separate;
Lean rasterizes at the current density. A resize retains the previous frame
until the shared desktop publishes its new layout.

As on Linux, scrolling uses the shared desktop path. The AppKit-specific
native momentum compositor is not used. Desktop camera/photo picking remains
unavailable, matching the other desktop shells. Mobile-only OS integrations
are not emulated. The shell does not expose a command socket.

## Build and launch

The staging host needs the repository's Lean 4.34.0 toolchain, Python 3,
Pillow/fontTools and font prerequisites from `docs/BUILD.md`, Rust with the
`x86_64-pc-windows-gnu` target, curl, zstd, rsync, and the Debian/Ubuntu
`clang`, `binutils-mingw-w64-x86-64` and `mingw-w64-x86-64-dev` packages. The latter
supplies the Windows import library used by Rust's standard library.

All generated files go under `out/`. Use a worktree on `/mnt/storage`, set
`TMPDIR=/mnt/storage/holmes-tmp`, and check free space before the first build.
`toolchain.sh` verifies the pinned official Windows Lean archive's SHA-256.
The host emits the exact shared desktop C closure. The staging host cross-compiles the small Win32/SQLite layer against the
Windows SDK. The Windows VM compiles the generated Lean C and links it using
that Windows compiler/runtime and the same Rust cryptography used by the phones.

The provisioned VM defaults to `/mnt/storage/windows-quiet-vm`; override with
`WINDOWS_VM`. Its `vm.py` runner must be active in a logged-in, unlocked Windows
11 x64 desktop, with `\\host.lan\Data` mapped to its narrow shared folder.
Open the VM's `open-console.sh` RDP viewer before UI tests. The runner serializes
PowerShell jobs; `ship.sh` also takes `WINDOWS_LOCK` (default
`/mnt/storage/holmes-wt/winvm.lock`). A timeout is a failed run, not cancellation
of a guest job; inspect the job log before retrying.

```sh
mise run windows:build
mise run windows:run
```

The portable archive is `out/windows/LeanQuiet-windows-x64.zip`; extract it and
open `LeanQuiet.exe` on Windows 11 x64. It needs no Lean installation.

The app is `C:\QuietVM\lean-quiet-windows\app\LeanQuiet.exe`.
`windows:run` creates a **Lean Quiet** desktop shortcut and opens the app.
Assets resolve beside the executable, independent of the launch directory.
Normal data lives in `%LOCALAPPDATA%\LeanQuiet\quiet.db`; `QUIET_DB` overrides
it. `--demo` seeds only a fresh database and disables networking; `--offline`
disables networking without seeding. Normal launches use the real TCP engine.
`--chaos N` and `--scroll-fixture` are the existing shared desktop fixtures.
This is an unsigned development build; distribution signing is separate work.

## Tests and release gates

- `mise run windows:input`: deterministic sanitizer tests of the running shell's
  UTF-16/scalar and CRLF/LF conversion, including Hebrew, Japanese, emoji,
  empty input and out-of-range selection positions. Default local CI's `app`
  gate invokes this task alongside the shared application suites.
- `mise run host:desktop`: shared desktop behavior, layout rendering, and proof
  audits. The Windows port reuses that code without forking its UI.
- `mise run windows:e2e`: includes staging and native builds, then runs the real
  encrypted TCP join/sync/removal/rejoin suite and the retained-listener
  close/rebind tests as Windows executables. It extracts the portable archive into a fresh folder and drives its native window using
  Windows `SendInput` mouse/keyboard/clipboard input, checks pixels, Unicode messages,
  scrolling, ten repeated resize/menu cycles, community switching, theme, zoom,
  fresh onboarding, persistence and closing from the Windows system menu.

`ci/local.sh windows-ui` is manual dispatch on the provisioned VM;
`ci/local.sh release-windows` is the Windows release gate. Both invoke the same
`windows:e2e` task and propagate failures. This repository uses local CI rather
than GitHub Actions. Retain `out/windows` and `out/ci/release-windows.log` with
release artifacts. The guest's `test/` and `network/` directories retain logs,
state, test-only databases and failure screenshots, copied back even on failure.
Tests use fresh databases and reap only their own app processes. The elevated
guest runner temporarily blocks external inbound TCP to the two test executables
(Windows exempts their loopback traffic), preventing firewall dialogs from
interrupting UI automation; it removes its own rules afterwards. Keep the desktop
idle while the suite owns the VM. `QUIET_INPUT_TRACE=1` retains native event traces
for diagnosing input failures. Ordinary launches do not enable tracing.
