# macOS desktop

This AppKit shell runs `platforms.desktop.Main`, the same Lean event loop,
component queries, layout, hover, zoom, theme, and painter used by Linux.
`platforms/linux/Main.lean` and `platforms/macos/Main.lean` are thin entry points.
The retired Catalyst build ran the phone UI and is not part of this source tree.
Do not bring its separate desktop renderer or old package layout back.

The shell owns a resizable window, native Unicode text editing/IME, selection,
Command+A/C/X/V, Return to send, Shift+Return, clipboard, pointer/wheel input,
and presenting Lean's RGBA rows. Command+/− and Command+0 feed the shared zoom
policy. Device-pixel coordinates cross the seam. Lean rasterizes at the backing density,
while AppKit presents those pixels 1:1 on Retina displays. Native display
density and user zoom are independent, including after monitor changes.
Desktop camera/photo picking remains unavailable, as on Linux.

## Build and run

On the Linux staging machine, use Lean 4.34.0, Rust with the
`aarch64-apple-darwin` target, Python 3/Pillow/fontTools and the pinned Noto/CJK
inputs documented in `docs/BUILD.md`. `LEAN_SRC` and `UV_SRC` select Lean 4.34.0
and libuv 1.51.0 sources. All generated files go to `out/`.

The Mac needs Apple Silicon, macOS 14+, SSH and Xcode (set `DEVELOPER_DIR` to
its Contents/Developer path; the default is Xcode-26.3.0.app). No Xcode project,
simulator, Catalyst, external widget toolkit, or signing profile is needed.
The output is ad-hoc signed for local development; distribution/notarization
is separate work.

```sh
export MAC=holmes@100.101.83.38
mac-turn wait my-desktop-build
mise run macos:build
mise run macos:run
# Quit the built app and clean your remote MAC_DIR before releasing the Mac.
mac-turn release my-desktop-build
```

`MAC_DIR` defaults to `lean-quiet-desktop-work` under the Mac's home.
Normal launches use Application Support/LeanQuietDesktop/quiet.db. `QUIET_DB`
can select an existing current-desktop database. Old Catalyst data in
Application Support/LeanQuiet is retained, not silently imported or deleted.
Assets are bundled. `--demo` seeds only a fresh database and disables networking;
`--chaos 500` explicitly adds 500 signed chaos messages (up to 5000 per call),
including profiles, attachments and reactions, to the selected community;
ordinary launches use the same TCP engine as Linux. The app exposes no control
socket. `QUIET_STATE` and `QUIET_SNAPSHOT` are opt-in test artifacts; SIGUSR1
writes the latter from the app's own frame, without Screen Recording permission.

## Tests and release gates

`mise run host:desktop` exercises the shared running Lean desktop and audits its
layout/hover proofs. `mise run linux:e2e` covers the Linux shell after changes to
the shared loop. `mise run macos:e2e` includes staging, setup and the native build;
it uses OS clicks and keystrokes to send a message, zoom, resize to narrow mode,
and reopen the same database. Snapshots and logs remain in `out/macos` even on
failure; test processes are reaped. The Mac must have a logged-in desktop and
allow System Events to send Accessibility input for this suite.

Local CI invokes these same tasks: `ci/local.sh macos-ui` for manual provisioned
runs, and `ci/local.sh release-macos` as the Mac release gate. A failed suite
fails the gate. Keep `out/macos` and `out/ci/release-macos.log` with release
artifacts. `ci/local.sh zoom` also verifies the running desktop and mobile font roots at
1×, 2× and 3×: glyph coverage must be freshly rasterized, not an enlarged
low-resolution bitmap. Host/visual deterministic suites remain in the default local CI run;
macOS is explicit because it requires a provisioned Mac and its turn.
