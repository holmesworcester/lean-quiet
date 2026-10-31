# Linux desktop

Lean paints the window using the same components, query lifetimes, Noto fonts,
images and page painters as the phones. `shell.c` provides xcb, MIT-SHM with a
PutImage fallback, native input, clipboard and integer scaling.

```sh
mise run linux:build
mkdir -p out/linux
QUIET_DB=out/linux/quiet.db .lake/build/bin/linux --demo
```

`--demo` seeds only an empty database and disables networking. `--offline`
also disables networking; normal startup uses the phone TCP runner. Run from
the repository root so the font and glyph assets resolve. The build generates
the shared font and icon assets. `QUIET_WIDTH`, `QUIET_HEIGHT` and
`QUIET_SCALE=1..4` select initial logical dimensions and integer scale.
Supported logical dimensions are 320–4096 by 480–2160.

The pinned libquiet layout shows a 220px sidebar from 720 logical pixels.
Below that boundary the mobile pages fill the window. Settings cover the right
375px on desktop, preserving the conversation width and its message layout;
on narrow windows they become full-width pages. Settings have their own scroll
viewport, and wheel events over the drawer never scroll the conversation.
Drafts and selection survive resizing and community drafts stay independent.

The composer, glyphs, profile hero, sidebar and settings share libquiet's
geometry. Unsupported settings open a page explaining their availability.
They do not pretend to change a preference. The current conversation is
`general`; multi-channel and thread storage are still separate feature work.
See [the pixel comparison harness](../../tests/visual/README.md) for the pinned
source, full-image comparisons, regression ceilings and remaining differences.
The previous hand-transcribed track/color fixture has been retired.

The native editor supports Unicode keysyms, selection, cursor navigation,
Ctrl+A/C/X/V, Shift+Return and Return to send. Clipboard transfers use
`TARGETS`/`UTF8_STRING`, up to 64 KiB. IME/dead-key composition, clipboard INCR,
keyboard focus traversal, fractional scaling and Wayland remain unsupported.
The shell requires a 24-bit little-endian TrueColor X server.

A persistent conversation scrollbar follows the bottom-anchored history
by message rank (the engine's counts of messages newer than the screen and
on it), not by estimated row heights, so it does not jump as rows are
measured (laws in engine/renderer/Scrollbar.lean, `Desktop.thumb_in_track`
and the rest in engine/renderer/desktop/Laws.lean). Dragging it or clicking the track reaches older messages and returns
to the newest. A resize retains the last frame while the new-width visible rows
finish painting. The shell uses north-west bit gravity and acknowledges
`_NET_WM_SYNC_REQUEST` after displaying that frame. The X server/window manager
are trusted; `Desktop.settled_no_hold` proves the Lean coverage implication.

| Task | Validation |
| --- | --- |
| `host:desktop` | Build and drive real community switching, drawer/mobile settings scroll, themes, text, resize, scrollbar and pixel composition; audit layout laws |
| `visual:compare` | Build and compare full images with independently rendered libquiet references |
| `linux:input` | Native editor/pixel conversion with ASan and UBSan |
| `linux:e2e` | Build/setup; real Xvfb pointer/keyboard, themes, resize, clipboard and scrollbar at scale 1/2 and without MIT-SHM |
| `host:desktop-negative` | Reject deliberately broken layout laws, native editor, dispatch, resize and X11 presentation |
| `linux:links` | Build/setup; install into private XDG folders; `leanquiet://` links on a cold start, by `xdg-open` (generic, XFCE's `exo-open`, GNOME's `gio`) and by a second launch, other databases' and stale sockets |
| `linux:links-negative` | Reject the old empty `lq_links`, one socket for every database, and a window never raised |

Local CI invokes these same tasks. Failure artifacts stay under `out/desktop`,
`out/linux`, `out/linux-links` and `out/visual`; failures propagate. Xvfb, xdotool, ImageMagick and
xcb development libraries are native-runner prerequisites. See `docs/BUILD.md`.
Tests own and reap their subprocesses. No GitHub Actions workflow is used.

[Layout laws](../../engine/renderer/desktop/Laws.lean) apply to the running
layout (`zoomLayout`, at every density) and control filter. They prove width coverage with overlapping context,
containment of the drawer, unchanged main width when the drawer opens, minimum
pane sizes, monotonic pane count, control containment and hit membership. They
do not prove raster identity or native platform scheduling. All are audited
against standard Lean axioms in `tests/app/DesktopAxioms.lean`.

Ctrl+/− zooms the whole interface (Ctrl+= and keypad variants are accepted);
Ctrl+0 resets. The requested level persists beside the database. See
[zoom and phone typography](../../docs/ZOOM.md) for supported limits,
accessibility policy, pixel comparisons, proofs and test tasks.

## Installing, and invite links

`install.sh` installs a built app for one user and makes it the handler of
`leanquiet://` links. It runs from a release folder holding `lean-quiet` (the
`linux` executable), `assets/`, `install.sh` and `lean-quiet.svg`, or from a
repository build (`.lake/build/bin/linux` and `assets/`):

```sh
mise run linux:build
platforms/linux/install.sh            # PREFIX=~/.local by default
```

Under `PREFIX` it writes `opt/lean-quiet/` (the program and its assets),
`bin/lean-quiet` (a launcher that runs from the program folder, defaults
`QUIET_DB` to `${XDG_DATA_HOME:-~/.local/share}/lean-quiet/quiet.db` and logs to
`lean-quiet.log` there without a terminal), the icon, and
`share/applications/lean-quiet.desktop` with
`MimeType=x-scheme-handler/leanquiet;`. Then `xdg-mime` makes that entry the
default handler. The entry's `Exec` is the launcher's absolute path plus `%u`,
unquoted: xdg-utils' generic `xdg-open` cannot run a quoted `Exec` and opens
the browser instead, so a `PREFIX` that would need quoting is refused.
`PREFIX/share` must be on the XDG data path, as `~/.local/share` and
`/usr/local/share` are.

The shell passes a link's text to Lean unchanged (`lq_links`); the app
parses it. A cold start takes a `://` argument. One instance runs per
database. Before opening its window, the instance locks
`$XDG_RUNTIME_DIR/lean-quiet/<hash>.lock` and listens on `<hash>.sock`
(folder 0700, socket 0600), named from a hash of the database's resolved path.
It accepts only its own uid (`SO_PEERCRED`) and reads at most 16 KiB of
newline-separated links. It raises its window with `_NET_ACTIVE_WINDOW`.
A later launch on the same database connects first. If the socket answers, it
writes its links there and exits 0. If not, it takes the free lock, removes the
stale socket and becomes the instance. Without `XDG_RUNTIME_DIR`, launches stay
independent. The window's `WM_CLASS` is `lean-quiet`, as is the entry's
`StartupWMClass`.
