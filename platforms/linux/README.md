# Linux desktop, first slice

Lean paints the complete window. `shell.c` supplies xcb, MIT-SHM (with a
PutImage fallback), input, clipboard ownership and integer scaling. It
links no GTK, SDL, Qt, Xlib, browser or GPU renderer. The current Lake link
paths target x86_64 Linux, as the app's existing SQLite link does.

From the repository root:

```sh
platforms/linux/build.sh
mkdir -p out/linux
QUIET_DB=out/linux/quiet.db .lake/build/bin/linux --demo
```

Create the database's parent directory first. `--demo` creates two real
communities and a message in an empty database; it disables networking.
`--offline` also disables networking. Normal startup uses the same TCP
runner as the phones. A new, ordinary database opens the existing
Get started flow. Assets and the reduced font are resolved from the
repository's root. The build is offline and requires `assets/font.bin`.

`QUIET_WIDTH` and `QUIET_HEIGHT` choose the initial logical size (default
1100×760); `QUIET_SCALE=1..4` sets integer scale. Supported logical sizes
are 320–4096 by 480–2160. Configure events resize the Lean root and
invalidate the actual app's row, image, page and chrome caches. Scaling
and hit coordinates use the same factor. Automatic per-monitor and
fractional scaling are not implemented.

The native editor supports Latin-1 and Unicode keysyms, selection, left/right,
Home/End, Backspace/Delete, Ctrl+A/C/X/V, Shift+Return and Return to send.
The compositor has hover feedback, clicks, right-click reactions, wheel
scrolling and composer drag selection. Clipboard transfer uses
`TARGETS`/`UTF8_STRING`, up to 64 KiB. IME/dead-key composition, clipboard
INCR transfers, legacy non-Latin keysyms, transcript drag selection, keyboard focus navigation and
Wayland are not implemented. The shell requires a 24-bit little-endian
TrueColor X server. Camera effects return no camera frames.

The new modules are `engine/renderer/desktop/{Layout,Laws}.lean` (the
tracks and their laws, which name no kind) and
`platforms/desktop/{View,Driver,Input}.lean` (the desktop root over App);
`platforms/linux/Main.lean` is the executable's main;
`App.lean` is unchanged. `Driver` runs the real `App.step`, database,
writer, accepted-community view, pages, chat rows and composer. The shell
also implements all of `Platform.lean`'s externs. Its extra frame and
selection externs carry desktop input in window coordinates.

Navigation contains the community switcher, the existing `general`
channel, People, Add members and Settings. Long community lists have
Previous/Next controls. Switching clears the old draft and native editor.
Settings opens a right pane whose actions reach existing pages. The
Threads pane explicitly reports that replies are unavailable: the Lean
app has no thread/reply domain or multi-channel domain yet. It does not
fabricate threads or channel data. Settings is a navigation slice, not
the full libquiet settings implementation. Photo attachment still uses
the existing app's sample assets, not an OS file picker.

## Measurements and visual scope

The provided `/home/holmes/libquiet/app/src` is absent because that
checkout is on an engine branch. The read-only reference was
`/home/holmes/libquiet/.worktrees/windows-main-parity`, pinned by commit
and source SHA-256 hashes in [measurements.json](reference/measurements.json).
No reference checkout was edited. Measurements were read with `rg -n`
and `sed`, then transcribed independently into the fixture:

| Source | Measurement |
| --- | --- |
| `styles.css:21`, `Sidebar.svelte:465` | 220px navigation; 45rem/720px breakpoint at 16px root font |
| `layout.ts:17`, `styles.css:5906` | context fits at 220 + 275 + 275 = 770px |
| `styles.css:5906` | context `minmax(275px, 375px)`; main takes remaining space |
| `Sidebar.svelte:465` | top 12px; horizontal inset 16px; channel rows 26px; people 30px |
| `Sidebar.svelte:504` | community name 18px/27px |
| `SettingsDrawer.svelte:407` | settings rows 48px; text 14px/20px |
| `styles.css:5911` onward | message text 14px/20px |
| `design/tokens.css:24` | current code's purple #7647c7 |

The cached Figma subtree was read from
`~/.local/share/figma-index/sidebar/section-6107-21330.json`, recursively
selecting `id == "6218:16416"`. Its bounding box is 220×755, spacing 8 and
bottom padding 48. The selected node's measurements and resolved fill
are in the JSON. [figma-sidebar.png](reference/figma-sidebar.png) is the
unmodified cached export, at 2× scale. It has the older purple; current
Svelte tokens take precedence here. No Figma/network request was made.

The reference comparison checks exact track edges at 320, 719, 720, 769,
770, 800, 869, 870 and 1440px, in chat/settings/threads states. Its raster
check compares three flat scanlines in each image and the gap between
composer controls at the tightest split: 67,733 pixels, zero geometric
or RGB tolerance. Those flat colors are the declared first-slice palette,
not a claim that libquiet's whole image matches. Text, avatars, content,
icons and other rows are outside this comparison.

**Full pixel parity is unfinished.** The existing phone renderer supplies
dark surfaces and a fixed-cell Unifont, reduced to 16px offline. libquiet
uses Noto Sans on Linux, with 14px message text. The root retains phone
page styling, adds a 40px toolbar, and uses a simplified sidebar. It lacks
the Figma community tile, unread badges, presence avatars and profile
footer. The two-button composer is an intentional improvement over
reusing the phone's six 48px controls in a 275px track: those overlap.
This is not a claim that libquiet's composer is wrong.

Committed examples of the actual Lean headless render:
[320px chat](reference/320-chat.png),
[770px settings](reference/770-settings.png),
[1440px settings](reference/1440-settings.png).
These are **not native X11 screenshots**. A live Svelte/native comparison
was blocked by this session's local-socket restrictions; the Figma export
is the visual reference. A local headless Chromium CSS probe also exited
in Crashpad with `setsockopt: Operation not permitted` before rendering.

## Resizing without a flash

A resize shows the last frame until the frame at the new size, which is
complete when shown:

- **Lean decides when to show it.** After the app's size changes,
  `Desktop.settleFrame` runs the app's steps (at most 50, 2 ms apart)
  until every row the list frame shows is painted at the new size, each
  with the pictures decoded before the step that painted it
  (`Desktop.framePainted`). [`Cover.painted_no_hold`](../../engine/renderer/Cover.lean)
  proves that a frame whose rows are each painted at their own height
  shows no row's placeholder, and `Desktop.settled_no_hold`
  (platforms/desktop/Laws.lean) that this holds of the rows
  `App.frameSlice` gives `App.listFrame`. Before, every configure event
  cleared the rows and showed one frame of placeholders.
- **The window keeps it meanwhile.** shell.c creates the window with no
  background and north-west bit gravity, so the X server neither clears
  it nor fills it on a resize. It answers a window manager's
  `_NET_WM_SYNC_REQUEST` after the first frame shown since the
  announced configure, so a compositing window manager shows the new
  size only with Lean's frame for it. This needs `libxcb-sync-dev`
  (the packages are listed in docs/BUILD.md).

Tested: `host:desktop` resizes a 41-message conversation seven times;
one frame after each, no row shows a placeholder and every row is painted.
`linux:e2e` stops the app, shrinks its window and finds the last frame
still shown. Acting as a window manager (`sync_test.c`), it asks for
`_NET_WM_SYNC_REQUEST`, resizes, and requires the counter to be set once
the frame at the new size is shown. Removing the settle, restoring the
black background with ForgetGravity, or never setting the counter each
fails its check (`host:desktop-negative`). The X server and the window
manager are trusted; only the Lean half is proven.

## Checks and limits

Named tasks in the root `mise.toml`:

| Task | Work |
| --- | --- |
| `host:desktop` | build; 94 behavior/geometry checks; 27 renders; raster comparison |
| `linux:build` | offline Rust crypto and Linux executable build |
| `linux:input` | compile; 21 native editor/pixel checks under ASan and UBSan |
| `linux:e2e` | build; input checks; three Xvfb sessions, scale 1/2 and PutImage fallback |
| `host:desktop-negative` | eight proof mutations, two native mutations, five UI mutations, two X11 mutations |
| `host:desktop` (again) | the eight desktop laws' own audit, `tests/app/DesktopAxioms.lean`, on standard axioms only |

`tests/app/run.sh` (`ci/local.sh app`) runs the desktop render and Linux
E2E tasks after the phone suites. The desktop's laws are audited apart
from `tests/Axioms.lean`: the desktop is not in the root README yet. E2E is a required check: inability to create a
display is a failure, not a silently passing skip. `linux:e2e` scripts
community switching, Settings, 1100→770→719→1100 resizing, keyboard input,
clipboard, drag selection, sending and screenshots. It owns and reaps
its subprocesses, never searches for processes to kill.

The first slice's session could not bind X sockets. After the move to
the repository's new layout (2026-10-28), `linux:e2e` ran here: 33 checks
in three Xvfb sessions (scale 1 and 2 over MIT-SHM, and PutImage),
including the window's presentation, the X pointer, keyboard, UTF-8
clipboard round trip and drag selection. The e2e reads the state file
the app writes; it is now written whole and renamed, since a read of a
half-written file once failed the scale-2 run. LeakSanitizer is disabled
(its process inspection is denied under ptrace); ASan and UBSan remain
enabled. HiDPI beyond integer scale, and native networking, are not
verified.

## Laws

[Laws.lean](../../engine/renderer/desktop/Laws.lean) contains the exact statements.
All refer to the functions used by the desktop root. Let `L = layout w o`.

- `widths`, for every `w, o`: `L.nav.w + L.main.w + L.context.w = w`.
- `adjacent`, for every `w, o`: `L.nav.x = 0`,
  `L.nav.x + L.nav.w = L.main.x`,
  `L.main.x + L.main.w = L.context.x`, and
  `L.context.x + L.context.w = w`. Half-open panes therefore do not overlap.
- `minimum`, for `w ≥ 320`: nav width is zero or at least 220; each
  content width is zero or at least 275.
- `monotone`, for `320 ≤ a ≤ b`, fixed `o`:
  `(layout a o).count ≤ (layout b o).count`. `count` counts positive widths.
- `controls_fit`: if `c ∈ controls g h xs`, then its left edge is at
  least its pane's left edge, its right edge is at most its pane's right
  edge, `c.box.y + c.box.h ≤ h`, `24 ≤ c.box.w`, and `24 ≤ c.box.h`.
- `controls_screen`: if `c ∈ controls (layout w o) h xs`, then
  `c.box.x + c.box.w ≤ w ∧ c.box.y + c.box.h ≤ h`.
- `hit_drawn`: `hit xs x y = some c → c ∈ xs`. Painting and dispatch
  traverse the same `scene` list. This proves membership, not the pixels
  of rasterized glyphs.
- `witness`: the context control with box `(495,0,24,24)`, action
  `0 : Nat` and label `"Close"` is in
  `controls (layout 770 true) 480 [c]`.

The minimum desktop target is **24×24 logical pixels**. These control
laws cover the new root's emitted controls, not inherited phone pages,
message reactions or the emoji sheet. Extending them to every inherited
control and proving the painter itself are still required for the full
requested guarantee. The app audit checks 95 declarations; the eight new
ones use only `propext`, `Classical.choice`, and/or `Quot.sound`.

## Negative controls executed

All were rejected, reverted, and the good sources rebuilt. Logs are
generated in `out/desktop/negative/`; scripts reproduce the mutations.

| Law/behavior | Deliberate break |
| --- | --- |
| `widths` | add one pixel to the middle width |
| `adjacent` | move the middle origin from 220 to 221 |
| `minimum` | cap the context width at 1 |
| `monotone` | collapse the split again at width 2000 |
| `controls_fit` | admit all candidate controls without the guard |
| `controls_screen` | allow a target to extend one pixel beyond its pane |
| `hit_drawn` | alter labels before hit-testing, returning an unpainted control |
| `witness` | reject all controls at width 770 |
| Native UTF-8 deletion | step back one byte instead of one code point |
| Native pixel conversion | copy RGB unchanged into the BGR X surface |
| Community dispatch | always switch to index zero |
| Draft isolation | leave the native editor's old draft intact |
| Resize | retain cached rows and heights at the old width |
| Composer | leave the six phone icons visible under the desktop controls |
| Resize settle | show the frame without waiting for the rows' paints |
| X11 gravity | a black background pixel and ForgetGravity, as before |
| X11 sync | never set the `_NET_WM_SYNC_REQUEST` counter |

The eight mutated layout modules compiled before their proofs were
checked. The four UI mutations built before their behavior/raster tests
failed. Native mutations failed assertions in the sanitizer test binary.

Final validation also ran the unchanged app suites: host with 500 messages
(29 checks), two nodes including QR joining (49), and arrival (24), all
passing. The app's 95-declaration audit passed after restoring mutations.
`ci/local.sh app engine` failed at Xvfb's denied socket bind in the app
gate, and at the engine's TCP suite with `operation not permitted`.
Before the latter, the engine audited 151 laws and passed scenario 67,
differential 517, querydiff 873, linkcheck 16, lifecycle 90, wire 29 and
syncpair 19 checks (1,611 total). TCP-dependent suites and the remainder
of those gates were not verified. The README theorem-link check passes.

Responsive usability integration (October 2026): the app occupies the full
content height, with the shared mobile header, composer, theme, and Noto fonts.
Below 720 logical pixels the desktop adds no toolbar or action overlay. From
720 pixels it adds the 220px sidebar; open context panels use the pinned
770px breakpoint and 275–375px width. At the smallest content width, composer
buttons contract without overlap and four photo chips wrap onto reachable rows.

`mise run host:desktop` checks every content pixel against the mobile frame
at each boundary, plus drafts, selection, scroll anchors, and chip/button bounds.
`mise run linux:e2e` exercises the real X11 app at 1x/2x and without MIT-SHM,
including narrow/wide resizing and selecting Dark through the Appearance page.
The preference persists locally through the checkpoint writer. Linux's current
System input defaults to light; Android/iOS supply their system appearance.

The conversation has a persistent scrollbar whenever its history exceeds
the viewport. The thumb follows the bottom-anchored history offset; dragging
it or clicking its track reaches older messages and returns to the newest.
The shared mobile pixels remain the content layer beneath this desktop
control. `host:desktop` checks visible thumb pixels, both scroll endpoints,
short-history hiding and context-panel hiding. `linux:e2e` drives the actual
pointer drag at 1×, 2× and without MIT-SHM, keeping composer selection separate.
