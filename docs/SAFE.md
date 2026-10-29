# Safe areas: implemented boundary and remaining work

This is a partial implementation of issue #1. It does **not** establish all
nine declared-occlusion laws for the existing app. The new functions run in
`App.step`, `present`, `onScreenTap` and `withToast`; the old text, row,
binding-order, switcher and Geometry functions are unchanged.

The integrated app uses the shared `Session`/`Surface` placement on every
platform, the live theme palette, and lifecycle-aware resize. Horizontal
safe-area padding wraps the published frames and hold plane; native code
continues to consume Lean's placement. Whole-control containment and all
nine declared-occlusion laws remain incomplete.

## Running code

- `Safe.content` takes the maximum of bars, cutout and IME on each edge,
  subtracts them from the window, and saturates to an empty content box.
  `Safe.reserved` partitions its complement into four bands.
- `SafeFrame.report` extends the six-word screen protocol to thirteen words:
  width, height, bar top, bar bottom, dpi, system-dark flag, bar left, bar right, IME bottom,
  cutout left/top/right/bottom. iOS reports its safe area in the bar fields.
- `App.resizeContent` retires paints, reloads the density-scaled font when
  needed and re-measures mounted rows while preserving the scroll anchor.
  `App.screenChanged` applies safe-area geometry before each frame.
  An extended report outranks an older queued IME event.
- `onScreenTap` rejects points outside the current safe rectangle, then
  translates horizontal coordinates for the existing handlers. This guards
  **touch points**, not every existing control's entire rectangle. The pure
  `Safe.target` supports whole rectangles; migrating all controls remains.
- `SafeFrame.edgeColour screen theme edge` is the policy for bar colours.
  Its `Colours` argument is a palette adapter; `colours` uses the active light/dark theme.
  Header, page, composer and sheet edge colours agree in the render tests.
  Side pixels repeat the adjacent row's edge, including header/sheet segments.
  Lean computes sRGB luminance and chooses the higher-contrast black or white
  glyphs for both light and dark backgrounds. This Float calculation
  is tested, not formally proved. Native shells apply Lean's values. The appearance integration supplies the palette and composited-pixel contrast policy.
- `Occlusion.Layer` names Page, Chrome, Marks, Surface and Toast.
  `MayCover` is a closed covering table. The Toast painter reads the layer
  field through `Occlusion.place`; modal tap/send dispatch uses `active`.
  Existing bitmap interiors do not yet carry individual element metadata.
- A toast uses monotonic milliseconds, not frame counts. It is drawn whole
  inside the current viewport, outside a page field and the entire composer,
  or deferred if it cannot fit. Its whole card is the dismissal target,
  at least 48 density-independent units. Taps clear it, and it times out at
  3000 ms. Standing removal notices also time out one at a time. Deferred
  alerts can currently expire unseen; a responsive fallback remains.

Android reports system bars, display cutouts and animated IME insets through
the API 30+ `WindowInsets` APIs (this shell's minimum API). API 35 edge-to-edge
is enabled. `BarState` holds only a weak window reference, keeps Lean's last
choice through recreation, ignores queued work for an outgoing window and
reads the latest choice when applying queued work. UIKit reports left/right
safe-area insets and the keyboard; it applies Lean's status style and bottom
fill. The home indicator remains system-owned.

## Proofs and assumptions

All new statements are in the app's axiom audit. `Inside` means rectangle
containment and `Disjoint` means no intersection of positive-area interiors.
The statements quantify over arbitrary natural dimensions, including zero.

| Law | Exact conclusion and premises |
|---|---|
| `Safe.content_inside` | `(content i).Inside ⟨0, 0, i.w, i.h⟩`. No premises. |
| `Safe.inside_disjoint` | `r.Inside (content i) → r.Disjoint (reserved i e)`. |
| `Safe.target_safe` | `target i r = some t → t.Disjoint (reserved i e)`. |
| `Safe.target_witness` | `target ⟨1080,2400,⟨0,72,0,63⟩,⟨0,128,0,0⟩,⟨0,0,0,900⟩⟩ ⟨48,200,126,126⟩ = some ⟨48,200,126,126⟩`. Insets are left/top/right/bottom. |
| `SafeFrame.target_minimum` | `48 * dpi ≤ 160 * targetPx dpi`. No premises; the shell must report the actual density for this to mean physical dp/pt. |
| `SafeFrame.band_colour` | `(band i screen theme edge).colour = edgeColour screen theme edge`. No palette assumption; native application is trusted. |
| `Occlusion.placed_table` | `place i a b inert focused = some out → MayCover out b inert`. `MayCover` is the closed five-layer table in `Occlusion.lean`. |
| `Occlusion.placed_safe` | `place i a b inert focused = some out → out.rect.Disjoint (reserved i e) ∧ out.rect.Disjoint focused`. |
| `Occlusion.modal_inert` | `layer ≠ .surface → active true layer = false`. Only dispatch through this gate is covered. |
| `Toast.placed_safe` | `layout i view focused w h key = some out → out.rect.Disjoint (reserved i edge) ∧ out.rect.Disjoint focused`. The caller supplies the actual protected input. |
| `Toast.placed_view` | `layout i view focused w h key = some out → out.rect.Inside view ∧ out.layer = .toast`. |
| `Toast.placed_size` | `layout i view focused w h key = some out → key ≤ out.rect.w ∧ key ≤ out.rect.h`. The caller supplies the pixel minimum; the app uses 48 dp/pt, including on iOS. |
| `Toast.expired` | `deadline ≤ now → showing now (some (text, deadline)) = none`. A monotonic clock must advance; a newly raised toast is a separate event. |
| `Toast.dismissed` | `showing now none = none`. |
| `Toast.raised_visible` | `showing now (raise now text) = some text`. Placement may still defer a non-fitting card. |
| `Toast.placed_witness` | `layout ⟨1080,2400,⟨0,128,0,63⟩,{},⟨0,0,0,900⟩⟩ ⟨0,350,1080,850⟩ ⟨0,1200,1080,300⟩ 735 280 = some ⟨.toast,⟨172,635,735,280⟩⟩`. Default `key = 1`. |
| `App.screenChanged_size` | `(screenChanged sc now s).W = (Safe.content { SafeFrame.report sc s.imeH with ime := {} }).w ∧ (screenChanged sc now s).Hs = (SafeFrame.report sc s.imeH).h`. Legacy reports use the last IME event. |
| `App.screenChanged_insets` | `(screenChanged sc now s).window = SafeFrame.report sc s.imeH ∧ (screenChanged sc now s).imeH = (SafeFrame.report sc s.imeH).ime.bottom ∧ (screenChanged sc now s).insetTop = (Safe.content { SafeFrame.report sc s.imeH with ime := {} }).y`. |

These are bounds and decision laws. They do not prove bitmap fidelity,
internal text non-overlap, all-control size/reachability, or native placement.
The runtime render checks test the composition beyond these bounds.

## Render fixtures and libquiet comparison

`mise run host:safe` builds and runs `platforms.headless.Safe`, writing PPMs to `out/safe`.
It drives one live app through rotations, keyboard changes and density changes
for onboarding, home, channel, a page input and a reaction sheet. There are no
settings or thread screens in this checkout. The grey keyboard is a simulated
occluder; there are no OS glyphs in these headless images.

| Fixture family | Portrait pixels | Landscape pixels | Density |
|---|---|---|---|
| iPhone 16e dimensions | 1170×2532 | 2532×1170 | 480 (3 pixels/pt) |
| Pixel 7 dimensions | 1080×2400 | 2400×1080 | 420 |

Sources for dimensions: `app/ios/README.md:56`; the local Android SDK's
`cmdline-tools/latest/lib/sdklib/sdklib.core.jar`, resource
`com/android/sdklib/devices/nexus.xml`, device `pixel_7` (1080, 2400, 420dpi).
**Inset and keyboard values below are explicit test assumptions, not device
measurements.** No device-specific screenshot claim is made.

| Fixture | Insets left/top/right/bottom | IME bottom when up |
|---|---|---|
| 1170 portrait | 0/141/0/102 | 900 |
| 1170 landscape | 141/0/141/63 | 600 |
| 1080 portrait | bars 0/72/0/63, cutout 0/128/0/0 | 900 |
| 1080 landscape | bars 0/63/0/63, cutout 128/0/0/0 | 550 |

The reference is libquiet `origin/main`, commit
`ab3d244cfb9937c05dc53736046127150c3e0bb9`, read with `git show`: its checked-out
tree has no `app/`. This is a **source comparison**, not a pixel comparison
against a running libquiet at matching states:

- `app/src/styles.css:149–165`: top padding and surface-owned bottom inset.
  Lean keeps top inset inside its header and the bottom fill under its composer.
- `app/src/Stage.svelte:89–102,147–155`: inset-aware onboarding with a scrolling
  stage and 24-unit top gap. Lean's existing stage is pinned and lacks that
  overflow scrolling; short/keyboard-open stages still need migration.
- `app/src/CommunitySwitcher.svelte:336–341,405–424`: ellipsized names and a
  mobile sheet below the status area, paying the bottom inset. Lean's switcher
  remains a full page; the old text ellipsis laws are unchanged.
- `app/src/styles.css:811–879` and `app/src/toast.ts:19–26`: one centred alert,
  up to 280 wide with 16-unit gutters and padding, 3000 ms lifetime. Lean keeps
  those sizes, centres in its unobscured viewport and protects page inputs.
  Its existing two-line text clamp has no added truncation cue yet.
- `app/src-tauri/gen/android/app/src/main/java/org/tryquiet/quiet/StatusBar.kt`:
  preserve the last icon choice without retaining an Activity, and ignore
  queued updates for outgoing windows. The local JVM tests cover this policy.

## Still unchecked / unfinished

- [ ] Integrate the actual seamui exports; no second placement path was added.
- [ ] Obtain measured iPhone 16e and Pixel 7 inset/IME reports for these states.
- [ ] Device screenshots and libquiet screenshots at matching states and themes.
- [ ] iOS compilation and device verification. No Apple SDK is available here;
  no Mac, phone or emulator was used.
- [ ] Issue #2's themes, composited contrast and non-colour cues.
- [ ] Full element layer assignment, same-layer non-overlap, cue-bearing
  clipping, body-size and all-control reachability laws. In particular, short
  landscape lists can crop a row at an edge, and sheets need responsive layout.
- [ ] Migrate full target rectangles, not just touch-point rejection.
- [ ] Responsive page scrolling and a visible fallback for deferred alerts.

Negative controls live in `tests/app/safe_negative.py`; they mutate production
definitions and restore them in `finally`. Run `mise run host:safe-negative`
without another build in the same worktree.

## Validation in this worktree (2026-10-28)

- `mise run check`: **105 theorems**, all on standard axioms; the original
  87 statements and proofs are unchanged. README theorem links: **209**, checked.
- `mise run host:safe`: **337 checks, zero failures**, **72 PPM renders**;
  its JVM bar-controller suite: **8 checks, zero failures**.
- `mise run host:two-nodes`: **49 checks, zero failures**.
- `mise run host:cross`: **6 passes, 12 failures**.
- `mise run host:attach`: **6 passes, 8 failures**. Both TCP suites report
  `node: cannot start: operation not permitted (error code: 1)` for both
  nodes. An independent Python loopback socket probe also raises
  `PermissionError(1, 'Operation not permitted')`. These required gates are
  **not green**; they must be rerun where localhost sockets are permitted.
- Android: API 35 Java compilation and NDK C syntax checks passed; the full
  **arm64-v8a APK built** (`out/safe/quiet.apk`). It was not installed or run.
- iOS: source updated, **not built**; no local Xcode tools/SDK were found.

**26 negative controls rejected, then reverted:** content bounds; reserved
band intersection; target acceptance; the accepted-target witness; edge
colour; covering table; overlay bounds; modal dispatch; toast bounds,
viewport, minimum size, expiry, dismissal, visible lifetime and placement
witness; stale size and inset reports; forgotten bar choice on recreation;
updates to an outgoing window; queued older bar choices; bypassed reserved
touch checks; wrong toast frame row; stale IME events; keyboard Send through
a modal; reversed icon contrast choice; minimum-target rounding downward.
The last control was run separately after adding `target_minimum`; the
checked-in harness includes all 26. The restored code passed the final
proof, headless, JVM and Android build checks above.

Logs are under `app/out/issue1-final-*.log` and `app/out/safe/negative/`.
`ci/local.sh app` now includes `host_safe.sh` and `safe_negative.py`; it still
requires the unchanged TCP suites to pass first.

The requested commit was attempted, but both staging and committing failed:
Git could not create `.git/worktrees/lq-issue1/index.lock` on the read-only
metadata mount. There is **no new commit**. The worktree retains all changes;
`out/issue1.patch` and `out/issue1.commit-message` preserve the complete patch
and intended co-authored commit message. No push was attempted.

## Integrated validation

`host:safe` now exercises the shared placement and current palette:
337 checks and 8 Android bar lifecycle checks pass. The safe-area report
retains the system theme at word 5; side/keyboard/cutout fields start at 6.
The suite mounts a real chat before opening its reaction sheet and checks
the visible toast edge, including over backgrounds with the same fill.
These generated images are fixtures, not physical-device screenshots.
