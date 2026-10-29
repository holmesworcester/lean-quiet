# Zoom and phone text sizing

The zoom change is based directly on main (`82da1c6`), including Noto and
libquiet responsive/pixel work. The CRD preview was originally built on
`refactor/component-queries`; photo-picker and clump changes from that branch
are excluded from this landing.

Linux accepts Ctrl+=, Ctrl+Shift+=, Ctrl+keypad-plus, Ctrl+minus,
Ctrl+keypad-minus and Ctrl+0 even outside the composer. Levels are 50, 67, 75,
80, 90, 100, 110, 125, 150, 175 and 200 percent. The requested level is saved
beside the database (`.zoom`). The native window stays the same size; Lean's
layout density changes. Breakpoints, navigation, overlays, padding, glyph/icon
raster sizes, wrapped content, composer, pointer targets and scrollbars all
use that density. Noto is rasterized again at the selected pixel size, including
sizes outside the typography table. No enlarged screenshot supplies the zoom.

The supported desktop viewport is at least 320 by 480 native logical pixels.
Effective zoom is capped to keep at least 320 by 240 CSS pixels available;
the requested level is retained and applies again when the window grows.
The existing `QUIET_SCALE` (display pixel ratio) remains a separate integer
presentation scale. At ratio 2 its final blit still replicates logical pixels;
it does not yet provide independent high-resolution glyph rasterization.

The design body is 14 CSS pixels in the wide conversation and 15 in the narrow
conversation/phone, replacing the old fallback-asset-derived approximately
18.3 dp body. Fixed labels use their existing typography roles.

Android asks `TypedValue.applyDimension(SP, 15, metrics)` for the user's actual
body size and derives layout density from it. This uses Android 14+'s nonlinear
conversion rather than multiplying `Configuration.fontScale`. `fontScale`
changes are handled live and retire width/density-sensitive layouts and paints.
The whole interface grows with the requested body size so fixed control chrome
cannot clip enlarged labels. This intentionally applies the body's ratio to
other typography roles and controls, rather than independently sampling every
role on Android's nonlinear curve. Native safe-area coordinates remain physical.

On iOS, `UIFontMetrics` for the body supplies the corresponding density from
Dynamic Type, and trait changes request layout. The iOS source change requires
native simulator/device validation on a Mac; Linux checks cannot establish
UIKit behavior.

Platform guidance:
- [Android 14 nonlinear font scaling](https://developer.android.com/about/versions/14/features#non-linear-font-scaling)
- [UIKit scaled values](https://developer.apple.com/documentation/uikit/uifontmetrics/scaledvalue(for:))

## Evidence and scope

`mise run test:zoom` builds/setup the desktop and tests real X11 input at display
ratios 1 and 2 and without MIT-SHM, zoom limits, draft preservation, scaled
settings/actions, reset and restart persistence. Screens and logs stay under
`out/zoom/native`; `zoom-comparison.png` shows the running application.

The geometry sweep uses real Noto metrics and row/composer layout at 17 densities
(80–1280 dpi) and eight widths (200–1280 dp). It checks header containment,
body line widths, preservation of all non-space body characters including bidi,
vertical separation, image/reaction containment and separation, four photo chips,
and composer/send control separation. It also rasterizes arbitrary Noto and
large bitmap fallback sizes. These are executable tests, not universal proofs of
all possible content.

`engine/renderer/desktop/ZoomLaws.lean` proves properties of `zoomLayout`, the
function called by the running driver: identity at 100%, disjoint navigation
and conversation, every track contained, emitted controls contained at any
minimum target size, monotone body size with increasing density, and unchanged main geometry when the drawer opens on a
wide viewport. Settings intentionally overlay the conversation. Existing
`Text.wrap_keeps`, `Text.wrap_fits`, `Text.oneLine_prefix` and composer separation
laws apply to the running wrapping/label/chip functions. The zoom gate audits
all eleven proofs against standard Lean axioms. Font bearings, native event order,
and raster equality are covered by tests, not claimed as formally verified.

The full-image comparison uses 32 pinned Chromium renders of actual libquiet
`App.svelte`, not a recreation, across 50–200%, light/dark, chat/appearance and
a 390px phone-sized viewport. Browser zoom is a smaller CSS viewport at a larger
device scale. The reference viewport is rounded up and its final edge cropped
by at most one pixel; no content regions are masked. Independent DOM track
measurements must match Lean within two device pixels. Mean RGB error ceilings
are 1%, with at most 3.5% of pixels differing by more than 16/255 and pooled
layout error at most 0.6%. These are regression limits, not pixel identity.
Current fixtures contain empty conversations; message content retention and
geometry are exercised separately. Rich conversation/markdown/clump pixel
parity is outside this change.

Refresh zoom references explicitly with the pinned libquiet checkout:

```
mise run visual:reference -- --cases tests/zoom/cases.tsv --output tests/zoom/reference
```

`mise run android:zoom` builds both Android ABIs, provisions and boots only its
own `lean-quiet-zoom` API 36 emulator (`emulator-5658`), changes system text size
through 85%, 100%, 130%, 200% and back, and checks the running font, layout-cache
generation, retained message and return from background. It waits for subsequent
frames after Android configuration transitions and measures actual screenshot
glyph ink, so reporting a new font size while showing stale glyphs fails. It retains APK,
screenshots, logcat, build and emulator logs under `out/zoom/android`. It never
changes a physical phone's settings. `ci/local.sh android-zoom` invokes this
same task for provisioned/manual runs. The release gate is
`ci/local.sh release-zoom` (deterministic gate plus the Android suite); the default local CI invokes the
deterministic `test:zoom` gate. This repository has no enabled hosted CI workflow.

Runner prerequisites: the repository Lean/Rust toolchains, fonts/glyph assets,
Python Pillow/NumPy, Xvfb, xdotool, ImageMagick and xcb development libraries.
Android also needs SDK/NDK, API 36 google_apis x86_64 system image, KVM, Java 17,
and Lean Android runtimes (`LEANRT` may point to an existing runtime). New disk
heavy outputs belong under `/mnt/storage`.

## Recorded validation

The 420 dpi Android emulator produced these live results without process restart:

| OS setting | Body pixels | Measured Latin ink height | Effective layout dpi |
| --- | ---: | ---: | ---: |
| 85% | 33 | 24 | 357 |
| 100% | 39 | 29 | 420 |
| 130% | 51 | 39 | 546 |
| 200% | 71 | 55 | 756 |
| Back to 100% | 39 | 29 | 420 |

The nonlinear 200% result comes from Android's SP conversion. Both x86_64 and
arm64-v8a APKs build. The suite uses complete APK installation, stops its own
package before replacement, resets only its own emulator's font setting, and
restores it after testing. An early incremental-install run crashed in Android's
native drawing threads at startup; that did not reproduce with complete
installation. Failed runs are not counted as passing evidence.

Unchanged APKs may be reused only when the source, generated assets, SDK version
and runtime fingerprint matches; tests always execute. Fresh assets are prepared
before fingerprinting, and changing inputs during a build fails the task.

Additional checks passed: desktop 204 checks/27 renders; mobile safety 341
checks plus eight native-bar lifecycle checks; the Noto/fontTools raster oracle
390 bitmaps and 11 script lines; and the compact font contract's 5,374
whole-result comparisons. The home status-bar policy now matches its purple
header. The zoom pixel matrix's worst mean RGB error is approximately 0.83%.
