# Appearance

`Quiet/Theme.lean` owns the device's setting (`system`, `light`, `dark`),
OS value and effective value. `Quiet/Palette.lean` exposes
`Palette.color : Theme.Value → Palette.Token → UInt32` (RGB).
The default setting is System. `ThemeStore` stores its spelling in one
SQLite row, outside the synchronised op tables. This is a temporary
local-settings seam pending the repository's planned state-as-ops cutover.

The source palette is libquiet's local `origin/main`, commit
`ab3d244cfb9937c05dc53736046127150c3e0bb9`. Pinned copies of its
`app/src/design/{tokens.css,theme.css,Contrast.svelte}`, Appearance page,
theme helpers, toast and switcher are in `tests/theme-reference`.
The ref was read locally: no fetch, GitHub call or network access.

| Layer owned by issue #1 | Tokens provided here |
|---|---|
| Page | bg, fg, muted, link, selected |
| Chrome | panel, fg, line; phone headers use panel |
| Marks | tint, accentInk, badge, badgeInk, edge |
| Surface | panel, fg, scrim |
| Toast | toast, toastInk, edge |

`Palette.color` is the app's UI colour source. Image, camera and colour
emoji pixels are content, not UI palette tokens. Meaningful edges use
`edge`; decorative separators can use `line`. The palette retains
libquiet's values, including muted light ink that does not reach 4.5:1
on every surface. The glyph painter therefore resolves ink against the
actual composited pixel below: retain the token when it passes, otherwise
choose palette black or white. This intentionally changes inaccessible
pairings rather than claiming the unmodified libquiet palette passes.
Identity avatar colours and their hash follow `avatar.ts`.
The badge's fill uses the text-safe light brand red in both themes.

The threshold is WCAG 2.x AA: 4.5:1 for body text and 3:1 for large text
and meaningful non-text cues. All monochrome glyphs take the stronger
4.5:1 threshold. `Contrast.svelte` distinguishes accent fill from accent
ink and records their ratios; it does not itself declare a universal
minimum. The numeric thresholds here are the issue owner's requirement.

The sRGB table is in millionths. `channel_bounds` checks every interval
using integer arithmetic: below the sRGB breakpoint the linear fraction,
above it the fifth power of the interval against the twelfth power of
`(200*c + 2805)/53805`. Luminance uses weights 2126, 7152 and 722.
`meets` allows the full rounding error in its denominator, so rounding
cannot turn an under-threshold pair into a passing one. No Float,
`sorry` or `native_decide` axiom is used.

The Surface scrim shades backgrounds and then repaints retained glyph
strokes against their shaded grounds. Toast and badge outer edges read
the real destination pixels, including images. Their inner fill is opaque.
A theme transition abandons colour-bearing workers and clears the row,
image, sheet-cell, page and chrome caches; thumbnails are rebuilt from
their source bytes. Cached font masks and raw image sources have no theme.

## What the laws say

These are the exact new audited statements (names abbreviated only by
opening their namespaces). They concern the code the app calls, not a
separate UI model:

```lean
Theme.follows (v : Value) : effective ⟨.system, v⟩ = v
Theme.forced (v : Value) :
  effective ⟨.light, v⟩ = .light ∧ effective ⟨.dark, v⟩ = .dark
Theme.roundtrip (s : Setting) : decode (encode s) = s
Appearance.selected_check (s : Theme.Setting) : chosen s s = true
Contrast.channel_bounds : ∀ c : Fin 256, channelBound c.val.toUInt8
Contrast.ink_meets (wanted ground : UInt32) : meets (ink wanted ground) ground
Contrast.ink_control (wanted ground : UInt32) : meets (ink wanted ground) ground 30
Contrast.ink_kept (wanted ground : UInt32) (h : meets wanted ground) :
  ink wanted ground = wanted
Contrast.possible : meets (Palette.color .light .fg) (Palette.color .light .panel) ∧
  ink (Palette.color .light .fg) (Palette.color .light .panel) = Palette.color .light .fg
Scrim.legible (wanted : Color) (ground : ByteArray) (x : Nat) :
  Contrast.meets (textColor (pixel wanted) (row ground) x) (getPx (row ground) x)
Overlay.edge_contrast (theme : Theme.Value) (under : Color) :
  Contrast.meets (edge theme under) under 30
Cue.nonempty (s : State) : words s ≠ ""
Cue.same (a b : Theme.Value) (s : State) : caption a s = caption b s
ThemeLaws.cleared (s : St) (t : Theme.State) :
  (themed s t).rows = {} ∧ (themed s t).imgs = {} ∧
  (themed s t).gridRows = {} ∧ (themed s t).pageNow = none ∧
  (themed s t).pageKey = none ∧ (themed s t).chromeKey = "" ∧
  (themed s t).topBmp.rows = #[] ∧ (themed s t).botBmp.rows = #[]
ThemeLaws.palette (s : St) (t : Theme.State) :
  (themed s t).dim.theme = Theme.effective t ∧
  (themed s t).bgRow = solid (Palette.color (Theme.effective t) .bg) s.W
ThemeLaws.content (s : St) (t : Theme.State) :
  (themed s t).me = s.me ∧ (themed s t).ids = s.ids ∧
  (themed s t).text = s.text ∧ (themed s t).W = s.W ∧
  (themed s t).dim.dpi = s.dim.dpi ∧ (themed s t).dim.cell = s.dim.cell
ThemeLaws.text (wanted : Color) (row : ByteArray) (x : Nat) :
  Contrast.meets (textColor wanted row x) (getPx row x)
```

`meets` defaults to 45, meaning 4.5:1. These proofs establish the colour
resolver, scrim ink, overlay edge and cache transition. They do **not**
yet compose into a universal theorem about the final OS screen: issue #1
owns layer assignment, allowed covering and clipping, and visibility.
The needed assumptions are that glyphs use `textColor`, UI colours come
from the palette, later painting does not silently cover those glyphs,
and native copies preserve Lean's pixel bytes. Non-colour cues must
remain visible after layout. Device bar rendering is trusted OS code.

## Shells and verification

`Platform.screen` appends OS appearance as word 5 (0 light, 1 dark).
Android reports `uiMode` at creation and on configuration changes; a
new Activity reapplies Lean's current bar style even if the effective
value did not change. iOS reads UITraitCollection at layout and on live
trait changes. Neither overwrites its OS observation with the user's
forced setting. `Platform.appearance` applies Lean's effective value to
bar icons and the window fill. The headless shell reports scripted OS
changes with `!theme light|dark`.

`host:theme-restart` uses distinct processes for each write and reopen.
`host:theme-live` drives the running app, all 18 page kinds in both themes
at 1080×2400 and 1170×2532, real message paints, selection, scrims,
composited edges, 66 RGB comparisons to libquiet's CSS, and the native
headless shell. It produces 72 full-size page screenshots and a palette
pixel strip under `out/appearance`. Both named tasks include their
build and are in `ci/local.sh app`.

No desktop shell has landed on this branch. No phone, emulator or Mac
was touched. Android Java and C syntax compilation uses the local SDK
and NDK. iOS compilation and live Android/iOS OS switches remain
unverified. This sandbox denies socket creation, so `host:cross` and
`host:attach` cannot start their TCP nodes. Chromium also aborts on a
denied socket operation, preventing whole-screen libquiet browser pixel
comparisons. The CSS pixel comparison is explicitly narrower than that
remaining requirement.

## Recorded validation and negative controls

The completed runs in this worktree:

- `mise run check`: 104 audited theorems on standard axioms, the original
  87 plus 17 new statements above.
- `mise run host:theme-restart`: 9 checks, three settings and separate
  write/read processes.
- `mise run host:theme-live`: 164 app/raster checks, 66 exact RGB
  comparisons to libquiet CSS/avatar values, and 6 native headless
  OS-report/frame checks. The raster suite includes warm catalogue
  cells compared with fresh paints after a live switch.
- `MESSAGES=40 mise run host:app`: 29 checks, including live query
  consistency, sending, reactions, sheets, catalogue scrolling and photos.
- Android `javac` against API 35 and arm64 NDK C syntax compilation: pass.
- `host:cross` and `host:attach`: attempted; their TCP nodes fail with
  `operation not permitted`. A standalone loopback socket attempt fails
  the same way. These gates are blocked, not reported as passing.

18 negative controls were run and reverted. `tests/theme-negative.py`
records the first 13: force System to light; swap the Light override;
break the durable decoder; remove the Selected label; corrupt an sRGB
interval; pick the ground as fallback ink; replace a passing requested
ink; erase a state's cue; vary the cue by theme; bypass adaptive overlay
edges; retain cached rows/images; keep the old painter palette; erase
the draft during a theme change. Each fails the relevant proof build.

`tests/theme-paint-negative.py` adds four: bypass the glyph colour
resolver (proof failure); omit glyph repainting under the scrim (live
raster failure); copy the toast fill instead of resolving its edge
against the destination (live raster failure); turn the preference
write into a read (persistence failure). The final control sets the
light foreground equal to the light panel: `Contrast.possible` fails.
The edge test also failed on the initial implementation's missing inner
rectangle bounds before that bug was fixed. Sources and binaries were
restored, and the positive tests rerun. Logs are under
`out/appearance/negative`; these mutation scripts are manual
validation tools, not concurrent CI tests.

What remains for the issue: compose the contrast and cue helpers with
issue #1's typed layer/visibility table to obtain laws about every final
visible run; migrate the device row to local ops when that cutover is
available; run the TCP gate and full-screen libquiet comparisons in an
environment allowing local sockets; and verify live appearance changes
and recreation on the native platforms. This commit does not claim
those remaining checks or the whole-screen theorem are complete.

Integration with the current app (October 2026): appearance is part of the
lifecycle checkpoint and committed on its existing retrying writer. The UI
never calls Theme.save. A held SQLite write-lock regression sends a real
`theme dark` command through App.step and checks eventual durability.

Noto coverage is retained with each monochrome stroke. Glyphs in a line
resolve ink against the line's original ground, so overlapping Arabic or
negative-bearing glyphs do not invert one another. Scrims restore the ground
and replay strokes in paint order. Tests check the resolved ink's contrast
and exact final coverage blend. Antialiased edge pixels themselves are not
claimed to have 4.5:1 contrast; neither are photographs or color emoji.
