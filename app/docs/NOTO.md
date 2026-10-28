# Lean Noto rendering

The UI's pixels now come from Lean's TrueType reader and rasterizer.
`Font.glyph?` chooses Noto and `Font.adv` supplies rounded hmtx advances;
`Paint.Bitmap.glyph` composites the cached coverage. `Text.lean`, its
laws, `Row.layout`, and the row laws are unchanged. App.start's only
change passes screen density to Font.load.

`tools/noto_assets.sh` copies nine local, SHA-256 pinned, OFL font files
from `/usr/share/fonts/truetype/noto` (override `NOTO_FONTS`). It is called
by the asset fetch step and the app tasks/gate. The license travels with
the fonts. No online font service or native font rasterizer is used.

Coverage: Latin, Greek, Cyrillic, Armenian, Georgian, Hebrew, Arabic
presentation forms, Thai, Ethiopic, Cherokee and Canadian Aboriginal
syllabics. Fallback is per code point. Colour emoji retain their existing
priority and pictures. CJK remains Unifont: the installed Noto CJK fonts
are CFF collections, which this reader does not accept. Indic and other
reordering/stacking scripts retain the previous fallback. This does not
add HarfBuzz, GSUB, GPOS mark positioning, or contextual pair adjustment.
The reader exposes legacy horizontal `kern` pairs; the pinned fonts use
GPOS instead. The existing presentation-form Arabic and mark placement
remain in Text. No TrueType hinting is executed.

The source font cell is scaled by screen DPI / 420 and clamped to 16–64
pixels. At the host's 420 DPI, the cell and em are 48 px. The Unifont
fallback is resampled from its original cell. Emoji retain their existing
size. Rasterization also supports 1–256 px em sizes independently.

## Reader and cache

`Ttf/Bytes.lean` uses proof-checked ByteArray indexing and Option-valued
big-endian reads. Offsets use unbounded Nat arithmetic. Each table is
sliced only after its extent is checked, so reads cannot spill into the
next table. The parser supports sfnt head, hhea, maxp, hmtx, loca, glyf,
cmap 4/12 and legacy kern format 0. Simple glyph flags/deltas, implied
on-curve points, scaled/transformed components, signed translations and
point attachments are decoded in Lean.

There is no partial recursion, unchecked indexing, unsafe code, native
parser or added axiom in Ttf or Noto. Composite ancestry detects cycles;
a depth bound of 32 and a shared budget of 4096 visits also bound work.
Each glyph has at most 8192 points and 64 components; files are capped at
32 MiB. These are supported-format limits: excessive or unsupported
input returns none. `Ttf.read` validates every glyph before publishing a
face, including unused glyphs. It is not an OpenType sanitizer: it does
not validate checksums, hint programs, or unsupported layout tables.

A `Noto.Cached` face owns one Lean Thunk for each glyph id at its pixel
size. Code points sharing a glyph share that thunk; layout reads metrics
without forcing it. The Lean runtime memoizes its result across paint
tasks. The cache grows only to the requested glyphs, with no eviction or
per-frame rasterization. Separate sizes have separate caches. Font.load
creates a fresh set per app instance; cold opens pay validation again.

## Raster and proofs

Quadratics are flattened adaptively to a nominal 1/256 px chord-error
bound (128 subdivisions maximum), then filled using nonzero winding on
an 8 × 8 sample grid. Coverage is saturated to 255. Bounds are computed
from transformed control points, so the ink can have explicitly declared
left/right/top/bottom overhang beyond the advance cell. Painting clips
signed positions before converting to pixel indices. Bold uses the
maximum of neighbouring coverage samples, not repeated alpha blending.

The 11 declarations in `Quiet/Ttf/Laws.lean` are in the app's axiom audit:

- `byte_in_bounds`: `u8 b i = some n` implies a proof `i < b.size` and
  `b[i].toNat = n`.
- `cmap_entry`: `lookup es c = some g` implies an entry `e ∈ es` with
  `e.contains c = true` and `e.glyph c = g`.
- `cmap12_glyph`: a sequential entry maps c to `first + c - lo`.
- `cmap4_delta`: a delta entry maps c to `((c + delta) mod 65536).toNat`.
- `cmap4_array`: an array entry gets `ids[c-lo]` (default 0), preserves
  zero, otherwise returns `((id + delta) mod 65536).toNat`.
- `coverage_value`: `(coverage n).toNat = min 255 (n * 255 / 64)`.
- `coverage_bound`: `(coverage n).toNat ≤ 255`.
- `checked_valid`: `checked b = some out` implies `out.Valid`.
- `raster_valid`: `raster f glyph size cell = some b` implies `b.Valid`.
- `raster_pixel`: for a returned bitmap and `x < b.w`, `y < b.h`,
  `y*b.w+x < b.pixels.size` and that byte's toNat is at most 255.
- `ink_witness`: a specified nonempty 2×2 bitmap with negative origin
  passes checked, full coverage is 255, and a sample cmap lookup succeeds.

`Valid` means exactly `pixels.size = w*h`, `-left ≤ x`,
`x+w ≤ advance+right`, `-top ≤ y`, and `y+h ≤ cell+bottom`.
The cmap laws concern the decoded table entries and lookup formulas;
byte-to-table decoding is additionally checked against fontTools over
all 5,955 mapped entries in the fixtures. There is no theorem equating
quadratic area with sampled coverage, or end-to-end pixel fidelity.

The existing `Text.place_starts` statement now uses real font metrics
without modification: non-mark placed x positions equal `starts x` of
the advances of the visible, non-mark input code points. All 87 existing
app laws remain, with 11 new ones (98 total).

## Reproduce

Use the repository's Lean toolchain and build the offline Rust crypto
first, as documented at the root. Then, in app:

```
mise run host:noto
mise run check
mise run host:cross
mise run host:attach
```

`host:noto` builds its executable. fontTools is imported from the normal
Python environment, or the already installed local Python libraries;
there is no pip invocation. Its BasePen independently subdivides curves
into 128 chords and samples the same grid. Tolerances are at most 32/255
per pixel and at most 1/255 mean error per glyph. It checks 390 glyph
bitmaps at 16, 32 and 48 px, 11 full script lines through Text and Paint,
all cmap/metric pairs, synthetic composite transforms/point attachment,
both cmap formats, density changes, clipping, fallback, and cache object
identity. Only the cache identity *test* uses unsafe pointer equality.
`out/noto/scripts.ppm` is the script sheet; `out/host/*.ppm` are app screens.

Truncation at header and table boundaries, oversized offsets in every
directory entry, and a composite self-cycle are refused (311 files).
A separate mutation run, `python3 tests/noto_negative.py`, changes the
actual code, requires a proof or runtime failure, and restores the source
after each fault. Run it without concurrent builds. Logs are written to
`out/noto-negative/`. Normal CI runs the positive suite, all headless app
scenarios and the axiom audit through `ci/local.sh app engine`.

No phone, emulator or Mac was used. Android/iOS execution and their font
asset loading are unverified; their existing packaging copies the flat
assets directory, which now includes the pinned TrueType files.

## Results in this worktree (2026-10-28)

`mise run check` passed: all 98 app theorems use standard axioms only.
The reference suite passed 5,955 cmap/hmtx pairs, 390 glyph bitmaps
(165,128 coverage pixels), and 11 lines through the real Text/Paint path
(1,111,000 RGB pixels). Maximum glyph error was 16/255, mean 0.0668/255;
maximum line error was 15/255. The kern suite passed 3 pair/scale checks
and refused all 30 truncated tables, in addition to the 311 hostile fonts.
Ten thousand distinct runtime cache requests took 475 microseconds and
returned the same pixel object. Density, fallback, clipping and bold
checks passed.

All 18 negative controls were detected: wrong byte value; wrong cmap
lookup, sequential start, delta and missing-glyph handling; wrong coverage;
removed bitmap and raster guards; a vacuous rejecting constructor; coarse
curves; transposed composite matrix; removed glyph memoization; ignored
screen density; accepted truncation; accepted composite cycle; wrong
advance; removed left clipping; and reversed kerning sign. Each mutation
was reverted and the positive suite rerun. The cache control first exposed
compiler common-subexpression reuse in the test; the final test reads its
lookup input through IO before checking object identity.

The same 500-message host workload, before and after:

| Measurement | Unifont | Noto | Change |
|---|---:|---:|---:|
| Cold open to painted screen | 22 ms | 69 ms | +47 ms |
| Fling step median | 2,441 µs | 2,488 µs | +47 µs (1.9%) |
| Fling step p95 | 4,240 µs | 4,403 µs | +163 µs (3.8%) |
| Fling step maximum | 10,012 µs | 9,995 µs | -17 µs |
| Frames with unpainted rows / worst rows | 0 / 0 | 0 / 0 | unchanged |
| Entire harness Lean average / p95 | 5,253 / 9,061 µs | 5,298 / 10,347 µs | +45 / +1,286 µs |
| Entire harness Lean maximum | 519,109 µs | 536,839 µs | +17,730 µs |

These are single runs, not a statistical benchmark. Proportional wrapping
changed the fling from 496 to 497 frames. The full harness includes chaos
insertion and other non-fling work. The fling remains below the 16.7 ms
frame budget; cold open now includes validating all Noto glyphs.

Headless `host` passed 29 assertions, `two_nodes` 49, and `host:arrival`
24. Screens in `out/host` were visually inspected and show Noto text.
The engine audit passed 151 laws; its first seven suites passed 1,611
assertions. README proof links validate (196 links, 286 audited laws).

The full gate is **not green in this sandbox**. `ci/local.sh app engine`
was run: app stops at `net_join`; engine stops at `tcppair`. The separately
required `mise run host:cross` and `mise run host:attach` were also run.
All fail because opening the loopback socket returns `operation not
permitted (error code: 1)`, before peers can connect. No network tests were
mocked, disabled or weakened. Re-run those gates in an environment that
permits loopback sockets. Mobile runtime checks also remain unverified.

Observed TCP-suite results under that denial: net_join 2 passed / 8 failed;
host:cross 6 passed / 12 failed; host:attach 6 passed / 8 failed. These are
cascading admission/transfer failures after node startup is denied, not
successful executions of the network scenarios. The remaining engine
executable suites after tcppair were not reached by the gate.

Commit was attempted, but Git could not create
`/mnt/storage/holmes-wt/lq/.git/worktrees/lq-noto/index.lock`: the Git
metadata filesystem is read-only. No commit hash exists. All changes
remain in this worktree; `app/out/noto-change.patch` also contains the
complete change, including new files. The prepared message is in
`app/out/noto-commit-message.txt` and ends with the requested co-author.
