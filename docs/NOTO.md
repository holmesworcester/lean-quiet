# Lean Noto rendering

The UI's pixels now come from Lean's TrueType reader and rasterizer.
`Font.glyph?` chooses Noto and `Font.adv` supplies rounded hmtx advances;
`Paint.Bitmap.glyph` composites the cached coverage. `Text.lean`, its
laws, `Row.layout`, and the row laws are unchanged. App.start's only
change passes screen density to Font.load.

`tools/noto_assets.sh` copies nine local, SHA-256 pinned, OFL core font files
from `/usr/share/fonts/truetype/noto` (override `NOTO_FONTS`). It is called
by the asset fetch step and the app tasks/gate. The license travels with
the fonts. No online font service or native font rasterizer is used.

Coverage: Latin, Greek, Cyrillic, Armenian, Georgian, Hebrew, Arabic
presentation forms, Thai, Ethiopic, Cherokee and Canadian Aboriginal
syllabics. Fallback is per code point. Colour emoji retain their existing
priority and pictures. Common CJK now uses the four pinned TrueType subsets
described below; the installed CFF collections are not used. Indic and other
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
parser or added axiom in the byte reader, cmap, outline reader or rasterizer.
The new memoization bridge uses unsafeBaseIO, as described below. Composite ancestry detects cycles;
a depth bound of 32 and a shared budget of 4096 visits also bound work.
Each glyph has at most 8192 points and 64 components; files are capped at
32 MiB. These are supported-format limits: excessive or unsupported
input returns none. `Ttf.read` validates every glyph before publishing a
face, including unused glyphs. The lazy app path uses `readHeader` on
first paint instead; `raster` then validates the requested outline and
its component graph. An invalid unused glyph is not scanned at startup. It is not an OpenType sanitizer: it does
not validate checksums, hint programs, or unsupported layout tables.

A `Noto.Cached` face owns a private, fresh identity, a pixel size, and its
immutable font bytes and a pure thunk for header parsing. Metrics never rasterize. All app instances and paint tasks
in a process share the bounded FIFO cache described below; font loading
does not allocate one permanently memoizing thunk per glyph any more.

## Raster and proofs

Quadratics are flattened adaptively to a nominal 1/256 px chord-error
bound (128 subdivisions maximum), then filled using nonzero winding on
an 8 × 8 sample grid. Coverage is saturated to 255. Bounds are computed
from transformed control points, so the ink can have explicitly declared
left/right/top/bottom overhang beyond the advance cell. Painting clips
signed positions before converting to pixel indices. Bold uses the
maximum of neighbouring coverage samples, not repeated alpha blending.

The 12 declarations in `engine/renderer/Ttf/Laws.lean` are in the unified axiom audit:

- `byte_in_bounds`: `u8 b i = some n` implies a proof `i < b.size` and
  `b[i].toNat = n`.
- `cmap_entry`: `lookup es c = some g` implies an entry `e ∈ es` with
  `e.contains c = true` and `e.glyph c = g`.
- `lookup_singleton`: `e.contains c = true` implies
  `lookup [e] c = some (e.glyph c)`. Header validation calls this lookup
  on each entry; this equivalence preserves its former glyph check.
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
the advances of the visible, non-mark input code points. These statements are unchanged in the layout port. The historical audit
counts below describe the old five-package tree; the unified port count
is recorded in the port report.

## Reproduce

Use the repository's Lean toolchain and build the offline Rust crypto
first, as documented at the root. Then, from the repository root:

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
A separate mutation run, `python3 tests/app/noto_negative.py`, changes the
actual code, requires a proof or runtime failure, and restores the source
after each fault. Run it without concurrent builds. Logs are written to
`out/noto-negative/`. Normal CI runs the positive suite, all headless app
scenarios and the axiom audit through `ci/local.sh check engine app readme`.

No phone, emulator or Mac was used. Android/iOS execution and their font
asset loading are unverified; their existing packaging copies the flat
assets directory, which now includes the pinned TrueType files.

## First-pass results (2026-10-28; committed as 29ea37e)

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

The full gate is **not green in this sandbox**. `ci/local.sh check engine app readme`
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

The first sandbox commit attempt could not create
`/mnt/storage/holmes-wt/lq/.git/worktrees/lq-noto/index.lock`: the Git
metadata filesystem is read-only. The lead subsequently ran the full gate outside the sandbox and committed
the first pass as `29ea37e`. The next pass below builds on that commit.

## CJK pass

Sources are the four Google Fonts TrueType variable builds at commit
`9b59ea9f333c5b8a99fa44e2a698496d6cde5b8e`. Exact URLs and SHA-256 hashes
are in `tools/cjk_fonts.tsv`, consumed by `tools/fetch_assets.sh` and
`tools/cjk_subset.py`. This run used only the supplied local files under
`/mnt/storage/holmes-wt/lq-tonight/fonts/`; nothing was downloaded.

All four sources default to weight 100, but body text ships at **400
(Regular)**. `fontTools.varLib.instancer.instantiateVariableFont` applies
wght=400 **before subsetting**; only then are variation/shaping tables and
hint programs removed. Each static result must have OS/2 weight 400 and
no fvar table. The resulting files are SHA-256 pinned in
`tools/cjk-subsets.sha256`. The source pins remain unchanged. Regenerating all four final outputs with
fontTools 4.68.0 reproduced every pinned SHA-256. Font family/style names identify
Regular; changing only those names left glyf/hmtx/cmap/loca byte-identical.
All nine earlier core Noto inputs were checked: each is already static
Regular, with OS/2 weight 400 and no fvar. The reference gate checks this
again. A CFF reader is unnecessary.

The character sets are generated by `tools/cjk_sets.py` from CPython's
local standard-code mappings (`gb2312`, `big5`, `euc_jp`, `euc_kr`; Python
3.14.4 in this run), with asserted standard-set cardinalities:

| Locale | Standard base set and encoded range | Base characters | Requested / present | Subset bytes |
|---|---|---:|---:|---:|
| SC | GB 2312-1980 level 1, zones 16–55 (B0–D7, A1–FE) | 3,755 | 4,059 / 4,043 | 1,143,236 |
| TC | Big5 common/first level, A440–C67E | 5,401 | 5,785 / 5,760 | 1,892,648 |
| JP | JIS X 0208 level 1, rows 16–47 (EUC B0–CF, A1–FE) | 2,965 | 3,477 / 3,458 | 966,220 |
| KR | KS X 1001 Hangul B0–C8 and Hanja CA–FD, trails A1–FE | 2,350 + 4,888 | 7,638 / 7,618 | 1,951,800 |

Every set adds U+3000–303F punctuation and U+FF00–FFEF fullwidth/halfwidth
forms. JP also adds U+3040–30FF and U+31F0–31FF kana; TC adds U+3100–312F
and U+31A0–31BF Bopomofo; KR adds U+3130–318F compatibility Jamo. The
manifest lists absent/unassigned requested points. The JP choice is JIS
level 1, **not** a claim to be the modern Jōyō list. The TC choice is
Big5's common level, not the different Taiwan MOE common-character list.
Only characters actually in the subset cmap can select Noto; other
points retain Unifont (tested with 龘), including Indic/reordering scripts.

The app has no per-message language tag. `Cjk.order` chooses JP for kana
and halfwidth katakana, KR for Hangul/compatibility Jamo, and TC for
Bopomofo. Shared Han and punctuation prefer SC, then TC, JP, KR if absent.
SC supplies a deterministic Simplified Chinese default; a code point
alone cannot identify the writer's language. Thus a Japanese paragraph's
shared Han may have SC forms. Locale-aware Han typography is not claimed.
The four routed sample lines and the fast-scroll screenshots are in
`out/cjk/scripts.ppm` and `out/cjk-after/`.

### Bounded cache

`Ttf.Cache` is the actual insertion/eviction code used by `Ttf.Memo`.
It uses 1,024 ring slots and a hash index containing slot numbers, not
extra bitmap copies. FIFO eviction keeps the newest insertion. A hit
shares the retained pixel object; oversized glyphs are drawn without
being retained. The global key is (fresh font-instance identity, glyph,
size, cell), so reloads, faces and sizes cannot reuse another's glyph.

The fixed charge budget is **4,194,304 bytes**:
`16*1024 + Σ(2*bitmap.pixels.size + 512)` for occupied slots. A compact
coverage copy has exact requested buffer capacity; the doubled payload
and per-entry charge allow buffer/metadata overhead. The formal bound is
on this charge and on retained coverage-byte counts, with at most 1,024
index entries. It is not a theorem about the Lean allocator or process
RSS: loaded font data, transient raster work, in-flight paint values,
and allocator overhead are outside the cache-state theorem.

`Ttf.Memo.Source.bitmap` is the **single memoization seam**, implemented
by private bitmapImpl/bitmapIO with `unsafeBaseIO`. Its contract is exact
equality with `Source.uncached`: the same Option result, origin, dimensions,
advance, cell, all four overhangs and every coverage byte. Hits, eviction,
fresh font instances, different sizes, failed parsing/rasterization and
concurrent calls must not change that result. Source's constructor,
identity, font thunk, size and cell are private; callers cannot substitute
another face while retaining an identity. Shared state is private too.

This is the review's permitted isolated, tested-contract option. Threading
an explicit cache through this renderer would change Bitmap.glyph/line,
Row.paint, Composer, Arrival, Sheet and the page painters, plus their
callers in App. Keeping one isolated function preserves those pure APIs
and the existing laws during the layout cutover. The README seam section
states the limitation: compiled memo/spec equivalence is **not proved**.
Kernel proofs establish bounds on the **same Cache.put called by bitmapIO**;
fresh identities and mutex/compiler behavior remain trusted and tested.

Parsing and raster work run outside the cache lock; concurrent misses may
compute the same glyph before publication. Eviction can cause re-rasterization.
The compact copy changes buffer capacity only; the contract compares its
whole value with the original raster result.

Five new audited statements, in `engine/renderer/Ttf/Cache.lean`:

- `empty_valid`: `Valid empty`.
- `checked_valid (s)`: `Valid (checked s)`.
- `put_bound (s key bitmap)`: for `r := put s key bitmap`,
  `bytes r ≤ budget ∧ r.slots.size = capacity ∧ r.index.size ≤ capacity ∧ r.hand < capacity`.
- `payload_le_bytes (s)`: `payload s ≤ bytes s`.
- `put_payload_bound (s key bitmap)`: `payload (put s key bitmap) ≤ budget`.

Here payload is the sum of occupied slots' coverage lengths, capacity is
1,024, and Valid is exactly the four conjuncts of put_bound. Empty-state
validity and the positive insertion/lookup/eviction tests give witnesses.
All 98 prior app theorems remain unchanged; the app audit now passes 103.
Text.lean, its laws, Row.layout and RowLaws.lean have no edits.

### Tests and performance

`mise run host:cjk` builds its two executables and is wired into both the
root mise app gate and `ci/local.sh`. It checks 20,879 cmap/hmtx pairs,
680 glyph bitmaps at 16, 32, 48 and 64 pixels, and four full Text/Paint
lines. The fontTools pen reads independently instanced, full original fonts at
wght=400 for the glyph references; it does not read the shipped subset
for those glyph comparisons. Reference cache stamps include the source
SHA, weight and fontTools version. The tolerance is unchanged:
32/255 maximum per-pixel error and 1/255 mean error. Observed maximum:
24/255 over 1,068,277 glyph pixels, mean 0.02929/255; routed lines:
15/255 maximum over 585,000 RGB pixels.

Cache tests perform 2,200 insertions, assert the new entry survives every
eviction, reject oversized retention, check the index, fill the real
runtime cache with 1,800 requests, compare a reloaded glyph, and compare
concurrent results from eight workers with direct rasterization. Runtime
stress reached 4,194,284 charged bytes; the scroll reached exactly the
4,194,304-byte budget. It never exceeded the budget.

Nine source mutations were detected and reverted (`tests/app/cjk_negative.py`):
invalid empty-state capacity; removed validation; bypassed put validation;
zero byte charge; disabled eviction; bypassed the bound in the runtime
hook; omitted font identity; changed Han priority; restored the old cmap
segment cap. The Korean subset has 4,889 segments, so the old arbitrary
4,096-segment cap was a real reader bug. The new cap is the maximum that
fits a format-4 table's 16-bit length; existing checked table reads remain.
A changed source-font hash was also refused. The old core-script crop
failed at error 235/255 because the following CJK line overhang entered
it; a pre-next-line snapshot fixes that test, and restoring the old crop
was verified to fail. No tolerances were relaxed.

### Lazy startup and the memo contract

The eager loader was profiled by stage (`platforms.headless.FontLoad`, log in
`out/review-before/profile.log`). On the pinned Thin inputs the costs were:

- Reading all 13 files: about 1.2 ms.
- Header/cmap parsing: about 3.2 ms.
- Validating every CJK outline: about 187 ms (core outlines: about 40 ms).
- Building the CJK union: 0.5 ms; repeated cmap searches for selection: 47 ms.

`tools/noto_index.py` now builds a **214,794-byte** cmap/hmtx index for all
13 static Regular faces. Its SHA-256 is pinned in `noto-index.sha256`.
Layout reads these bounded, sorted records and selects faces directly;
it neither parses outlines nor repeatedly searches cmap lists. The index
uses the same per-code-point locale priority as Cjk.order. Every record
and every selected runtime glyph/advance is compared with the actual
TrueType reader in the gate. This build-time correspondence is tested,
not a kernel theorem.

Font files are still read into immutable bytes at load: profiling showed
that avoiding these roughly 1 ms reads would not explain the regression.
This is the review's compact-lookup alternative, without introducing a
native mmap reader. Each source holds a **pure thunk** for readHeader,
forced only by its first painted glyph. Requested outlines are decoded
by the existing bounded raster path. Unused scripts never parse cmap or
outlines. The strict whole-file Ttf.read remains unchanged for validation
and the hostile-font tests.

`mise run host:font-contract` builds and runs the new contract test and is
wired into both app gates. It checks **26,829 compact records**, **16,543
selected glyph/advance pairs**, **68 malformed indices**, and **5,374
whole-result memo comparisons**, including eight concurrent workers.
A composite loop is rejected on first use. The loader has a 40 ms budget;
measured runs were 2,621–18,315 µs. An eager-loader negative control took
266,742 µs and failed that budget.

Seven review controls were caught and reverted: instancing Thin instead of
Regular; retaining a Thin family name; comparing against a Thin reference; reinstating eager whole-font
validation; changing compact advances; corrupting only cache-hit metadata;
and corrupting only cache-miss metadata. The last two demonstrate why
comparing only coverage pixels was insufficient. These are reproducible
with `tests/app/font_review_negative.py`.

The 500-post CJK corpus samples all four sets with the same signed app
posts and 250-pixel-per-frame scroll. It includes unassigned points from
the added ranges to exercise fallback. Three alternating runs compared the old eager loader with the new lazy
loader using identical Regular glyph/metric assets. The final family-name
correction changed metadata only. Logs and the exact before/after binaries
are in `out/font-perf/`; the driver is `out/font_perf_compare.py`.

| Measurement (median across three runs) | Eager Regular | Lazy Regular |
|---|---:|---:|
| Cold open | 337 ms | 43 ms |
| Normal host step median | 2,381 µs | 2,390 µs |
| Normal host step p95 | 4,309 µs | 4,382 µs |
| Normal host maximum | 12,479 µs | 8,683 µs |
| Normal host total fling | 15,060 ms | 14,976 ms |
| CJK step median | 2,012 µs | 2,138 µs |
| CJK step p95 | 4,373 µs | 4,282 µs |
| CJK maximum | 12,088 µs | 9,861 µs |

Cold-open ranges were 336–338 ms eager and 41–47 ms lazy, below the original
69 ms target. All six final lazy flings had zero unpainted frames. Normal
host p95 increased 73 µs (1.7%); it ranged 4,131–4,394 µs lazy versus
4,227–13,729 µs eager. These measurements do not establish a statistically
significant speed change. The CJK p95 and total fling times improved, and
all lazy p95 values remained far below the 16,667 µs frame budget.

Timing outliers are retained in the logs, not discarded: one eager CJK run
had 452 unpainted frames under contention. Earlier standalone lazy runs
also had 48 and 1 unpainted frames, so these tests do not promise smooth
painting under arbitrary system load. The repeated final lazy runs were
fully painted. Compared with the earlier Thin pass's single run, CJK p95
is 4,282 versus 4,899 µs; Regular has not introduced a sustained fling
regression in these measurements.


The final `ci/local.sh app` run measured 42 ms cold open, normal-host
p95 4,373 µs and CJK p95 4,270 µs, with zero unpainted rows in both
flings. The CJK maximum was 10,082 µs over 509 frames. Screenshots in
`out/cjk/scripts.ppm` and `out/host/open.ppm` were inspected and show
Regular CJK alongside the unchanged core fonts.


### Package sizes after the review fixes

The four final Regular subsets total **5,953,904 bytes**; the compact
index adds **214,794 bytes**, for **6,168,698 asset bytes** over 29ea37e.
No original variable font or reference font is packaged.

| Artifact | Before CJK (29ea37e) | Final Regular CJK | Delta |
|---|---:|---:|---:|
| Android arm64 APK | 38,533,047 | 42,379,589 | +3,846,542 bytes |
| Android arm64 native library, uncompressed | 63,897,280 | 64,047,520 | +150,240 bytes |
| Linux headless Main executable | 12,125,384 | 12,181,472 | +56,088 bytes |

The APK adds 3,680,576 compressed font bytes, 122,953 compressed index
bytes, 41,862 compressed native-code bytes and 1,151 packaging bytes.
Compared with the reviewed Thin APK, the Regular/lazy fixes add 376,906
APK bytes. Linux's executable plus unpacked assets grows by **6,224,786
bytes** over 29ea37e. There is no separate desktop GUI package here.
iOS assets add **6,168,698 bytes**; iOS code and IPA sizes remain unmeasured
without a local SDK. The arm64 APK was built, never installed or run.
No device, emulator, Mac or network service was used.


### Final gate and handoff

All **103 app theorems** pass `mise run check` on standard axioms; the
review fixes add no new theorem statements or axioms. The five cache laws
above and the existing Text/Row/Paint/Noto laws are unchanged. README proof
links validate (198 links, 291 audited laws). The standard Noto suite passes
5,955 mappings/metrics, 390 bitmaps, 311 hostile files and 11 reference lines.
Host passes 29 assertions, two_nodes 49 and arrival 24. The nine earlier
CJK source controls were rerun and all rejected; seven review controls
were also rejected and reverted, in addition to the two artifact controls
recorded above (18 controls across the CJK work).

`ci/local.sh app` passed its font, contract, scroll, host and two_nodes
checks, then stopped at net_join because node startup returned
`operation not permitted (error code: 1)`. The explicitly required
`host:cross` and `host:attach` tasks were also run to completion, without
weakening their assertions. The lead must rerun TCP outside this sandbox.
No engine source was changed. Device runtime checks and iOS code/package
sizes remain unverified.

Observed TCP results were net_join 2 pass / 8 fail, host:cross 6 pass /
12 fail, and host:attach 6 pass / 8 fail, cascading from socket denial.
The required tasks were run again for this review, not inferred from the
previous pass.

At that historical handoff, Git could not create the worktree's index.lock: the shared metadata
filesystem is read-only. HEAD was `29ea37e`; the lead subsequently committed and accepted the work as `fb6584b`.
`out/cjk-commit-message.txt` has been overwritten with the final message
and Codex coauthor trailer. `out/cjk-change.patch` contains all source,
test and documentation changes and passes `git apply --reverse --check`.

## Unified-tree port (2026-10-28)

The accepted `fb6584b` implementation is ported onto the fetched main
snapshot `ab55590328f206d263c810477bdc946062cc3a57`, following
`ci/reorg-map.tsv` and `ci/reorg-imports.py`. The shared remote-tracking
ref advanced while work was underway; this exact snapshot is the gate's
base. There was no network fetch. This pass adds no font feature.

All 37 additions have these destinations (the names within each row
are separate files):

| Destination directory | Files |
|---|---|
| `engine/renderer/` | `Cjk.lean`, `Noto.lean` |
| `engine/renderer/Ttf/` | `Blit.lean`, `Bytes.lean`, `Cache.lean`, `Cmap.lean`, `Index.lean`, `Laws.lean`, `Memo.lean`, `Raster.lean`, `Read.lean` |
| `platforms/headless/` | `Cjk.lean`, `CjkScroll.lean`, `FontContract.lean`, `FontLoad.lean`, `Noto.lean` |
| `tests/app/` | `cjk.sh`, `cjk_negative.py`, `cjk_reference.py`, `font_contract.sh`, `font_review_negative.py`, `noto.sh`, `noto_kern.lean`, `noto_negative.py`, `noto_reference.py` |
| `tools/` | `NOTO-LICENSE.txt`, `cjk-manifest.json`, `cjk-subsets.sha256`, `cjk_assets.sh`, `cjk_fonts.tsv`, `cjk_sets.py`, `cjk_subset.py`, `noto-index.sha256`, `noto.sha256`, `noto_assets.sh`, `noto_index.py` |
| `docs/` | `NOTO.md` |

The app hooks are in `App.lean`, `engine/renderer/Font.lean` and
`engine/renderer/Paint.lean`; platform packaging hooks are in
`platforms/android/twin/build_apk.sh` and `platforms/ios/ship.sh`.
The audit is `tests/Axioms.lean`, and the named mise tasks and the app
CI gate build the new root-level executables. No compatibility modules
were introduced. Main's Text, TextLaws, WrapLaws, Row, RowLaws, Image and
ReaderLaws sources are byte-identical to the selected main snapshot.
The scroll fixture supplies main's new message sequence argument to
`sealedPost`; main's implementation is untouched.

### Port proof and wiring gate

`ci/local.sh check` passes **547 laws**, using only standard axioms.
`ci/local.sh readme` passes **357 generated links** and its six negative
controls. `ci/proof-links.py` generated the lead and wiring section:
**374 wired, 7 World, 166 model**, with **all 17 Ttf/cache laws wired**.
The README's Quality cell and seam both explicitly say:
**Source.bitmap's compiled equivalence is tested, not proven**.

The compact index had left `Ttf.lookup` outside the running path. Header
validation now calls it for each entry's character, instead of duplicating
its glyph selection. The one added theorem states exactly:

```lean
theorem lookup_singleton (e : Entry) (c : Nat) (h : e.contains c = true) :
    lookup [e] c = some (e.glyph c)
```

`tests/wiring.txt` identifies `Cache.payload` as the mathematical sum of
retained bytes measured on the running cache. Its `wired` lines assert the
checker's result; they do not override classification. No main law was
weakened. The new law's negative control changed lookup to return
`e.glyph c + 1`: `cmap_entry`, `lookup_singleton` and `ink_witness` failed.
The mutation was reverted, and the restored proof and full audit passed.
Logs are in `out/port/lookup-negative.log` and `lookup-restored.log`.

The first build's extra virtual-address limit caused thread-creation
failures, not a 48 GB memory-cap failure or a tactic exhausting memory.
Removing that limit and serializing module builds fixed it; the isolated
`engine/wire/Frame.lean` probe peaked at 844,596 KiB RSS. Native modules
were also built serially. Temporary Lean `-j1 -M8192` build arguments
were removed from the delivered lakefile. An optional build of main's
`platforms/headless/Dump.lean` found its existing `Body.post` arity error
at line 20; that unrelated diagnostic is unchanged and is not an app
gate target.

### Port runtime results

`SKIP_TCP=1 ci/local.sh app` passes with the normal runtime worker pool
(75 seconds). It builds the socket executables too. Results:

- Core Noto: 5,955 cmap/metric pairs, 390 bitmaps, 311 hostile fonts,
  11 reference lines; maximum error 16/255 for glyphs, 15/255 for lines.
  Kerning: 3 pair/scale checks and 30 truncated tables refused.
- CJK: 20,879 cmap/metric pairs, 680 bitmaps, 4 reference lines;
  maximum glyph error 24/255, mean 0.02929/255, line maximum 15/255.
  Both reference suites retain their 32/255 maximum and 1/255 mean
  per-glyph tolerance, comparing Regular with Regular.
- Cache: 2,200 explicit insertions, 1,800 runtime misses and eight workers;
  the contract checks 26,829 compact pairs, 16,543 selected metrics,
  68 invalid indices and 5,374 whole-result comparisons. Peak charge
  is exactly 4,194,304 bytes. Compact font load took 3,199 microseconds.
- App: host 29, two_nodes 49 and arrival 24 assertions pass (102 total).
  CJK scrolling completes 500 posts in 509 frames within its p95 budget.
  Regular CJK script and app screenshots were inspected.

These are the final gate's numbers, with the earlier standalone default
worker run retained to show variation on this shared machine:

| Measurement | Accepted historical baseline | Port standalone | Port final app gate |
|---|---:|---:|---:|
| Cold open | 43 ms | 58 ms | 58 ms |
| Normal-scroll median | 2,390 µs | 2,037 µs | 1,603 µs |
| Normal-scroll p95 | 4,382 µs | 8,724 µs | 2,698 µs |
| Normal-scroll maximum | 8,683 µs | 14,912 µs | 4,079 µs |
| CJK median | 2,138 µs | 2,018 µs | 2,568 µs |
| CJK p95 | 4,282 µs | 3,126 µs | 4,252 µs |
| CJK maximum | 9,861 µs | 7,330 µs | 11,512 µs |
| Unpainted normal frames / worst rows | 0 / 0 | 0 / 0 | 0 / 0 |
| Unpainted CJK frames / worst rows | 0 / 0 | 0 / 0 | 9 / 1 |

Cold open is 15 ms (34.9%) above the historical 43 ms and still below
the original 69 ms target. The preserved accepted binary, rerun now,
measured 52 ms cold open and 5,472 µs normal p95. This is not a controlled
attribution of the change to Noto: main and machine load changed. The
normal p95 range is too wide to claim a stable improvement. The final
CJK run's nine transient blank frames are retained as a limitation;
its final screen is fully painted. No renderer scheduling or main
layout changes were made to improve these measurements.

The initial app gate inadvertently inherited `LEAN_NUM_THREADS=1` from
serial build setup. It also passed, but measured 209 ms cold open,
8,235 µs normal p95 and 11,322 µs CJK p95, with 471 CJK unpainted frames
(worst eight rows). Repeating with the normal worker pool removes that
build-only restriction. This first result is preserved in
`out/port/app-one-worker.log`; the final gate is `out/ci/app.log`.
Standalone timing logs and lossless screenshot previews are under
`out/port/`. The default-worker standalone processes peaked at
216,132 KiB (CJK) and 284,668 KiB (host) RSS.

### Port handoff limits

`net_join`, `cross` and `attach` were built but deliberately skipped:
TCP sockets are unavailable in this sandbox. The lead still needs
`ci/local.sh check engine net app readme` outside it. Android/iOS packages
were not rebuilt in this layout pass, and no phone, emulator or Mac was
used. All existing font assets and pins were present; nothing was fetched.

Git's shared metadata remains read-only: creating
`/mnt/storage/holmes-wt/lq/.git/worktrees/lq-noto/ORIG_HEAD.lock` returns
`Read-only file system`. The attempted merge could not begin, so HEAD
remains `fb6584b`; **there is no port commit or recorded merge yet**.
The working files contain the gated merge result. `out/port/noto-port.patch`
is the port delta against the exact main snapshot above;
`out/port/files.tsv` maps every moved addition, and
`out/port/commit-message.txt` contains both requested coauthor trailers.
Recording the merge commit requires writable shared Git metadata.
