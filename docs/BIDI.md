# Paragraph bidi (Unicode 16.0.0)

The renderer calls `Text.visualIn` through `visualL`/`visual`, for both
message lines and names. `engine/renderer/bidi/Basic.lean` owns the
algorithm. The old code used handwritten script ranges, with no Unicode
version. `bidi/Class.lean` now contains Unicode 16.0.0 Bidi_Class data,
generated offline by `tools/bidi_table.py` from Python's UCD 16.0.0 and
UAX #44 defaults for unassigned characters. The generated data is checked
in; the renderer does not depend on Python or a native bidi library.

## Rule audit

| Rule | Before this change | Running code and scope now |
|---|---|---|
| P2–P3 | First strong in incomplete script ranges | `paragraph`: first L/R/AL, otherwise LTR; explicit LTR/RTL available through `visualIn` |
| X1–X8 | No explicit embedding, override or isolate stack | Out of scope; embeddings, overrides, isolates and directional marks are ON under Quiet's control policy |
| X9 | Controls retained | Out of scope; BN retained as ON to preserve `visual_perm` |
| X10 | No isolating run sequences | One implicit embedding level, sos/eos from paragraph direction; explicit runs out of scope |
| W1 | Marks copied the preceding *level* after resolution | `w1`: NSM inherits preceding type or sos |
| W2 | EN treated like the preceding strong direction | `w23`: EN after AL becomes AN |
| W3 | AL and R conflated by script range | `w23`: AL becomes R, after W2 |
| W4 | Missing | `w4`: single ES/CS between EN becomes EN; single CS between AN becomes AN |
| W5 | Missing | `et` in both directions: entire ET sequence adjacent to EN becomes EN |
| W6 | All punctuation was neutral from the start | `w67`: remaining ES/ET/CS become ON, after W4/W5 |
| W7 | Approximation by preceding strong direction | `w67`: EN after L becomes L; EN/AN never update the preceding strong type |
| N0 | Missing | Paired brackets out of scope; bracket characters use their ordinary ON behavior |
| N1–N2 | Approximation; numbers incorrectly inherited preceding direction | `following`/`neutrals`: EN/AN count as R, agreeing neighbours resolve neutrals, otherwise embedding direction |
| I1–I2 | Approximation | `implicit`: exact increments for base level 0 or 1 |
| L1 | Missing | `reset`: B/S, WS preceding B/S, and trailing WS reset to paragraph level |
| L2 | Level-run reversals | `reorder`: passes at levels 2 and 1 over numeric blocks; all other blocks are single characters |
| L3 | Limited mark placement | Existing `placeL` mark positioning; full combining-cluster shaping is not covered by this change or the Unicode test files |
| L4 | Missing | Mirrored glyph substitution out of scope |

Each renderer line is treated as a single paragraph, as before. Resolving
one paragraph across soft wraps, full X-level processing, bracket pairing,
mirroring, and full script shaping remain outside this scope. NSM type
resolution (W1) is implemented; glyph positioning for every Unicode mark
is a separate renderer concern.

Quiet intentionally neutralizes LRM, RLM and ALM as well as embedding and
isolate controls. `controls_neutral` checks this classification, not
invariance under inserting arbitrary ON characters. ON insertion can
split a number or neutral run. Internal plane-15 emoji tokens also remain ON, preserving the renderer's
existing emoji policy. BN characters are retained as ON; the
Unicode conformance harness excludes these policy differences explicitly.

## Number runs and proofs

`runs` is the single definition used by rendering, laws and the harness.
It groups maximal adjacent equal EN or AN types **after W1–W5**, including
single W4 separators and complete W5 terminator sequences. W1 can also
attach NSMs to these runs. Other characters form singleton blocks.

`numbers_keep_order rtl cs run` and `arabic_numbers_keep_order rtl cs run`
say that membership in `numberRuns .en rtl cs` or `.an rtl cs` implies
`run <:+: visualIn rtl cs`: the whole run is contiguous and in logical
order. They quantify over all lines and both directions. The underlying
`run_contiguous` law also works on logical indices, so equal digits do not
hide exchanges. `numbers_witness` includes `$12:30%` between Hebrew
letters, and `arabic_numbers_witness` includes Arabic-Indic `١,٢`.
`visual_perm`, placement, wrapping, and names laws remain separate.

W2 matters: in `ا 3-4 ب`, the digits become AN before W4, so ES does not
join them; its Unicode visual order is `ب 4-3 ا`. Similarly, `ا 50% ب`
becomes `ب %50 ا` because W5 applies only to EN. These are two separate
number runs / a number next to a neutral, not failures of the run law.
The same strings after Hebrew retain `3-4` and `50%`; Arabic decimal,
comma and colon examples retain their numeric order through AN/CS.

## Cost

Classification uses a balanced, bounded Unicode table. W1–W7, run
formation, neutral resolution, level attachment, L1 and both L2 passes
visit each character/block a constant number of times: O(n) time and
O(n) space per line. There is no repeated linked-list indexing, suffix
search or repeated append to a growing prefix. Numeric blocks remain
in logical order because their final levels are even (0 or 2); the net
L2 reversal inside such a block is the identity. No formal cost theorem
is claimed.

## Validation

`mise run test:bidi` builds and runs the corpus harness. `mise run
host:bidi` builds and runs the pixel regression on the headless app.
Both run in the app gate. The Unicode corpus headers and data are kept
unchanged under `tests/app/unicode-bidi-16.0.0/`.

The harness checks expected levels, exact logical indices in visual
order, and the renderer's code-point order. Exclusions are disjoint in
this precedence: embeddings/overrides/PDF; isolates; BN; Quiet's
LRM/RLM/ALM policy; paired-bracket characters (conservative N0 exclusion,
including unmatched brackets); internal emoji tokens. No exclusion depends
on test output. Counts count paragraph modes, not comments or directives:

| Corpus | Data records | Passed | Failed | Embeddings | Isolates | BN | Marks policy | Brackets | Emoji tokens |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| BidiTest | 490,846 | 73,593 | 0 | 488,220 | 181,983 | 26,445 | 0 | 0 | 0 |
| BidiCharacterTest | 91,707 | 6 | 0 | 81 | 21 | 8 | 3 | 91,588 | 0 |

Together: 861,948 paragraph cases visited, 73,599 passing, zero failing,
788,349 explicitly excluded. The shared run check covers 43,502 numeric
runs by index. The harness rejects incomplete corpus files. The unusually
small character-file count is intentional and visible: this file mostly
exercises paired brackets, and N0 is not implemented.

There are 40 focused checks (the five issue strings in Hebrew/Arabic and
both explicit directions plus auto, weak-type boundary cases, and the
corpus-discovered L1 regression). The headless app has 9 checks: opening
the conversation and, for each of Hebrew and Arabic, sending/storing the
message, glyph order, name order, and all 5,760 pixels of a clock strip.
The pixel oracle paints the five expected glyphs directly, without bidi,
layout or placement. Screens and row crops remain in `out/bidi-host/`.

The first full corpus run exposed 14 cases in which NSM inherited WS/S
under W1 and was then incorrectly reset by L1. Blocks now retain the
original class for L1. The explicit regression is `[R, S, NSM, AN]`,
whose LTR levels must be `[1, 0, 1, 2]`.

`python3 tests/app/bidi_negative.py` temporarily mutates the actual running
code, requires rejection, and restores sources in a `finally` block.
All 28 controls were caught (15 proof, 12 behavior, 1 pixel). Disabling
W4 caused 170 corpus failures and 25 focused failures; disabling W5
caused 1,131 corpus failures and 6 focused failures. Restoring the old L1
reset caused exactly 14 corpus failures and one focused failure.
Proof controls drop payloads at each pass, lose/duplicate blocks, reverse
number blocks, and disable W4/W5 to invalidate the witnesses. Behavior
controls break each weak rule, N1/N2, I1/I2, L1 and L2. The pixel control
swaps the clock's edge digits during painting while leaving placement
unchanged. Logs are in `out/bidi-negative/`.


The full gate can run with `SKIP_TCP=1 ci/local.sh check app engine readme`
in this sandbox. That flag still builds all TCP executables and prints
an explicit UNVERIFIED line; the default gate runs them. Device execution
is not part of these checks.
