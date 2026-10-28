# lean-qr

QR codes in Lean 4 with no dependencies: an encoder (bytes to a symbol and
a bitmap), a decoder for camera frames (grayscale pixels to bytes), laws
proven on the decoder's own functions, and a minimal Android camera
harness whose frames are decoded by Lean. The harness also has the
composer's image tools (Pic, below): the system Photo Picker and the
system camera hand pictures to Lean, which stores them as QOI and draws
their thumbnails.

For a Lean Quiet: the inviter shows the invite link as a QR code (the
encoder); the joiner points the phone at it, a small native tool hands
each camera frame's luma plane over, and Lean does all the parsing (the
decoder).

## The laws (Qr/Laws.lean)

They are proven on the functions `decode` runs, not on a model of them.

Data stream (Qr/SegLaws.lean):

- **`parse_dataStream`**: `(∀ s ∈ ss, s.Valid v) → dataStream v cap ss =
  some cw → parse v (bytesBits cw) = some ss`. The data codewords the
  encoder writes for valid segments (numeric, alphanumeric, byte, ECI;
  with the terminator, the zero bits to the byte and the 0xEC/0x11 pad
  bytes) parse back to those segments.
- **`parse_segsBits`**: the same at the bit level, for any tail that
  starts with the terminator or is shorter than 4 bits.
- **`parse_valid`**: `parse v bs = some ss → ∀ s ∈ ss, s.Valid v`. What
  the parser accepts is valid (counts fit their field, digits are digits,
  characters are in the alphanumeric set, ECI numbers are below 10⁶), so
  it can be written back and read again.

Format and version information (Qr/Format.lean):

- **`decodeFormat_correct`**: `mask < 8 → hd 15 (formatBits e mask) x ≤ 3
  → decodeFormat x = some (e, mask)`. A format reading with at most three
  wrong bits decodes to the level and mask that were written (the BCH(15,5)
  code's codewords are proven at least 7 apart: `format_distance`).
- **`decodeVersion_correct`**: the same for version information, versions
  7–40 (BCH(18,6), codewords at least 8 apart: `version_distance`).

Reed–Solomon over GF(256) (Qr/RS.lean, Qr/Laws.lean):

- **`RS.correct_sound`**: `RS.correct k r = some c → (∀ j < k, eval c (exp
  j) = 0) ∧ c.size = r.size ∧ dist r c ≤ k / 2`. A block the corrector
  returns has zero syndromes (it vanishes at the generator's roots α⁰ …
  α^(k−1), so it is a codeword), is as long as the received block, and
  differs from it in at most ⌊k/2⌋ places. Whatever Berlekamp–Massey and
  Forney compute, the decoder never hands on a block that is not a
  codeword within capacity.
- **`RS.correct_clean`**: a block with zero syndromes comes back unchanged.

Frames:

- **`decodeImage_malformed`**: a frame whose buffer does not hold `h`
  rows of `stride` bytes (or that is empty, or over 16384 pixels a side)
  decodes to `none`.

The decoder is total. Lean accepts every definition without `partial`,
`unsafe` or fuel; the recursive parsers (`parse`, the segment readers) are
well-founded or structural and Lean checks their termination; every loop
is a `for` over a finite range (no `while`/`repeat`); every array read is
`a[i]?` with a default and every write `setIfInBounds` or a size-checked
`set`. The gate scans the whole library for `sorry`, `partial`, `unsafe`,
`panic`, `!`-indexing and `!`-functions, `while`, `repeat`,
`native_decide` and `extern`, and checks with `#print axioms` that every
law uses only `propext`, `Classical.choice` and `Quot.sound`. The proofs
by computation (`format_distance`, `version_distance`, the alphanumeric
table) use `decide +kernel`, which the kernel checks.

### What is proven and what is only tested

Proven: the bit layer (`readBits_bitsOf`, `bytesBits_packBytes`), the
segment layer both ways (round trip and soundness), format and version
information decoding with up to 3 errors, Reed–Solomon soundness, and the
decoder's totality and termination as Lean's type checker sees it.

Only tested:

- That Reed–Solomon correction *succeeds* within capacity (Berlekamp–
  Massey/Forney completeness) and that the encoder's blocks have zero
  syndromes: 2808 cases over all 117 block shapes QR uses.
- The matrix layer: function patterns, the zigzag placement, masks,
  interleaving, block tables. Tested by round trips over every version,
  level and mask, and module for module against qrencode and Nayuki's
  qrcodegen.
- Everything about pixels: binarization, finder detection, the
  homography, alignment search, sampling. Tested on rendered and
  synthetically distorted frames, cross-tool symbols, hostile frames and
  fuzzing, and on the emulator's camera.
- That the decoder's work is bounded is by construction (bounded `for`
  loops, at most 48 finder candidates, 4 triangles, 3 sizes), and
  measured (hostile frames take at most tens of milliseconds), not proven.

## API

```lean
import Qr
open Qr

-- Encoding
inductive Ecc | L | M | Q | H
inductive Seg | numeric (ds : List UInt8) | alnum (cs : List UInt8) | bytes (bs : List UInt8) | eci (n : Nat)
structure Symbol where version : Nat; ecc : Ecc; mask : Nat; grid : Grid
encode     : ByteArray → (e : Ecc := .M) → (minVersion : Nat := 1) → (mask : Option Nat := none) → Option Symbol
encodeSegs : List Seg → (e : Ecc := .M) → (minVersion : Nat := 1) → (mask : Option Nat := none) → Option Symbol
render     : Symbol → (scale : Nat := 4) → (quiet : Nat := 4) → Image   -- grayscale, black on white

-- Decoding
structure Image where w h stride : Nat; px : ByteArray                  -- row-major luma
decode       : (w h : Nat) → ByteArray → (stride : Nat := w) → Option ByteArray
decodeImage  : Image → Option Decoded        -- version, ecc, mask, segs, corrected, mirrored
decodeGrid   : Grid → Option Decoded         -- a module matrix, as is
decodeGridAny : Grid → Option Decoded        -- or its mirror image

-- For native callers (Android JNI)
@[export lean_qr_decode_luma] decodeLuma : UInt32 → UInt32 → UInt32 → ByteArray → Option (ByteArray × String)
```

`encode` uses byte mode at the smallest version from `minVersion` that
holds the data, and the mask of lowest penalty (the standard's four rules,
as Nayuki's qrcodegen scores them: they pick the same mask in every
cross-checked symbol) unless `mask` names one. Versions 1–40 and levels
L, M, Q, H all work. `Decoded.payload` is the bytes of the segments; ECI
designators are passed through as `.eci n` segments in `segs` and do not
change the bytes.

From another Lake package:

```toml
[[require]]
name = "qr"
path = "/mnt/storage/holmes-wt/lean-qr"
```

The library imports only `Init`, so it cross-compiles to Android with
Lean's runtime and nothing else.

## How a frame is decoded

1. Binarize with local thresholds (8×8 blocks, the mean black point of the
   5×5 blocks around), falling back to a global one.
2. Find finder patterns: 1:1:3:1:1 runs on every row, cross-checked down
   the column, along the row and the diagonal, merged.
3. Take the three that best make a right isosceles triangle; the
   right-angle one is top-left, the turn decides top-right (a mirror image
   comes out transposed and is read transposed).
4. Measure the module size along the lines between finder centres; try the
   sizes it suggests (and the size version information gives).
5. Map module coordinates to pixels: a homography through the finder
   centres and the 12 corners of the finders' dark rings (or, without
   them, an affine map); the timing patterns must show through it. Then
   the bottom-right alignment pattern is searched for by matching the 5×5
   pattern through the map, the homography refitted, every other alignment
   pattern found near its prediction, and a least-squares homography fitted
   to all of them.
6. Sample each module at nine points (majority), read format information
   (either copy), unmask, read the codewords in zigzag order, deinterleave,
   Reed–Solomon-correct each block, parse the segments.

## Tests

`mise run check` is the deterministic gate (tests/check.sh):

- builds the library (which checks the proofs), prints the laws' axioms
  and fails on anything beyond the standard three, and scans for escape
  hatches;
- runs `qr_check` (Tests/Check.lean), 45,092 checks:
  - pictures (Pic): QOI round trips, Pillow-made QOI blobs
    (tests/fixtures/qoi), every truncation and 2,000 mutations of a blob,
    hostile headers, sizes, the tray's layout and the composer's
    refusals: 4,872
  - qrencode's matrices for every version 1–40 (tests/fixtures, frozen),
    decoded as matrices and as frames: 80
  - data streams: 3,000 random segment lists of every mode round trip,
    and 3,000 random bit strings parse to nothing or to segments that
    round trip again: 5,895
  - Reed–Solomon over all 117 block shapes QR uses, 0 to capacity errors
    corrected exactly, beyond capacity refused (or, allowed by the law but
    not seen, corrected to another codeword): 2,808
  - format and version information with every pattern of up to 3 (format)
    or 2 (version) wrong bits: 27,574
  - matrices, versions 1–40 × L M Q H × masks 0–7, as drawn, mirrored, and
    with a quarter of the correctable modules flipped: 2,880
  - frames: every version and level rendered and decoded, every mask at
    versions 1, 2, 7, 10, 14 in four rotations, plain and mirrored: 480
  - 31 hostile frames (empty, a short buffer, a stride below the width, a
    10⁶-pixel-square header over 100 bytes, one pixel, flat, stripes,
    gradients, rings, 8 checkerboards, finder-pattern wallpaper at 3
    scales, 6 noise frames, three finders around garbage) all give `none`,
    the slowest in 20 ms
  - fuzzing: 1,500 matrices with 0–29% of modules flipped and 300 frames
    with 0–24% of pixels replaced: 218 decoded right, 1,582 gave nothing,
    0 decoded to a wrong payload
- the camera suite (tests/camera.sh, tools/distort): the invite link
  `quiet://join/` + 187 base62 characters (200 bytes; versions 9, 10, 12,
  15 at L, M, Q, H), encoded by Lean and put into 640×480 frames with a
  perspective view, rotation, scale, blur, noise, uneven lighting, low
  contrast, partial occlusion and mirror images: 254 frames, 254 decoded,
  37 ms a frame on average (69 ms the slowest) on this machine. The sweeps:
  rotation 0–345°, perspective (the far edge shrunk 10–30%, five
  directions), 3–8 pixels a module, Gaussian blur σ 0.8–1.6 px, noise σ
  8–28, lighting gradients down to 15% brightness, contrast 25–40%, a
  dark square over 4% (M), 9% (Q) and 16% (H) of the symbol, mirror
  images; then 16 random combinations per level.
- QOI against Pillow (tools/xcheck/qoi.py): 7 pictures each way, 14 of 14
  agree;
- the cross-checks (tests/xcheck.sh, tools/xcheck), versions 1–40 in 20
  steps × L M Q H × invite/mixed text/binary:
  - qrencode → Lean: 240 of 240 decode from pixels and 240 of 240 from
    the module matrix (byte mode and qrencode's own numeric/alphanumeric/
    byte segmentation);
  - Lean's encoder draws qrencode's matrix module for module (byte mode,
    same version, level and mask): 160 of 160;
  - Lean → zbarimg: 240 of 240 decode to the same bytes;
  - segno → Lean: 240 of 240, and 16 of 16 with an ECI (UTF-8) segment;
  - qrcodegen (Nayuki's reference): Lean draws the same matrix at every
    mask (1,920 of 1,920) and picks the same mask by penalty (240 of 240).
    segno picks the same mask in 97 of 240: it scores finder-like runs
    differently.

  qrencode and zbarimg are fetched without root (apt-get download, dpkg
  -x; their libraries were installed), segno and qrcodegen from PyPI into
  out/xtools (tools/xcheck/fetch.sh). A tool that cannot be found is
  skipped and said so.
- the negative controls (tests/negative_controls.sh): 34 mutants, each
  built from one snapshot of the tree, all killed: 19 by the proofs, 15 by
  the checks. For the QR codec, eleven are refused by the proofs or by
  Lean's termination check (bits written least significant first, digit
  groups up to 1023, alphanumeric pairs up to 2047, a byte read off by
  one, unchecked 21-bit ECI numbers, a parser that recurses without
  consuming, no terminator, format or version readings 4 bits off,
  corrections beyond capacity, a corrected block not re-checked). Twelve
  the laws do not cover are caught by the checks (Berlekamp–Massey's
  length rule, Forney without X, the format XOR constant, mask 4's
  pattern, the zigzag direction, a 9-bit byte count, version 32's
  alignment step, deinterleaving order, the finder triangle's orientation,
  sampling at module corners, a global threshold only, no alignment
  patterns). For the pictures: fit rounding down, fit not shrinking the
  shorter side, thumbnails without the gap, thumbnails hanging below the
  box, the tray copying alpha, the composer skipping the size check, QOI
  decoding 3 bytes a pixel or accepting sides over 2048 (the proofs);
  QOI's difference bias, runs of 63 and a hash without alpha (the checks).
  A mutant that does not compile at all, rather than failing a proof,
  fails the run, and the unmutated copy must pass first.

`mise run android:e2e` is the camera harness on its own emulator (below).

## The Android harness (android/)

A standalone APK built with no Gradle and no libraries beyond the SDK and
NDK: `ScanActivity.java` (Camera2: a preview and an `ImageReader` of
YUV_420_888 frames) and `libleanqr.so`, which is the Qr library compiled
to C by Lean, Lean's runtime cross-built for Android
(android/leanrt/build.sh, copied from lean-chat), and `jni/qr_jni.c`.

The native side does no parsing. For each frame Java passes the Y plane's
direct `ByteBuffer`, width, height and row stride; the C seam copies the
buffer into a Lean `ByteArray` with one `memcpy` and calls
`lean_qr_decode_luma`; Lean does everything else and returns the payload
and a description, which Java shows on screen and logs under the tag
`LeanQR`.

- `mise run android:runtime`: Lean's runtime, Init and libuv for x86_64
  and arm64-v8a, into out/leanrt.
- `mise run android:apk`: out/leanqr.apk.
- `mise run android:e2e` (android/test/e2e.sh): creates the AVD
  `qr-harness-20261027` if missing (an x86_64 API 36 google_apis image,
  back camera = virtual scene), boots it on emulator-5578 with Lean's
  rendering of a fresh invite as the wall poster, installs the APK, grants
  the camera, walks the virtual camera up to the poster over gRPC, and
  passes when logcat shows Lean decoded the invite. It talks only to its
  own serial, after checking the AVD's name. Logcat, a screenshot and the
  poster go to out/e2e.

Result on qr-harness-20261027 (API 36, x86_64, swiftshader, KVM): the
camera delivers 1280×720 YUV frames; the virtual camera ends looking at
the poster obliquely, with the dining table and a chair in front of its
lower corner; Lean decodes the 200-byte invite (version 10, level M)
within a few seconds of the camera arriving, correcting 28 to 58
codewords a frame (of 13 per block, 65 in all) in three runs. Decoding takes 260–450 ms
a 1280×720 frame on the emulator (no downscaling). The log line:

```
I LeanQR  : decoded (v10 M mask 2 fixed 58 mirrored no, 899 ms, frame 38): quiet://join/pfN64A3M7vDMHWBg61f7Qe…
PASS: Lean decoded the invite from the emulator's camera
```

The screenshot (out/e2e/screen.png) shows the poster behind the table and
Lean's text over the preview.

## The composer's image tools (Pic/, android/app/.../Pics.java)

The platform's own pickers, with as little native code as they allow, as
libquiet does it (app/src-tauri/src/source/pick.rs, Picker.kt):

- **Photos**: the system Photo Picker (`MediaStore.ACTION_PICK_IMAGES`,
  images, multi-select up to `getPickImagesMaxLimit()`), no in-app gallery.
- **Camera**: the system camera (`ACTION_IMAGE_CAPTURE`, `EXTRA_OUTPUT`
  into a file in the app's cache, lent through a 20-line `ContentProvider`
  of the app's own, since FileProvider is androidx); the file is deleted
  and its grant revoked once read, and leftovers are cleared at start. The
  QR scanner keeps its own Camera2 preview, which needs live frames.
- **Native side** (Pics.java, jni/pic_jni.c): decode with the platform's
  `ImageDecoder` (it applies EXIF orientation and samples while decoding;
  libquiet's Picker.kt uses it too), at the size Lean's `fit` gives
  (`lean_pic_fit`: the longer side at most 2048), unpremultiplied, and hand
  the RGBA to Lean. It shows the tray Lean draws, as it is.
- **Lean** (Pic/): checks the picture (exactly `w × h` RGBA, and exactly
  `fit` of the original's size), encodes it as QOI for storage (lean-quiet
  stores pictures as QOI), decodes the stored QOI back and refuses it
  unless it is the same pixels, draws its thumbnail from that copy, lays
  out and paints the tray, and describes the picture ("2 · 400×600 (from
  400×600) · QOI 6 KB").

```lean
import Pic
open Pic
encode : Rgba → ByteArray                      -- QOI, 4 channels
decode : ByteArray → Option Rgba               -- untrusted bytes; sides 1..2048
fit    : Nat → Nat → Nat → Nat × Nat           -- w h edge
add    : Composer → (ow oh w h : Nat) → ByteArray → Composer × String
layout : Geom → List (Nat × Nat) → List Slot × Nat
render : Geom → List Rgba → Rgba               -- the tray, opaque RGBA
-- exports for JNI: lean_pic_fit, lean_pic_empty, lean_pic_add, lean_pic_tray, lean_pic_blob, lean_pic_count
```

Laws (Pic/Laws.lean, on the running code, standard axioms only):
`fit_small`, `fit_le`, `fit_pos`, `fit_long`, `fit_round` (the size rule:
kept if it fits, else the longer side exactly the edge and the other the
nearest pixel, never 0); `layout_sizes`, `layout_inside`, `layout_apart`
(every thumbnail is its picture fitted into the box, inside the tray, and
any two at least the gap apart, so none overlap); `render_wellFormed`,
`render_opaque` (every tray pixel has alpha 255); `scale_wellFormed`;
`decode_sized` (whatever bytes QOI's decoder is given, a picture it
returns has sides of 1 to 2048 and exactly their pixels' bytes);
`add_stored` (an accepted picture is exactly `fit` of its original, well
formed, and its stored QOI decodes to exactly its pixels).

`render_opaque` is a UI fix made by proof: the first tray copied each
picture's alpha, so a transparent PNG left a hole showing what was under
the tray. The property was stated as a theorem about `render`; it is false
for that code (a negative control keeps the old line and the proof refuses
it), and `render` now blends a picture over the tray's ground, for which
the proof goes through.

QOI itself is tested, not proven: `decode (encode p) = p` on 129 pictures
covering every op (runs at 62, 63 and 200, differences, luma, index hits,
alpha changes, 2048-pixel rows and columns), Pillow's QOI decoding in Lean
and Lean's in Pillow (Lean's blobs came out the same size as Pillow's for
every picture tried), every truncation and 2,000 mutations of a
blob (none, or a well-formed picture of the header's size). `add_stored`
does not depend on that: the composer checks the round trip before it
keeps a picture.

`mise run android:e2e` covers the tools after the scanner (android/test/
pics.py): three pictures are pushed into the emulator's MediaStore (a
4000×3000 JPEG in quadrants, a 600×400 JPEG whose EXIF says "rotate 90°",
a 300×300 PNG with alpha), picked together in the system Photo Picker, and
a photo is taken with the system camera. Every stored QOI is pulled from
the app and checked with Pillow. On qr-harness-20261027 Lean stored
2048×1536 (quadrants intact), 400×600 (the red block at the top-right:
turned upright), 300×300 (alpha 200 kept exactly, unpremultiplied) and the
camera's 960×1280 photo (EXIF-rotated by the camera app); when the virtual
camera was still at the poster, Lean also decoded the invite from that
stored photo (reported, not required: the emulator can reset the virtual
camera's pose when the system camera opens). Screenshot: out/e2e/pics.png.
The Photo Picker syncs its own copy of the MediaStore, so pictures pushed
a moment ago may not be in it yet: the test closes and reopens it until
they are.

## Limits

- Segment modes: numeric, alphanumeric, byte and ECI (passed through).
  Kanji mode, structured append and FNC1 are refused (`none`); a symbol
  that uses them does not decode. `encode` writes byte mode only (mixed
  segments with `encodeSegs`, chosen by the caller: there is no mode
  optimizer). No Micro QR or rMQR.
- Dark modules on a light ground only: an inverted (light-on-dark) symbol
  is not tried.
- One symbol a frame: the first finder triangle that decodes wins.
- From the stress sweep (tools/distort/stress.py; all four levels, 640×480
  frames): it decodes down to 2.5 pixels a module (not 2.0), Gaussian blur
  σ 2.0 px at 5 px a module (H, the largest symbol at 77 modules, fails
  at 2.0; all fail at 2.5), noise σ 40 (55 for all but H; none at 70), a
  far edge shrunk 40%
  (not 50%), contrast 10%, lighting gradients to 3%, and occlusion as far
  as each level's error correction goes (a square over 16% of the symbol
  at Q and H, not 20%).
- One homography for the whole symbol, refined by every alignment pattern
  found: strong lens distortion on a large version is not modelled.
- Speed: about 40 ms a 640×480 frame on this machine, 260–450 ms a
  1280×720 frame on the x86_64 emulator; the harness decodes the latest
  frame on one thread and drops the rest. Not measured on a phone: the
  harness was run only on its own emulator (the arm64-v8a library is in
  the APK but untested on hardware).
- The harness's preview is not aspect-corrected (the TextureView stretches
  the frame); the decoder sees the camera's own pixels.
- Proven only as stated above: Reed–Solomon correction succeeding within
  capacity, the matrix layout and everything about pixels (floating-point
  geometry included) are tested, not proven. That decoding small changes
  to the format XOR constant would go unnoticed shows the other side of
  BCH correction: the negative control uses a constant 6 bits off.
- Image tools: QOI's round trip is tested, not proven (the composer
  checks it at run time instead); the Photo Picker path is Android 13+
  (or a Photo Picker backport), with no ACTION_OPEN_DOCUMENT fallback; an
  animated image is decoded to its first frame (libquiet refuses those);
  only the emulator was tested.
- The e2e needs python3.13 with grpcio and grpcio-tools for the scene
  camera; the emulator smooths the camera's velocity, so its final pose
  (and how much the table hides) varies a little between runs.
