/-
Images: QOI bytes to rows at the size they are drawn (box-filtered,
composited over the background), and an encoder for the chaos
generator's pictures.
-/
import Quiet.Qoi
import Quiet.Paint

namespace Image
open Paint

/-- Source pixels: width, height, r << 24 | g << 16 | b << 8 | a. -/
structure Src where
  w : Nat
  h : Nat
  px : Array UInt32
  deriving Inhabited

def Src.ofQoi (q : Qoi.Qoi) : Src := ⟨q.w.toNat, q.h.toNat, q.px⟩

def decode (bytes : ByteArray) : Option Src := (Qoi.decode bytes).map Src.ofQoi

/-- The rectangle [x0, x0 + cw) x [y0, y0 + ch) of s, box-filtered down
(or repeated up) to tw x th, laid over bg, as rows. -/
def scaleCrop (s : Src) (x0 y0 cw ch tw th : Nat) (bg : Color) : Bitmap := Id.run do
  let tw := max tw 1
  let th := max th 1
  let mut rows := Array.mkEmpty th
  for ty in [0:th] do
    let sy0 := y0 + ty * ch / th
    let sy1 := max (sy0 + 1) (y0 + (ty + 1) * ch / th)
    let mut row := ByteArray.emptyWithCapacity (4 * tw)
    for tx in [0:tw] do
      let sx0 := x0 + tx * cw / tw
      let sx1 := max (sx0 + 1) (x0 + (tx + 1) * cw / tw)
      -- at most a 4 x 4 sample of the source box: the cost stays per
      -- target pixel, whatever the source's size
      let stepY := max 1 ((sy1 - sy0) / 4)
      let stepX := max 1 ((sx1 - sx0) / 4)
      let mut r := 0
      let mut g := 0
      let mut b := 0
      let mut n := 0
      let mut y := sy0
      while y < sy1 && y < s.h do
        let mut x := sx0
        while x < sx1 && x < s.w do
          let p := s.px[y * s.w + x]!
          let a := (p &&& 255).toNat
          let na := 255 - a
          r := r + (((p >>> 24) &&& 255).toNat * a + ((bg >>> 16) &&& 255).toNat * na) / 255
          g := g + (((p >>> 16) &&& 255).toNat * a + ((bg >>> 8) &&& 255).toNat * na) / 255
          b := b + (((p >>> 8) &&& 255).toNat * a + (bg &&& 255).toNat * na) / 255
          n := n + 1
          x := x + stepX
        y := y + stepY
      let k := max n 1
      row := row.push (r / k).toUInt8 |>.push (g / k).toUInt8 |>.push (b / k).toUInt8 |>.push 255
    rows := rows.push row
  return { w := tw, rows := rows }

/-- The whole image fitted into at most mw x mh, its aspect kept. -/
def fit (s : Src) (mw mh : Nat) : Nat × Nat :=
  let w := max s.w 1
  let h := max s.h 1
  if w * mh ≤ h * mw then (max 1 (w * mh / h), mh) |>.map (min mw ·) id
  else (mw, max 1 (h * mw / w))

def scaled (s : Src) (tw th : Nat) (bg : Color) : Bitmap := scaleCrop s 0 0 s.w s.h tw th bg

/-- A centred square crop, at d x d: an avatar. -/
def square (s : Src) (d : Nat) (bg : Color) : Bitmap :=
  let m := min s.w s.h
  scaleCrop s ((s.w - m) / 2) ((s.h - m) / 2) m m d d bg

/-! ## Encoding (QOI) -/

def encode (w h : Nat) (px : Array UInt32) : ByteArray := Id.run do
  let be32 (n : Nat) : List UInt8 := [(n >>> 24).toUInt8, (n >>> 16).toUInt8, (n >>> 8).toUInt8, n.toUInt8]
  let mut out := ByteArray.mk (("qoif".toUTF8.toList ++ be32 w ++ be32 h ++ [4, 0]).toArray)
  let mut ix := Array.replicate 64 (0 : UInt32)
  let mut prev : UInt32 := 255
  let mut run := 0
  for i in [0:w * h] do
    let p := px[i]!
    if p == prev then
      run := run + 1
      if run == 62 || i + 1 == w * h then out := out.push (0xC0 + (run - 1).toUInt8); run := 0
      continue
    if run > 0 then out := out.push (0xC0 + (run - 1).toUInt8); run := 0
    let hsh := (Qoi.Px.hash p).toNat
    if ix[hsh]! == p then
      out := out.push hsh.toUInt8
    else
      ix := ix.set! hsh p
      if Qoi.Px.a p == Qoi.Px.a prev then
        let dr := (Qoi.Px.r p).toNat + 256 - (Qoi.Px.r prev).toNat
        let dg := (Qoi.Px.g p).toNat + 256 - (Qoi.Px.g prev).toNat
        let db := (Qoi.Px.b p).toNat + 256 - (Qoi.Px.b prev).toNat
        -- signed differences in -128..127
        let sr := (dr + 128) % 256
        let sg := (dg + 128) % 256
        let sb := (db + 128) % 256
        let rg := (sr + 256 - sg + 128) % 256
        let bg := (sb + 256 - sg + 128) % 256
        if 126 ≤ sr && sr ≤ 129 && 126 ≤ sg && sg ≤ 129 && 126 ≤ sb && sb ≤ 129 then
          out := out.push (0x40 + (((sr - 126) <<< 4) + ((sg - 126) <<< 2) + (sb - 126))).toUInt8
        else if 96 ≤ sg && sg ≤ 159 && 120 ≤ rg && rg ≤ 135 && 120 ≤ bg && bg ≤ 135 then
          out := out.push (0x80 + (sg - 96)).toUInt8 |>.push (((rg - 120) <<< 4) + (bg - 120)).toUInt8
        else
          out := out.push 254 |>.push (Qoi.Px.r p).toUInt8 |>.push (Qoi.Px.g p).toUInt8 |>.push (Qoi.Px.b p).toUInt8
      else
        out := out.push 255 |>.push (Qoi.Px.r p).toUInt8 |>.push (Qoi.Px.g p).toUInt8
          |>.push (Qoi.Px.b p).toUInt8 |>.push (Qoi.Px.a p).toUInt8
    prev := p
  if run > 0 then out := out.push (0xC0 + (run - 1).toUInt8)
  return out ++ ByteArray.mk #[0, 0, 0, 0, 0, 0, 0, 1]

end Image
