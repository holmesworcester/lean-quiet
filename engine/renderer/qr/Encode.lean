/-
The encoder: segments (or bytes, in byte mode) to a QR symbol, and a
symbol to a grayscale bitmap.

The smallest version from `minVersion` that holds the data at the chosen
level is used. The data codewords (`dataStream`) are split into blocks,
each gets its Reed–Solomon codewords, and the blocks are interleaved;
the bits go into the matrix in the zigzag order, and the mask with the
lowest penalty score is applied (or the one asked for).
-/
import engine.renderer.qr.Segment
import engine.renderer.qr.RS
import engine.renderer.qr.Matrix

namespace Qr

/-- A QR symbol: its modules (row-major, 1 dark) and how it was made. -/
structure Symbol where
  version : Nat
  ecc : Ecc
  mask : Nat
  grid : Grid

def Symbol.size (s : Symbol) : Nat := s.grid.n

/-- A grayscale bitmap, row-major, `stride` bytes a row (0 black, 255 white). -/
structure Image where
  w : Nat
  h : Nat
  stride : Nat
  px : ByteArray

/-- Data length of block `b` of a layout. -/
def Layout.dataLen (l : Layout) (b : Nat) : Nat := l.short + (if b < l.nShort then 0 else 1)

/-- Data codewords split into blocks, each followed by its error
correction, interleaved: data codewords column by column (short blocks
have no last column), then error-correction codewords. -/
def interleave (v : Nat) (e : Ecc) (data : Array UInt8) : Array UInt8 := Id.run do
  let l := layout v e
  let mut blocks : Array (Array UInt8) := #[]
  let mut eccs : Array (Array UInt8) := #[]
  let mut at_ := 0
  for b in [0:l.nb] do
    let len := l.dataLen b
    let d := data.extract at_ (at_ + len)
    blocks := blocks.push d
    eccs := eccs.push (RS.encode l.ecLen d)
    at_ := at_ + len
  let mut out : Array UInt8 := Array.mkEmpty (rawCodewords v)
  for i in [0:l.short + 1] do
    for b in [0:l.nb] do
      if i < l.dataLen b then out := out.push ((blocks[b]?.getD #[])[i]?.getD 0)
  for i in [0:l.ecLen] do
    for b in [0:l.nb] do
      out := out.push ((eccs[b]?.getD #[])[i]?.getD 0)
  return out

/-- The symbol with codewords `cw` (all of them, interleaved) and mask `k`. -/
def drawSymbol (v : Nat) (e : Ecc) (cw : Array UInt8) (k : Nat) : Grid := Id.run do
  let c := functionCanvas v
  let n := sizeOf v
  let pos := dataPositions n c.fn
  let mut g := c.mods
  for i in [0:pos.size] do
    let p := pos[i]?.getD 0
    let x := p % n
    let y := p / n
    let bit := (cw[i / 8]?.getD 0).toNat.testBit (7 - i % 8)
    g := g.set x y (bit != maskBit k x y)
  let c := ({ mods := g, fn := c.fn } : Canvas).formatBits (formatBits e k)
  return c.mods

def Seg.valid (v : Nat) : Seg → Bool
  | .numeric ds => decide (ds.length < 2 ^ countWidth v 0) && ds.all isDigit
  | .alnum cs => decide (cs.length < 2 ^ countWidth v 1) && cs.all (fun c => (alnumIdx c).isSome)
  | .bytes bs => decide (bs.length < 2 ^ countWidth v 2)
  | .eci n => decide (n < 1000000)

/-- Segments as a symbol at level `e`: the smallest version from
`minVersion` (to 40) that holds them, with the mask of lowest penalty
unless `mask` names one (0 to 7). -/
def encodeSegs (ss : List Seg) (e : Ecc := .M) (minVersion : Nat := 1)
    (mask : Option Nat := none) : Option Symbol :=
  let pick := (List.range' (max minVersion 1) (41 - max minVersion 1)).findSome? fun v =>
    if ss.all (Seg.valid v) then (dataStream v (dataCodewords v e) ss).map (v, ·) else none
  pick.map fun (v, data) =>
    let cw := interleave v e data.toArray
    let k := match mask with
      | some k => k % 8
      | none =>
        let scores := (List.range 8).map fun k => (penalty (drawSymbol v e cw k), k)
        (scores.foldl (fun (b : Nat × Nat) s => if s.1 < b.1 then s else b) (scores.headD (0, 0))).2
    { version := v, ecc := e, mask := k, grid := drawSymbol v e cw k }

/-- Bytes as a symbol, in byte mode. -/
def encode (data : ByteArray) (e : Ecc := .M) (minVersion : Nat := 1)
    (mask : Option Nat := none) : Option Symbol :=
  encodeSegs [.bytes data.toList] e minVersion mask

/-- The symbol as a bitmap: `scale` pixels a module and a quiet zone of
`quiet` modules (4 by the standard), black on white. -/
def render (s : Symbol) (scale : Nat := 4) (quiet : Nat := 4) : Image := Id.run do
  let n := s.size
  let side := (n + 2 * quiet) * scale
  let mut px := ByteArray.mk (Array.replicate (side * side) 255)
  for y in [0:n] do
    for x in [0:n] do
      if s.grid.get x y then
        for dy in [0:scale] do
          for dx in [0:scale] do
            px := bset px (((y + quiet) * scale + dy) * side + (x + quiet) * scale + dx) 0
  return { w := side, h := side, stride := side, px }

end Qr
