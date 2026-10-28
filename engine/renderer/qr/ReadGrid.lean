/-
Reading a module matrix: format information, the codewords under the
mask, the blocks (deinterleaved), Reed–Solomon correction, and the
segments. The same placement functions as the encoder's say where each
bit is.
-/
import Qr.Encode
import Qr.SegLaws

namespace Qr

/-- What a decoded symbol says, and how it was read. -/
structure Decoded where
  version : Nat
  ecc : Ecc
  mask : Nat
  segs : List Seg
  /-- codewords Reed–Solomon corrected -/
  corrected : Nat
  /-- read from the transposed matrix (a mirror image) -/
  mirrored : Bool := false

def Decoded.payload (d : Decoded) : ByteArray := ⟨(payloadOf d.segs).toArray⟩

/-- The two format readings: around the top-left finder, and split
between the other two. -/
def readFormat (g : Grid) : Nat × Nat := Id.run do
  let mut a := 0
  let mut b := 0
  for i in [0:15] do
    let (x, y) := formatPos1 i
    if g.get x y then a := a + 2 ^ i
    let (x, y) := formatPos2 g.n i
    if g.get x y then b := b + 2 ^ i
  return (a, b)

/-- The version information, if the symbol is large enough to carry it and
either copy decodes. -/
def readVersion (g : Grid) : Option Nat := Id.run do
  let mut a := 0
  let mut b := 0
  for i in [0:18] do
    let (x, y) := versionPos g.n i
    if g.get x y then a := a + 2 ^ i
    if g.get y x then b := b + 2 ^ i
  return (decodeVersion a).orElse fun _ => decodeVersion b

/-- All codewords under mask `k`, in placement order. -/
def readCodewords (g : Grid) (v k : Nat) : Array UInt8 := Id.run do
  let n := g.n
  let pos := dataPositions n (functionCanvas v).fn
  let mut out : Array UInt8 := Array.mkEmpty (rawCodewords v)
  let mut acc := 0
  for i in [0:rawCodewords v * 8] do
    let p := pos[i]?.getD 0
    let x := p % n
    let y := p / n
    let bit := g.get x y != maskBit k x y
    acc := acc * 2 + (if bit then 1 else 0)
    if i % 8 == 7 then
      out := out.push acc.toUInt8
      acc := 0
  return out

/-- The blocks (data then error correction) of interleaved codewords. -/
def deinterleave (v : Nat) (e : Ecc) (raw : Array UInt8) : Array (Array UInt8) := Id.run do
  let l := layout v e
  let mut blocks : Array (Array UInt8) := Array.replicate l.nb #[]
  let mut at_ := 0
  for i in [0:l.short + 1] do
    for b in [0:l.nb] do
      if i < l.dataLen b then
        blocks := blocks.modify b (·.push (raw[at_]?.getD 0))
        at_ := at_ + 1
  for _ in [0:l.ecLen] do
    for b in [0:l.nb] do
      blocks := blocks.modify b (·.push (raw[at_]?.getD 0))
      at_ := at_ + 1
  return blocks

/-- The data codewords of the blocks, each corrected, and how many
codewords were changed; `none` if a block has more errors than its code
corrects. -/
def correctBlocks (v : Nat) (e : Ecc) (blocks : Array (Array UInt8)) :
    Option (List UInt8 × Nat) := Id.run do
  let l := layout v e
  let mut data : Array UInt8 := #[]
  let mut fixed := 0
  for b in [0:l.nb] do
    let blk := blocks[b]?.getD #[]
    match RS.correct l.ecLen blk with
    | none => return none
    | some c =>
      fixed := fixed + RS.dist blk c
      data := data ++ c.extract 0 (l.dataLen b)
  return some (data.toList, fixed)

/-- The symbol in matrix `g` with format (level, mask) `fmt`. -/
def readWith (g : Grid) (v : Nat) (fmt : Ecc × Nat) : Option Decoded := do
  let (e, k) := fmt
  let raw := readCodewords g v k
  let (data, fixed) ← correctBlocks v e (deinterleave v e raw)
  let segs ← parse v (bytesBits data)
  pure { version := v, ecc := e, mask := k, segs, corrected := fixed }

/-- Decodes a module matrix as it stands (not mirrored). The version is
the matrix's size; format information is taken from either copy. -/
def decodeGrid (g : Grid) : Option Decoded :=
  if g.n < 21 || g.n > 177 || g.n % 4 != 1 then none
  else
    let v := (g.n - 17) / 4
    let (a, b) := readFormat g
    let fmts := [decodeFormat a, decodeFormat b].filterMap id
    fmts.findSome? (readWith g v)

/-- Decodes a module matrix, or its mirror image. -/
def decodeGridAny (g : Grid) : Option Decoded :=
  (decodeGrid g).orElse fun _ => (decodeGrid g.transpose).map ({ · with mirrored := true })

end Qr
