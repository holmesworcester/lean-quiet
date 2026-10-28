/-
Binary PGM (P5) files: how the tests and tools hand frames around.
-/
import Qr

namespace Qr.Pgm

def write (path : System.FilePath) (img : Image) : IO Unit := do
  let mut px := ByteArray.emptyWithCapacity (img.w * img.h)
  for y in [0:img.h] do
    for x in [0:img.w] do
      px := px.push (bget img.px (y * img.stride + x))
  IO.FS.writeBinFile path ((s!"P5\n{img.w} {img.h}\n255\n").toUTF8 ++ px)

/-- The header's next number from position `i` (skipping blanks and
comments), and the position after it. -/
def num (b : ByteArray) (i : Nat) : Option (Nat × Nat) := Id.run do
  let mut i := i
  let mut inComment := false
  for _ in [0:b.size] do
    match b[i]? with
    | none => return none
    | some c =>
      if inComment then
        if c == 10 then inComment := false
        i := i + 1
      else if c == 35 then inComment := true; i := i + 1
      else if c == 32 || c == 9 || c == 10 || c == 13 then i := i + 1
      else break
  let mut v := 0
  let mut any := false
  for _ in [0:b.size] do
    match b[i]? with
    | some c =>
      if 48 ≤ c && c ≤ 57 then
        v := v * 10 + (c - 48).toNat
        any := true
        i := i + 1
      else break
    | none => break
  return if any then some (v, i) else none

def parse (b : ByteArray) : Option Image := do
  if b[0]? != some 80 || b[1]? != some 53 then none
  let (w, i) ← num b 2
  let (h, i) ← num b i
  let (mx, i) ← num b i
  if mx > 255 then none
  let i := i + 1
  if b.size < i + w * h then none
  pure { w, h, stride := w, px := b.extract i (i + w * h) }

def read (path : System.FilePath) : IO Image := do
  match parse (← IO.FS.readBinFile path) with
  | some img => pure img
  | none => throw (IO.userError s!"{path}: not a binary PGM")

end Qr.Pgm
