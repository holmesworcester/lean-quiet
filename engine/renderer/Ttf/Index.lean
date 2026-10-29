/-
Compact build-time cmap/hmtx records used by layout before a face is
parsed. Checked byte reads, count limits and glyph bounds reject bad
indices. The reference suite compares every record with its TrueType.
-/
import engine.renderer.Ttf.Bytes

namespace Ttf.Index

structure Metrics where
  bytes : Nat
  units : Nat
  glyphs : Nat
  chars : Array (Nat × Nat × Nat)
  deriving Inhabited

def read (b : ByteArray) : Option (Array Metrics) := do
  if (← u32 b 0) != 0x514E5431 then failure
  let count ← u16 b 4
  if count == 0 || count > 64 then failure
  let mut pos := 6
  let mut out := #[]
  for _ in [0:count] do
    let bytes ← u32 b pos
    let units ← u16 b (pos+4)
    let glyphs ← u16 b (pos+6)
    let n ← u32 b (pos+8)
    if bytes > 32*1024*1024 || units < 16 || units > 16384 || glyphs == 0 || n > 0x110000 then failure
    pos := pos+12
    let _ ← slice b pos (8*n)
    let mut chars := #[]
    let mut prev := 0
    for i in [0:n] do
      let c ← u32 b pos
      let g ← u16 b (pos+4)
      let a ← u16 b (pos+6)
      if c > 0x10FFFF || (i > 0 && c ≤ prev) || g ≥ glyphs then failure
      chars := chars.push (c,g,a)
      prev := c
      pos := pos+8
    out := out.push ⟨bytes,units,glyphs,chars⟩
  if pos != b.size then failure
  return out

end Ttf.Index
