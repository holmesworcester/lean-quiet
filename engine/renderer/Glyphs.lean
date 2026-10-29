/- Pinned libquiet glyphs as coverage, independent of fonts and colours.
The build rasterizes source SVGs at each integer device size. Runtime
lookup and compositing are bounded by the requested glyph's square. -/
import Std

namespace Glyphs

structure Set where
  bytes : ByteArray := .empty
  entries : Std.HashMap (String × Nat) Nat := {}
  deriving Inhabited

def parse (bytes : ByteArray) : Option Set := do
  if bytes.size < 8 || bytes.extract 0 4 != "QICO".toUTF8 then none else do
    let count := bytes[4]!.toNat + bytes[5]!.toNat * 256 + bytes[6]!.toNat * 65536 + bytes[7]!.toNat * 16777216
    if count > 10000 then none else do
      let mut pos := 8
      let mut entries : Std.HashMap (String × Nat) Nat := {}
      for _ in [0:count] do
        let len := (← bytes[pos]?).toNat
        if len == 0 || len > 64 || pos + 2 + len > bytes.size then return ← none
        let name ← String.fromUTF8? (bytes.extract (pos + 1) (pos + 1 + len))
        let size := bytes[pos + 1 + len]!.toNat
        if size < 8 || size > 96 then return ← none
        pos := pos + len + 2
        if pos + size * size > bytes.size || entries.contains (name, size) then return ← none
        entries := entries.insert (name, size) pos
        pos := pos + size * size
      if pos != bytes.size then none else some ⟨bytes, entries⟩

def Set.coverage (s : Set) (name : String) (size : Nat) : Option ByteArray := do
  let pos ← s.entries[(name, size)]?
  return s.bytes.extract pos (pos + size * size)

def load : IO Set := do
  let some glyphs := parse (← IO.FS.readBinFile "assets/ui-glyphs.bin")
    | throw (IO.userError "invalid glyph atlas")
  return glyphs

end Glyphs
