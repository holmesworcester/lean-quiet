/-
A real invite link and its QR code, for the camera e2e's poster: a fresh
community's root and an invitation from its founder (Community.issue), the
link's text in <out>/invite and the code (Link.qr, as Add members draws it)
as a PGM in <out>/poster.pgm.

    invite_link <out>
-/
import Quiet

open Community

def main (args : List String) : IO UInt32 := do
  let out := args[0]?.getD "out/scan"
  IO.FS.createDirAll out
  let seed ← IO.getRandomBytes 32
  let bearer ← IO.getRandomBytes 32
  let d := Device.ofSeed seed
  let r := root d
  let (_, i) := issue r.id r.id d bearer ["10.0.2.2:47100".toUTF8]
  IO.FS.writeFile (out ++ "/invite") i.text
  let some b := Link.qr i.text 1000 | IO.eprintln "no QR for the link"; return 1
  let mut pgm := s!"P5\n{b.w} {b.h}\n255\n".toUTF8
  for row in b.rows do
    for x in [0:b.w] do pgm := pgm.push row[4 * x]!
  IO.FS.writeBinFile (out ++ "/poster.pgm") pgm
  IO.println s!"{i.text.length} chars, {b.w} px"
  return 0
