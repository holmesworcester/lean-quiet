/-
What the sim-e2e needs from Lean, so the UI test computes no layout of its
own, for a screen W pixels wide at a density. Printed one per line:

    field X Y W H         the Paste page's field (Pages.paste, page rows)
    continue X Y W H      its Continue button
    composer H TEXTROWS   the empty composer's height, and its text rows
                          (Composer.layout: a tap above TEXTROWS opens the
                          keyboard)
    link quiet://join/…   a valid invite link (Community.Invite.text)

    lake env lean --run ios/test/Targets.lean W DPI
-/
import ops.app.Pages
import ops.app.Composer
import ops.community.Community

def main (args : List String) : IO Unit := do
  let W := (args[0]? >>= String.toNat?).getD 1170
  let dpi := (args[1]? >>= String.toNat?).getD 480
  let f ← Font.load
  let dm : Row.Dim := ⟨dpi, f.cell, .light⟩
  let pg := Pages.paste f dm W 2000 "" true none
  for (b, a) in pg.taps do
    let name := match a with
      | .field => "field" | .continue_ => "continue" | _ => "other"
    IO.println s!"{name} {b.x} {b.y} {b.w} {b.h}"
  let l := Composer.layout f dm W "" 0
  IO.println s!"composer {l.h} {l.chipsY}"
  let id (n : UInt8) := ByteArray.mk (Array.replicate 32 n)
  let i : Community.Invite := ⟨id 1, id 2, id 3, [], id 4⟩
  IO.println s!"link {i.text}"
