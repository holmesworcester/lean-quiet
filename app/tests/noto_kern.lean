/- A real format-0 kern subtable: two signed pairs, plus malformed lengths. -/
import Quiet.Ttf.Read

private def check (b : Bool) (s : String) : IO Unit :=
  unless b do throw (IO.userError s)

def main : IO Unit := do
  let bytes : ByteArray := ⟨#[0,0, 0,1,
    0,0, 0,26, 0,1, 0,2, 0,12, 0,1, 0,0,
    0,1, 0,2, 255,156, 0,2, 0,3, 0,50]⟩
  let some k := Ttf.readKern bytes | throw (IO.userError "kern rejected")
  check (k[(1,2)]? == some (-100) && k[(2,3)]? == some 50) "signed kern pairs"
  let f : Ttf.Face := { (default : Ttf.Face) with units := 1000, kern := k }
  check (Ttf.kerning f 1 2 50 == -5 && Ttf.kerning f 2 3 100 == 5) "scaled kerning"
  check (Ttf.kerning f 1 3 50 == 0) "absent kerning"
  for i in [0:bytes.size] do
    check ((Ttf.readKern (bytes.extract 0 i)).isNone) s!"kern truncation {i}"
  IO.println "kern: 3 pair/scale checks, 30 truncated tables refused"
