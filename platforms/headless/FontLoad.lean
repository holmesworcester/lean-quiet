/- Stage timings for the eager loader, used to locate startup costs. -/
import engine.renderer.Noto

def main : IO Unit := do
  let mut fonts := #[]
  for name in (Noto.names.map (· ++ "-Regular")) ++ Cjk.names do
    let t0 ← IO.monoNanosNow
    let bytes ← IO.FS.readBinFile s!"assets/{name}.ttf"
    let t1 ← IO.monoNanosNow
    let some f := Ttf.readHeader bytes | throw (IO.userError "header")
    let t2 ← IO.monoNanosNow
    for g in [0:f.advances.size] do
      unless (Ttf.outline f g).isSome do throw (IO.userError "outline")
    let t3 ← IO.monoNanosNow
    IO.println s!"{name}: read {(t1-t0)/1000} us, header/cmap {(t2-t1)/1000} us, all outlines {(t3-t2)/1000} us"
    if name.endsWith "Common" then fonts := fonts.push f
  let t0 ← IO.monoNanosNow
  let mut codes : Std.HashSet Nat := {}
  for f in fonts do
    for e in f.cmap do
      for c in [e.lo:e.hi+1] do codes := codes.insert c
  let t1 ← IO.monoNanosNow
  let mut selected : Std.HashMap Nat (Nat × Nat) := {}
  for c in codes.toList do
    if let some p := Cjk.choose fonts c then selected := selected.insert c p
  let t2 ← IO.monoNanosNow
  IO.println s!"CJK tables: union {(t1-t0)/1000} us, selection {(t2-t1)/1000} us, {selected.size} entries"
