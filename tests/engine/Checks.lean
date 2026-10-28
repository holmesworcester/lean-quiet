/- Counted runtime assertions shared by the engine suites. -/
namespace Tests

structure Checks where
  failed : IO.Ref Nat
  passed : IO.Ref Nat

def Checks.new : IO Checks := do return ⟨← IO.mkRef 0, ← IO.mkRef 0⟩

def Checks.ok (c : Checks) (name : String) (b : Bool) : IO Unit := do
  if b then c.passed.modify (· + 1)
  else
    c.failed.modify (· + 1)
    IO.eprintln s!"FAIL: {name}"

def Checks.finish (c : Checks) (suite : String) : IO UInt32 := do
  let f ← c.failed.get
  let p ← c.passed.get
  IO.println s!"{suite}: {p} passed, {f} failed"
  return if f == 0 then 0 else 1

end Tests
