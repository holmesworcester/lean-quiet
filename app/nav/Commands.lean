import app.nav.Family

/-
Nav's intent: a change of page writes one op, a generation past the
newest, naming the page shown and the pages under it by number. An
honest one is Valid (`go_valid`).
-/

namespace Nav
open Engine Codec

/-- The op placing this window at page `page` over `stack`, at generation `gen`. -/
def place (gen page : Nat) (stack : List Nat) : Op := mkOp [] ⟨gen, page, stack⟩

/-- **An honest place is Valid,** with its fields. -/
theorem place_valid (gen page : Nat) (stack : List Nat) :
    validate (place gen page stack) [] = some ⟨gen, page, stack⟩ := by
  simp [validate, place, mkOp, Codec.decode_encode, Body.kind, check]

end Nav
