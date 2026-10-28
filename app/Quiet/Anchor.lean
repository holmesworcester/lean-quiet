/-
The message under the viewport's bottom edge, captured before a list
refresh. Restoring its distance from that edge keeps arrivals from
moving what is being read. Laws: pinned, restored, and possible.
-/
namespace Anchor

def base {α : Type} [BEq α] (key : α) : List (α × Nat) → Nat → Option Nat
  | [], _ => none
  | (k, h) :: rest, y => if k == key then some y else base key rest (y + h)

def capture {α : Type} : List (α × Nat) → Nat → Nat → Option (α × Nat)
  | [], _, _ => none
  | (k, h) :: rest, y, b =>
    if y ≤ b && b < y + h then some (k, b - y) else capture rest (y + h) b

/-- Keep the old window reachable when new rows enter a bottom-indexed
list. Pinned readers only need the newest window. Tested with a burst
larger than the original fetch limit in QTests.Ux. -/
def grow (b limit oldTotal newTotal : Nat) : Nat :=
  if b ≤ 4 then limit else limit + (newTotal - oldTotal)

def restore {α : Type} [BEq α] (b : Nat) (saved : Option (α × Nat))
    (rows : List (α × Nat)) (pad : Nat) : Nat :=
  if b ≤ 4 then b else
    ((saved.bind fun (k, off) => (base k rows pad).map (· + off)).getD b)

theorem pinned {α : Type} [BEq α] (b : Nat) (saved : Option (α × Nat))
    (rows : List (α × Nat)) (pad : Nat) (h : b ≤ 4) :
    restore b saved rows pad = b := by simp [restore, h]

theorem restored {α : Type} [BEq α] (b off y pad : Nat) (key : α)
    (rows : List (α × Nat)) (hb : 4 < b) (h : base key rows pad = some y) :
    restore b (some (key, off)) rows pad = y + off := by
  simp [restore, Nat.not_le.mpr hb, h]

/-- A real insertion below the anchor: its screen position stays fixed. -/
theorem possible :
    capture [(7, 100)] 16 40 = some (7, 24) ∧
    base 7 [(8, 60), (7, 100)] 16 = some 76 ∧
    restore 40 (capture [(7, 100)] 16 40) [(8, 60), (7, 100)] 16 = 100 := by decide

end Anchor
