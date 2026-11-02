/-
What a list frame shows at each content position: the code the app's
frame runs. Its laws are in engine/renderer/Cover.lean.
-/
namespace Cover

inductive Px where
  /-- Row i's bitmap line li (top down). -/
  | line (i li : Nat)
  /-- Row i, not painted yet (or painted at another height). -/
  | hold (i : Nat)
  /-- A message outside the loaded window: below it (newer) or above it
  (older). -/
  | unloaded
  /-- Padding below the first row, or above the last with nothing older. -/
  | blank
  deriving DecidableEq, Repr

/-- The row covering p, from row i whose bottom is y up; each row is its
height and its painted bitmap's height, if painted. -/
def find (p : Nat) : Nat → Nat → List (Nat × Option Nat) → Option Px
  | _, _, [] => none
  | i, y, (h, pt) :: t =>
    if p < y + h then
      let li := y + h - 1 - p
      some (match pt with
        | some bh => if li < bh then .line i li else .hold i
        | none => .hold i)
    else find p (i + 1) (y + h) t

/-- What content position p shows: newer messages from `pad` to
`bottom`, the rows from `bottom` up, older messages above them if
`more`. -/
def seen (pad bottom : Nat) (more : Bool) (rows : List (Nat × Option Nat)) (p : Nat) : Px :=
  if p < pad then .blank
  else if p < bottom then .unloaded
  else match find p 0 bottom rows with
    | some x => x
    | none => if more then .unloaded else .blank

end Cover
