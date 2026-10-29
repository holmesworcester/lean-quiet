/- Pointer input is supplied by the native shell. Touch supplies `none`.
A component receives a pointer only through the topmost visible surface, in
its own coordinates. Hover is paint input, never a subscription or layout input. -/
namespace Hover

abbrev Point := Nat × Nat
abbrev Context := Option Point

structure Box where
  x : Nat
  y : Nat
  w : Nat
  h : Nat
  deriving BEq, DecidableEq, Repr, Inhabited

def Box.has (b : Box) (p : Point) : Bool :=
  b.x ≤ p.1 && p.1 < b.x + b.w && b.y ≤ p.2 && p.2 < b.y + b.h

def active (p : Context) (b : Box) (enabled := true) : Bool :=
  enabled && p.any b.has

/-- Topmost surfaces come first, including surfaces with no enabled controls:
a disabled control or empty modal space must not expose a covered surface. -/
def front (p : Context) (surfaces : List (α × Box)) : Option (α × Box) :=
  surfaces.find? fun (_, box) => active p box

/-- Coordinates cross a component boundary only while inside its viewport. -/
def within (p : Context) (b : Box) : Context :=
  p.bind fun q => if b.has q then some (q.1 - b.x, q.2 - b.y) else none

def move (p : Context) (x y : Nat) : Context := p.map fun q => (q.1 + x, q.2 + y)

inductive Event where
  | motion (x y : Nat) | leave | blur | touch
  deriving BEq, Repr

def update (_ : Context) : Event → Context
  | .motion x y => some (x, y)
  | .leave | .blur | .touch => none

/-- An inactive component paints its resting value, even with a pointer. -/
def choose (p : Context) (box : Box) (enabled : Bool) (rest hovered : α) : α :=
  if active p box enabled then hovered else rest

end Hover

namespace Hover
/-- A surface's children receive no pointer when another surface covers it. -/
def routed [BEq α] (p : Context) (surfaces : List (α × Box)) (key : α) : Context :=
  match front p surfaces with
  | some (k, _) => if k == key then p else none
  | none => none
end Hover

namespace Hover
private def side (p a b : Point) : Int :=
  (Int.ofNat b.1 - a.1) * (Int.ofNat p.2 - a.2) -
    (Int.ofNat b.2 - a.2) * (Int.ofNat p.1 - a.1)

private def triangle (p a b c : Point) : Bool :=
  let ds := [side p a b, side p b c, side p c a]
  !(ds.any (· < 0) && ds.any (· > 0)) &&
    min a.1 (min b.1 c.1) ≤ p.1 && p.1 ≤ max a.1 (max b.1 c.1) &&
    min a.2 (min b.2 c.2) ≤ p.2 && p.2 ≤ max a.2 (max b.2 c.2)

/-- The convex hull of the last point inside a message and its toolbar.
Retaining ownership here lets a diagonal pointer cross the previous row. -/
def toward (origin p : Point) (b : Box) : Bool :=
  let a := (b.x, b.y)
  let c := (b.x+b.w, b.y)
  let d := (b.x+b.w, b.y+b.h)
  let e := (b.x, b.y+b.h)
  b.has p || triangle p origin a c || triangle p origin c d || triangle p origin d e || triangle p origin e a

def graceLive (started now : Nat) : Bool := now < started + 400
end Hover
