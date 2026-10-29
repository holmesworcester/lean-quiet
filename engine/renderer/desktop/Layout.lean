/-
Desktop tracks, in logical pixels. libquiet: 45rem = 720, sidebar 220.
Settings overlay the rightmost 375 pixels without shrinking the main
conversation. Below the breakpoint a drawer occupies the whole window.
-/
namespace Desktop

inductive Pane where
  | nav | main | context
  deriving BEq, DecidableEq, Repr, Inhabited

structure Track where
  x : Nat
  w : Nat
  deriving BEq, Repr, Inhabited

structure Layout where
  width : Nat
  nav : Track
  main : Track
  context : Track
  deriving BEq, Repr, Inhabited

def layout (w : Nat) (opened : Bool) : Layout :=
  if 720 ≤ w then
    ⟨w, ⟨0, 220⟩, ⟨220, w - 220⟩, if opened then ⟨w - 375, 375⟩ else ⟨w, 0⟩⟩
  else if opened then ⟨w, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, w⟩⟩
  else ⟨w, ⟨0, 0⟩, ⟨0, w⟩, ⟨w, 0⟩⟩

/-- Device-pixel tracks at a CSS density. Settings deliberately cover main;
nav and main partition the viewport. This is used by the live driver. -/
def zoomLayout (w : Nat) (opened : Bool) (dpi : Nat) : Layout :=
  let px := fun n => (n * dpi + 80) / 160
  if px 720 ≤ w then
    ⟨w, ⟨0, px 220⟩, ⟨px 220, w - px 220⟩,
      if opened then ⟨w - px 375, px 375⟩ else ⟨w, 0⟩⟩
  else if opened then ⟨w, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, w⟩⟩
  else ⟨w, ⟨0, 0⟩, ⟨0, w⟩, ⟨w, 0⟩⟩

def Layout.track (g : Layout) : Pane → Track
  | .nav => g.nav
  | .main => g.main
  | .context => g.context

def Layout.count (g : Layout) : Nat :=
  (if g.nav.w > 0 then 1 else 0) + (if g.main.w > 0 then 1 else 0) +
  (if g.context.w > 0 then 1 else 0)

structure Box where
  x : Nat
  y : Nat
  w : Nat
  h : Nat
  deriving BEq, DecidableEq, Repr, Inhabited

def Box.has (b : Box) (x y : Nat) : Bool :=
  b.x ≤ x && x < b.x + b.w && b.y ≤ y && y < b.y + b.h

/-- The desktop minimum hit target, in logical pixels (not device pixels). -/
def target : Nat := 24

def Fits (g : Layout) (height : Nat) (p : Pane) (b : Box) (minimum : Nat := target) : Prop :=
  (g.track p).x ≤ b.x ∧ b.x + b.w ≤ (g.track p).x + (g.track p).w ∧
  b.y + b.h ≤ height ∧ minimum ≤ b.w ∧ minimum ≤ b.h

instance : Decidable (Fits g h p b minimum) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

structure Control (α : Type) where
  pane : Pane
  box : Box
  action : α
  label : String
  deriving Repr, DecidableEq

/-- Offscreen or undersized controls are neither painted nor clickable.
The root paginates long lists before applying this final clipping guard. -/
def controls (g : Layout) (h : Nat) (xs : List (Control α)) (minimum : Nat := target) : List (Control α) :=
  xs.filter fun c => decide (Fits g h c.pane c.box minimum)

def hit (xs : List (Control α)) (x y : Nat) : Option (Control α) :=
  xs.find? fun c => c.box.has x y

end Desktop
