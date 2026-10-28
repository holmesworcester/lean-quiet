/-
Declared occlusion: the five layers, and the table the overlay placement
code reads. A rectangle is a whole element, not an individual paint stroke.
The table allows decoration only inside a partly visible host, modal
surfaces only over inert content, and transient toasts only outside the
focused input. Safety against the keyboard and bars is checked separately.
-/
import Quiet.Safe

namespace Occlusion
open Safe

inductive Layer where
  | page | chrome | marks | surface | toast
  deriving BEq, DecidableEq, Repr, Inhabited

def Layer.z : Layer → Nat
  | .page => 0 | .chrome => 1 | .marks => 2 | .surface => 3 | .toast => 4

/-- Every element has exactly one layer. The compositor reads this field. -/
structure Element where
  layer : Layer
  rect : Rect
  deriving BEq, DecidableEq, Repr, Inhabited

/-- The table, deliberately a closed definition. New covering needs a row
here, not an exception supplied by the caller. -/
def MayCover (upper lower : Element) (inert : Bool) : Prop :=
  match upper.layer with
  | .page | .chrome => False
  | .marks => lower.layer.z < Layer.marks.z ∧ upper.rect.Inside lower.rect ∧
      upper.rect.w * upper.rect.h < lower.rect.w * lower.rect.h
  | .surface => lower.layer.z < Layer.surface.z ∧ inert = true
  | .toast => lower.layer.z < Layer.toast.z

instance (a b : Element) (i : Bool) : Decidable (MayCover a b i) := by
  unfold MayCover; cases a.layer <;> infer_instance

/-- Placement enforces the table, containment and exclusion of protected
input. A non-fitting overlay is deferred, never cut across its glyphs. -/
def place (i : Input) (upper lower : Element) (inert : Bool) (focused : Rect) : Option Element :=
  if upper.rect.Inside (content i) ∧ upper.rect.Disjoint focused ∧ MayCover upper lower inert
    then some upper else none

theorem placed_table (i : Input) (a b out : Element) (inert : Bool) (focused : Rect)
    (h : place i a b inert focused = some out) : MayCover out b inert := by
  unfold place at h
  split at h
  next hp => cases h; exact hp.2.2
  next => contradiction

theorem placed_safe (i : Input) (a b out : Element) (inert : Bool) (focused : Rect)
    (h : place i a b inert focused = some out) (e : Edge) :
    out.rect.Disjoint (reserved i e) ∧ out.rect.Disjoint focused := by
  unfold place at h
  split at h
  next hp => cases h; exact ⟨inside_disjoint i a.rect hp.1 e, hp.2.1⟩
  next => contradiction

/-- A Surface activates only its own controls; Marks and Toasts are not
modal. This is the gate used before dispatching underlying taps. -/
def active (modal : Bool) (layer : Layer) : Bool := !modal || decide (layer = .surface)

theorem modal_inert (layer : Layer) (h : layer ≠ .surface) : active true layer = false := by
  simp [active, h]

end Occlusion
