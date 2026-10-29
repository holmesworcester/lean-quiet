/-
Safe rectangles, in physical pixels. The shell reports the window, bars,
cutout and keyboard; `content` unions their insets before layout. Oversized
insets leave an empty rectangle. `reserved` tiles its complement with four
Chrome fills. The laws relate containment to these actual reserved boxes.
-/
namespace Safe

structure Insets where
  left : Nat := 0
  top : Nat := 0
  right : Nat := 0
  bottom : Nat := 0
  deriving BEq, DecidableEq, Repr, Inhabited

def Insets.union (a b : Insets) : Insets :=
  ⟨max a.left b.left, max a.top b.top, max a.right b.right, max a.bottom b.bottom⟩

structure Input where
  w : Nat
  h : Nat
  bars : Insets := {}
  cutout : Insets := {}
  ime : Insets := {}
  deriving BEq, DecidableEq, Repr, Inhabited

def Input.insets (i : Input) : Insets := (i.bars.union i.cutout).union i.ime

structure Rect where
  x : Nat
  y : Nat
  w : Nat
  h : Nat
  deriving BEq, DecidableEq, Repr, Inhabited

def Rect.right (r : Rect) := r.x + r.w
def Rect.bottom (r : Rect) := r.y + r.h

def Rect.Inside (a b : Rect) : Prop :=
  b.x ≤ a.x ∧ b.y ≤ a.y ∧ a.right ≤ b.right ∧ a.bottom ≤ b.bottom

instance (a b : Rect) : Decidable (a.Inside b) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def Rect.Disjoint (a b : Rect) : Prop :=
  a.w = 0 ∨ a.h = 0 ∨ b.w = 0 ∨ b.h = 0 ∨
  a.right ≤ b.x ∨ b.right ≤ a.x ∨ a.bottom ≤ b.y ∨ b.bottom ≤ a.y

instance (a b : Rect) : Decidable (a.Disjoint b) := inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _))

def Rect.has (r : Rect) (x y : Nat) : Bool :=
  r.x ≤ x && x < r.right && r.y ≤ y && y < r.bottom

/-- The intersection of all reported unobscured rectangles. -/
def content (i : Input) : Rect :=
  let n := i.insets
  let x := min i.w n.left
  let y := min i.h n.top
  ⟨x, y, i.w - x - n.right, i.h - y - n.bottom⟩

inductive Edge where
  | top | bottom | left | right
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Disjoint bands, including corners exactly once. -/
def reserved (i : Input) (e : Edge) : Rect :=
  let r := content i
  match e with
  | .top => ⟨0, 0, i.w, r.y⟩
  | .bottom => ⟨0, r.bottom, i.w, i.h - r.bottom⟩
  | .left => ⟨0, r.y, r.x, r.h⟩
  | .right => ⟨r.right, r.y, i.w - r.right, r.h⟩

/-- A control is accepted only as a whole, never by clipping its target. -/
def target (i : Input) (r : Rect) : Option Rect :=
  if r.Inside (content i) ∧ 0 < r.w ∧ 0 < r.h then some r else none

theorem content_inside (i : Input) : (content i).Inside ⟨0, 0, i.w, i.h⟩ := by
  simp only [content, Rect.Inside, Rect.right, Rect.bottom]
  have := Nat.min_le_left i.w i.insets.left
  have := Nat.min_le_left i.h i.insets.top
  omega

/-- No rectangle wholly in content meets any reserved band. -/
theorem inside_disjoint (i : Input) (r : Rect) (h : r.Inside (content i)) (e : Edge) :
    r.Disjoint (reserved i e) := by
  cases e <;> simp only [reserved, Rect.Disjoint, Rect.Inside, Rect.right, Rect.bottom] at * <;> omega

/-- Every target returned to hit testing is outside every reserved band. -/
theorem target_safe (i : Input) (r t : Rect) (h : target i r = some t) (e : Edge) :
    t.Disjoint (reserved i e) := by
  unfold target at h
  split at h
  next ht => cases h; exact inside_disjoint i r ht.1 e
  next => contradiction

/-- A real, nonempty target is accepted with both a cutout and keyboard. -/
theorem target_witness :
    target ⟨1080, 2400, ⟨0, 72, 0, 63⟩, ⟨0, 128, 0, 0⟩, ⟨0, 0, 0, 900⟩⟩
      ⟨48, 200, 126, 126⟩ = some ⟨48, 200, 126, 126⟩ := by decide

end Safe
