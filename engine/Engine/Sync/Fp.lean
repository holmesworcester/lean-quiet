/-
The fingerprint of a range of items, as Meyer and Scherer's RBSR without
homomorphic hashing defines it: the count of the items, and the Merkle
label of their canonical treap.

- An item sorts by its key: its claimed time, then its id read as a
  number (`num`, injective). A range is `[lo, hi)` over keys.
- The canonical treap of a set has the item with the largest priority
  (its id's number) at the root, the items below its key on the left,
  the items above on the right. `lbl` is that tree's Merkle label:
  `h ""` for the empty tree, `h (left ‖ id ‖ right)` for a node. It
  reads the set only through `top` and `filter`, so it is a function of
  the set, not of the list holding it.
- `lbl_inj`: equal labels mean equal sets, if `h` has no collision on
  what the two labellings hashed (`pres`). This is the one assumption
  sync makes of its fingerprints, of the same kind as `Distinct` for op
  ids.

This file computes a label from the items, which is what a cached tree
(Engine/Sync/Treap.lean) must agree with.
-/
import Engine.Core

namespace Engine.Sync

/-! ## Keys -/

/-- An id as a number, first byte lowest; the leading 1 keeps lengths
apart, so distinct ids get distinct numbers (`num_inj`). -/
def num (l : List UInt8) : Nat := l.foldr (fun b a => b.toNat + 256 * a) 1

theorem num_pos (l : List UInt8) : 0 < num l := by
  induction l with
  | nil => simp [num]
  | cons b t ih => simp only [num, List.foldr_cons] at *; omega

theorem num_inj {l m : List UInt8} (h : num l = num m) : l = m := by
  induction l generalizing m with
  | nil =>
    cases m with
    | nil => rfl
    | cons y u =>
      have := num_pos u
      simp only [num, List.foldr_nil, List.foldr_cons] at h this; omega
  | cons x t ih =>
    cases m with
    | nil =>
      have := num_pos t
      simp only [num, List.foldr_nil, List.foldr_cons] at h this; omega
    | cons y u =>
      simp only [num, List.foldr_cons] at h
      have hx := x.toNat_lt
      have hy := y.toNat_lt
      have e1 : x.toNat = y.toNat := by omega
      have e2 : num t = num u := by simp only [num]; omega
      rw [UInt8.toNat_inj.mp e1, ih e2]

/-- Where an item sorts: claimed time, then id number. -/
structure Key where
  t : Nat
  n : Nat
  deriving DecidableEq, Inhabited, Repr

namespace Key

protected def lt (a b : Key) : Prop := a.t < b.t ∨ (a.t = b.t ∧ a.n < b.n)

instance : LT Key := ⟨Key.lt⟩

instance (a b : Key) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.t < b.t ∨ (a.t = b.t ∧ a.n < b.n)))

theorem lt_def {a b : Key} : a < b ↔ a.t < b.t ∨ (a.t = b.t ∧ a.n < b.n) := Iff.rfl

theorem lt_irrefl (a : Key) : ¬ a < a := by
  rw [lt_def]; omega

theorem lt_trans {a b c : Key} (h1 : a < b) (h2 : b < c) : a < c := by
  rw [lt_def] at *; omega

theorem lt_asymm {a b : Key} (h : a < b) : ¬ b < a := fun h' => lt_irrefl a (lt_trans h h')

theorem lt_trichotomy (a b : Key) : a < b ∨ a = b ∨ b < a := by
  rcases a with ⟨t, n⟩
  rcases b with ⟨t', n'⟩
  simp only [lt_def, Key.mk.injEq]
  omega

theorem not_lt {a b : Key} : ¬ a < b ↔ b < a ∨ a = b := by
  rcases lt_trichotomy a b with h | h | h
  · exact ⟨fun h' => absurd h h', fun h' => h'.elim (fun h'' => absurd h (lt_asymm h''))
      (fun e => by subst e; exact absurd h (lt_irrefl _))⟩
  · subst h; exact ⟨fun _ => Or.inr rfl, fun _ => lt_irrefl _⟩
  · exact ⟨fun _ => Or.inl h, fun _ => lt_asymm h⟩

end Key

/-! ## Ranges -/

/-- The keys from `lo` (included) up to `hi` (excluded; none: no end). -/
structure Range where
  lo : Key
  hi : Option Key
  deriving DecidableEq, Inhabited, Repr

/-- Whether k is in r. -/
def Range.has (r : Range) (k : Key) : Bool :=
  !Decidable.decide (k < r.lo) && (match r.hi with | none => true | some h => Decidable.decide (k < h))

/-- The range from time `floor` on: a window. -/
def Range.from (floor : Nat) : Range := ⟨⟨floor, 0⟩, none⟩

/-! ## Labels -/

section
variable {α : Type} (key : α → Key) (ident : α → ByteArray)

/-- The item with the largest priority (its key's id number). -/
def top : List α → Option α
  | [] => none
  | a :: t => match top t with
    | none => some a
    | some b => if (key b).n < (key a).n then some a else some b

theorem top_none {l : List α} : top key l = none ↔ l = [] := by
  cases l with
  | nil => simp [top]
  | cons a t =>
    simp only [top, reduceCtorEq, iff_false]
    split <;> (try split) <;> simp

theorem top_mem {l : List α} {m : α} (h : top key l = some m) : m ∈ l := by
  induction l with
  | nil => simp [top] at h
  | cons a t ih =>
    simp only [top] at h
    split at h
    · cases h; exact List.mem_cons_self ..
    · rename_i b hb
      split at h
      · cases h; exact List.mem_cons_self ..
      · cases h; exact List.mem_cons_of_mem _ (ih hb)

/-- No item of l has a larger priority than the top. -/
theorem top_max {l : List α} {m : α} (h : top key l = some m) : ∀ a ∈ l, (key a).n ≤ (key m).n := by
  induction l generalizing m with
  | nil => simp [top] at h
  | cons a t ih =>
    simp only [top] at h
    split at h
    · rename_i hn
      cases h
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Nat.le_refl _
      · rw [top_none] at hn; subst hn; cases hx
    · rename_i b hb
      split at h
      · rename_i hlt
        cases h
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Nat.le_refl _
        · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (ih hb x hx) hlt)
      · rename_i hlt
        cases h
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Nat.le_of_not_lt hlt
        · exact ih hb x hx

/-- The items below m's key, and above it. -/
def below (l : List α) (m : α) : List α := l.filter fun a => Decidable.decide (key a < key m)
def above (l : List α) (m : α) : List α := l.filter fun a => Decidable.decide (key m < key a)

theorem below_lt {l : List α} {m : α} (hm : m ∈ l) : (below key l m).length < l.length := by
  apply List.length_filter_lt_length_iff_exists.mpr
  exact ⟨m, hm, by simp [Key.lt_irrefl]⟩

theorem above_lt {l : List α} {m : α} (hm : m ∈ l) : (above key l m).length < l.length := by
  apply List.length_filter_lt_length_iff_exists.mpr
  exact ⟨m, hm, by simp [Key.lt_irrefl]⟩

variable (h : ByteArray → ByteArray)

/-- The Merkle label of the canonical treap of l's items. -/
def lbl (l : List α) : ByteArray :=
  match hm : top key l with
  | none => h .empty
  | some m =>
    have := below_lt key (top_mem key hm)
    have := above_lt key (top_mem key hm)
    h (Codec.encode (lbl (below key l m), ident m, lbl (above key l m)))
termination_by l.length

/-- Every byte string `lbl l` hashes. -/
def pres (l : List α) : List ByteArray :=
  match hm : top key l with
  | none => [.empty]
  | some m =>
    have := below_lt key (top_mem key hm)
    have := above_lt key (top_mem key hm)
    Codec.encode (lbl key ident h (below key l m), ident m, lbl key ident h (above key l m)) ::
      (pres (below key l m) ++ pres (above key l m))
termination_by l.length

/-- A range's fingerprint: its count and its label. -/
def fp (l : List α) : Nat × ByteArray := (l.length, lbl key ident h l)

/-- h has no collision among these byte strings. -/
def NoCollision (S : List ByteArray) : Prop := ∀ a ∈ S, ∀ b ∈ S, h a = h b → a = b

/-- Items are named by their keys and by their idents, over these lists. -/
def Named (l : List α) : Prop :=
  ∀ a ∈ l, ∀ b ∈ l, (key a = key b → a = b) ∧ (ident a = ident b → a = b)

end

section
variable {α : Type} {key : α → Key} {ident : α → ByteArray} {h : ByteArray → ByteArray}

theorem lbl_eq (l : List α) : lbl key ident h l = match top key l with
    | none => h .empty
    | some m => h (Codec.encode (lbl key ident h (below key l m), ident m, lbl key ident h (above key l m))) := by
  rw [lbl]; split <;> rename_i hm <;> simp [hm]

theorem pres_eq (l : List α) : pres key ident h l = match top key l with
    | none => [.empty]
    | some m => Codec.encode (lbl key ident h (below key l m), ident m, lbl key ident h (above key l m)) ::
      (pres key ident h (below key l m) ++ pres key ident h (above key l m)) := by
  rw [pres]; split <;> rename_i hm <;> simp [hm]

/-- Each item of l is below the top, the top, or above it. -/
theorem split_mem {l : List α} {m : α} (hn : Named key ident l) (hm : m ∈ l) (a : α) :
    a ∈ l ↔ a ∈ below key l m ∨ a = m ∨ a ∈ above key l m := by
  simp only [below, above, List.mem_filter, decide_eq_true_eq]
  constructor
  · intro ha
    rcases Key.lt_trichotomy (key a) (key m) with h | h | h
    · exact Or.inl ⟨ha, h⟩
    · exact Or.inr (Or.inl ((hn a ha m hm).1 h))
    · exact Or.inr (Or.inr ⟨ha, h⟩)
  · rintro (⟨ha, _⟩ | rfl | ⟨ha, _⟩) <;> assumption

theorem named_sub {l l' : List α} (hn : Named key ident l) (hs : ∀ a ∈ l', a ∈ l) :
    Named key ident l' := fun a ha b hb => hn a (hs a ha) b (hs b hb)

theorem nocol_sub {S S' : List ByteArray} (hc : NoCollision h S) (hs : ∀ a ∈ S', a ∈ S) :
    NoCollision h S' := fun a ha b hb => hc a (hs a ha) b (hs b hb)

theorem encNat_ne (n : Nat) : Codec.encNat n ≠ [] := by
  rw [Codec.encNat]; split <;> simp

/-- The empty encoding is not a node's. -/
theorem encode_ne_empty (x : ByteArray × ByteArray × ByteArray) : Codec.encode x ≠ .empty := by
  intro he
  have h1 : (Codec.encode x).data.toList = [] := by rw [he]; rfl
  have h2 : Codec.enc x = [] := by simpa [Codec.encode] using h1
  change Codec.enc x.1 ++ Codec.enc x.2 = [] at h2
  have h3 := (List.append_eq_nil_iff.mp h2).1
  change Codec.encNat _ ++ _ = [] at h3
  exact encNat_ne _ (List.append_eq_nil_iff.mp h3).1

/-- **Equal labels, equal sets**, if h has no collision on what the two
labellings hashed. -/
theorem lbl_inj : ∀ (n : Nat) (l₁ l₂ : List α), l₁.length + l₂.length ≤ n →
    Named key ident (l₁ ++ l₂) → NoCollision h (pres key ident h l₁ ++ pres key ident h l₂) →
    lbl key ident h l₁ = lbl key ident h l₂ → ∀ a, a ∈ l₁ ↔ a ∈ l₂ := by
  intro n
  induction n with
  | zero =>
    intro l₁ l₂ hlen _ _ _ a
    have h1 : l₁ = [] := List.eq_nil_of_length_eq_zero (by omega)
    have h2 : l₂ = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst h1 h2; exact Iff.rfl
  | succ n ih =>
    intro l₁ l₂ hlen hn hc he a
    rw [lbl_eq, lbl_eq] at he
    have hp1 := pres_eq (key := key) (ident := ident) (h := h) l₁
    have hp2 := pres_eq (key := key) (ident := ident) (h := h) l₂
    cases ht1 : top key l₁ with
    | none =>
      cases ht2 : top key l₂ with
      | none => rw [(top_none key).mp ht1, (top_none key).mp ht2]
      | some m₂ =>
        rw [ht1, ht2] at he
        rw [ht1] at hp1; rw [ht2] at hp2
        have := hc _ (by rw [hp1]; simp) _ (by rw [hp2]; simp) he
        exact absurd this.symm (encode_ne_empty _)
    | some m₁ =>
      cases ht2 : top key l₂ with
      | none =>
        rw [ht1, ht2] at he
        rw [ht1] at hp1; rw [ht2] at hp2
        have := hc _ (by rw [hp1]; simp) _ (by rw [hp2]; simp) he
        exact absurd this (encode_ne_empty _)
      | some m₂ =>
        rw [ht1, ht2] at he
        rw [ht1] at hp1; rw [ht2] at hp2
        have hm1 := top_mem key ht1
        have hm2 := top_mem key ht2
        have := hc _ (by rw [hp1]; simp) _ (by rw [hp2]; simp) he
        have e := Codec.encode_inj this
        simp only [Prod.mk.injEq] at e
        obtain ⟨eb, ei, ea⟩ := e
        have em : m₁ = m₂ := (hn m₁ (List.mem_append_left _ hm1) m₂ (List.mem_append_right _ hm2)).2 ei
        subst em
        have sub1 : ∀ x ∈ below key l₁ m₁, x ∈ l₁ := fun x hx => (List.mem_filter.mp hx).1
        have sub2 : ∀ x ∈ below key l₂ m₁, x ∈ l₂ := fun x hx => (List.mem_filter.mp hx).1
        have sub3 : ∀ x ∈ above key l₁ m₁, x ∈ l₁ := fun x hx => (List.mem_filter.mp hx).1
        have sub4 : ∀ x ∈ above key l₂ m₁, x ∈ l₂ := fun x hx => (List.mem_filter.mp hx).1
        have hb := ih (below key l₁ m₁) (below key l₂ m₁)
          (by have := below_lt key hm1; have := below_lt key hm2; omega)
          (named_sub hn (fun x hx => by
            rcases List.mem_append.mp hx with hx | hx
            · exact List.mem_append_left _ (sub1 x hx)
            · exact List.mem_append_right _ (sub2 x hx)))
          (nocol_sub hc (fun x hx => by
            rw [hp1, hp2]
            rcases List.mem_append.mp hx with hx | hx
            · simp [hx]
            · simp [hx]))
          eb
        have ha := ih (above key l₁ m₁) (above key l₂ m₁)
          (by have := above_lt key hm1; have := above_lt key hm2; omega)
          (named_sub hn (fun x hx => by
            rcases List.mem_append.mp hx with hx | hx
            · exact List.mem_append_left _ (sub3 x hx)
            · exact List.mem_append_right _ (sub4 x hx)))
          (nocol_sub hc (fun x hx => by
            rw [hp1, hp2]
            rcases List.mem_append.mp hx with hx | hx
            · simp [hx]
            · simp [hx]))
          ea
        rw [split_mem (named_sub hn (fun x hx => List.mem_append_left _ hx)) hm1 a,
          split_mem (named_sub hn (fun x hx => List.mem_append_right _ hx)) hm2 a, hb a, ha a]

end

end Engine.Sync
