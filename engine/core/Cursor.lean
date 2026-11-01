/-
A cursor scan of an ordered list: each step visits up to `n` rows past the
cursor, or from the start once none is past it, and moves the cursor to the
last row it visited. **Every row is visited within |U| + 2 steps** (`visits`),
where U holds every key filed at any step of the window: rows filed while the
scan runs (anywhere, even just ahead of the cursor) count once in U, never
more. The dialer's scan of pending joins and members runs this (`page`).
-/
import engine.core.Order

namespace Engine.Cursor

/-- A strict total order, as a Boolean test. -/
structure Strict {κ : Type} (lt : κ → κ → Bool) : Prop where
  irrefl : ∀ a, lt a a = false
  trans : ∀ {a b c}, lt a b = true → lt b c = true → lt a c = true
  total : ∀ a b, a ≠ b → lt a b = true ∨ lt b a = true

section
variable {κ β : Type} (lt : κ → κ → Bool) (key : β → κ)

/-- Past the cursor (everything, with none). -/
def after : Option κ → κ → Bool
  | some a, x => lt a x
  | none, _ => true

@[simp] theorem after_some (a x : κ) : after lt (some a) x = lt a x := rfl
@[simp] theorem after_none (x : κ) : after lt none x = true := rfl

/-- The rows past the cursor. -/
def past (c : Option κ) (R : List β) : List β := R.filter fun x => after lt c (key x)

/-- One step's rows: up to `n` past the cursor, or from the start once none
is past it. -/
def page (R : List β) (n : Nat) (c : Option κ) : List β :=
  if (past lt key c R).isEmpty && c.isSome then R.take n else (past lt key c R).take n

/-- The cursor after a step: its last row's key, or where it was. -/
def next (R : List β) (n : Nat) (c : Option κ) : Option κ :=
  match (page lt key R n c).getLast? with
  | some x => some (key x)
  | none => c

/-- Ascending, strictly. -/
def Sorted (R : List β) : Prop := R.Pairwise fun x y => lt (key x) (key y) = true

/-- How far the cursor is from key t, counted in U's keys: the ones between
them before the scan wraps, or past the cursor plus before t, plus the wrap. -/
def dist (U : List κ) (t : κ) (c : Option κ) : Nat :=
  if after lt c t then (U.filter fun u => after lt c u && lt u t).length
  else (U.filter fun u => after lt c u).length + (U.filter fun u => lt u t).length + 1

end

/-! ## Counting lemmas -/

theorem filter_length_mono {α} (U : List α) (P Q : α → Bool) (hPQ : ∀ x, Q x = true → P x = true) :
    (U.filter Q).length ≤ (U.filter P).length := by
  induction U with
  | nil => simp
  | cons a t ih =>
    simp only [List.filter_cons]
    have := hPQ a
    cases hq : Q a <;> cases hp : P a <;> simp_all <;> omega

theorem filter_length_lt {α} (U : List α) (P Q : α → Bool) (hPQ : ∀ x, Q x = true → P x = true)
    {y : α} (hy : y ∈ U) (hP : P y = true) (hQ : Q y = false) :
    (U.filter Q).length < (U.filter P).length := by
  induction U with
  | nil => cases hy
  | cons a t ih =>
    have hm := filter_length_mono t P Q hPQ
    simp only [List.filter_cons]
    rcases List.mem_cons.1 hy with rfl | ht
    · simp [hP, hQ]; omega
    · have := ih ht
      have := hPQ a
      cases hq : Q a <;> cases hp : P a <;> simp_all <;> omega

theorem filter_disjoint_length {α} (U : List α) (P Q : α → Bool) (h : ∀ x, P x = true → Q x = false) :
    (U.filter P).length + (U.filter Q).length ≤ U.length := by
  induction U with
  | nil => simp
  | cons a t ih =>
    simp only [List.filter_cons]
    have := h a
    cases hp : P a <;> cases hq : Q a <;> simp_all <;> omega

/-! ## A step that misses the target moves the cursor closer -/

section
variable {κ β : Type} {lt : κ → κ → Bool} {key : β → κ}

theorem dist_le (hs : Strict lt) (U : List κ) (t : κ) (c : Option κ) :
    dist lt U t c ≤ U.length + 1 := by
  unfold dist
  split
  · have := List.length_filter_le (fun u => after lt c u && lt u t) U; omega
  · rename_i hc
    cases c with
    | none => simp [after] at hc
    | some a =>
      have hc' : lt a t = false := by simpa [after] using hc
      have := filter_disjoint_length U (fun u => after lt (some a) u) (fun u => lt u t) (by
        intro x hx
        have hx' : lt a x = true := by simpa [after] using hx
        cases e : lt x t
        · rfl
        · exfalso
          rcases Classical.em (a = t) with h0 | hne
          · subst h0
            have := hs.trans hx' e; rw [hs.irrefl] at this; cases this
          · rcases hs.total a t hne with h | h
            · rw [hc'] at h; cases h
            · have := hs.trans (hs.trans h hx') e; rw [hs.irrefl] at this; cases this)
      omega

/-- Of a sorted list, a row past a member's prefix-free position: every row
of `take n` before one in `drop n` is before it. -/
theorem take_before (R : List β) (n : Nat) (hR : Sorted lt key R) {t : β}
    (ht : t ∈ R) (hn : t ∉ R.take n) : ∀ x ∈ R.take n, lt (key x) (key t) = true := by
  have hd : t ∈ R.drop n := by
    have := List.take_append_drop n R
    rw [← this, List.mem_append] at ht
    exact ht.resolve_left hn
  have hp := hR
  unfold Sorted at hp
  rw [← List.take_append_drop n R, List.pairwise_append] at hp
  intro x hx
  exact hp.2.2 x hx t hd

theorem sorted_filter (R : List β) (P : β → Bool) (hR : Sorted lt key R) : Sorted lt key (R.filter P) :=
  List.Pairwise.filter _ hR

theorem getLast_mem_take {R : List β} {n : Nat} {x : β} (h : (R.take n).getLast? = some x) :
    x ∈ R.take n := List.mem_of_getLast? h

/-- **A step that does not visit t brings the cursor strictly closer to it**,
in U's count, when U holds every key of the list. -/
theorem dist_step (hs : Strict lt) (U : List κ) (R : List β) (n : Nat) (hn : 0 < n)
    (hR : Sorted lt key R) (hU : ∀ x ∈ R, key x ∈ U) {t : β} (ht : t ∈ R)
    (c : Option κ) (hmiss : t ∉ page lt key R n c) :
    dist lt U (key t) (next lt key R n c) < dist lt U (key t) c := by
  have hT : ∀ x ∈ R, key x ∈ U := hU
  have hne : ∀ (L : List β) (z : β), z ∈ L → L.take n ≠ [] := by
    intro L z hL h0
    rcases List.take_eq_nil_iff.1 h0 with h0 | h0
    · omega
    · subst h0; cases hL
  have last : ∀ (L : List β), L.take n ≠ [] → ∃ x, (L.take n).getLast? = some x ∧ x ∈ L.take n := by
    intro L hL
    cases e : (L.take n).getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.1 e) hL
    | some x => exact ⟨x, rfl, List.mem_of_getLast? e⟩
  have aft_trans : ∀ (c : Option κ) (a u : κ), after lt c a = true → lt a u = true → after lt c u = true := by
    intro c a u h1 h2
    cases c with
    | none => rfl
    | some b => exact hs.trans h1 h2
  unfold next page at *
  by_cases hw : ((past lt key c R).isEmpty && c.isSome) = true
  · -- wrapped: nothing past the cursor, so t is not past it either
    rw [if_pos hw] at hmiss ⊢
    obtain ⟨x, hx, hxm⟩ := last R (hne R t ht)
    rw [hx]
    have hxt := take_before R n hR ht hmiss x hxm
    cases c with
    | none => simp at hw
    | some a =>
      have hct : lt a (key t) = false := by
        cases e : lt a (key t)
        · rfl
        · have : t ∈ past lt key (some a) R := List.mem_filter.2 ⟨ht, e⟩
          simp only [Bool.and_eq_true, List.isEmpty_iff] at hw
          rw [hw.1] at this; cases this
      unfold dist
      simp only [after, hxt, ite_true, hct, Bool.false_eq_true, ite_false]
      have := filter_length_mono U (fun u => lt u (key t)) (fun u => lt (key x) u && lt u (key t))
        (by intro u hu; simp only [Bool.and_eq_true] at hu; exact hu.2)
      omega
  · rw [if_neg hw] at hmiss ⊢
    have hP : t ∈ past lt key c R ∨ after lt c (key t) = false := by
      cases e : after lt c (key t)
      · exact Or.inr rfl
      · exact Or.inl (List.mem_filter.2 ⟨ht, e⟩)
    have hnonempty : past lt key c R ≠ [] := by
      intro h0
      cases c with
      | none =>
        have : t ∈ past lt key none R := List.mem_filter.2 ⟨ht, rfl⟩
        rw [h0] at this; cases this
      | some a => simp [h0] at hw
    obtain ⟨y, hy0⟩ := List.exists_mem_of_ne_nil _ hnonempty
    obtain ⟨x, hx, hxm⟩ := last (past lt key c R) (hne _ y hy0)
    rw [hx]
    have hxp : after lt c (key x) = true := (List.mem_filter.1 (List.mem_of_mem_take hxm)).2
    have hxU : key x ∈ U := hU x (List.mem_filter.1 (List.mem_of_mem_take hxm)).1
    rcases hP with htp | hct
    · -- t is ahead: x is between the cursor and t
      have hxt := take_before (past lt key c R) n (sorted_filter R _ hR) htp hmiss x hxm
      have hct : after lt c (key t) = true := (List.mem_filter.1 htp).2
      unfold dist
      simp only [after_some, hxt, ite_true, hct]
      exact filter_length_lt U _ _
        (by intro u hu; simp only [Bool.and_eq_true] at hu ⊢; exact ⟨aft_trans c _ _ hxp hu.1, hu.2⟩)
        hxU (by simp [hxp, hxt]) (by simp [hs.irrefl])
    · -- t is behind: x is past the cursor, and so past t
      cases c with
      | none => simp [after] at hct
      | some a =>
        have hxt : lt (key x) (key t) = false := by
          cases e : lt (key x) (key t)
          · rfl
          · simp only [after] at hxp hct; rw [hs.trans hxp e] at hct; cases hct
        have hct' : lt a (key t) = false := by simpa using hct
        unfold dist
        simp only [after_some, hxt, hct', Bool.false_eq_true, ite_false]
        have := filter_length_lt U (fun u => lt a u) (fun u => lt (key x) u)
          (by intro u hu; exact hs.trans hxp hu) hxU hxp (hs.irrefl _)
        omega

end

/-- **Every row is visited within |U| + 2 steps.** Whatever is filed or
unfiled between steps (anywhere, just ahead of the cursor included), as long
as t stays filed and U holds every key filed during the window. -/
theorem visits {κ β : Type} {lt : κ → κ → Bool} {key : β → κ} (hs : Strict lt) (n : Nat) (hn : 0 < n)
    (U : List κ) (R : Nat → List β) (c : Nat → Option κ)
    (hR : ∀ k, k ≤ U.length + 1 → Sorted lt key (R k))
    (hU : ∀ k, k ≤ U.length + 1 → ∀ x ∈ R k, key x ∈ U)
    (hc : ∀ k, c (k + 1) = next lt key (R k) n (c k))
    {t : β} (ht : ∀ k, k ≤ U.length + 1 → t ∈ R k) :
    ∃ k, k ≤ U.length + 1 ∧ t ∈ page lt key (R k) n (c k) := by
  -- if every step up to j missed, the distance fell by j
  have fall : ∀ j, j ≤ U.length + 2 → (∀ k, k < j → t ∉ page lt key (R k) n (c k)) →
      dist lt U (key t) (c j) + j ≤ dist lt U (key t) (c 0) := by
    intro j
    induction j with
    | zero => intros; simp
    | succ j ih =>
      intro hj hm
      have h1 := ih (by omega) (fun k hk => hm k (by omega))
      have h2 := dist_step hs U (R j) n hn (hR j (by omega)) (hU j (by omega)) (ht j (by omega)) (c j) (hm j (by omega))
      rw [hc j]; omega
  apply Classical.byContradiction
  intro hno
  have hm : ∀ k, k < U.length + 2 → t ∉ page lt key (R k) n (c k) := by
    intro k hk hk'
    exact hno ⟨k, by omega, hk'⟩
  have := fall (U.length + 2) (by omega) hm
  have := dist_le hs U (key t) (c 0)
  omega

end Engine.Cursor
