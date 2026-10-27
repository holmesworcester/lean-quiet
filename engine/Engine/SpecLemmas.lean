/-
The spec's shape: a verdict, once reached, stays (deeper derivations
and more ops only add verdicts), and it is unique.
-/
import Engine.Spec

namespace Engine
variable {F : Type} {fam : Family F}

/-- f is below g where it is decided: each undecided or equal. -/
def Below (l : List Id) (f g : Id → Option (Verdict F)) : Prop :=
  ∀ r ∈ l, f r = none ∨ f r = g r

theorem anyInvalid_mono {l : List Id} {f g : Id → Option (Verdict F)}
    (h : anyInvalid (l.map f) = true) (hb : Below l f g) : anyInvalid (l.map g) = true := by
  induction l with
  | nil => simp [anyInvalid] at h
  | cons r t ih =>
    have hb' : Below t f g := fun x hx => hb x (List.mem_cons_of_mem _ hx)
    have hr := hb r (List.mem_cons_self ..)
    simp only [List.map_cons] at h ⊢
    cases hfr : f r with
    | none =>
      rw [hfr] at h
      have := ih (by simpa [anyInvalid] using h) hb'
      cases hg : g r with
      | none => simpa [anyInvalid] using this
      | some v => cases v <;> simp [anyInvalid, this]
    | some v =>
      have hg : g r = some v := by rcases hr with h1 | h1 <;> simp_all
      rw [hfr] at h; rw [hg]
      cases v with
      | invalid => simp [anyInvalid]
      | valid w => simp only [anyInvalid] at h ⊢; exact ih h hb'

theorem allValid_mono {l : List Id} {f g : Id → Option (Verdict F)} {fs : List F}
    (h : allValid (l.map f) = some fs) (hb : Below l f g) : allValid (l.map g) = some fs := by
  induction l generalizing fs with
  | nil => simpa using h
  | cons r t ih =>
    have hb' : Below t f g := fun x hx => hb x (List.mem_cons_of_mem _ hx)
    have hr := hb r (List.mem_cons_self ..)
    simp only [List.map_cons] at h ⊢
    cases hfr : f r with
    | none => rw [hfr] at h; simp [allValid] at h
    | some v =>
      have hg : g r = some v := by rcases hr with h1 | h1 <;> simp_all
      rw [hfr] at h; rw [hg]
      cases v with
      | invalid => simp [allValid] at h
      | valid w =>
        simp only [allValid, Option.map_eq_some_iff] at h ⊢
        obtain ⟨a, ha, rfl⟩ := h
        exact ⟨a, ih ha hb', rfl⟩

theorem allValid_noInvalid {sts : List (Option (Verdict F))} {fs : List F}
    (h : allValid sts = some fs) : anyInvalid sts = false := by
  induction sts generalizing fs with
  | nil => rfl
  | cons s t ih =>
    match s, h with
    | some (.valid w), h =>
      simp only [allValid, Option.map_eq_some_iff] at h
      obtain ⟨a, ha, _⟩ := h
      simpa [anyInvalid] using ih ha

/-- judge only gains verdicts as requirements gain them. -/
theorem judge_mono {o : Op} {f g : Id → Option (Verdict F)} {v : Verdict F}
    (h : judge fam o (o.reqs.map f) = some v) (hb : Below o.reqs f g) :
    judge fam o (o.reqs.map g) = some v := by
  unfold judge at h ⊢
  by_cases hi : anyInvalid (o.reqs.map f) = true
  · simp [hi, anyInvalid_mono hi hb] at h ⊢; exact h
  · simp only [hi, Bool.false_eq_true, ite_false] at h
    cases ha : allValid (o.reqs.map f) with
    | none => rw [ha] at h; simp at h
    | some fs =>
      rw [ha] at h
      have hg := allValid_mono ha hb
      rw [allValid_noInvalid hg, hg]; simpa using h

theorem specAt_succ {ops : Id → Option Op} :
    ∀ n x v, specAt fam ops n x = some v → specAt fam ops (n + 1) x = some v := by
  intro n
  induction n with
  | zero => intro x v h; simp [specAt] at h
  | succ n ih =>
    intro x v h
    unfold specAt at h ⊢
    cases hx : ops x with
    | none => rw [hx] at h; simp at h
    | some o =>
      rw [hx] at h; simp only
      refine judge_mono h ?_
      intro r _
      cases hr : specAt fam ops n r with
      | none => exact Or.inl rfl
      | some w => exact Or.inr (ih r w hr).symm

theorem specAt_le {ops : Id → Option Op} {n m : Nat} {x : Id} {v : Verdict F}
    (h : specAt fam ops n x = some v) (hnm : n ≤ m) : specAt fam ops m x = some v := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact specAt_succ _ _ _ ih

theorem specAt_det {ops : Id → Option Op} {n m : Nat} {x : Id} {v w : Verdict F}
    (h1 : specAt fam ops n x = some v) (h2 : specAt fam ops m x = some w) : v = w := by
  have a := specAt_le h1 (Nat.le_max_left n m)
  have b := specAt_le h2 (Nat.le_max_right n m)
  rw [a] at b; exact Option.some.inj b

theorem spec_det {ops : Id → Option Op} {x : Id} {v w : Verdict F}
    (h1 : Spec fam ops x v) (h2 : Spec fam ops x w) : v = w := by
  obtain ⟨n, hn⟩ := h1; obtain ⟨m, hm⟩ := h2; exact specAt_det hn hm

/-- ops' extends ops. -/
def Extends (ops ops' : Id → Option Op) : Prop := ∀ i o, ops i = some o → ops' i = some o

theorem specAt_extends {ops ops' : Id → Option Op} (he : Extends ops ops') :
    ∀ n x v, specAt fam ops n x = some v → specAt fam ops' n x = some v := by
  intro n
  induction n with
  | zero => intro x v h; simp [specAt] at h
  | succ n ih =>
    intro x v h
    unfold specAt at h ⊢
    cases hx : ops x with
    | none => rw [hx] at h; simp at h
    | some o =>
      rw [hx] at h; rw [he x o hx]; simp only
      refine judge_mono h ?_
      intro r _
      cases hr : specAt fam ops n r with
      | none => exact Or.inl rfl
      | some w => exact Or.inr (ih r w hr).symm

/-- A verdict, once reached, survives any further ops. -/
theorem spec_extends {ops ops' : Id → Option Op} (he : Extends ops ops') {x : Id} {v : Verdict F}
    (h : Spec fam ops x v) : Spec fam ops' x v := by
  obtain ⟨n, hn⟩ := h; exact ⟨n, specAt_extends he n x v hn⟩

/-- One depth past every given verdict of a list's ops. -/
theorem common_depth {ops : Id → Option Op} (st : Id → Option (Verdict F)) :
    ∀ l : List Id, (∀ r ∈ l, ∀ w, st r = some w → Spec fam ops r w) →
    ∃ N, ∀ r ∈ l, ∀ w, st r = some w → specAt fam ops N r = some w := by
  intro l
  induction l with
  | nil => intro _; exact ⟨0, by simp⟩
  | cons r t ih =>
    intro h
    obtain ⟨N, hN⟩ := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    cases hr : st r with
    | none =>
      refine ⟨N, ?_⟩
      intro x hx w hw
      rcases List.mem_cons.1 hx with rfl | hx
      · rw [hr] at hw; cases hw
      · exact hN x hx w hw
    | some w0 =>
      obtain ⟨M, hM⟩ := h r (List.mem_cons_self ..) w0 hr
      refine ⟨max N M, ?_⟩
      intro x hx w hw
      rcases List.mem_cons.1 hx with rfl | hx
      · rw [hr] at hw; cases hw; exact specAt_le hM (Nat.le_max_right _ _)
      · exact specAt_le (hN x hx w hw) (Nat.le_max_left _ _)

/-- The spec unfolded: an op's verdict is judge over its requirements'
verdicts. -/
theorem spec_of_judge {ops : Id → Option Op} {x : Id} {o : Op} {v : Verdict F}
    (hx : ops x = some o) (st : Id → Option (Verdict F))
    (hst : ∀ r ∈ o.reqs, ∀ w, st r = some w → Spec fam ops r w)
    (hj : judge fam o (o.reqs.map st) = some v) : Spec fam ops x v := by
  obtain ⟨N, hN⟩ := common_depth st o.reqs hst
  refine ⟨N + 1, ?_⟩
  unfold specAt; rw [hx]; simp only
  refine judge_mono hj ?_
  intro r hr
  cases h : st r with
  | none => exact Or.inl rfl
  | some w => exact Or.inr (hN r hr w h).symm

end Engine
