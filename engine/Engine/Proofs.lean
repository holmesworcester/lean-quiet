/-
The engine is correct: whatever ops arrive, in whatever order, and
however the judging and purges interleave with arrivals, the persisted
tables keep `Inv`. When the queue is empty, the persisted verdicts are
exactly the spec's (`status_iff_spec`), so they depend only on the set
of ops held (`order_free`), and the index holds exactly the Valid facts'
keys (`Inv.idx`).
-/
import Engine.Run
import Engine.SpecLemmas
import Engine.Purge

namespace Engine
variable {F : Type} {fam : Family F}

/-! ## What each routine does to the tables -/

theorem waitOnS_ops (x : Id) (l : List Id) (s : DB F) : (waitOnS x l s).ops = s.ops := by
  induction l generalizing s with
  | nil => rfl
  | cons r t ih => simp only [waitOnS]; rw [ih]; split <;> rfl
theorem waitOnS_status (x : Id) (l : List Id) (s : DB F) : (waitOnS x l s).status = s.status := by
  induction l generalizing s with
  | nil => rfl
  | cons r t ih => simp only [waitOnS]; rw [ih]; split <;> rfl
theorem waitOnS_queue (x : Id) (l : List Id) (s : DB F) : (waitOnS x l s).queue = s.queue := by
  induction l generalizing s with
  | nil => rfl
  | cons r t ih => simp only [waitOnS]; rw [ih]; split <;> rfl
theorem waitOnS_idx (x : Id) (l : List Id) (s : DB F) : (waitOnS x l s).idx = s.idx := by
  induction l generalizing s with
  | nil => rfl
  | cons r t ih => simp only [waitOnS]; rw [ih]; split <;> rfl
theorem waitOnS_stored (x : Id) (l : List Id) (s : DB F) : (waitOnS x l s).stored = s.stored := by
  induction l generalizing s with
  | nil => rfl
  | cons r t ih => simp only [waitOnS]; rw [ih]; split <;> rfl

theorem mem_waitOnS (x : Id) (l : List Id) (s : DB F) (r y : Id) :
    y ∈ (waitOnS x l s).waits r ↔ y ∈ s.waits r ∨ (y = x ∧ r ∈ l ∧ s.status r = none) := by
  induction l generalizing s with
  | nil => simp [waitOnS]
  | cons a t ih =>
    simp only [waitOnS]
    by_cases ha : (s.status a).isNone = true
    · simp only [ha, ite_true, ih]
      have hst : (s.addWait a x).status = s.status := rfl
      rw [hst]
      by_cases hra : r = a
      · subst hra
        simp only [DB.addWait, ite_true, mem_ins, List.mem_cons]
        have : s.status r = none := by simpa using ha
        constructor
        · rintro ((h | h) | ⟨h1, h2, h3⟩)
          · exact Or.inl h
          · exact Or.inr ⟨h, Or.inl trivial, this⟩
          · exact Or.inr ⟨h1, Or.inr h2, h3⟩
        · rintro (h | ⟨h1, _, _⟩)
          · exact Or.inl (Or.inl h)
          · exact Or.inl (Or.inr h1)
      · simp only [DB.addWait, hra, ite_false, List.mem_cons]
        constructor
        · rintro (h | ⟨h1, h2, h3⟩)
          · exact Or.inl h
          · exact Or.inr ⟨h1, Or.inr h2, h3⟩
        · rintro (h | ⟨h1, h2 | h2, h3⟩)
          · exact Or.inl h
          · exact h2.elim
          · exact Or.inr ⟨h1, h2, h3⟩
    · simp only [ha, Bool.false_eq_true, ite_false, ih, List.mem_cons]
      have : s.status a ≠ none := by simpa using ha
      constructor
      · rintro (h | ⟨h1, h2, h3⟩)
        · exact Or.inl h
        · exact Or.inr ⟨h1, Or.inr h2, h3⟩
      · rintro (h | ⟨h1, rfl | h2, h3⟩)
        · exact Or.inl h
        · exact absurd h3 this
        · exact Or.inr ⟨h1, h2, h3⟩

theorem indexAllS_fields (x : Id) (ks : List ByteArray) (s : DB F) :
    (indexAllS x ks s).ops = s.ops ∧ (indexAllS x ks s).status = s.status ∧
    (indexAllS x ks s).waits = s.waits ∧ (indexAllS x ks s).queue = s.queue := by
  induction ks generalizing s with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons k t ih => exact ih (s.index k x)

theorem indexAllS_stored (x : Id) (ks : List ByteArray) (s : DB F) :
    (indexAllS x ks s).stored = s.stored := by
  induction ks generalizing s with
  | nil => rfl
  | cons k t ih => exact ih (s.index k x)

theorem mem_indexAllS (x : Id) (ks : List ByteArray) (s : DB F) (k : ByteArray) (y : Id) :
    y ∈ (indexAllS x ks s).idx k ↔ y ∈ s.idx k ∨ (y = x ∧ k ∈ ks) := by
  induction ks generalizing s with
  | nil => simp [indexAllS]
  | cons a t ih =>
    simp only [indexAllS, ih, List.mem_cons]
    by_cases hk : k = a
    · subst hk; simp only [DB.index, ite_true, mem_ins]
      constructor
      · rintro ((h | h) | ⟨h1, h2⟩)
        · exact Or.inl h
        · exact Or.inr ⟨h, Or.inl trivial⟩
        · exact Or.inr ⟨h1, Or.inr h2⟩
      · rintro (h | ⟨h1, _⟩)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h1)
    · simp only [DB.index, hk, ite_false]
      constructor
      · rintro (h | ⟨h1, h2⟩)
        · exact Or.inl h
        · exact Or.inr ⟨h1, Or.inr h2⟩
      · rintro (h | ⟨h1, h2 | h2⟩)
        · exact Or.inl h
        · exact h2.elim
        · exact Or.inr ⟨h1, h2⟩

/-- What deciding x does: its verdict set, its fact indexed, its
waiters moved to the queue. -/
theorem decideS_fields (x : Id) (v : Verdict F) (s : DB F) :
    (decideS fam x v s).ops = s.ops ∧
    (decideS fam x v s).status = (fun i => if i = x then some v else s.status i) ∧
    (decideS fam x v s).queue = s.queue ++ s.waits x ∧
    (∀ r, (decideS fam x v s).waits r = if r = x then [] else s.waits r) ∧
    (∀ k y, y ∈ (decideS fam x v s).idx k ↔
      y ∈ s.idx k ∨ (y = x ∧ ∃ f, v = .valid f ∧ k ∈ fam.fileKeys x f)) := by
  cases v with
  | valid f =>
    obtain ⟨h1, h2, h3, h4⟩ := indexAllS_fields x (fam.fileKeys x f) (s.setStatus x (.valid f))
    refine ⟨h1, h2, ?_, ?_, ?_⟩
    · show (indexAllS x (fam.fileKeys x f) (s.setStatus x (.valid f))).queue ++
        (indexAllS x (fam.fileKeys x f) (s.setStatus x (.valid f))).waits x = _
      rw [h3, h4]; rfl
    · intro r; show (if r = x then [] else (indexAllS x (fam.fileKeys x f) (s.setStatus x (.valid f))).waits r) = _
      rw [h3]; rfl
    · intro k y
      show y ∈ (indexAllS x (fam.fileKeys x f) (s.setStatus x (.valid f))).idx k ↔ _
      rw [mem_indexAllS]
      constructor
      · rintro (h | ⟨h1, h2⟩)
        · exact Or.inl h
        · exact Or.inr ⟨h1, f, rfl, h2⟩
      · rintro (h | ⟨h1, g, hg, h2⟩)
        · exact Or.inl h
        · cases hg; exact Or.inr ⟨h1, h2⟩
  | invalid =>
    refine ⟨rfl, rfl, rfl, fun r => rfl, ?_⟩
    intro k y
    show y ∈ s.idx k ↔ _
    constructor
    · exact Or.inl
    · rintro (h | ⟨_, g, hg, _⟩)
      · exact h
      · cases hg

theorem decideS_stored (x : Id) (v : Verdict F) (s : DB F) :
    (decideS fam x v s).stored = s.stored := by
  cases v with
  | valid f => exact indexAllS_stored x (fam.fileKeys x f) (s.setStatus x (.valid f))
  | invalid => rfl

theorem stepS_stored (s : DB F) : (stepS fam s).stored = s.stored := by
  unfold stepS
  cases s.queue with
  | nil => rfl
  | cons x q =>
    simp only
    cases s.status x with
    | some _ => rfl
    | none =>
      simp only
      cases s.ops x with
      | none => rfl
      | some o =>
        simp only
        cases judge fam o (o.reqs.map s.status) with
        | some v => exact decideS_stored x v _
        | none => exact waitOnS_stored _ _ _

/-! ## The invariant -/

/-- What the persisted tables always satisfy. -/
structure Inv (fam : Family F) (s : DB F) : Prop where
  /-- Ops are stored under their own ids. -/
  key : ∀ x o, s.ops x = some o → o.id = x
  /-- Every persisted verdict is the spec's. -/
  sound : ∀ x v, s.status x = some v → Spec fam s.ops x v
  /-- An undecided op is queued, or judge has no verdict for it yet and
  it waits on each of its undecided requirements. -/
  wait : ∀ x o, s.ops x = some o → s.status x = none →
    x ∈ s.queue ∨ (judge fam o (o.reqs.map s.status) = none ∧
      ∀ r ∈ o.reqs, s.status r = none → x ∈ s.waits r)
  /-- The index holds exactly the Valid facts' keys. -/
  idx : ∀ k x, x ∈ s.idx k ↔ ∃ f, s.status x = some (.valid f) ∧ k ∈ fam.fileKeys x f
  /-- The stored list names exactly the stored ops. -/
  stored : ∀ x, x ∈ s.stored ↔ (s.ops x).isSome

theorem inv_empty : Inv fam (DB.empty : DB F) where
  key := by intro x o h; cases h
  sound := by intro x v h; cases h
  wait := by intro x o h; cases h
  idx := by intro k x; simp [DB.empty]
  stored := by intro x; simp [DB.empty]

theorem inv_ingest {s : DB F} (h : Inv fam s) (o : Op) : Inv fam (ingestS o s) := by
  unfold ingestS
  cases hx : s.ops o.id with
  | some _ => exact h
  | none =>
    have he : Extends s.ops (s.putOp o |>.push o.id).ops := by
      intro i p hp
      show (if i = o.id then some o else s.ops i) = some p
      by_cases hi : i = o.id
      · subst hi; rw [hx] at hp; cases hp
      · simp [hi, hp]
    refine ⟨?_, ?_, ?_, h.idx, ?_⟩
    · intro x p hp
      change (if x = o.id then some o else s.ops x) = some p at hp
      by_cases hi : x = o.id
      · subst hi; simp at hp; rw [← hp]
      · simp [hi] at hp; exact h.key x p hp
    · intro x v hv; exact spec_extends he (h.sound x v hv)
    · intro x p hp hs
      change (if x = o.id then some o else s.ops x) = some p at hp
      by_cases hi : x = o.id
      · left; subst hi; show o.id ∈ s.queue ++ [o.id]; simp
      · simp [hi] at hp
        rcases h.wait x p hp hs with hq | hw
        · left; show x ∈ s.queue ++ [o.id]; simp [hq]
        · right; exact hw
    · intro x
      show x ∈ ins s.stored o.id ↔ (if x = o.id then some o else s.ops x).isSome
      rw [mem_ins, h.stored]
      by_cases hi : x = o.id <;> simp [hi]

theorem inv_step {s : DB F} (h : Inv fam s) : Inv fam (stepS fam s) := by
  unfold stepS
  cases hq : s.queue with
  | nil => exact h
  | cons x q =>
    -- Any other undecided op is still queued or waiting once x leaves the queue.
    have other : ∀ y o, s.ops y = some o → s.status y = none → y ≠ x →
        y ∈ q ∨ (judge fam o (o.reqs.map s.status) = none ∧
          ∀ r ∈ o.reqs, s.status r = none → y ∈ s.waits r) := by
      intro y o hy hs hne
      rcases h.wait y o hy hs with hq' | hw
      · rw [hq] at hq'
        rcases List.mem_cons.1 hq' with rfl | hq'
        · exact absurd rfl hne
        · exact Or.inl hq'
      · exact Or.inr hw
    simp only
    cases hs : s.status x with
    | some w =>
      refine ⟨h.key, h.sound, ?_, h.idx, h.stored⟩
      intro y o hy hsy
      have : y ≠ x := by rintro rfl; rw [hs] at hsy; cases hsy
      exact other y o hy hsy this
    | none =>
      cases ho : s.ops x with
      | none =>
        refine ⟨h.key, h.sound, ?_, h.idx, h.stored⟩
        intro y o hy hsy
        have : y ≠ x := by rintro rfl; rw [ho] at hy; cases hy
        exact other y o hy hsy this
      | some o =>
        simp only
        cases hj : judge fam o (o.reqs.map s.status) with
        | none =>
          simp only
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · rw [waitOnS_ops]; exact h.key
          · rw [waitOnS_ops, waitOnS_status]; exact h.sound
          · rw [waitOnS_ops, waitOnS_status, waitOnS_queue]
            intro y p hy hsy
            by_cases hyx : y = x
            · subst hyx; rw [ho] at hy; cases hy
              refine Or.inr ⟨hj, fun r hr hsr => ?_⟩
              exact (mem_waitOnS _ _ _ r y).2 (Or.inr ⟨rfl, hr, hsr⟩)
            · rcases other y p hy hsy hyx with hq' | ⟨hj', hw⟩
              · exact Or.inl hq'
              · exact Or.inr ⟨hj', fun r hr hsr => (mem_waitOnS _ _ _ r y).2 (Or.inl (hw r hr hsr))⟩
          · rw [waitOnS_idx, waitOnS_status]; exact h.idx
          · rw [waitOnS_ops, waitOnS_stored]; exact h.stored
        | some v =>
          simp only
          obtain ⟨d1, d2, d3, d4, d5⟩ := decideS_fields (fam := fam) x v { s with queue := q }
          refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · rw [d1]; exact h.key
          · rw [d1, d2]
            intro y w hy
            by_cases hyx : y = x
            · subst hyx; simp at hy; subst hy
              exact spec_of_judge ho s.status (fun r _ w hw => h.sound r w hw) hj
            · simp [hyx] at hy; exact h.sound y w hy
          · rw [d1, d2, d3]
            intro y p hy hsy
            have hyx : y ≠ x := by rintro rfl; simp at hsy
            simp only [hyx, ite_false] at hsy
            rcases other y p hy hsy hyx with hq' | ⟨hj', hw⟩
            · exact Or.inl (List.mem_append_left _ hq')
            · by_cases hxr : x ∈ p.reqs
              · exact Or.inl (List.mem_append_right _ (hw x hxr hs))
              · right
                have hmap : p.reqs.map (fun i => if i = x then some v else s.status i) =
                    p.reqs.map s.status := by
                  apply List.map_congr_left
                  intro r hr
                  have : r ≠ x := by rintro rfl; exact hxr hr
                  simp [this]
                refine ⟨by rw [hmap]; exact hj', fun r hr hsr => ?_⟩
                have hrx : r ≠ x := by rintro rfl; exact hxr hr
                simp only [hrx, ite_false] at hsr
                rw [d4]; simp only [hrx, ite_false]; exact hw r hr hsr
          · intro k y
            rw [d5, d2]
            by_cases hyx : y = x
            · subst hyx
              have hn : y ∉ s.idx k := by
                intro hm; obtain ⟨f, hf, _⟩ := (h.idx k y).1 hm; rw [hs] at hf; cases hf
              simp only [ite_true]
              constructor
              · rintro (hm | ⟨_, f, rfl, hk⟩)
                · exact absurd hm hn
                · exact ⟨f, rfl, hk⟩
              · rintro ⟨f, hf, hk⟩; cases hf; exact Or.inr ⟨trivial, f, rfl, hk⟩
            · simp only [hyx, ite_false, false_and, or_false]; exact h.idx k y
          · rw [d1, decideS_stored]; exact h.stored

/-! ## Purging keeps it -/

/-- The closure of a purge holds every stored op that requires one of
its members. -/
theorem closeUp_dependents {s : DB F} (h : Inv fam s) (ids : List Id) :
    ∀ y o r, s.ops y = some o → r ∈ o.reqs → r ∈ closeUp s ids → y ∈ closeUp s ids :=
  fun y o r hy hr hc => closeUp_closed s ids ((h.stored y).2 (by simp [hy])) hy hr hc

/-- **The purged ops are exactly the conn and local ops among `ids` and
their stored dependents** (x requires one of `ids`, recursively). -/
theorem mem_purgeSet {s : DB F} (h : Inv fam s) (ids : List Id) (x : Id) :
    x ∈ purgeSet fam s ids ↔
      (∃ o, s.ops x = some o ∧ fam.room o = none) ∧ ∃ y ∈ ids, Sync.Reach s.ops x y := by
  rw [mem_purgeSet_iff]
  constructor
  · rintro ⟨hc, ho⟩; exact ⟨ho, closeUp_sound s ids hc⟩
  · rintro ⟨ho, y, hy, hxy⟩
    exact ⟨reach_closed (C := (· ∈ closeUp s ids)) (closeUp_dependents h ids) hxy
      (closeUp_sub s ids hy), ho⟩

/-- **A purge keeps the invariant**, at rest or not. No remaining
decided op requires a purged one, so its verdict is still the spec's
over the remaining ops (`Sync.spec_local`); the shared ops that did are
back on the queue, to be judged again. -/
theorem purge_inv {s : DB F} (h : Inv fam s) (ids : List Id) : Inv fam (purgeS fam ids s) := by
  have hcl := closeUp_dependents h ids
  -- A stored op of the closure is purged or judged again.
  have again : ∀ x o, s.ops x = some o → x ∈ closeUp s ids → x ∉ purgeSet fam s ids →
      x ∈ rejudgeSet fam s ids := by
    intro x o ho hc hp
    refine mem_rejudgeSet_iff.2 ⟨hc, o, ho, ?_⟩
    cases hr : fam.room o with
    | some _ => rfl
    | none => exact absurd (mem_purgeSet_iff.2 ⟨hc, o, ho, hr⟩) hp
  have kept : ∀ x o, (purgeS fam ids s).ops x = some o →
      x ∉ purgeSet fam s ids ∧ s.ops x = some o := by
    intro x o hx
    by_cases hp : x ∈ purgeSet fam s ids
    · rw [purgeS_ops_mem s ids hp] at hx; cases hx
    · exact ⟨hp, by rw [purgeS_ops_not s ids hp] at hx; exact hx⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x o hx; exact h.key x o (kept x o hx).2
  · intro x v hx
    by_cases hc : x ∈ closeUp s ids
    · rw [purgeS_status_mem s ids hc] at hx; cases hx
    rw [purgeS_status_not s ids hc] at hx
    refine Sync.spec_local fam (h.sound x v hx) fun y o hxy hy => ?_
    have hyp : y ∉ purgeSet fam s ids := fun hp =>
      hc (reach_closed (C := (· ∈ closeUp s ids)) hcl hxy (purgeSet_closeUp hp))
    rw [purgeS_ops_not s ids hyp]; exact hy
  · intro x o hx hsx
    obtain ⟨hp, ho⟩ := kept x o hx
    by_cases hc : x ∈ closeUp s ids
    · exact Or.inl ((mem_purgeS_queue s ids x).2 (Or.inr (again x o ho hc hp)))
    rw [purgeS_status_not s ids hc] at hsx
    -- None of its requirements is in the closure, or it would be.
    have hr : ∀ r ∈ o.reqs, r ∉ closeUp s ids := fun r hr hrc => hc (hcl x o r ho hr hrc)
    rcases h.wait x o ho hsx with hq | ⟨hj, hw⟩
    · exact Or.inl ((mem_purgeS_queue s ids x).2 (Or.inl ⟨hq, hc⟩))
    · right
      have hmap : o.reqs.map (purgeS fam ids s).status = o.reqs.map s.status :=
        List.map_congr_left fun r hr' => purgeS_status_not s ids (hr r hr')
      refine ⟨by rw [hmap]; exact hj, fun r hr' hsr => ?_⟩
      rw [purgeS_status_not s ids (hr r hr')] at hsr
      exact (mem_purgeS_waits s ids r x).2
        ⟨fun hp' => hr r hr' (purgeSet_closeUp hp'), hw r hr' hsr, hp⟩
  · intro k x
    rw [mem_purgeS_idx]
    by_cases hc : x ∈ closeUp s ids
    · rw [purgeS_status_mem s ids hc]; simp [hc]
    · rw [purgeS_status_not s ids hc, h.idx]; simp [hc]
  · intro x
    rw [mem_purgeS_stored, h.stored]
    by_cases hp : x ∈ purgeSet fam s ids
    · rw [purgeS_ops_mem s ids hp]; simp [hp]
    · rw [purgeS_ops_not s ids hp]; simp [hp]

/-! ## At rest, the persisted verdicts are the spec's -/

/-- With the queue empty, an undecided op has no verdict at any depth. -/
theorem undecided_spec {s : DB F} (h : Inv fam s) (hq : s.queue = []) :
    ∀ n x, s.status x = none → specAt fam s.ops n x = none := by
  intro n
  induction n with
  | zero => intro x _; rfl
  | succ n ih =>
    intro x hx
    unfold specAt
    cases ho : s.ops x with
    | none => rfl
    | some o =>
      simp only
      rcases h.wait x o ho hx with hq' | ⟨hj, _⟩
      · rw [hq] at hq'; cases hq'
      · cases hsp : judge fam o (o.reqs.map (specAt fam s.ops n)) with
        | none => rfl
        | some v =>
          have := judge_mono (g := s.status) hsp (by
            intro r _
            cases hr : s.status r with
            | none => exact Or.inl (ih r hr)
            | some w =>
              cases hn : specAt fam s.ops n r with
              | none => exact Or.inl rfl
              | some w' =>
                obtain ⟨m, hm⟩ := h.sound r w hr
                exact Or.inr (congrArg some (specAt_det hn hm)))
          rw [hj] at this; cases this

/-- At rest, an op's persisted verdict is exactly its spec verdict. -/
theorem status_iff_spec {s : DB F} (h : Inv fam s) (hq : s.queue = []) (x : Id) (v : Verdict F) :
    s.status x = some v ↔ Spec fam s.ops x v := by
  constructor
  · exact h.sound x v
  · intro hv
    cases hx : s.status x with
    | none =>
      obtain ⟨n, hn⟩ := hv
      rw [undecided_spec h hq n x hx] at hn; cases hn
    | some w => exact congrArg some (spec_det (h.sound x w hx) hv)

/-- At rest, the verdicts are a function of the stored ops alone. -/
theorem status_eq_of_ops {s t : DB F} (hs : Inv fam s) (ht : Inv fam t)
    (qs : s.queue = []) (qt : t.queue = []) (hops : s.ops = t.ops) : s.status = t.status := by
  funext x
  cases h1 : s.status x with
  | none =>
    cases h2 : t.status x with
    | none => rfl
    | some w =>
      have := (status_iff_spec hs qs x w).2 (hops ▸ (status_iff_spec ht qt x w).1 h2)
      rw [h1] at this; cases this
  | some v =>
    exact ((status_iff_spec ht qt x v).2 (hops ▸ (status_iff_spec hs qs x v).1 h1)).symm

/-! ## Any interleaving of arrivals and steps -/

/-- The states reachable from empty tables, having received the ops in
L (in some order), with judging steps and purges anywhere in between. A
purge takes what it deleted out of L: L is what was received and is
still held. -/
inductive Reach (fam : Family F) : List Op → DB F → Prop
  | empty : Reach fam [] DB.empty
  | ingest {L s} (o : Op) : Reach fam L s → Reach fam (o :: L) (ingestS o s)
  | step {L s} : Reach fam L s → Reach fam L (stepS fam s)
  | purge {L s} (ids : List Id) : Reach fam L s →
      Reach fam (L.filter fun o => !has (purgeSet fam s ids) o.id) (purgeS fam ids s)

theorem reach_inv {L : List Op} {s : DB F} (h : Reach fam L s) : Inv fam s := by
  induction h with
  | empty => exact inv_empty
  | ingest o _ ih => exact inv_ingest ih o
  | step _ ih => exact inv_step ih
  | purge ids _ ih => exact purge_inv ih ids

theorem reach_drain {L : List Op} {s : DB F} (h : Reach fam L s) (n : Nat) :
    Reach fam L (drainS fam n s) := by
  induction n generalizing s with
  | zero => exact h
  | succ n ih =>
    unfold drainS; split
    · exact Reach.step h
    · exact ih (Reach.step h)

/-- No two received ops share an id (the hash is collision-free on
them). -/
def Distinct (L : List Op) : Prop := ∀ a ∈ L, ∀ b ∈ L, a.id = b.id → a = b

/-- SHA-256 has no collision on these ops' bytes. -/
def CollisionFree (L : List Op) : Prop :=
  ∀ a ∈ L, ∀ b ∈ L, sha256 a.bytes = sha256 b.bytes → a.bytes = b.bytes

/-- **`Distinct` asks nothing of peers:** ids are the hashes of the ops'
bytes (`Op.id_bytes`), so ops can share an id only through a SHA-256
collision, whatever a peer sends. -/
theorem distinct_of_collisionFree {L : List Op} (h : CollisionFree L) : Distinct L := by
  intro a ha b hb hid
  rw [Op.id_bytes, Op.id_bytes] at hid
  exact Codec.encode_inj (h a ha b hb hid)

theorem stepS_ops (s : DB F) : (stepS fam s).ops = s.ops := by
  unfold stepS
  cases s.queue with
  | nil => rfl
  | cons x q =>
    simp only
    cases s.status x with
    | some _ => rfl
    | none =>
      simp only
      cases s.ops x with
      | none => rfl
      | some o =>
        simp only
        cases judge fam o (o.reqs.map s.status) with
        | some v => exact (decideS_fields (fam := fam) x v _).1
        | none => exact waitOnS_ops _ _ _

/-- Every stored op was received, and is stored under its id. -/
theorem reach_stored {L : List Op} {s : DB F} (h : Reach fam L s) :
    ∀ i o, s.ops i = some o → o ∈ L ∧ o.id = i := by
  induction h with
  | empty => intro i o h; cases h
  | @ingest L s o _ ih =>
    intro i p hp
    unfold ingestS at hp
    split at hp
    · have := ih i p hp; exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩
    · change (if i = o.id then some o else s.ops i) = some p at hp
      by_cases hi : i = o.id
      · simp only [hi, ite_true, Option.some.injEq] at hp
        subst hp; exact ⟨List.mem_cons_self .., hi.symm⟩
      · simp only [hi, ite_false] at hp
        have := ih i p hp; exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩
  | step _ ih => intro i o h; rw [stepS_ops] at h; exact ih i o h
  | @purge L s ids _ ih =>
    intro i o h
    by_cases hp : i ∈ purgeSet fam s ids
    · rw [purgeS_ops_mem s ids hp] at h; cases h
    rw [purgeS_ops_not s ids hp] at h
    obtain ⟨hL, rfl⟩ := ih i o h
    exact ⟨List.mem_filter.2 ⟨hL, by simpa using (has_false _ _).2 hp⟩, rfl⟩

/-- Every op received (and not purged since) is stored under its id. -/
theorem reach_held {L : List Op} {s : DB F} (h : Reach fam L s) :
    ∀ o ∈ L, (s.ops o.id).isSome := by
  induction h with
  | empty => intro o h; cases h
  | @ingest L s o _ ih =>
    intro p hp
    unfold ingestS
    split
    · rename_i q hq
      rcases List.mem_cons.1 hp with rfl | hp
      · rw [hq]; rfl
      · exact ih p hp
    · show (if p.id = o.id then some o else s.ops p.id).isSome
      by_cases hi : p.id = o.id
      · simp [hi]
      · simp only [hi, ite_false]
        rcases List.mem_cons.1 hp with rfl | hp
        · exact absurd rfl hi
        · exact ih p hp
  | step _ ih => intro o ho; rw [stepS_ops]; exact ih o ho
  | @purge L s ids _ ih =>
    intro o ho
    obtain ⟨ho, hn⟩ := List.mem_filter.1 ho
    have hp : o.id ∉ purgeSet fam s ids := (has_false _ _).1 (by simpa using hn)
    rw [purgeS_ops_not s ids hp]; exact ih o ho

/-- The stored ops are exactly the ops received and not purged. -/
theorem reach_ops {L : List Op} {s : DB F} (h : Reach fam L s) (hd : Distinct L) :
    ∀ i o, s.ops i = some o ↔ o ∈ L ∧ o.id = i := by
  intro i o
  refine ⟨reach_stored h i o, ?_⟩
  rintro ⟨ho, rfl⟩
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 (reach_held h o ho)
  have := reach_stored h _ p hp
  rw [hp, hd p this.1 o ho this.2]

/-- **Order does not matter.** Two nodes that received the same ops, in
any orders and with any interleaving of judging, hold the same verdicts
once both queues are empty. -/
theorem order_free {L M : List Op} {s t : DB F} (hs : Reach fam L s) (ht : Reach fam M t)
    (hd : Distinct (L ++ M)) (hsame : ∀ o, o ∈ L ↔ o ∈ M)
    (qs : s.queue = []) (qt : t.queue = []) : s.status = t.status := by
  have dL : Distinct L := fun a ha b hb => hd a (List.mem_append_left _ ha) b (List.mem_append_left _ hb)
  have dM : Distinct M := fun a ha b hb => hd a (List.mem_append_right _ ha) b (List.mem_append_right _ hb)
  refine status_eq_of_ops (reach_inv hs) (reach_inv ht) qs qt ?_
  funext i
  cases h1 : s.ops i with
  | none =>
    cases h2 : t.ops i with
    | none => rfl
    | some o =>
      have := (reach_ops ht dM i o).1 h2
      have := (reach_ops hs dL i o).2 ⟨(hsame o).2 this.1, this.2⟩
      rw [h1] at this; cases this
  | some o =>
    have := (reach_ops hs dL i o).1 h1
    exact ((reach_ops ht dM i o).2 ⟨(hsame o).1 this.1, this.2⟩).symm

end Engine
