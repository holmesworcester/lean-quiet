/-
What a capped turn leaves queued is carried, and nothing waits forever
(engine/core/TurnLaws.lean has the turn). The queue is first in, first
out: new ops and the waiters a decision wakes join its back, so an op
judge can already decide only moves forward.

- `Ready x o s`: x is stored as o, judge already has its verdict, and x
  is decided or queued. Every part of a turn keeps it (`ready_turn`).
- `rank x s`: 0 once x is decided, else one more than the ops ahead of
  it. No part of a turn raises it, and a turn's drain (a cap of at least
  one) lowers it (`ready_turn`).
- `ready_decides`: in a run of the tables where each step is a turn or
  nothing, and turns recur, a ready op is decided within `rank` turns.
- `spec_eventually`: in such a run of reachable states, once an op's
  closure is held, its spec verdict becomes its status, for good. New
  ops may keep arriving meanwhile.
-/
import engine.core.TurnLaws

namespace Engine
variable {F : Type} {fam : Family F}

/-! ## Place in the queue -/

/-- The ops ahead of x's first place in q. -/
def pos (x : Id) : List Id → Nat
  | [] => 0
  | y :: q => if y = x then 0 else pos x q + 1

theorem pos_append {x : Id} : ∀ {q : List Id}, x ∈ q → ∀ r, pos x (q ++ r) = pos x q
  | [], h, _ => by cases h
  | y :: q, h, r => by
    simp only [List.cons_append, pos]
    by_cases hy : y = x
    · simp [hy]
    · rw [if_neg hy, if_neg hy, pos_append ((List.mem_cons.1 h).resolve_left fun e => hy e.symm) r]

/-- x's rank: 0 once decided, else one more than the ops ahead of it. -/
def rank (x : Id) (s : DB F) : Nat := if (s.status x).isSome then 0 else pos x s.queue + 1

theorem rank_zero {x : Id} {s : DB F} (h : rank x s = 0) : (s.status x).isSome := by
  unfold rank at h; split at h
  · assumption
  · omega

variable (fam) in
/-- x is stored as o, judge has its verdict, and it is decided or queued. -/
def Ready (x : Id) (o : Op) (s : DB F) : Prop :=
  s.ops x = some o ∧ (judge fam o (o.reqs.map s.status)).isSome ∧ ((s.status x).isSome ∨ x ∈ s.queue)

/-- t keeps s's verdicts and ops. -/
def Grows (s t : DB F) : Prop :=
  (∀ y v, s.status y = some v → t.status y = some v) ∧ (∀ y o, s.ops y = some o → t.ops y = some o)

theorem Grows.refl (s : DB F) : Grows s s := ⟨fun _ _ h => h, fun _ _ h => h⟩

theorem Grows.trans {s t u : DB F} (a : Grows s t) (b : Grows t u) : Grows s u :=
  ⟨fun y v h => b.1 y v (a.1 y v h), fun y o h => b.2 y o (a.2 y o h)⟩

theorem Grows.judge {s t : DB F} (g : Grows s t) {o : Op} (h : (judge fam o (o.reqs.map s.status)).isSome) :
    (judge fam o (o.reqs.map t.status)).isSome := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h
  have hb : Below o.reqs s.status t.status := by
    intro r _
    cases hs : s.status r with
    | none => exact Or.inl rfl
    | some w => exact Or.inr (g.1 r w hs).symm
  rw [judge_mono hv hb]; rfl

theorem Grows.isSome {s t : DB F} (g : Grows s t) {x : Id} (h : (s.status x).isSome) : (t.status x).isSome := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h
  rw [g.1 x v hv]; rfl

/-- A table that keeps s's verdicts and ops and only adds to the queue's
back keeps x ready, and its rank. -/
theorem ready_extend {s t : DB F} {x : Id} {o : Op} (g : Grows s t) (hq : ∃ r, t.queue = s.queue ++ r)
    (h : Ready fam x o s) : Ready fam x o t ∧ rank x t ≤ rank x s := by
  obtain ⟨ho, hj, hx⟩ := h
  obtain ⟨r, hr⟩ := hq
  by_cases hd : (s.status x).isSome
  · have := g.isSome hd
    refine ⟨⟨g.2 x o ho, g.judge hj, Or.inl this⟩, ?_⟩
    unfold rank; rw [if_pos this]; exact Nat.zero_le _
  · have hm := hx.resolve_left hd
    refine ⟨⟨g.2 x o ho, g.judge hj, Or.inr (by rw [hr]; exact List.mem_append_left _ hm)⟩, ?_⟩
    unfold rank
    split
    · exact Nat.zero_le _
    · rw [hr, pos_append hm]; exact Nat.le_refl _

/-! ## What each part of a turn does -/

theorem grows_ingest (o : Op) (s : DB F) : Grows s (ingestS o s) := by
  unfold ingestS
  cases h : s.ops o.id with
  | some _ => exact Grows.refl s
  | none =>
    refine ⟨fun y v hv => hv, fun y p hp => ?_⟩
    show (if y = o.id then some o else s.ops y) = some p
    rw [if_neg]; · exact hp
    rintro rfl; rw [h] at hp; cases hp

theorem ingest_queue (o : Op) (s : DB F) : ∃ r, (ingestS o s).queue = s.queue ++ r := by
  unfold ingestS
  cases s.ops o.id with
  | some _ => exact ⟨[], (List.append_nil _).symm⟩
  | none => exact ⟨[o.id], rfl⟩

theorem grows_decide {s : DB F} {y : Id} (hy : s.status y = none) (v : Verdict F) :
    Grows s (decideS fam y v s) := by
  obtain ⟨h1, h2, -, -, -⟩ := decideS_fields (fam := fam) y v s
  refine ⟨fun z w hz => ?_, fun z p hp => by rw [h1]; exact hp⟩
  rw [h2]
  have : z ≠ y := by rintro rfl; rw [hy] at hz; cases hz
  simp only [this, ite_false]; exact hz

theorem grows_waitOn (y : Id) (l : List Id) (s : DB F) : Grows s (waitOnS y l s) := by
  refine ⟨fun z w hz => ?_, fun z p hp => ?_⟩
  · rw [waitOnS_status]; exact hz
  · rw [waitOnS_ops]; exact hp

/-- A step with y at the queue's head, the rest q: it keeps the rest's
tables and adds to their back, and y, undecided and judgeable, is
decided. -/
theorem stepS_pop {s : DB F} {y : Id} {q : List Id} (hq : s.queue = y :: q) :
    Grows { s with queue := q } (stepS fam s) ∧ (∃ r, (stepS fam s).queue = q ++ r) ∧
      (∀ o, s.status y = none → s.ops y = some o → (judge fam o (o.reqs.map s.status)).isSome →
        ((stepS fam s).status y).isSome) := by
  unfold stepS
  rw [hq]
  cases hs : s.status y with
  | some w =>
    simp only [hs]
    exact ⟨Grows.refl _, ⟨[], (List.append_nil _).symm⟩, fun _ h => by cases h⟩
  | none =>
    cases ho : s.ops y with
    | none =>
      simp only [hs, ho]
      exact ⟨Grows.refl _, ⟨[], (List.append_nil _).symm⟩, fun _ _ h => by cases h⟩
    | some o =>
      cases hj : judge fam o (o.reqs.map s.status) with
      | some v =>
        simp only [hs, ho, hj]
        obtain ⟨-, h2, h3, -, -⟩ := decideS_fields (fam := fam) y v { s with queue := q }
        refine ⟨grows_decide (fam := fam) (s := { s with queue := q }) hs v, ⟨_, h3⟩, fun _ _ _ _ => ?_⟩
        rw [h2]; simp
      | none =>
        simp only [hs, ho, hj]
        refine ⟨grows_waitOn _ _ _, ⟨[], by rw [waitOnS_queue, List.append_nil]⟩, fun p _ hp hjp => ?_⟩
        obtain rfl : o = p := by simpa using hp
        rw [hj] at hjp; cases hjp

theorem grows_step (s : DB F) : Grows s (stepS fam s) := by
  cases hq : s.queue with
  | nil => have : stepS fam s = s := by unfold stepS; rw [hq]
           rw [this]; exact Grows.refl s
  | cons y q => exact (stepS_pop hq).1

/-- **A step keeps x ready and never raises its rank; with x queued, it
lowers it.** -/
theorem ready_step {s : DB F} {x : Id} {o : Op} (h : Ready fam x o s) :
    Ready fam x o (stepS fam s) ∧ (rank x (stepS fam s) = 0 ∨ rank x (stepS fam s) < rank x s) := by
  obtain ⟨ho, hj, hx⟩ := h
  cases hq : s.queue with
  | nil =>
    have e : stepS fam s = s := by unfold stepS; rw [hq]
    rw [e]
    have hd : (s.status x).isSome := hx.resolve_right (by rw [hq]; exact List.not_mem_nil)
    refine ⟨⟨ho, hj, hx⟩, Or.inl ?_⟩
    unfold rank; rw [if_pos hd]
  | cons y q =>
    obtain ⟨g, ⟨r, hr⟩, hd⟩ := stepS_pop (fam := fam) hq
    have g' : Grows s (stepS fam s) := Grows.trans (Grows.refl s) g
    by_cases hs : (s.status x).isSome
    · have := g'.isSome hs
      refine ⟨⟨g'.2 x o ho, g'.judge hj, Or.inl this⟩, Or.inl ?_⟩
      unfold rank; rw [if_pos this]
    · have hn : s.status x = none := by simpa using hs
      have hm := hx.resolve_left hs
      rw [hq] at hm
      by_cases hyx : y = x
      · subst hyx
        have := hd o hn ho hj
        refine ⟨⟨g'.2 y o ho, g'.judge hj, Or.inl this⟩, Or.inl ?_⟩
        unfold rank; rw [if_pos this]
      · have hq' : y ≠ x := hyx
        have hmq : x ∈ q := (List.mem_cons.1 hm).resolve_left fun e => hyx e.symm
        refine ⟨⟨g'.2 x o ho, g'.judge hj, Or.inr (by rw [hr]; exact List.mem_append_left _ hmq)⟩, ?_⟩
        unfold rank
        split
        · exact Or.inl rfl
        · right
          rw [hr, pos_append hmq, hq]
          simp only [pos, if_neg hq']
          omega

theorem ready_judgeAhead (b : Bool) (y : Id) {s : DB F} {x : Id} {o : Op} (h : Ready fam x o s) :
    Ready fam x o (judgeAheadS fam b y s).2 ∧ rank x (judgeAheadS fam b y s).2 ≤ rank x s ∧
      Grows s (judgeAheadS fam b y s).2 := by
  rcases judgeAheadS_eq (fam := fam) b y s with e | e <;> rw [e]
  · exact ⟨h, Nat.le_refl _, Grows.refl s⟩
  · obtain ⟨g, hq, -⟩ := stepS_pop (fam := fam) (s := { s with queue := y :: s.queue }) rfl
    have g' : Grows s (stepS fam { s with queue := y :: s.queue }) := g
    exact ⟨(ready_extend g' hq h).1, (ready_extend g' hq h).2, g'⟩

theorem grows_judgeAhead (b : Bool) (y : Id) (s : DB F) : Grows s (judgeAheadS fam b y s).2 := by
  rcases judgeAheadS_eq (fam := fam) b y s with e | e <;> rw [e]
  · exact Grows.refl s
  · exact (stepS_pop (fam := fam) (s := { s with queue := y :: s.queue }) rfl).1

theorem ready_judgeJob : ∀ (xs : List Id) {s : DB F} {x : Id} {o : Op}, Ready fam x o s →
    Ready fam x o (judgeJobS fam xs s).2 ∧ rank x (judgeJobS fam xs s).2 ≤ rank x s ∧
      Grows s (judgeJobS fam xs s).2
  | [], _, _, _, h => ⟨h, Nat.le_refl _, Grows.refl _⟩
  | y :: xs, s, _, _, h => by
    obtain ⟨h1, r1, g1⟩ := ready_judgeAhead (fam := fam) false y h
    obtain ⟨h2, r2, g2⟩ := ready_judgeJob xs h1
    exact ⟨h2, Nat.le_trans r2 r1, g1.trans g2⟩

theorem ready_urgentClose : ∀ (n : Nat) (xs : List Id) {s : DB F} {x : Id} {o : Op}, Ready fam x o s →
    Ready fam x o (urgentCloseS fam n xs s) ∧ rank x (urgentCloseS fam n xs s) ≤ rank x s ∧
      Grows s (urgentCloseS fam n xs s)
  | 0, _, _, _, _, h => ⟨h, Nat.le_refl _, Grows.refl _⟩
  | _ + 1, [], _, _, _, h => ⟨h, Nat.le_refl _, Grows.refl _⟩
  | n + 1, y :: xs, s, _, _, h => by
    obtain ⟨h1, r1, g1⟩ := ready_judgeAhead (fam := fam) true y h
    obtain ⟨h2, r2, g2⟩ := ready_urgentClose n _ h1
    exact ⟨h2, Nat.le_trans r2 r1, g1.trans g2⟩

theorem ready_ingests : ∀ (ops : List Op) {s : DB F} {x : Id} {o : Op}, Ready fam x o s →
    Ready fam x o (ops.foldl (fun s o => ingestS o s) s) ∧
      rank x (ops.foldl (fun s o => ingestS o s) s) ≤ rank x s ∧ Grows s (ops.foldl (fun s o => ingestS o s) s)
  | [], _, _, _, h => ⟨h, Nat.le_refl _, Grows.refl _⟩
  | p :: ops, s, _, _, h => by
    obtain ⟨h1, r1⟩ := ready_extend (grows_ingest p s) (ingest_queue p s) h
    obtain ⟨h2, r2, g2⟩ := ready_ingests ops h1
    exact ⟨h2, Nat.le_trans r2 r1, (grows_ingest p s).trans g2⟩

theorem grows_drain : ∀ (n : Nat) (s : DB F), Grows s (drainS fam n s)
  | 0, s => Grows.refl s
  | n + 1, s => by
    unfold drainS
    split
    · exact grows_step s
    · exact (grows_step s).trans (grows_drain n _)

theorem ready_drain : ∀ (n : Nat) {s : DB F} {x : Id} {o : Op}, Ready fam x o s →
    Ready fam x o (drainS fam n s) ∧ rank x (drainS fam n s) ≤ rank x s
  | 0, _, _, _, h => ⟨h, Nat.le_refl _⟩
  | n + 1, s, x, _, h => by
    unfold drainS
    obtain ⟨h1, r1⟩ := ready_step h
    have r1' : rank x (stepS fam s) ≤ rank x s := by omega
    split
    · exact ⟨h1, r1'⟩
    · obtain ⟨h2, r2⟩ := ready_drain n h1
      exact ⟨h2, Nat.le_trans r2 r1'⟩

/-- A drain of at least one step lowers a queued op's rank. -/
theorem ready_drain_lt (n : Nat) {s : DB F} {x : Id} {o : Op} (h : Ready fam x o s) :
    rank x (drainS fam (n + 1) s) = 0 ∨ rank x (drainS fam (n + 1) s) < rank x s := by
  by_cases hd : (s.status x).isSome
  · left
    have := (grows_drain (fam := fam) (n + 1) s).isSome hd
    unfold rank; rw [if_pos this]
  · have hm := h.2.2.resolve_left hd
    have hne : s.queue.isEmpty = false := by
      cases hq : s.queue with
      | nil => rw [hq] at hm; cases hm
      | cons _ _ => rfl
    simp only [drainS, hne, Bool.false_eq_true, ite_false]
    obtain ⟨h1, r1⟩ := ready_step h
    obtain ⟨_, r2⟩ := ready_drain n h1
    rcases r1 with r1 | r1
    · left; omega
    · by_cases z : rank x (drainS fam n (stepS fam s)) = 0
      · exact Or.inl z
      · right; omega

/-- **A turn keeps x ready, its verdicts and ops, and lowers x's rank
(a cap of at least one).** -/
theorem ready_turn {cap : Nat} (hcap : 0 < cap) (ops : List Op) {s : DB F} {x : Id} {o : Op}
    (h : Ready fam x o s) :
    Ready fam x o (turnCappedS fam cap ops s) ∧
      (rank x (turnCappedS fam cap ops s) = 0 ∨ rank x (turnCappedS fam cap ops s) < rank x s) := by
  obtain ⟨h1, r1, -⟩ := ready_ingests (fam := fam) ops h
  obtain ⟨h2, r2, -⟩ := ready_judgeJob (fam := fam) (ops.map (·.id)) h1
  obtain ⟨h3, r3, -⟩ := ready_urgentClose (fam := fam)
    ((judgeJobS fam (ops.map (·.id)) (ops.foldl (fun s o => ingestS o s) s)).1.length +
      (judgeJobS fam (ops.map (·.id)) (ops.foldl (fun s o => ingestS o s) s)).2.stored.length *
      ((judgeJobS fam (ops.map (·.id)) (ops.foldl (fun s o => ingestS o s) s)).2.stored.length + 1))
    (judgeJobS fam (ops.map (·.id)) (ops.foldl (fun s o => ingestS o s) s)).1 h2
  obtain ⟨k, rfl⟩ : ∃ k, cap = k + 1 := ⟨cap - 1, by omega⟩
  have h4 := (ready_drain (k + 1) h3).1
  have r4 := ready_drain_lt k h3
  refine ⟨h4, ?_⟩
  show rank x (drainS fam (k + 1) _) = 0 ∨ rank x (drainS fam (k + 1) _) < rank x s
  rcases r4 with r4 | r4
  · exact Or.inl r4
  · right; omega

theorem grows_turn (cap : Nat) (ops : List Op) (s : DB F) : Grows s (turnCappedS fam cap ops s) := by
  have g1 : Grows s (ops.foldl (fun s o => ingestS o s) s) := by
    induction ops generalizing s with
    | nil => exact Grows.refl s
    | cons p ops ih => exact (grows_ingest p s).trans (ih _)
  have g2 : ∀ (xs : List Id) (t : DB F), Grows t (judgeJobS fam xs t).2 := by
    intro xs
    induction xs with
    | nil => intro t; exact Grows.refl t
    | cons y xs ih => intro t; exact (grows_judgeAhead false y t).trans (ih _)
  have g3 : ∀ (n : Nat) (xs : List Id) (t : DB F), Grows t (urgentCloseS fam n xs t) := by
    intro n
    induction n with
    | zero => intro _ t; exact Grows.refl t
    | succ n ih =>
      intro xs t
      cases xs with
      | nil => exact Grows.refl t
      | cons y xs => exact (grows_judgeAhead true y t).trans (ih _ _)
  exact g1.trans ((g2 _ _).trans ((g3 _ _ _).trans (grows_drain _ _)))

/-! ## Runs of turns -/

variable (fam) in
/-- One step of a run of the tables: a capped turn of some ops, or
nothing. -/
def TurnStep (cap : Nat) (s t : DB F) : Prop := t = s ∨ ∃ ops, t = turnCappedS fam cap ops s

variable (fam) in
/-- Turns recur: after any step, a later one is a turn. -/
def TurnsRecur (cap : Nat) (st : Nat → DB F) : Prop :=
  ∀ N, ∃ j ≥ N, ∃ ops, st (j + 1) = turnCappedS fam cap ops (st j)

theorem TurnStep.grows {cap : Nat} {s t : DB F} (h : TurnStep fam cap s t) : Grows s t := by
  rcases h with rfl | ⟨ops, rfl⟩
  · exact Grows.refl _
  · exact grows_turn cap ops s

theorem grows_run {cap : Nat} {st : Nat → DB F} (step : ∀ n, TurnStep fam cap (st n) (st (n + 1)))
    (T : Nat) : ∀ d, Grows (st T) (st (T + d))
  | 0 => Grows.refl _
  | d + 1 => (grows_run step T d).trans (step (T + d)).grows

theorem ready_run {cap : Nat} (hcap : 0 < cap) {st : Nat → DB F}
    (step : ∀ n, TurnStep fam cap (st n) (st (n + 1))) {x : Id} {o : Op} (T : Nat) (h : Ready fam x o (st T)) :
    ∀ d, Ready fam x o (st (T + d)) ∧ rank x (st (T + d)) ≤ rank x (st T)
  | 0 => ⟨h, Nat.le_refl _⟩
  | d + 1 => by
    obtain ⟨h1, r1⟩ := ready_run hcap step T h d
    rcases step (T + d) with e | ⟨ops, e⟩
    · rw [show T + (d + 1) = T + d + 1 from rfl, e]; exact ⟨h1, r1⟩
    · rw [show T + (d + 1) = T + d + 1 from rfl, e]
      obtain ⟨h2, r2⟩ := ready_turn hcap ops h1
      exact ⟨h2, by omega⟩

/-- **A ready op is decided**, in a run where turns recur, whatever
else arrives meanwhile. -/
theorem ready_decides {cap : Nat} (hcap : 0 < cap) {st : Nat → DB F}
    (step : ∀ n, TurnStep fam cap (st n) (st (n + 1))) (turns : TurnsRecur fam cap st)
    {x : Id} {o : Op} : ∀ (m T : Nat), rank x (st T) = m → Ready fam x o (st T) →
      ∃ k ≥ T, ((st k).status x).isSome := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro T hm h
    by_cases m0 : m = 0
    · exact ⟨T, Nat.le_refl _, rank_zero (hm.trans m0)⟩
    obtain ⟨j, hj, ops, e⟩ := turns T
    obtain ⟨hr, hle⟩ := ready_run hcap step T h (j - T)
    rw [show T + (j - T) = j by omega] at hr hle
    obtain ⟨h2, r2⟩ := ready_turn hcap ops hr
    rw [← e] at h2 r2
    rcases r2 with r2 | r2
    · exact ⟨j + 1, by omega, rank_zero r2⟩
    · obtain ⟨k, hk, hs⟩ := ih (rank x (st (j + 1))) (by omega) (j + 1) rfl h2
      exact ⟨k, by omega, hs⟩

/-! ## Spec verdicts arrive -/

theorem eventually_all {α : Type} (P : α → Nat → Prop) :
    ∀ (l : List α), (∀ a ∈ l, ∃ k, ∀ j ≥ k, P a j) → ∃ k, ∀ j ≥ k, ∀ a ∈ l, P a j
  | [], _ => ⟨0, fun _ _ a ha => by cases ha⟩
  | a :: l, h => by
    obtain ⟨k1, h1⟩ := h a (List.mem_cons_self ..)
    obtain ⟨k2, h2⟩ := eventually_all P l (fun b hb => h b (List.mem_cons_of_mem _ hb))
    refine ⟨max k1 k2, fun j hj b hb => ?_⟩
    rcases List.mem_cons.1 hb with rfl | hb
    · exact h1 j (by omega)
    · exact h2 j (by omega) b hb

/-- **Once an op's closure is held, its spec verdict becomes its status,
for good**, in a run of reachable states where each step is a turn or
nothing and turns recur. Other ops may keep arriving. -/
theorem spec_eventually {cap : Nat} (hcap : 0 < cap) {st : Nat → DB F}
    (step : ∀ n, TurnStep fam cap (st n) (st (n + 1))) (turns : TurnsRecur fam cap st)
    (inv : ∀ n, Inv fam (st n)) {source : Id → Option Op} {seed : Id} {T : Nat}
    (held : ∀ y o, Sync.Reach source seed y → source y = some o → ∀ j ≥ T, (st j).ops y = some o) :
    ∀ n y v, Sync.Reach source seed y → specAt fam source n y = some v →
      ∃ k ≥ T, ∀ j ≥ k, (st j).status y = some v := by
  intro n
  induction n with
  | zero => intro y v _ h; cases h
  | succ n ih =>
    intro y v hy hv
    simp only [specAt] at hv
    cases ho : source y with
    | none => rw [ho] at hv; cases hv
    | some o =>
      rw [ho] at hv
      -- Each requirement with a verdict at depth n has it, from some turn on.
      obtain ⟨K, hK⟩ := eventually_all
        (fun r j => ∀ w, specAt fam source n r = some w → (st j).status r = some w) o.reqs
        (fun r hr => by
          cases hw : specAt fam source n r with
          | none => exact ⟨0, fun _ _ w h => by cases h⟩
          | some w =>
            obtain ⟨k, -, hk⟩ := ih r w (.step hy ho hr) hw
            exact ⟨k, fun j hj w' h => by cases h; exact hk j hj⟩)
      let K' := max K T
      have hb : Below o.reqs (specAt fam source n) (st K').status := by
        intro r hr
        cases hw : specAt fam source n r with
        | none => exact Or.inl rfl
        | some w => exact Or.inr (hK K' (by omega) r hr w hw).symm
      have hj := judge_mono hv hb
      have hop : (st K').ops y = some o := held y o hy ho K' (by omega)
      have ready : Ready fam y o (st K') := by
        refine ⟨hop, by rw [hj]; rfl, ?_⟩
        cases hs : (st K').status y with
        | some _ => exact Or.inl rfl
        | none =>
          rcases (inv K').wait y o hop hs with hq | ⟨hn, -⟩
          · exact Or.inr hq
          · rw [hj] at hn; cases hn
      obtain ⟨k, hk, hs⟩ := ready_decides hcap step turns _ K' rfl ready
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 hs
      refine ⟨k, by omega, fun j hj => ?_⟩
      have hwj : (st j).status y = some w := by
        have := (grows_run step k (j - k)).1 y w hw
        rwa [show k + (j - k) = j by omega] at this
      have hspec : Spec fam (st j).ops y v :=
        Sync.spec_local fam ⟨n + 1, by simp only [specAt, ho]; exact hv⟩
          (fun z p hz hp => held z p (hy.trans hz) hp j (by omega))
      rw [hwj, spec_det ((inv j).sound y w hwj) hspec]

end Engine
