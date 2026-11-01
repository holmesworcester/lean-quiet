/-
The capped write turn on the model's tables (Core.lean's `turnCapped`),
and what it keeps.

- `judgeAheadS`, `urgentCloseS`, `judgeJobS`, `turnCappedS`: the turn's
  parts on the tables; `run_judgeAhead`, `run_urgentClose`,
  `run_judgeJob`, `run_turnCapped`: what runs is them.
- `reach_judgeAhead`, `reach_turnCapped`: a turn reaches a reachable
  state (`Reach.judge`: an op judged ahead is as if it were at the queue's
  head and stepped), so every law of reachable states holds after it.
-/
import engine.core.Urgent
import engine.core.Budget

namespace Engine
variable {F : Type} (fam : Family F)

/-- `judgeAhead` on the tables: the waiters woken, and the tables after. -/
def judgeAheadS (onlyUrgent : Bool) (x : Id) (s : DB F) : List Id × DB F :=
  match s.status x with
  | some _ => ([], s)
  | none => match s.ops x with
    | none => ([], s)
    | some o =>
      if onlyUrgent && !urgentOf fam o then ([], s) else
      match judge fam o (o.reqs.map s.status) with
      | some v => (s.waits x, decideS fam x v s)
      | none => ([], waitOnS x o.reqs s)

def judgeJobS : List Id → DB F → List Id × DB F
  | [], s => ([], s)
  | x :: xs, s =>
    let a := judgeAheadS fam false x s
    let b := judgeJobS xs a.2
    (a.1 ++ b.1, b.2)

def urgentCloseS : Nat → List Id → DB F → DB F
  | 0, _, s => s
  | _, [], s => s
  | n + 1, x :: xs, s =>
    let a := judgeAheadS fam true x s
    urgentCloseS n (a.1 ++ xs) a.2

/-- The turn on the tables. -/
def turnCappedS (cap : Nat) (ops : List Op) (s : DB F) : DB F :=
  let s1 := ops.foldl (fun s o => ingestS o s) s
  let j := judgeJobS fam (ops.map (·.id)) s1
  let n := j.2.stored.length
  drainS fam cap (urgentCloseS fam (j.1.length + n * (n + 1)) j.1 j.2)

variable {fam}

theorem run_judgeAhead (onlyUrgent : Bool) (x : Id) (s : DB F) :
    (judgeAhead (m := Model F) fam onlyUrgent x).run s = judgeAheadS fam onlyUrgent x s := by
  unfold judgeAhead judgeAheadS
  simp only [Model.run_bind, run_getStatus]
  cases hs : s.status x with
  | some _ => rfl
  | none =>
    simp only [Model.run_bind, run_getOp]
    cases ho : s.ops x with
    | none => rfl
    | some o =>
      simp only
      split
      · rfl
      · simp only [Model.run_bind, run_statuses]
        cases hj : judge fam o (o.reqs.map s.status) with
        | some v => simp only [Model.run_bind, run_waiters, run_decide]; rfl
        | none => simp only [Model.run_bind, run_waitOn]; rfl

theorem run_judgeJob : ∀ (xs : List Id) (s : DB F),
    (judgeJob (m := Model F) fam xs).run s = judgeJobS fam xs s
  | [], s => rfl
  | x :: xs, s => by
    simp only [judgeJob, judgeJobS, Model.run_bind, run_judgeAhead, run_judgeJob xs]; rfl

theorem run_urgentClose : ∀ (n : Nat) (xs : List Id) (s : DB F),
    ((urgentClose (m := Model F) fam n xs).run s).2 = urgentCloseS fam n xs s
  | 0, _, s => rfl
  | n + 1, [], s => rfl
  | n + 1, x :: xs, s => by
    simp only [urgentClose, urgentCloseS, Model.run_bind, run_judgeAhead]
    exact run_urgentClose n _ _

/-- What an op judged ahead does to the tables: nothing, or a step with
it at the queue's head. -/
theorem judgeAheadS_eq (onlyUrgent : Bool) (x : Id) (s : DB F) :
    (judgeAheadS fam onlyUrgent x s).2 = s ∨
      (judgeAheadS fam onlyUrgent x s).2 = stepS fam { s with queue := x :: s.queue } := by
  unfold judgeAheadS
  cases hs : s.status x with
  | some _ => exact Or.inl rfl
  | none =>
    cases ho : s.ops x with
    | none => exact Or.inl rfl
    | some o =>
      simp only
      split
      · exact Or.inl rfl
      · right
        unfold stepS
        simp only [hs, ho]
        cases judge fam o (o.reqs.map s.status) <;> rfl

theorem reach_judgeAhead {L : List Op} {s : DB F} (h : Reach fam L s) (onlyUrgent : Bool) (x : Id) :
    Reach fam L (judgeAheadS fam onlyUrgent x s).2 := by
  rcases judgeAheadS_eq onlyUrgent x s with e | e <;> rw [e]
  · exact h
  · exact Reach.judge x h

theorem reach_judgeJob {L : List Op} : ∀ (xs : List Id) {s : DB F}, Reach fam L s →
    Reach fam L (judgeJobS fam xs s).2
  | [], _, h => h
  | x :: xs, _, h => reach_judgeJob xs (reach_judgeAhead h false x)

theorem reach_urgentClose {L : List Op} : ∀ (n : Nat) (xs : List Id) {s : DB F}, Reach fam L s →
    Reach fam L (urgentCloseS fam n xs s)
  | 0, _, _, h => h
  | n + 1, [], _, h => h
  | n + 1, x :: xs, _, h => reach_urgentClose n _ (reach_judgeAhead h true x)

theorem reach_ingests {L : List Op} : ∀ (ops : List Op) {s : DB F}, Reach fam L s →
    Reach fam (ops.reverse ++ L) (ops.foldl (fun s o => ingestS o s) s)
  | [], _, h => h
  | o :: os, _, h => by
    have := reach_ingests os (Reach.ingest o h)
    simpa [List.reverse_cons] using this

/-- **A turn reaches a reachable state.** -/
theorem reach_turnCapped {L : List Op} {s : DB F} (h : Reach fam L s) (cap : Nat) (ops : List Op) :
    Reach fam (ops.reverse ++ L) (turnCappedS fam cap ops s) :=
  reach_drain (reach_urgentClose _ _ (reach_judgeJob _ (reach_ingests ops h))) cap

/-! ## Urgent work stays settled

`UrgentWaitingBut W s`: every stored urgent op whose closure is all
urgent is decided, or in the worklist W, or not yet judgeable and waiting
on each of its undecided requirements. With W empty it is
`UrgentWaiting`, which gives `UrgentSettled`. -/

variable (fam) in
def UrgentWaitingBut (W : List Id) (s : DB F) : Prop :=
  ∀ x o, s.ops x = some o → UrgentClosed fam s x → s.status x = none →
    x ∈ W ∨ (judge fam o (o.reqs.map s.status) = none ∧ ∀ r ∈ o.reqs, s.status r = none → x ∈ s.waits r)

variable (fam) in
abbrev UrgentWaiting (s : DB F) : Prop := UrgentWaitingBut fam [] s

theorem UrgentWaiting.settled {s : DB F} (h : UrgentWaiting fam s) : UrgentSettled fam s :=
  fun x o ho hc hx => ((h x o ho hc hx).resolve_left (List.not_mem_nil)).1

theorem UrgentWaitingBut.mono {W W' : List Id} {s : DB F} (h : UrgentWaitingBut fam W s)
    (hW : ∀ x ∈ W, x ∈ W') : UrgentWaitingBut fam W' s :=
  fun x o ho hc hx => (h x o ho hc hx).imp (hW x) id

/-- Registering an op's waits keeps it. -/
theorem but_waitOn {W : List Id} {s : DB F} (h : UrgentWaitingBut fam W s) (y : Id) (l : List Id) :
    UrgentWaitingBut fam W (waitOnS y l s) := by
  intro x o ho hc hx
  rw [waitOnS_ops] at ho
  rw [waitOnS_status] at hx ⊢
  have hc' : UrgentClosed fam s x := fun z p hz hp => hc z p (by rwa [waitOnS_ops]) (by rwa [waitOnS_ops])
  refine (h x o ho hc' hx).imp id fun ⟨hj, hw⟩ => ⟨hj, fun r hr hrs => ?_⟩
  exact (mem_waitOnS y l s r x).2 (Or.inl (hw r hr hrs))

/-- Deciding an undecided op y adds its waiters to the worklist. -/
theorem but_decide {W : List Id} {s : DB F} (h : UrgentWaitingBut fam W s) {y : Id} (hy : s.status y = none)
    (v : Verdict F) : UrgentWaitingBut fam (s.waits y ++ W) (decideS fam y v s) := by
  obtain ⟨d1, d2, -, d4, -⟩ := decideS_fields (fam := fam) y v s
  intro x o ho hc hx
  rw [d1] at ho
  have hc' : UrgentClosed fam s x := fun z p hz hp => hc z p (by rwa [d1]) (by rwa [d1])
  have hxy : x ≠ y := by intro e; subst e; rw [d2] at hx; simp at hx
  have hx' : s.status x = none := by rw [d2] at hx; simpa [hxy] using hx
  rcases h x o ho hc' hx' with hw | ⟨hj, hreg⟩
  · exact Or.inl (List.mem_append_right _ hw)
  · by_cases hyr : y ∈ o.reqs
    · exact Or.inl (List.mem_append_left _ (hreg y hyr hy))
    · right
      have hst : o.reqs.map (decideS fam y v s).status = o.reqs.map s.status := by
        apply List.map_congr_left
        intro r hr
        rw [d2]
        have : r ≠ y := fun e => hyr (e ▸ hr)
        simp [this]
      refine ⟨by rw [hst]; exact hj, fun r hr hrs => ?_⟩
      have hry : r ≠ y := fun e => hyr (e ▸ hr)
      rw [d4 r, if_neg hry]
      rw [d2] at hrs
      simp only [hry, ite_false] at hrs
      exact hreg r hr hrs

/-- An op that is decided, or not stored, can leave the worklist. -/
theorem but_drop {L W : List Id} {t : DB F} {y : Id} (h : UrgentWaitingBut fam (L ++ y :: W) t)
    (hy : (t.status y).isSome ∨ t.ops y = none) : UrgentWaitingBut fam (L ++ W) t := by
  intro x o ho hc hx
  rcases h x o ho hc hx with hm | hr
  · left
    rcases List.mem_append.1 hm with hm | hm
    · exact List.mem_append_left _ hm
    · rcases List.mem_cons.1 hm with rfl | hm
      · rcases hy with hy | hy
        · rw [hx] at hy; cases hy
        · rw [hy] at ho; cases ho
      · exact List.mem_append_right _ hm
  · exact Or.inr hr

/-- **An op judged ahead leaves the worklist**: decided (its waiters join
it), waiting, or none of the closure's business. -/
theorem but_judgeAhead {W : List Id} {s : DB F} {y : Id} (h : UrgentWaitingBut fam (y :: W) s)
    (onlyUrgent : Bool) :
    UrgentWaitingBut fam ((judgeAheadS fam onlyUrgent y s).1 ++ W) (judgeAheadS fam onlyUrgent y s).2 := by
  unfold judgeAheadS
  cases hs : s.status y with
  | some w => exact but_drop (L := []) h (Or.inl (by rw [hs]; rfl))
  | none =>
    cases ho : s.ops y with
    | none => exact but_drop (L := []) h (Or.inr ho)
    | some o =>
      simp only
      split
      · rename_i hskip
        intro x p hp hc hx
        rcases h x p hp hc hx with hm | hr
        · rcases List.mem_cons.1 hm with rfl | hm
          · exfalso
            simp only [Bool.and_eq_true, Bool.not_eq_true'] at hskip
            rw [ho] at hp; cases hp
            exact absurd (hc _ o .refl ho) (by rw [hskip.2]; simp)
          · exact Or.inl hm
        · exact Or.inr hr
      · cases hj : judge fam o (o.reqs.map s.status) with
        | some v =>
          have := but_decide (fam := fam) h hs v
          exact but_drop (L := s.waits y) this (Or.inl (by
            rw [(decideS_fields (fam := fam) y v s).2.1]; simp))
        | none =>
          have hw := but_waitOn (fam := fam) h y o.reqs
          intro x p hp hc hx
          rcases hw x p hp hc hx with hm | hr
          · rcases List.mem_cons.1 hm with rfl | hm
            · right
              rw [waitOnS_ops, ho] at hp; cases hp
              rw [waitOnS_status]
              refine ⟨hj, fun r hr hrs => ?_⟩
              exact (mem_waitOnS x o.reqs s r x).2 (Or.inr ⟨rfl, hr, hrs⟩)
            · exact Or.inl hm
          · exact Or.inr hr

/-! ## The turn keeps urgent work settled -/

theorem but_judgeJob : ∀ (xs : List Id) {W : List Id} {s : DB F}, UrgentWaitingBut fam (xs ++ W) s →
    UrgentWaitingBut fam ((judgeJobS fam xs s).1 ++ W) (judgeJobS fam xs s).2
  | [], _, _, h => h
  | x :: xs, W, s, h => by
    have h1 := but_judgeAhead (fam := fam) (W := xs ++ W) h false
    have h2 := but_judgeJob xs (W := (judgeAheadS fam false x s).1 ++ W)
      (h1.mono fun z hz => by
        simp only [List.mem_append] at hz ⊢
        rcases hz with hz | hz | hz
        · exact Or.inr (Or.inl hz)
        · exact Or.inl hz
        · exact Or.inr (Or.inr hz))
    show UrgentWaitingBut fam (((judgeAheadS fam false x s).1 ++
      (judgeJobS fam xs (judgeAheadS fam false x s).2).1) ++ W) (judgeJobS fam xs (judgeAheadS fam false x s).2).2
    refine h2.mono fun z hz => ?_
    simp only [List.mem_append] at hz ⊢
    rcases hz with hz | hz | hz
    · exact Or.inl (Or.inr hz)
    · exact Or.inl (Or.inl hz)
    · exact Or.inr hz

/-- The undecided stored ops. -/
def undecidedS (s : DB F) : Nat := (s.stored.filter fun x => (s.status x).isNone).length

theorem undecided_decide {s : DB F} {y : Id} (hy : s.status y = none) (hs : y ∈ s.stored) (v : Verdict F) :
    undecidedS (decideS fam y v s) + 1 ≤ undecidedS s := by
  obtain ⟨-, d2, -, -, -⟩ := decideS_fields (fam := fam) y v s
  unfold undecidedS
  rw [decideS_stored, d2]
  have := filter_lt s.stored (fun x => (s.status x).isNone)
    (fun x => (if x = y then some v else s.status x).isNone)
    (fun x _ hx => by by_cases e : x = y <;> simp_all) ⟨y, hs, by simp [hy], by simp⟩
  show (List.filter (fun x => (if x = y then some v else s.status x).isNone) s.stored).length + 1 ≤ _
  omega

theorem undecided_waitOn (y : Id) (l : List Id) (s : DB F) : undecidedS (waitOnS y l s) = undecidedS s := by
  unfold undecidedS; rw [waitOnS_stored, waitOnS_status]

theorem waits_le_stored {s : DB F} (hw : WaitsOk s) (hi : Inv fam s) (y : Id) :
    (s.waits y).length ≤ s.stored.length :=
  nodup_length_le (hw y).1 fun z hz => (hi.stored z).2 ((hw y).2 z hz)

/-- **With enough attempts, the closure empties its worklist** and leaves
urgent work settled. -/
theorem urgentClose_waiting {L : List Op} : ∀ (fuel : Nat) (W : List Id) {s : DB F}, Reach fam L s →
    UrgentWaitingBut fam W s → W.length + undecidedS s * (s.stored.length + 1) ≤ fuel →
    UrgentWaiting fam (urgentCloseS fam fuel W s)
  | _, [], s, _, h, _ => by cases ‹Nat› <;> exact h
  | 0, x :: xs, _, _, _, hf => by simp at hf
  | fuel + 1, y :: W, s, hr, h, hf => by
    simp only [urgentCloseS]
    have h1 := but_judgeAhead (fam := fam) (W := W) h true
    have hr1 := reach_judgeAhead hr true y
    refine urgentClose_waiting fuel _ hr1 h1 ?_
    have hi := reach_inv hr
    have hw := waitsOk_reach hr
    have hwl := waits_le_stored hw hi y
    unfold judgeAheadS
    cases hs : s.status y with
    | some _ => simp only [List.nil_append, List.length_cons] at hf ⊢; omega
    | none =>
      cases ho : s.ops y with
      | none => simp only [List.nil_append, List.length_cons] at hf ⊢; omega
      | some o =>
        simp only
        split
        · simp only [List.nil_append, List.length_cons] at hf ⊢; omega
        · cases hj : judge fam o (o.reqs.map s.status) with
          | some v =>
            simp only [List.length_append, List.length_cons] at hf ⊢
            have hys : y ∈ s.stored := (hi.stored y).2 (by rw [ho]; rfl)
            have hu := undecided_decide (fam := fam) hs hys v
            rw [decideS_stored]
            have hm := Nat.mul_le_mul_right (s.stored.length + 1) hu
            rw [Nat.add_mul, Nat.one_mul] at hm
            omega
          | none =>
            simp only [List.nil_append, List.length_cons] at hf ⊢
            rw [undecided_waitOn, waitOnS_stored]; omega

theorem closed_of_extends {s t : DB F} (he : ∀ i o, s.ops i = some o → t.ops i = some o) {x : Id}
    (hc : UrgentClosed fam t x) : UrgentClosed fam s x := by
  intro y o hy ho
  have hy' : Sync.Reach t.ops x y := by
    clear ho
    induction hy with
    | refl => exact .refl
    | step _ hz hr ih => exact .step ih (he _ _ hz) hr
  exact hc y o hy' (he y o ho)

/-- Taking an op in leaves the invariant open only at that op. -/
theorem but_ingest {W : List Id} {s : DB F} (h : UrgentWaitingBut fam W s) (o : Op) :
    UrgentWaitingBut fam (o.id :: W) (ingestS o s) := by
  intro x p hp hc hx
  cases hn : s.ops o.id with
  | some _ =>
    have e : ingestS o s = s := by unfold ingestS; rw [hn]
    rw [e] at hp hc hx ⊢
    exact (h x p hp hc hx).imp (List.mem_cons_of_mem _) id
  | none =>
    have e : ingestS o s = (s.putOp o).push o.id := by unfold ingestS; rw [hn]
    rw [e] at hp hc hx ⊢
    by_cases hxo : x = o.id
    · exact Or.inl (hxo ▸ List.mem_cons_self ..)
    · have hp' : s.ops x = some p := by
        change (if x = o.id then some o else s.ops x) = some p at hp; simpa [hxo] using hp
      have he : ∀ i q, s.ops i = some q → ((s.putOp o).push o.id).ops i = some q := by
        intro i q hq
        change (if i = o.id then some o else s.ops i) = some q
        by_cases hi : i = o.id
        · subst hi; rw [hn] at hq; cases hq
        · simp [hi, hq]
      exact (h x p hp' (closed_of_extends he hc) hx).imp (List.mem_cons_of_mem _) id

theorem but_ingests : ∀ (ops : List Op) {W : List Id} {s : DB F}, UrgentWaitingBut fam W s →
    UrgentWaitingBut fam (ops.reverse.map (·.id) ++ W) (ops.foldl (fun s o => ingestS o s) s)
  | [], _, _, h => h
  | o :: os, W, s, h => by
    have := but_ingests os (but_ingest (fam := fam) h o)
    refine this.mono fun z hz => ?_
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil, List.mem_append,
      List.mem_cons, List.mem_nil_iff, or_false] at hz ⊢
    rcases hz with hz | hz | hz
    · exact Or.inl (Or.inl hz)
    · exact Or.inl (Or.inr hz)
    · exact Or.inr hz

/-- **A step of the queue keeps urgent work settled**: it never decides
an urgent op whose closure is all urgent (none is judgeable), so it
wakes none. -/
theorem waiting_step {s : DB F} (h : UrgentWaiting fam s) : UrgentWaiting fam (stepS fam s) := by
  unfold stepS
  cases hq : s.queue with
  | nil => exact h
  | cons y q =>
    have h0 : UrgentWaiting fam ({ s with queue := q } : DB F) := h
    simp only
    cases hs : s.status y with
    | some _ => exact h0
    | none =>
      simp only
      cases ho : s.ops y with
      | none => exact h0
      | some o =>
        simp only
        cases hj : judge fam o (o.reqs.map s.status) with
        | some v =>
          simp only
          intro x p hp hc hx
          obtain ⟨d1, d2, -, d4, -⟩ := decideS_fields (fam := fam) y v ({ s with queue := q } : DB F)
          rw [d1] at hp
          have hc' : UrgentClosed fam s x := fun z r hz hr => hc z r (by rwa [d1]) (by rwa [d1])
          have hxy : x ≠ y := by intro e; subst e; rw [d2] at hx; simp at hx
          have hx' : s.status x = none := by rw [d2] at hx; simpa [hxy] using hx
          obtain ⟨hjx, hreg⟩ := (h x p hp hc' hx').resolve_left List.not_mem_nil
          have hyr : y ∉ p.reqs := by
            intro hyr
            have hcy := hc'.req hp hyr
            have := ((h y o ho hcy hs).resolve_left List.not_mem_nil).1
            rw [hj] at this; cases this
          right
          have hst : p.reqs.map (decideS fam y v ({ s with queue := q } : DB F)).status = p.reqs.map s.status := by
            apply List.map_congr_left
            intro r hr; rw [d2]
            have : r ≠ y := fun e => hyr (e ▸ hr)
            simp [this]
          refine ⟨by rw [hst]; exact hjx, fun r hr hrs => ?_⟩
          have hry : r ≠ y := fun e => hyr (e ▸ hr)
          rw [d4 r, if_neg hry]
          rw [d2] at hrs; simp only [hry, ite_false] at hrs
          exact hreg r hr hrs
        | none => exact but_waitOn (fam := fam) h0 y o.reqs

theorem waiting_drain {s : DB F} (h : UrgentWaiting fam s) : ∀ n, UrgentWaiting fam (drainS fam n s)
  | 0 => h
  | n + 1 => by
    unfold drainS; split
    · exact waiting_step h
    · exact waiting_drain (waiting_step h) n

theorem undecided_le (s : DB F) : undecidedS s ≤ s.stored.length := List.length_filter_le _ _

/-- **A capped turn keeps urgent work settled**, whatever its job and
whatever it leaves queued: every urgent op whose closure is all urgent is
decided, or not yet judgeable. -/
theorem turn_waiting {L : List Op} {s : DB F} (hr : Reach fam L s) (h : UrgentWaiting fam s)
    (cap : Nat) (ops : List Op) : UrgentWaiting fam (turnCappedS fam cap ops s) := by
  unfold turnCappedS
  apply waiting_drain
  have h1 := but_ingests ops (W := []) h
  have hr1 := reach_ingests ops hr
  have h2 := but_judgeJob (fam := fam) (ops.map (·.id)) (W := [])
    (h1.mono fun z hz => by simpa using hz)
  have hr2 := reach_judgeJob (fam := fam) (ops.map (·.id)) hr1
  generalize hj : judgeJobS fam (ops.map (·.id)) (ops.foldl (fun s o => ingestS o s) s) = j at h2 hr2
  refine urgentClose_waiting _ _ hr2 (by simpa using h2) ?_
  have := undecided_le j.2
  have hm := Nat.mul_le_mul_right (j.2.stored.length + 1) this
  omega

theorem waiting_empty : UrgentWaiting fam (DB.empty : DB F) := by
  intro x o ho; cases ho

end Engine
