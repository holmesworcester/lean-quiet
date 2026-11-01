/-
What capped turns cost, amortized (engine/core/TurnLaws.lean has the
turn). The potential `pot`: the queue's length, plus twice each stored
op's open requirements (an undecided op's undecided requirements; a
decided op's requirements it still waits on). Each attempt of the urgent
closure and each queue step spends at least one; an op taken in adds at
most 1 + 2·(its requirements); nothing else adds any.

- `Tidy`: what the tables always satisfy here: each waiter is a stored
  op requiring its blocker, and the blocker is undecided; the stored
  list names the stored ops once each. Every part of a turn keeps it.
- `decide_pot`, `waitOn_pot`, `ingest_pot`, `step_pot`, `judgeAhead_pot`:
  each part's effect on the potential.
- `close_pot`: the urgent closure's attempts, plus the potential after,
  are at most the potential before plus its worklist. So one turn's
  closure is bounded by what the tables hold, not by its fuel n·(n+1).
- `turn_pot`: **a turn's closure attempts and queue steps, plus the
  potential after, are at most the potential before plus 1 + 2·reqs per
  op taken in**. Summed over turns from empty (`turns_pot`), all of them
  are at most (1 + 2·maxReqs) per op taken in, under the intake cap.
-/
import engine.core.TurnLaws
import engine.core.Sync

namespace Engine
variable {F : Type} {fam : Family F}

/-! ## What the tables satisfy -/

/-- The waits table's meaning and the stored list's shape. -/
structure Tidy (s : DB F) : Prop where
  waits : ∀ r, (s.waits r).Nodup
  req : ∀ r y, y ∈ s.waits r → s.status r = none ∧ ∃ o, s.ops y = some o ∧ r ∈ o.reqs
  nodup : s.stored.Nodup
  stored : ∀ x, x ∈ s.stored ↔ (s.ops x).isSome

theorem tidy_empty : Tidy (DB.empty : DB F) where
  waits _ := List.nodup_nil
  req _ _ h := by cases h
  nodup := List.nodup_nil
  stored x := by simp [DB.empty]

theorem Tidy.waitsOk {s : DB F} (t : Tidy s) : WaitsOk s := fun r =>
  ⟨t.waits r, fun y hy => by obtain ⟨-, o, ho, -⟩ := t.req r y hy; rw [ho]; rfl⟩

theorem Tidy.queue {s : DB F} (t : Tidy s) (q : List Id) : Tidy { s with queue := q } :=
  ⟨t.waits, t.req, t.nodup, t.stored⟩

/-! ## The potential -/

/-- An op's open requirements: undecided, its undecided requirements;
decided, the requirements it still waits on. -/
def opens (s : DB F) (y : Id) : Nat :=
  match s.ops y with
  | none => 0
  | some o => if (s.status y).isNone then (o.reqs.filter fun r => (s.status r).isNone).length
    else (o.reqs.filter fun r => has (s.waits r) y).length

/-- The potential: the queue, and twice the stored ops' open requirements. -/
def pot (s : DB F) : Nat := s.queue.length + 2 * (s.stored.map (opens s)).sum

theorem opens_queue (s : DB F) (q : List Id) : opens { s with queue := q } = opens s := rfl

theorem sum_le_sum {l : List Id} {f g : Id → Nat} (h : ∀ y ∈ l, f y ≤ g y) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h a (List.mem_cons_self ..)) (ih fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem sum_eq_sum {l : List Id} {f g : Id → Nat} (h : ∀ y ∈ l, f y = g y) :
    (l.map f).sum = (l.map g).sum :=
  Nat.le_antisymm (sum_le_sum fun y hy => Nat.le_of_eq (h y hy)) (sum_le_sum fun y hy => Nat.le_of_eq (h y hy).symm)

theorem sum_add (l : List Id) (f g : Id → Nat) :
    (l.map fun y => f y + g y).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons a t ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem sum_ind (l : List Id) (p : Id → Bool) :
    (l.map fun y => if p y then 1 else 0).sum = (l.filter p).length := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    cases h : p a <;> simp only [List.map_cons, List.sum_cons, List.filter_cons, h, ih] <;> simp <;> omega

/-- Each of w (distinct, stored) losing one, and nothing gaining, takes
|w| off the sum. -/
theorem sum_drop {l w : List Id} {f g : Id → Nat} (hw : w.Nodup) (hsub : ∀ y ∈ w, y ∈ l)
    (h : ∀ y ∈ l, f y + (if has w y then 1 else 0) ≤ g y) :
    (l.map f).sum + w.length ≤ (l.map g).sum := by
  have h1 : w.length ≤ (l.filter (has w)).length :=
    nodup_length_le hw (fun y hy => List.mem_filter.2 ⟨hsub y hy, (has_iff w y).2 hy⟩)
  have h2 := sum_le_sum (l := l) (f := fun y => f y + (if has w y then 1 else 0)) h
  rw [sum_add] at h2
  have h3 := sum_ind l (has w)
  omega

theorem has_eq {l l' : List Id} {x : Id} (h : x ∈ l ↔ x ∈ l') : has l x = has l' x := by
  apply Bool.eq_iff_iff.2
  rw [has_iff, has_iff]; exact h

theorem has_nil (x : Id) : has [] x = false := by
  cases h : has [] x
  · rfl
  · exact absurd ((has_iff _ _).1 h) List.not_mem_nil

/-- A filter by a weaker test, short by one when some element passes
only the stronger. -/
theorem filter_drop {α : Type} (L : List α) (p q : α → Bool) (c : Bool) (hsub : ∀ a ∈ L, q a = true → p a = true)
    (hx : c = true → ∃ a ∈ L, p a = true ∧ q a = false) :
    (L.filter q).length + (if c then 1 else 0) ≤ (L.filter p).length := by
  cases c with
  | false => simpa using filter_le L p q hsub
  | true => have := filter_lt L p q hsub (hx rfl); simp only [ite_true]; omega

/-! ## Each part of a turn -/

theorem opens_some {s : DB F} {y : Id} {o : Op} (ho : s.ops y = some o) :
    opens s y = if (s.status y).isNone then (o.reqs.filter fun r => (s.status r).isNone).length
      else (o.reqs.filter fun r => has (s.waits r) y).length := by
  unfold opens; rw [ho]

theorem opens_decide {s : DB F} (t : Tidy s) {x : Id} (hx : s.status x = none) (v : Verdict F) (y : Id) :
    opens (decideS fam x v s) y + (if has (s.waits x) y then 1 else 0) ≤ opens s y := by
  obtain ⟨h1, h2, -, h4, -⟩ := decideS_fields (fam := fam) x v s
  have st : ∀ i, (decideS fam x v s).status i = if i = x then some v else s.status i := fun i => by rw [h2]
  cases ho : s.ops y with
  | none =>
    have hn : has (s.waits x) y = false := by
      cases h : has (s.waits x) y
      · rfl
      · obtain ⟨-, o, ho', -⟩ := t.req x y ((has_iff _ _).1 h); rw [ho] at ho'; cases ho'
    have e1 : opens (decideS fam x v s) y = 0 := by unfold opens; rw [h1, ho]
    have e2 : opens s y = 0 := by unfold opens; rw [ho]
    rw [e1, e2, hn]; simp
  | some o =>
    rw [opens_some (by rw [h1]; exact ho), opens_some ho]
    by_cases hyx : y = x
    · subst hyx
      rw [st y, if_pos rfl, hx]
      simp only [Option.isNone_some, Option.isNone_none, Bool.false_eq_true, ite_false, ite_true]
      refine filter_drop o.reqs _ _ _ (fun r _ hr => ?_) (fun hw => ?_)
      · try dsimp only at hr ⊢
        rw [h4] at hr
        split at hr
        · rw [has_nil] at hr; cases hr
        · rw [(t.req r y ((has_iff _ _).1 hr)).1]; rfl
      · obtain ⟨-, o', ho', hr⟩ := t.req y y ((has_iff _ _).1 hw)
        rw [ho] at ho'; cases ho'
        refine ⟨y, hr, by rw [hx]; rfl, ?_⟩
        try dsimp only
        rw [h4, if_pos rfl, has_nil]
    · have sy : (decideS fam x v s).status y = s.status y := by rw [st, if_neg hyx]
      rw [sy]
      cases hy : s.status y with
      | none =>
        simp only [Option.isNone_none, ite_true]
        refine filter_drop o.reqs _ _ _ (fun r _ hr => ?_) (fun hw => ?_)
        · try dsimp only at hr ⊢
          rw [st] at hr
          split at hr
          · cases hr
          · exact hr
        · obtain ⟨-, o', ho', hr⟩ := t.req x y ((has_iff _ _).1 hw)
          rw [ho] at ho'; cases ho'
          refine ⟨x, hr, by rw [hx]; rfl, ?_⟩
          try dsimp only
          rw [st, if_pos rfl]; rfl
      | some w =>
        simp only [Option.isNone_some, Bool.false_eq_true, ite_false]
        refine filter_drop o.reqs _ _ _ (fun r _ hr => ?_) (fun hw => ?_)
        · try dsimp only at hr ⊢
          rw [h4] at hr
          split at hr
          · rw [has_nil] at hr; cases hr
          · exact hr
        · obtain ⟨-, o', ho', hr⟩ := t.req x y ((has_iff _ _).1 hw)
          rw [ho] at ho'; cases ho'
          refine ⟨x, hr, hw, ?_⟩
          try dsimp only
          rw [h4, if_pos rfl, has_nil]

/-- **Deciding an undecided op**: its waiters move to the queue, each
paying one. -/
theorem decide_pot {s : DB F} (t : Tidy s) {x : Id} (hx : s.status x = none) (v : Verdict F) :
    pot (decideS fam x v s) + (s.waits x).length ≤ pot s ∧ Tidy (decideS fam x v s) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := decideS_fields (fam := fam) x v s
  have st' : ∀ i, (decideS fam x v s).status i = if i = x then some v else s.status i := fun i => by rw [h2]
  have hst := decideS_stored (fam := fam) x v s
  refine ⟨?_, ?_⟩
  · have := sum_drop (l := s.stored) (w := s.waits x) (f := opens (decideS fam x v s)) (g := opens s)
      (t.waits x) (fun y hy => (t.stored y).2 (by obtain ⟨-, o, ho, -⟩ := t.req x y hy; rw [ho]; rfl))
      (fun y _ => opens_decide t hx v y)
    unfold pot; rw [h3, hst, List.length_append]; omega
  · refine ⟨fun r => ?_, fun r y hy => ?_, by rw [hst]; exact t.nodup, fun y => by rw [hst, h1]; exact t.stored y⟩
    · rw [h4]; split
      · exact List.nodup_nil
      · exact t.waits r
    · rw [h4] at hy
      split at hy
      · cases hy
      · rename_i hrx
        obtain ⟨hr, o, ho, hro⟩ := t.req r y hy
        refine ⟨?_, o, by rw [h1]; exact ho, hro⟩
        rw [st' r]; rw [if_neg hrx]; exact hr

/-- **Waiting costs nothing**: the waits it adds are open requirements
already counted. -/
theorem waitOn_pot {s : DB F} (t : Tidy s) {y : Id} {o : Op} (ho : s.ops y = some o) (hy : s.status y = none) :
    pot (waitOnS y o.reqs s) = pot s ∧ Tidy (waitOnS y o.reqs s) := by
  have e : ∀ z, opens (waitOnS y o.reqs s) z = opens s z := by
    intro z
    cases hz : s.ops z with
    | none =>
      have e1 : opens (waitOnS y o.reqs s) z = 0 := by unfold opens; rw [waitOnS_ops, hz]
      have e2 : opens s z = 0 := by unfold opens; rw [hz]
      rw [e1, e2]
    | some p =>
      rw [opens_some (by rw [waitOnS_ops]; exact hz), opens_some hz, waitOnS_status]
      split
      · rfl
      · rename_i hzd
        have hzy : z ≠ y := by rintro rfl; rw [hy] at hzd; exact hzd rfl
        congr 1
        apply List.filter_congr
        intro r _
        exact has_eq (by rw [mem_waitOnS]; simp [hzy])
  refine ⟨?_, ?_⟩
  · unfold pot; rw [waitOnS_queue, waitOnS_stored, show opens (waitOnS y o.reqs s) = opens s from funext e]
  · have wk := waitsOk_waitOnS t.waitsOk (x := y) (by rw [ho]; rfl) o.reqs
    refine ⟨fun r => (wk r).1, fun r z hz => ?_, by rw [waitOnS_stored]; exact t.nodup,
      fun z => by rw [waitOnS_stored, waitOnS_ops]; exact t.stored z⟩
    rw [waitOnS_status, waitOnS_ops]
    rcases (mem_waitOnS y o.reqs s r z).1 hz with hz | ⟨rfl, hr, hs⟩
    · exact t.req r z hz
    · exact ⟨hs, o, ho, hr⟩

/-- **An op taken in adds at most 1 + 2·(its requirements).** -/
theorem ingest_pot {s : DB F} (t : Tidy s) (o : Op) :
    pot (ingestS o s) ≤ pot s + 1 + 2 * o.reqs.length ∧ Tidy (ingestS o s) := by
  unfold ingestS
  cases hn : s.ops o.id with
  | some _ => refine ⟨?_, t⟩; show pot s ≤ _; omega
  | none =>
    simp only
    have hnot : o.id ∉ s.stored := fun h => by have := (t.stored _).1 h; rw [hn] at this; cases this
    have hins : ins s.stored o.id = s.stored ++ [o.id] := by
      unfold ins; rw [if_neg]; intro h; exact hnot ((has_iff _ _).1 h)
    have same : ∀ z ∈ s.stored, opens ((s.putOp o).push o.id) z = opens s z := by
      intro z hz
      have hzo : z ≠ o.id := fun e => hnot (e ▸ hz)
      unfold opens
      show (match (if z = o.id then some o else s.ops z) with
        | none => 0
        | some p => if (s.status z).isNone then (p.reqs.filter fun r => (s.status r).isNone).length
          else (p.reqs.filter fun r => has (s.waits r) z).length) = _
      rw [if_neg hzo]
    refine ⟨?_, ?_⟩
    · have hlast : opens ((s.putOp o).push o.id) o.id ≤ o.reqs.length := by
        have e : ((s.putOp o).push o.id).ops o.id = some o := by simp [DB.push, DB.putOp]
        unfold opens; simp only [e]
        split <;> exact List.length_filter_le _ _
      unfold pot
      show (s.queue ++ [o.id]).length + 2 * ((ins s.stored o.id).map _).sum ≤ _
      rw [hins, List.map_append, List.sum_append, sum_eq_sum same, List.length_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil]
      omega
    · refine ⟨t.waits, fun r y hy => ?_, ?_, fun z => ?_⟩
      · obtain ⟨hr, p, hp, hrp⟩ := t.req r y hy
        refine ⟨hr, p, ?_, hrp⟩
        show (if y = o.id then some o else s.ops y) = some p
        rw [if_neg]; · exact hp
        rintro rfl; rw [hn] at hp; cases hp
      · show (ins s.stored o.id).Nodup; exact ins_nodup t.nodup
      · show z ∈ ins s.stored o.id ↔ (if z = o.id then some o else s.ops z).isSome
        rw [mem_ins]
        by_cases hz : z = o.id
        · simp [hz]
        · simp only [hz, or_false, ite_false]; exact t.stored z

/-- **A queue step pays one.** -/
theorem step_pot {s : DB F} (t : Tidy s) :
    pot (stepS fam s) + (if s.queue.isEmpty then 0 else 1) ≤ pot s ∧ Tidy (stepS fam s) := by
  cases hq : s.queue with
  | nil =>
    have e : stepS fam s = s := by unfold stepS; rw [hq]
    rw [e]; exact ⟨by simp, t⟩
  | cons y q =>
    have t1 := t.queue q
    have p1 : pot { s with queue := q } + 1 = pot s := by
      unfold pot; rw [opens_queue, hq]; simp only [List.length_cons]; omega
    simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false]
    unfold stepS
    rw [hq]
    cases hs : s.status y with
    | some w => simp only [hs]; exact ⟨by omega, t1⟩
    | none =>
      cases ho : s.ops y with
      | none => simp only [hs, ho]; exact ⟨by omega, t1⟩
      | some o =>
        cases hj : judge fam o (o.reqs.map s.status) with
        | some v =>
          simp only [hs, ho, hj]
          obtain ⟨d1, d2⟩ := decide_pot (fam := fam) t1 (x := y) hs v
          exact ⟨by omega, d2⟩
        | none =>
          simp only [hs, ho, hj]
          obtain ⟨w1, w2⟩ := waitOn_pot (s := { s with queue := q }) t1 ho hs
          exact ⟨by omega, w2⟩

/-- **An op judged ahead pays for what it wakes.** -/
theorem judgeAhead_pot {s : DB F} (t : Tidy s) (b : Bool) (x : Id) :
    pot (judgeAheadS fam b x s).2 + (judgeAheadS fam b x s).1.length ≤ pot s ∧ Tidy (judgeAheadS fam b x s).2 := by
  unfold judgeAheadS
  cases hs : s.status x with
  | some _ => exact ⟨by simp, t⟩
  | none =>
    cases ho : s.ops x with
    | none => exact ⟨by simp, t⟩
    | some o =>
      simp only
      split
      · exact ⟨by simp, t⟩
      · cases hj : judge fam o (o.reqs.map s.status) with
        | some v => exact decide_pot t hs v
        | none =>
          obtain ⟨w1, w2⟩ := waitOn_pot t ho hs
          exact ⟨by simp [w1], w2⟩

theorem judgeJob_pot : ∀ (xs : List Id) {s : DB F}, Tidy s →
    pot (judgeJobS fam xs s).2 + (judgeJobS fam xs s).1.length ≤ pot s ∧ Tidy (judgeJobS fam xs s).2
  | [], _, t => ⟨by simp [judgeJobS], t⟩
  | x :: xs, s, t => by
    obtain ⟨a1, a2⟩ := judgeAhead_pot (fam := fam) t false x
    obtain ⟨b1, b2⟩ := judgeJob_pot xs a2
    refine ⟨?_, b2⟩
    show pot (judgeJobS fam xs (judgeAheadS fam false x s).2).2 +
      ((judgeAheadS fam false x s).1 ++ (judgeJobS fam xs (judgeAheadS fam false x s).2).1).length ≤ _
    rw [List.length_append]; omega

variable (fam) in
/-- The urgent closure's attempts: one per op it takes off its worklist. -/
def closeAttempts : Nat → List Id → DB F → Nat
  | 0, _, _ => 0
  | _, [], _ => 0
  | n + 1, x :: xs, s => 1 + closeAttempts n ((judgeAheadS fam true x s).1 ++ xs) (judgeAheadS fam true x s).2

/-- **The urgent closure's attempts are paid by the potential and its
worklist**, whatever its fuel. -/
theorem close_pot : ∀ (n : Nat) (W : List Id) {s : DB F}, Tidy s →
    pot (urgentCloseS fam n W s) + closeAttempts fam n W s ≤ pot s + W.length ∧ Tidy (urgentCloseS fam n W s)
  | 0, _, _, t => ⟨by simp [urgentCloseS, closeAttempts], t⟩
  | _ + 1, [], _, t => ⟨by simp [urgentCloseS, closeAttempts], t⟩
  | n + 1, x :: xs, s, t => by
    obtain ⟨a1, a2⟩ := judgeAhead_pot (fam := fam) t true x
    obtain ⟨b1, b2⟩ := close_pot n ((judgeAheadS fam true x s).1 ++ xs) a2
    refine ⟨?_, b2⟩
    simp only [urgentCloseS, closeAttempts]
    rw [List.length_append] at b1
    simp only [List.length_cons]
    omega

/-- **What runs reports its attempts**: the running closure's count is
`closeAttempts`. -/
theorem run_urgentClose_count : ∀ (n : Nat) (xs : List Id) (s : DB F),
    ((urgentClose (m := Model F) fam n xs).run s).1 = closeAttempts fam n xs s
  | 0, _, _ => rfl
  | _ + 1, [], _ => rfl
  | n + 1, x :: xs, s => by
    simp only [urgentClose, closeAttempts, Model.run_bind, run_judgeAhead]
    show ((urgentClose (m := Model F) fam n _).run _).1 + 1 = _
    rw [run_urgentClose_count n]; omega

variable (fam) in
/-- The queue steps a drain takes: those with something queued. -/
def drainPops : Nat → DB F → Nat
  | 0, _ => 0
  | n + 1, s => if s.queue.isEmpty then 0 else 1 + drainPops n (stepS fam s)

theorem drain_pot : ∀ (n : Nat) {s : DB F}, Tidy s →
    pot (drainS fam n s) + drainPops fam n s ≤ pot s ∧ Tidy (drainS fam n s)
  | 0, _, t => ⟨by simp [drainS, drainPops], t⟩
  | n + 1, s, t => by
    obtain ⟨a1, a2⟩ := step_pot (fam := fam) t
    unfold drainS drainPops
    cases he : s.queue.isEmpty with
    | true => simp only [he, ite_true] at a1 ⊢; exact ⟨by omega, a2⟩
    | false =>
      simp only [he, Bool.false_eq_true, ite_false] at a1 ⊢
      obtain ⟨b1, b2⟩ := drain_pot n a2
      exact ⟨by omega, b2⟩

theorem ingests_pot : ∀ (ops : List Op) {s : DB F}, Tidy s →
    pot (ops.foldl (fun s o => ingestS o s) s) ≤ pot s + (ops.map fun o => 1 + 2 * o.reqs.length).sum ∧
      Tidy (ops.foldl (fun s o => ingestS o s) s)
  | [], _, t => ⟨by simp, t⟩
  | o :: ops, s, t => by
    obtain ⟨a1, a2⟩ := ingest_pot t o
    obtain ⟨b1, b2⟩ := ingests_pot ops a2
    refine ⟨?_, b2⟩
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    omega

variable (fam) in
/-- A turn's urgent-closure attempts and queue steps. -/
def turnWork (cap : Nat) (ops : List Op) (s : DB F) : Nat :=
  let s1 := ops.foldl (fun s o => ingestS o s) s
  let j := judgeJobS fam (ops.map (·.id)) s1
  let n := j.2.stored.length
  closeAttempts fam (j.1.length + n * (n + 1)) j.1 j.2 +
    drainPops fam cap (urgentCloseS fam (j.1.length + n * (n + 1)) j.1 j.2)

variable (fam) in
/-- A turn's urgent-closure attempts. -/
def turnAttempts (cap : Nat) (ops : List Op) (s : DB F) : Nat :=
  let s1 := ops.foldl (fun s o => ingestS o s) s
  let j := judgeJobS fam (ops.map (·.id)) s1
  let n := j.2.stored.length
  closeAttempts fam (j.1.length + n * (n + 1)) j.1 j.2

/-- **The running turn reports `turnAttempts`.** -/
theorem run_turnCapped_count (cap : Nat) (ops : List Op) (s : DB F) :
    ((turnCapped (m := Model F) fam cap ops).run s).1 = turnAttempts fam cap ops s := by
  unfold turnCapped turnAttempts
  simp only [Model.run_bind, run_ingestEach, run_judgeJob, run_countOps]
  show ((urgentClose (m := Model F) fam _ _).run _).1 = _
  rw [run_urgentClose_count]; rfl

theorem turnAttempts_le (cap : Nat) (ops : List Op) (s : DB F) : turnAttempts fam cap ops s ≤ turnWork fam cap ops s := by
  simp only [turnAttempts, turnWork]; omega

/-- **A turn's urgent-closure attempts and queue steps, plus the potential
after, are at most the potential before plus 1 + 2·reqs per op taken
in**, and the turn keeps the tables tidy. -/
theorem turn_pot (cap : Nat) (ops : List Op) {s : DB F} (t : Tidy s) :
    pot (turnCappedS fam cap ops s) + turnWork fam cap ops s ≤
      pot s + (ops.map fun o => 1 + 2 * o.reqs.length).sum ∧ Tidy (turnCappedS fam cap ops s) := by
  obtain ⟨a1, a2⟩ := ingests_pot ops t
  obtain ⟨b1, b2⟩ := judgeJob_pot (fam := fam) (ops.map (·.id)) a2
  generalize hj : judgeJobS fam (ops.map (·.id)) (ops.foldl (fun s o => ingestS o s) s) = j at b1 b2
  obtain ⟨c1, c2⟩ := close_pot (fam := fam) (j.1.length + j.2.stored.length * (j.2.stored.length + 1)) j.1 b2
  obtain ⟨d1, d2⟩ := drain_pot (fam := fam) cap c2
  simp only [turnCappedS, turnWork, hj]
  exact ⟨by omega, d2⟩

/-! ## Runs of turns -/

variable (fam) in
/-- Turns of these jobs, one after another. -/
def runTurns (cap : Nat) : List (List Op) → DB F → DB F
  | [], s => s
  | ops :: rest, s => runTurns cap rest (turnCappedS fam cap ops s)

variable (fam) in
/-- Their urgent-closure attempts and queue steps, all together. -/
def runWork (cap : Nat) : List (List Op) → DB F → Nat
  | [], _ => 0
  | ops :: rest, s => turnWork fam cap ops s + runWork cap rest (turnCappedS fam cap ops s)

/-- What a job's ops may add to the potential. -/
def credit (ops : List Op) : Nat := (ops.map fun o => 1 + 2 * o.reqs.length).sum

theorem turns_pot (cap : Nat) : ∀ (jobs : List (List Op)) {s : DB F}, Tidy s →
    pot (runTurns fam cap jobs s) + runWork fam cap jobs s ≤ pot s + (jobs.map credit).sum
  | [], _, _ => by simp [runTurns, runWork]
  | ops :: rest, s, t => by
    obtain ⟨a1, a2⟩ := turn_pot (fam := fam) cap ops t
    have := turns_pot cap rest a2
    simp only [runTurns, runWork, List.map_cons, List.sum_cons, credit] at this a1 ⊢
    omega

theorem credit_capped : ∀ {ops : List Op}, (∀ o ∈ ops, o.capped = true) →
    credit ops ≤ (1 + 2 * maxReqs) * ops.length
  | [], _ => by simp [credit]
  | o :: ops, h => by
    have ho : o.reqs.length ≤ maxReqs := by
      have := h o (List.mem_cons_self ..); unfold Op.capped at this; simpa using this
    have := credit_capped (ops := ops) fun p hp => h p (List.mem_cons_of_mem _ hp)
    simp only [credit, List.map_cons, List.sum_cons, List.length_cons] at this ⊢
    rw [Nat.mul_succ]
    omega

theorem pot_empty : pot (DB.empty : DB F) = 0 := rfl

/-- **Over any run of capped turns from empty, all urgent-closure attempts
and queue steps together are at most (1 + 2·maxReqs) per op taken in**,
whatever the fuel each closure is given. -/
theorem run_work_capped (cap : Nat) (jobs : List (List Op)) (h : ∀ ops ∈ jobs, ∀ o ∈ ops, o.capped = true) :
    runWork fam cap jobs DB.empty ≤ (1 + 2 * maxReqs) * (jobs.map List.length).sum := by
  have h1 := turns_pot (fam := fam) cap jobs tidy_empty
  rw [pot_empty] at h1
  have h2 : (jobs.map credit).sum ≤ (1 + 2 * maxReqs) * (jobs.map List.length).sum := by
    clear h1
    induction jobs with
    | nil => simp
    | cons ops rest ih =>
      have a := credit_capped (h ops (List.mem_cons_self ..))
      have b := ih fun o ho => h o (List.mem_cons_of_mem _ ho)
      simp only [List.map_cons, List.sum_cons, Nat.mul_add]
      omega
  omega

end Engine
