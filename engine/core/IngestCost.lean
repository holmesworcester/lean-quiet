/-
What taking in and judging an op costs the store, over every store: the
engine's own code (engine/core/Core.lean) counted in `CostT m`, with
`Costs` budgets (the bound template, engine/core/Cost.lean; docs/PERF.md
works `ingest_costs` and `step_costs` through as its example).

- `ingest_costs`: an op taken in costs one read and at most two writes.
- `statuses_costs`, `waitOn_costs`, `indexAll_costs`, `pushAll_costs`:
  a pass over a list costs one door, or two, per element.
- `decide_costs`: recording a verdict costs O(K + W): the K keys its
  fact is filed under, and the W ops that waited on it, woken.
- `step_capped`: with the intake cap (engine/core/Sync.lean), R is the
  constant `maxReqs` on every store fed through intake (`fed_reqs`).
- `step_costs`: judging one queued op costs O(R + K + W), R its
  requirements. Nothing in it grows with the store, but through the
  SQLite assumption (`levels`, a seek's pages); W does grow with an op's
  fan-in: an op that n ops arrived before wakes all n in one step (the
  O(N) table in docs/PERF.md).

What the store returns is assumed only where a bound needs it, per door
(`Sat`): that its ops have at most R requirements (`ReqsLe`), its waiter
lists at most W ops (`WaitersLe`), and the family files a fact under at
most K keys.

The mutant control is in tests/engine/CostCheck.lean: a `waitOn` that
reads every requirement's status again for each one (`waitOnSlow`) is
over `waitOn_costs` for every op of two or more requirements.
-/
import engine.core.CostStore
import engine.core.Sync

namespace Engine
open CostT

/-- Every op the store returns has at most R requirements. -/
def ReqsLe (R : Nat) (r : Option Op) : Prop := ∀ o, r = some o → o.reqs.length ≤ R

/-- A waiter list of at most W ops. -/
def WaitersLe (W : Nat) (ws : List Id) : Prop := ws.length ≤ W

section
variable {F : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Store F m]

/-- **An op taken in costs one read and at most two writes.** -/
theorem ingest_costs (o : Op) :
    Costs { reads := 1, writes := 2, seeks := 3 } (ingest (F := F) (m := CostT m) o) := by
  unfold ingest
  refine costs_bind_le (B := { writes := 2, seeks := 2 }) (costs_charged { reads := 1, seeks := 1 } _)
    (fun r => ?_) (by meter_le)
  cases r with
  | some _ => exact (costs_pure _).mono (by meter_le)
  | none =>
    exact costs_bind_le (costs_charged { writes := 1, seeks := 1 } _)
      (fun _ => costs_charged { writes := 1, seeks := 1 } _) (by meter_le)

/-- **Reading the statuses of l costs a read each.** -/
theorem statuses_costs : ∀ l : List Id,
    Costs { reads := l.length, seeks := l.length } (statuses (F := F) (m := CostT m) l)
  | [] => (costs_pure _).mono (by meter_le)
  | r :: rest => by
    unfold statuses
    exact costs_bind_le (costs_charged { reads := 1, seeks := 1 } _)
      (fun _ => costs_bind (statuses_costs rest) fun _ => costs_pure _) (by meter_le)

/-- **Waiting on l costs a read and at most a write each.** -/
theorem waitOn_costs (x : Id) : ∀ l : List Id,
    Costs { reads := l.length, writes := l.length, seeks := 2 * l.length }
      (waitOn (F := F) (m := CostT m) x l)
  | [] => (costs_pure _).mono (by meter_le)
  | r :: rest => by
    unfold waitOn
    refine costs_bind_le (costs_charged { reads := 1, seeks := 1 } _) (fun s => ?_) (by meter_le)
      (B := { reads := rest.length, writes := rest.length + 1, seeks := 2 * rest.length + 1 })
    dsimp only
    split
    · exact costs_bind_le (costs_charged { writes := 1, seeks := 1 } _)
        (fun _ => waitOn_costs x rest) (by meter_le)
    · exact (waitOn_costs x rest).mono (by meter_le)

theorem indexAll_costs (x : Id) : ∀ l : List ByteArray,
    Costs { writes := l.length, seeks := 2 * l.length } (indexAll (F := F) (m := CostT m) x l)
  | [] => (costs_pure _).mono (by meter_le)
  | k :: rest => by
    unfold indexAll
    exact costs_bind_le (costs_charged { writes := 1, seeks := 2 } _)
      (fun _ => indexAll_costs x rest) (by meter_le)

theorem pushAll_costs : ∀ l : List Id,
    Costs { writes := l.length, seeks := l.length } (pushAll (F := F) (m := CostT m) l)
  | [] => (costs_pure _).mono (by meter_le)
  | w :: rest => by
    unfold pushAll
    exact costs_bind_le (costs_charged { writes := 1, seeks := 1 } _)
      (fun _ => pushAll_costs rest) (by meter_le)

/-- **Recording a verdict costs O(K + W)**: K keys filed, W ops woken. -/
theorem decide_costs (fam : Family F) {K W : Nat} (hK : ∀ x f, (fam.fileKeys x f).length ≤ K)
    (hW : ∀ x, Sat (WaitersLe W) (Store.waiters (F := F) (m := m) x)) (x : Id) (v : Verdict F) :
    Costs { reads := 1, writes := 2 + K + W, seeks := 3 + 2 * K + W, rows := W }
      (decide (F := F) (m := CostT m) fam x v) := by
  unfold decide
  refine costs_bind_le (costs_charged { writes := 1, seeks := 1 } _) (fun _ => ?_) (by meter_le)
    (B := { reads := 1, writes := 1 + K + W, seeks := 2 + 2 * K + W, rows := W })
  -- the woken: a read of the waiter list, charged by its length
  have tail : Costs { reads := 1, writes := 1 + W, seeks := 2 + W, rows := W }
      (do let ws ← Store.waiters (F := F) (m := CostT m) x
          Store.clearWaiters (F := F) (m := CostT m) x
          pushAll (F := F) (m := CostT m) ws) := by
    refine (costs_bindP (A := { reads := 1, seeks := 1, rows := W }) (B := { writes := 1 + W, seeks := 1 + W })
      (hW x) (fun ws (h : ws.length ≤ W) => by meter_le) (fun ws (h : ws.length ≤ W) => ?_)).mono
      (by meter_le)
    exact costs_bind_le (costs_charged { writes := 1, seeks := 1 } _) (fun _ => pushAll_costs ws)
      (by meter_le)
  dsimp only
  cases v with
  | valid f => exact costs_bind_le (indexAll_costs x _) (fun _ => tail) (by have := hK x f; meter_le)
  | invalid => exact tail.mono (by meter_le)

/-- **Judging one queued op costs O(R + K + W)**, whatever the store
holds besides: R its requirements, K the keys its fact is filed under, W
the ops that waited on it. -/
theorem step_costs (fam : Family F) {R K W : Nat} (hK : ∀ x f, (fam.fileKeys x f).length ≤ K)
    (hR : ∀ x, Sat (ReqsLe R) (Store.getOp (F := F) (m := m) x))
    (hW : ∀ x, Sat (WaitersLe W) (Store.waiters (F := F) (m := m) x)) :
    Costs { reads := 4 + 2 * R, writes := 3 + K + W + R, seeks := 7 + 3 * R + 2 * K + W, rows := W }
      (step (F := F) (m := CostT m) fam) := by
  unfold step
  refine costs_bind_le (costs_charged { reads := 1, writes := 1, seeks := 2 } _) (fun x? => ?_) (by meter_le)
    (B := { reads := 3 + 2 * R, writes := 2 + K + W + R, seeks := 5 + 3 * R + 2 * K + W, rows := W })
  cases x? with
  | none => exact (costs_pure _).mono (by meter_le)
  | some x =>
    refine costs_bind_le (costs_charged { reads := 1, seeks := 1 } _) (fun s => ?_) (by meter_le)
      (B := { reads := 2 + 2 * R, writes := 2 + K + W + R, seeks := 4 + 3 * R + 2 * K + W, rows := W })
    cases s with
    | some _ => exact (costs_pure _).mono (by meter_le)
    | none =>
      refine (costs_bindP (A := { reads := 1, seeks := 1 }) (f := fun _ => { reads := 1, seeks := 1 })
        (B := { reads := 1 + 2 * R, writes := 2 + K + W + R, seeks := 3 + 3 * R + 2 * K + W, rows := W })
        (hR x) (fun _ _ => by meter_le) (fun r? hr => ?_)).mono (by meter_le)
      cases r? with
      | none => exact (costs_pure _).mono (by meter_le)
      | some o =>
        have ho : o.reqs.length ≤ R := hr o rfl
        refine costs_bind_le ((statuses_costs o.reqs).mono (B := { reads := R, seeks := R }) (by meter_le))
          (fun sts => ?_) (by meter_le)
          (B := { reads := 1 + R, writes := 2 + K + W + R, seeks := 3 + 2 * R + 2 * K + W, rows := W })
        dsimp only
        split
        · exact costs_bind_le (decide_costs fam hK hW x _) (fun _ => costs_pure _) (by meter_le)
        · exact costs_bind_le (waitOn_costs x o.reqs) (fun _ => costs_pure _) (by meter_le)

/-- **With the intake cap, judging one op costs a constant, O(K + W)**:
R is `maxReqs` on every store fed through intake (`stored_capped`: each
op it holds cites at most `maxReqs`), so the reads are at most
4 + 2 · maxReqs whatever the store holds. -/
theorem step_capped (fam : Family F) {K W : Nat} (hK : ∀ x f, (fam.fileKeys x f).length ≤ K)
    (hR : ∀ x, Sat (ReqsLe maxReqs) (Store.getOp (F := F) (m := m) x))
    (hW : ∀ x, Sat (WaitersLe W) (Store.waiters (F := F) (m := m) x)) :
    Costs { reads := 4 + 2 * maxReqs, writes := 3 + K + W + maxReqs,
            seeks := 7 + 3 * maxReqs + 2 * K + W, rows := W }
      (step (F := F) (m := CostT m) fam) :=
  step_costs fam hK hR hW

end

/-- On the model, a store fed through intake answers every op read
within the cap: the `ReqsLe maxReqs` that `step_capped` asks of the
store, at every state the node reaches. -/
theorem fed_reqs {F : Type} {fam : Family F} {M : List Op} {s : DB F} (h : Fed fam M s) (x : Id) :
    ReqsLe maxReqs (s.ops x) := fun _ hx => stored_capped h hx

/-! ## At every state the node reaches

`step_capped` asks `ReqsLe maxReqs` of the store's every answer, in
every state (`Sat`); the model reaches only states fed through intake
(`Fed`), where `fed_reqs` gives it. Here the bound is taken at each such
state, on the counted run itself (`cr`): judging one op there reads at
most 4 + 2 · maxReqs rows (`step_reads_fed`), whatever the store holds;
what it writes still grows with the op's fan-in (W). -/

section
variable {F : Type}

/-- The model is a lawful monad: a state function, its binds threading
the state. -/
instance : LawfulMonad (Model F) := LawfulMonad.mk'
  (id_map := fun _ => rfl)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun _ _ _ => rfl)

/-- A counted run on the model from state s: value, meter, state. -/
def cr {α : Type} (x : CostT (Model F) α) (s : DB F) : (α × Meter) × DB F := (x.run).run s

theorem cr_bind_meter {α β : Type} (x : CostT (Model F) α) (f : α → CostT (Model F) β) (s : DB F) :
    (cr (x >>= f) s).1.2 = (cr x s).1.2 + (cr (f (cr x s).1.1) (cr x s).2).1.2 := rfl

theorem cr_pure_meter {α : Type} (a : α) (s : DB F) : (cr (pure a : CostT (Model F) α) s).1.2 = 0 := rfl

/-- **On the model, a budget holds at every state.** -/
theorem within_at {α : Type} {g : Meter → Nat} {B : Nat} {x : CostT (Model F) α} (h : Within g B x) (s : DB F) :
    g (cr x s).1.2 ≤ B := by
  obtain ⟨y, hy⟩ := h
  have : cr x s = (((y s).1).1, (y s).2) := by unfold cr; rw [← hy]; rfl
  rw [this]; exact (y s).1.2

end

section
variable {F : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Store F m]

/-- A door charged by its value, under a bound in g for every value. -/
theorem within_chargedBy_all {α : Type} {g : Meter → Nat} {B : Nat} {f : α → Meter} {y : m α}
    (hf : ∀ a, g (f a) ≤ B) : Within g B (CostT.chargedBy f y) :=
  (withinP_chargedBy (P := fun _ => True) ⟨(fun a => ⟨a, trivial⟩) <$> y, by rw [Functor.map_map]; simp⟩
    fun a _ => hf a).within

/-- **Recording a verdict reads one row**, the waiter list, whatever its
length. -/
theorem decide_reads (fam : Family F) (x : Id) (v : Verdict F) :
    Within Meter.reads 1 (decide (F := F) (m := CostT m) fam x v) := by
  unfold decide
  refine within_bind_le (A := 0) (B := 1) ((costs_charged { writes := 1, seeks := 1 } _).field Meter.reads)
    (fun _ => ?_) (by omega)
  have tail : Within Meter.reads 1
      (do let ws ← Store.waiters (F := F) (m := CostT m) x
          Store.clearWaiters (F := F) (m := CostT m) x
          pushAll (F := F) (m := CostT m) ws) :=
    within_bind_le (A := 1) (B := 0) (within_chargedBy_all (fun _ => Nat.le_refl 1)) (fun ws =>
      within_bind_le (A := 0) (B := 0) ((costs_charged { writes := 1, seeks := 1 } _).field Meter.reads)
        (fun _ => ((pushAll_costs ws).field Meter.reads).mono (by simp)) (by omega)) (by omega)
  dsimp only
  cases v with
  | valid f =>
    exact within_bind_le (A := 0) (B := 1) (((indexAll_costs x _).field Meter.reads).mono (by simp))
      (fun _ => tail) (by omega)
  | invalid => exact tail

end

/-- **At every state a node reaches, judging one op reads at most
4 + 2 · maxReqs rows**: the pop, its status, the op, its requirements'
statuses, and the verdict's waiter list or the requirements' statuses
again; the op, read from a store fed through intake, cites at most
`maxReqs`. -/
theorem step_reads_fed {F : Type} {fam : Family F} {M : List Op} {s : DB F} (h : Fed fam M s) :
    (cr (step (F := F) (m := CostT (Model F)) fam) s).1.2.reads ≤ 4 + 2 * maxReqs := by
  unfold step
  rw [cr_bind_meter]
  have popc : ∀ s : DB F, cr (Store.pop (F := F) (m := CostT (Model F))) s =
      (((Model.run (Store.pop (F := F)) s).1, ({ reads := 1, writes := 1, seeks := 2 } : Meter)),
        (Model.run (Store.pop (F := F)) s).2) := fun _ => rfl
  cases hq : s.queue with
  | nil =>
    rw [popc, run_pop_nil s hq]
    simp only [Meter.reads_add, cr_pure_meter, Meter.reads_zero]; omega
  | cons x q =>
    rw [popc, run_pop_cons s x q hq]
    try dsimp only
    rw [cr_bind_meter]
    have stc : cr (Store.getStatus (F := F) (m := CostT (Model F)) x) { s with queue := q } =
        ((s.status x, { reads := 1, seeks := 1 }), { s with queue := q }) := rfl
    rw [stc]
    try dsimp only
    cases hs : s.status x with
    | some _ =>
      simp only [Meter.reads_add, cr_pure_meter, Meter.reads_zero]; omega
    | none =>
      try dsimp only
      rw [cr_bind_meter]
      have opc : cr (Store.getOp (F := F) (m := CostT (Model F)) x) { s with queue := q } =
          ((s.ops x, { reads := 1, seeks := 1 }), { s with queue := q }) := rfl
      rw [opc]
      try dsimp only
      cases ho : s.ops x with
      | none => simp only [Meter.reads_add, cr_pure_meter, Meter.reads_zero]; omega
      | some o =>
        have hc : o.reqs.length ≤ maxReqs := stored_capped h ho
        try dsimp only
        rw [cr_bind_meter]
        have h1 := within_at ((statuses_costs (F := F) (m := Model F) o.reqs).field Meter.reads) { s with queue := q }
        simp only at h1
        generalize hst : cr (statuses (F := F) (m := CostT (Model F)) o.reqs) { s with queue := q } = st at h1 ⊢
        try dsimp only
        split
        · rename_i v _
          rw [cr_bind_meter]
          have h2 := within_at (decide_reads (F := F) (m := Model F) fam x v) st.2
          simp only [Meter.reads_add, cr_pure_meter, Meter.reads_zero] at h1 h2 ⊢
          omega
        · rw [cr_bind_meter]
          have h2 := within_at ((waitOn_costs (F := F) (m := Model F) x o.reqs).field Meter.reads) st.2
          simp only [Meter.reads_add, cr_pure_meter, Meter.reads_zero] at h1 h2 ⊢
          omega

end Engine
