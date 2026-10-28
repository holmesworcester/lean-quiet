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

end Engine
