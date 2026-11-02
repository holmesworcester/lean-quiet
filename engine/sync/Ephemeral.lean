/-
The app's ephemeral log: its working state as ops (where a window is,
later unsent text), judged and read like any op, in memory only
(`Scope.ephemeral`; the store's `intake` drops them, `stored_durable`).
It is a held store rebuilt from its live ops whenever one changes
(`Held.ofOps`, engine/core/Held.lean), so it holds only them, however
long the app runs.

Laws: `ofOps_reach` (the log is an engine history of exactly its ops),
`ofOps_waiting` (no urgent work undone), `ofOps_inv` (the engine's invariant),
`ofOps_valid` (an op of the log that cites nothing is Valid with what its
validator gives), `ofOps_from` (every op the log judged Valid is one of
its ops, with what its validator gave), and `run_eval` (a view run on the
log answers as the model does on its tables, and changes nothing).
-/
import engine.core.Held
import engine.core.View
import engine.core.Project
import engine.sync.ClosureStore
import engine.wire.NodeLaws

namespace Engine.Sync
open Engine

variable {F : Type}

/-- **A view run on a held store answers as on its tables,** and leaves
the store as it was. -/
theorem run_eval [SortKey F] {α : Type} (v : View F α) (h : Held F) :
    ((v.run : HeldM F α).run h) = (v.eval h.db, h) := by
  induction v with
  | pure a => rfl
  | list q k ih => exact ih (Engine.eval h.db q)

/-- **The log is an engine history of exactly its ops.** -/
theorem ofOps_reach (fam : Family F) (L : List Op) :
    ∃ history, Engine.Reach fam history (Held.ofOps fam L).db ∧ ∀ o, o ∈ history ↔ o ∈ L := by
  obtain ⟨history, hr, same⟩ := turn_reachable fam L {} (held_empty_reachable fam)
  refine ⟨history, hr, fun o => ?_⟩
  have := same o
  simpa [Held.ofOps, turn_apply] using this

/-- **Judging the log leaves no urgent work undone** (every op not shared
is urgent, and the log's are ephemeral): a capped turn from empty
(`turn_waiting`). -/
theorem ofOps_waiting (fam : Family F) (L : List Op) : UrgentWaiting fam (Held.ofOps fam L).db :=
  turn_waiting_held fam L {} (held_empty_reachable fam) waiting_empty

/-- **The log keeps the engine's invariant.** -/
theorem ofOps_inv (fam : Family F) (L : List Op) : Inv fam (Held.ofOps fam L).db := by
  obtain ⟨_, hr, _⟩ := ofOps_reach fam L
  exact reach_inv hr

/-- The log stores exactly its ops, under their ids. -/
theorem ofOps_ops (fam : Family F) {L : List Op} (hd : Distinct L) (x : Id) (o : Op) :
    (Held.ofOps fam L).db.ops x = some o ↔ o ∈ L ∧ o.id = x := by
  obtain ⟨history, hr, same⟩ := ofOps_reach fam L
  have hd' : Distinct history := fun a ha b hb => hd a ((same a).1 ha) b ((same b).1 hb)
  rw [reach_ops hr hd' x o, same]

/-- **An op of the log that cites nothing is Valid,** with what its
validator gives. -/
theorem ofOps_valid (fam : Family F) {L : List Op} (hd : Distinct L) {o : Op} (ho : o ∈ L)
    (hr : o.reqs = []) {f : F} (hv : fam.validate o [] = some f) :
    (Held.ofOps fam L).db.status o.id = some (.valid f) := by
  have hstored := (ofOps_ops fam hd o.id o).2 ⟨ho, rfl⟩
  have hspec : Spec fam (Held.ofOps fam L).db.ops o.id (.valid f) := ⟨1, by
    simp only [specAt, hstored, hr, List.map_nil, judge, anyInvalid, allValid, hv, Bool.false_eq_true, ite_false]⟩
  -- The turn's job decides it: it cites nothing.
  have hs : ((Held.ofOps fam L).db.status o.id).isSome := by
    show ((turnCappedS fam drainCap L DB.empty).status o.id).isSome
    refine turn_nil_reqs drainCap L (List.mem_map.2 ⟨o, ho, rfl⟩) ?_ hr
    have := hstored
    change (turnCappedS fam drainCap L DB.empty).ops o.id = some o at this
    rwa [turnCappedS_ops] at this
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 hs
  rw [hw, spec_det ((ofOps_inv fam L).sound _ _ hw) hspec]

/-- **Every op the log judged Valid is one of its ops,** with what its
validator gave for some facts. -/
theorem ofOps_from (fam : Family F) {L : List Op} (hd : Distinct L) {x : Id} {f : F}
    (hx : (Held.ofOps fam L).db.status x = some (.valid f)) :
    ∃ o fs, o ∈ L ∧ o.id = x ∧ fam.validate o fs = some f := by
  obtain ⟨n, hn⟩ := (ofOps_inv fam L).sound x _ hx
  cases n with
  | zero => simp [specAt] at hn
  | succ n =>
    obtain ⟨o, fs, ho, -, hv⟩ := specAt_valid_inv hn
    obtain ⟨hl, hid⟩ := (ofOps_ops fam hd x o).1 ho
    exact ⟨o, fs, hl, hid, hv⟩

end Engine.Sync
