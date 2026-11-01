import app.settings.appearance.Proofs
import tests.vacuity.Projection

/-
The app's own ops on top of the node's, witnessed: one real appearance
op (Dark, revision 1, built by the intent the app runs) taken into an
empty store of the node's running family (`Quiet.node`, for any
cryptography and keys) and judged. The store keeps the engine's
invariant, holds the op Valid as an app fact, and the appearance laws
apply to it.
-/

namespace Vacuity.Settings
open Engine

section
variable (C : Community.Crypto) (K : Connection.Keys)

def op : Op := Settings.Appearance.choose 1 .dark
def fact : Quiet.F := .inr (.ofAppearance ⟨1, .dark⟩)
def pending : DB Quiet.F := ingestS op DB.empty
def settled : DB Quiet.F := stepS (Quiet.node C K) pending

theorem owned : Settings.owns op.kind = true := by decide

theorem op_reqs : op.reqs = [] := rfl

theorem judged : (Quiet.node C K).validate op [] = some fact := by
  have := Quiet.node_app (C := C) (K := K) owned []
  simp only [List.map_nil] at this
  rw [this]
  show Option.map Sum.inr (Settings.validate (Settings.Appearance.choose 1 .dark) []) = _
  rw [Settings.Appearance.choose_valid]; rfl

theorem pendingInv : Inv (Quiet.node C K) pending := inv_ingest inv_empty op
theorem settledInv : Inv (Quiet.node C K) (settled C K) := inv_step (pendingInv C K)

theorem shape : settled C K = decideS (Quiet.node C K) op.id (.valid fact) { pending with queue := [] } := by
  have hq : pending.queue = [op.id] := rfl
  have hs : pending.status op.id = none := rfl
  have ho : pending.ops op.id = some op := by
    show (if op.id = op.id then some op else none) = some op
    simp
  have hj : judge (Quiet.node C K) op (op.reqs.map pending.status) = some (.valid fact) := by
    rw [op_reqs]; simp only [List.map_nil, judge, anyInvalid, allValid, judged]; rfl
  unfold settled stepS
  simp only [hq, hs, ho, hj]

theorem valid : (settled C K).status op.id = some (.valid fact) := by
  rw [shape, (decideS_fields op.id (.valid fact) { pending with queue := [] }).2.1]
  simp

/-- The preference read on that store is a stored appearance's, at or
after the one written. -/
theorem newest : ∃ y' f', (Settings.Appearance.current.liftR : View Quiet.F _).eval (settled C K) = (f'.setting, f'.rev) ∧
    (settled C K).status y' = some (.valid (.inr (.ofAppearance f'))) ∧
    Pos.cmp (Settings.Appearance.sortKey ⟨1, .dark⟩, op.id) (Settings.Appearance.sortKey f', y') ≠ .gt :=
  Settings.Appearance.current_newest (settledInv C K) (valid C K)

theorem rightKey : RightKey (settled C K) Settings.Appearance.query.key :=
  Settings.Appearance.query_right (settledInv C K)

theorem stays : (Quiet.node C K).scope op = .local := Settings.Appearance.choose_local 1 .dark

theorem appVerdict : (Quiet.node C K).validate op (([] : List Quiet.AppFact).map .inr) =
    (Settings.validate op []).map .inr := Quiet.node_app owned []

/-- A community op (the projection fixture's, kind 1) keeps its verdict. -/
theorem nodeVerdict : (Quiet.node C K).validate Vacuity.Projection.op (([] : List Connection.F).map .inl) =
    ((Connection.node C K).validate Vacuity.Projection.op []).map .inl :=
  Quiet.node_left (by decide) []
end

theorem honest : Settings.validate (Settings.Appearance.choose 1 .dark) [] =
    some (Settings.Fact.ofAppearance ⟨1, .dark⟩) := Settings.Appearance.choose_valid 1 .dark

/-- The node's hooks' reads, witnessed on the projection fixture's
composed store at rest. -/
theorem hooksRead : Model.run (Lists.list Vacuity.Projection.query : LeftM Unit (Model (Unit ⊕ Unit)) (Answer Unit))
    Vacuity.Projection.settled =
    (eval (Vacuity.Projection.settled.proj Vacuity.Projection.first Vacuity.Projection.second.owns) Vacuity.Projection.query,
      Vacuity.Projection.settled) :=
  left_list Vacuity.Projection.settledInv Vacuity.Projection.atRest Vacuity.Projection.leftKey

end Vacuity.Settings
