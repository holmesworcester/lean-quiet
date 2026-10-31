import engine.core.Project
import engine.core.WindowMutants

namespace Vacuity.Projection
open Engine
attribute [local instance] lawfulBEqByteArray

def first : Family Unit := Mutants.fam
def second : Family₂ Unit Unit where
  validate _ _ := some ()
  keys _ := ["local/sessions".toUTF8]
  scope _ := .local
  owns k := k == 2

def op : Op := Op.make 1 [] "Alice: hello Bob".toUTF8
def combined : Family (Unit ⊕ Unit) := first.sum second
def pending : DB (Unit ⊕ Unit) := ingestS op DB.empty
def settled : DB (Unit ⊕ Unit) := stepS combined pending

theorem pendingInv : Inv combined pending := inv_ingest inv_empty op
theorem settledInv : Inv combined settled := inv_step pendingInv

theorem shape : settled = decideS combined op.id (.valid (.inl ()))
    { pending with queue := [] } := by
  simp [settled, pending, stepS, ingestS, DB.empty, DB.putOp, DB.push]
  rfl

theorem atRest : settled.queue = [] := by
  rw [shape, (decideS_fields op.id (.valid (.inl ())) { pending with queue := [] }).2.2.1]
  rfl

theorem valid : settled.status op.id = some (.valid (.inl ())) := by
  rw [shape, (decideS_fields op.id (.valid (.inl ())) { pending with queue := [] }).2.1]
  simp

theorem filedRow : op.id ∈ settled.idx Mutants.k :=
  settledInv.idx _ _ |>.2 ⟨.inl (), valid, by simp [combined, first, Mutants.fam, Family.fileKeys, Family.sum]⟩

theorem leftKey : LeftKey settled Mutants.k := by
  intro x hx
  rw [shape] at hx
  obtain h | ⟨rfl, f, hf, _⟩ := (decideS_fields op.id (.valid (.inl ())) { pending with queue := [] }).2.2.2.2 _ _ |>.1 hx
  · cases h
  · exact ⟨(), valid⟩

theorem validatesLeft : combined.validate op (([] : List Unit).map Sum.inl) =
    (first.validate op []).map Sum.inl := sum_left first second op [] (by decide)

theorem scopeLeft : combined.scope op = first.scope op := sum_scope_left first second op (by decide)

theorem specLeft : Spec combined settled.ops op.id (.valid (.inl ())) ↔
    Spec first (leftOps second.owns settled.ops) op.id (.valid ()) := spec_sum_left

theorem projectedIndex : op.id ∈ (settled.proj first second.owns).idx Mutants.k ↔
    op.id ∈ settled.idx Mutants.k ∧ leftValid (settled.status op.id) = true := mem_proj_idx _ _

theorem actualProjectedRow : op.id ∈ (settled.proj first second.owns).idx Mutants.k :=
  projectedIndex.mpr ⟨filedRow, by rw [valid]; rfl⟩

def query : ListQ := { key := Mutants.k, limit := some 50 }
theorem matchingRows : matching settled query = (matching (settled.proj first second.owns) query).map inlRow :=
  matching_proj settledInv atRest leftKey

theorem evalRows : eval settled query = ⟨(eval (settled.proj first second.owns) query).rows.map inlRow,
    (eval (settled.proj first second.owns) query).inRange, (eval (settled.proj first second.owns) query).total⟩ :=
  eval_proj settledInv atRest leftKey

def view : View Unit (Answer Unit) := View.read query
theorem readsLeft : view.Reads (LeftKey settled) := View.Reads.read leftKey

theorem viewRows : (view.liftL : View (Unit ⊕ Unit) (Answer Unit)).eval settled =
    view.eval (settled.proj first second.owns) := view_proj settledInv atRest readsLeft

-- The whole result is retained: invariant, empty queue, exact op ownership,
-- valid facts and agreement for every appropriately keyed view.
def wholeProjection := sum_project settledInv atRest

theorem specVerdictPresent : specVerdict combined settled.ops op.id = some (.valid (.inl ())) :=
  specVerdict_eq_some.mpr (settledInv.sound _ _ valid)

def row : Pos × Unit := ((⟨#[0]⟩, op.id), ())
def otherRow : Pos × Unit := ((⟨#[1]⟩, "other-message".toUTF8), ())
theorem insertionMap : insertBy (inlRow (B := Unit) row) ([otherRow].map inlRow) =
    (insertBy row [otherRow]).map inlRow := insertBy_map (g := inlRow (B := Unit)) (fun _ => rfl) row [otherRow]
theorem sortingMap : sortPos ([otherRow, row].map (inlRow (B := Unit))) =
    (sortPos [otherRow, row]).map inlRow := sortPos_map (g := inlRow (B := Unit)) (fun _ => rfl) _

def unleft : Pos × (Unit ⊕ Unit) → Option (Pos × Unit)
  | (p, .inl f) => some (p, f)
  | (_, .inr _) => none
theorem filteringMap : ([otherRow, row].map (inlRow (B := Unit))).filterMap unleft = [otherRow, row] :=
  filterMap_inlRow (fun _ => rfl) _

end Vacuity.Projection
