import engine.core.WindowRead
import engine.core.WindowCost
import engine.core.WindowMutants

namespace Vacuity.Query
open Engine
attribute [local instance] lawfulBEqByteArray

def listKey : ByteArray := "community/alice-bob/messages".toUTF8
def pos1 : Pos := (⟨#[1]⟩, "message-1".toUTF8)
def pos2 : Pos := (⟨#[2]⟩, "message-2".toUTF8)
def cost : SeekCost := ⟨2, 1, 100000⟩
def page : ListQ := { key := listKey, limit := some 50 }
def ranged : ListQ := { page with after := some pos1, cap := 200 }
def rowStmt : Stmt := .rows listKey [] none none true (some 50)

theorem pageCost : planCost cost 100000 (readPlan page page.key []) ≤
    2 * cost.seek + 50 * (cost.step + cost.seek) := readPlan_cost cost 100000 50 rfl rfl rfl rfl

theorem rangeCost : planCost cost 100000 (readPlan ranged ranged.key []) ≤
    3 * cost.seek + 50 * (cost.step + cost.seek) + ranged.cap * cost.step :=
  readPlan_cost_range cost 100000 50 rfl rfl (by decide)

theorem overallCost : planCost cost 100000 (readPlan ranged listKey []) ≤
    (ranged.also.length + 1) * cost.seek +
    3 * (cost.seek + 100000 * (cost.step + ( ([] : List ByteArray).length + 1) * cost.seek)) :=
  readPlan_cost_le cost 100000 ranged listKey []

theorem statementCost : rowStmt.cost cost 100000 ≤
    cost.seek + 100000 * (cost.step + (([] : List ByteArray).length + 1) * cost.seek) :=
  plan_stmt_cost cost 100000 (q := page) (k := listKey) (others := []) (by
    simp [rowStmt, listPlan, page, Plan.stmts, splitOf])

theorem rowsWalkBound : rowStmt.walks 100000 ≤ 100000 := Stmt.walks_le 100000 rowStmt
example : rowStmt.walks 100000 = 50 := by decide

-- A 31-row side next to a 100000-row side: doubling bounds reach the
-- smaller side, and the algorithm counts exactly rather than sampling.
theorem sideCounter : (sideCount 31 100000 true (some 16)).run (2, 5) = (16, (3, 21)) :=
  sideCount_run 31 100000 true (some 16) (2, 5)
theorem splitExact : ((splitWalk (sideCount 31 100000) 100031 10 4).run (0, 0)).1 = 31 :=
  splitWalk_exact 31 100000 10 4 (0, 0)
theorem splitSteps : ((splitWalk (sideCount 31 100000) 100031 10 4).run (0, 0)).2.1 ≤ 0 + 2 * 3 + 2 ∧
    ((splitWalk (sideCount 31 100000) 100031 10 4).run (0, 0)).2.2 ≤
    0 + (if min 31 100000 < 4 then 4 + min 31 100000 else 7 * min 31 100000 - 2 * 4) :=
  splitWalk_steps 31 100000 10 4 3 (0, 0) (by decide) (by decide) (by decide)
theorem splitCost :
    let st := ((splitWalk (sideCount 31 100000) 100031 10 4).run (0, 0)).2
    st.1 ≤ 2 * 3 + 2 ∧ st.2 ≤ 4 + 7 * min 31 100000 :=
  splitWalk_cost 31 100000 10 4 3 (by decide) (by decide) (by decide)
example : ¬ min 31 100000 < 4 * 2 ^ 2 := by decide
example : ((splitWalk (sideCount 31 100000) 100031 10 4).run (0, 0)) = (31, (7, 87)) := by rfl

-- Two real subscriptions, including a bounded window and all rows.
def window1 : Win := { key := listKey, lo := some (pos1, true), hi := some (pos2, true) }
def subscriptions : List (Nat × Win) := [(7, window1), (8, Win.all listKey)]
def index : Subs Nat := Subs.ofList subscriptions

theorem indexWF : index.WF := Subs.ofList_wf subscriptions

theorem indexHas : index.Has 7 window1 ↔ (7, window1) ∈ subscriptions :=
  Subs.has_ofList subscriptions 7 window1

theorem containsWindow : index.Has 7 window1 := indexHas.mpr (by simp [subscriptions])

theorem findCost : Costs { work := listKey.size + 1 + (searchSteps (2 * (index.at_ listKey).size) + 1) * posWork pos1 }
    (index.find (m := CostT Id) listKey pos1) := find_costs indexWF listKey pos1

theorem notifyCost :
    (Counted.cost (index.notifyM (m := Counted) [(listKey, pos1), (listKey, pos2)])).work ≤
      ([(listKey, pos1), (listKey, pos2)].map fun e => e.1.size + 1 +
        (searchSteps (2 * (index.at_ e.1).size) + 1) * posWork e.2).sum +
      (Id.run (index.notifyM (m := Id) [(listKey, pos1), (listKey, pos2)])).size :=
  notify_cost indexWF _

-- The existing negative controls already contain concrete nonempty stored
-- op/journal fixtures. Keep these in the gate as specification failures of
-- key-only matching and unnetted journals, not claims about real users.
theorem keyOnlyFails : Mutants.keyNotified (runJ Mutants.fam [.step] Mutants.σ).2 Mutants.w5 = true ∧
    window Mutants.σ Mutants.w5 = window (runJ Mutants.fam [.step] Mutants.σ).1 Mutants.w5 :=
  Mutants.key_notice_imprecise

theorem unnettedFails : Mutants.rawNotified
    (runJ Mutants.fam [.step, .purge [Mutants.o.id]] Mutants.σ).2 Mutants.wk = true ∧
    window Mutants.σ Mutants.wk = window (runJ Mutants.fam [.step, .purge [Mutants.o.id]] Mutants.σ).1 Mutants.wk :=
  Mutants.unnetted_imprecise

def afterStep : DB Unit := (runJ Mutants.fam [.step] Mutants.σ).1
theorem afterInv : Inv Mutants.fam afterStep := run_inv [.step] Mutants.σ_inv

theorem stepShape : afterStep = decideS Mutants.fam Mutants.o.id (.valid ()) { Mutants.σ with queue := [] } := by
  have ho : Mutants.σ.ops Mutants.o.id = some Mutants.o := by simp [Mutants.σ]
  unfold afterStep runJ Change.apply stepS
  simp only [Mutants.σ, ite_eq_left]
  rfl

theorem decided : afterStep.status Mutants.o.id = some (.valid ()) := by
  rw [stepShape, (decideS_fields Mutants.o.id (.valid ()) { Mutants.σ with queue := [] }).2.1]
  simp

def wholeWindow : Win := Win.all Mutants.k
def row : Pos × Unit := ((⟨#[0]⟩, Mutants.o.id), ())
theorem rowAppears : row ∈ window afterStep wholeWindow := by
  apply mem_window.mpr
  refine ⟨rfl, filed_iff.mpr ⟨(), ?_, decided, rfl⟩, decided⟩
  exact afterInv.idx _ _ |>.2 ⟨(), decided, by simp [wholeWindow, Win.all, Mutants.fam, Family.fileKeys]⟩

theorem windowChanged : window Mutants.σ wholeWindow ≠ window afterStep wholeWindow := by
  intro h
  have hr := rowAppears
  rw [← h] at hr
  have hs := (mem_window.mp hr).2.2
  cases hs

def watched : Subs Nat := Subs.ofList [(7, wholeWindow)]
theorem noticeExact : 7 ∈ watched.notify (runJ Mutants.fam [.step] Mutants.σ).2.toArray ↔
    ∃ w, watched.Has 7 w ∧ window Mutants.σ w ≠ window afterStep w :=
  notice_iff Mutants.σ_inv Mutants.σ_one_step (Subs.ofList_wf _) 7

theorem notified : 7 ∈ watched.notify (runJ Mutants.fam [.step] Mutants.σ).2.toArray :=
  noticeExact.mpr ⟨wholeWindow, (Subs.has_ofList _ _ _).mpr (by simp), windowChanged⟩

def allRows : ListQ := { key := Mutants.k, limit := none }
theorem readRowsChange : (eval afterStep allRows).rows = (eval Mutants.σ allRows).rows ↔
    window afterStep (allRows.win (eval Mutants.σ allRows)) = window Mutants.σ (allRows.win (eval Mutants.σ allRows)) :=
  read_rows_iff Mutants.σ_inv afterInv rfl (by simp [allRows])

theorem loadedRow : row ∈ window afterStep (allRows.win (eval afterStep allRows)) ↔
    row ∈ (eval afterStep allRows).rows :=
  window_rows afterInv rfl (by simp [allRows]) row

theorem actualRead : row ∈ (eval afterStep allRows).rows := loadedRow.mp rowAppears

theorem readNoticeExact : 7 ∈ watched.notify (runJ Mutants.fam [.step] Mutants.σ).2.toArray ↔
    (eval afterStep allRows).rows ≠ (eval Mutants.σ allRows).rows :=
  read_notice_iff Mutants.σ_inv Mutants.σ_one_step (Subs.ofList_wf _) rfl (by simp [allRows])
    (by intro w; simp [Subs.has_ofList, allRows, ListQ.win, wholeWindow, Win.all])

theorem journalExact : filed afterStep Mutants.k row.1 =
    (filed Mutants.σ Mutants.k row.1 ^^ flips (runJ Mutants.fam [.step] Mutants.σ).2 Mutants.k row.1) :=
  run_exact [.step] Mutants.σ_inv Mutants.k row.1

def cancelled : DB Unit := (runJ Mutants.fam [.step, .purge [Mutants.o.id]] Mutants.σ).1

theorem cancelledInv : Inv Mutants.fam cancelled :=
  run_inv [.step, .purge [Mutants.o.id]] Mutants.σ_inv

theorem cancelledWatch :
    window cancelled (allRows.watch (eval Mutants.σ allRows)) =
      window Mutants.σ (allRows.watch (eval Mutants.σ allRows)) := by
  simpa [allRows, ListQ.watch, ListQ.win, ListQ.rangeWin, Mutants.wk, Win.all, cancelled]
    using Mutants.unnetted_imprecise.2.symm

theorem watchStable : allRows.kept (eval cancelled allRows) = allRows.kept (eval Mutants.σ allRows) :=
  watch_stable Mutants.σ_inv cancelledInv rfl cancelledWatch

-- fact_stable with facts that carry something (an op's body size) and two
-- different stores: `kept` has its op Valid with fact 3; `again` is the
-- same store with the op queued once more, as a second requirement's
-- wake-up pushes an op that is decided before it is popped. The law
-- fixes `again`'s fact from `kept`'s: whatever it holds there is 3.
namespace Sized
scoped instance : SortKey Nat := ⟨fun _ => ⟨#[0]⟩⟩

def fam : Family Nat where
  validate o _ := some o.body.size
  keys _ := [Mutants.k]
  scope _ := .local

def op : Op := Op.make 0 [] ⟨#[1, 2, 3]⟩
def kept : DB Nat := stepS fam (ingestS op DB.empty)
theorem keptInv : Inv fam kept := inv_step (inv_ingest inv_empty op)

theorem shape : kept = decideS fam op.id (.valid 3) { ingestS op DB.empty with queue := [] } := by
  simp [kept, stepS, ingestS, DB.empty, DB.putOp, DB.push]
  rfl

theorem keptValid : kept.status op.id = some (.valid 3) := by
  rw [shape, (decideS_fields op.id (.valid 3) { ingestS op DB.empty with queue := [] }).2.1]
  simp

theorem keptQueue : kept.queue = [] := by
  rw [shape, (decideS_fields op.id (.valid 3) { ingestS op DB.empty with queue := [] }).2.2.1]
  rfl

def again : DB Nat := { kept with queue := [op.id] }

theorem againInv : Inv fam again where
  key := keptInv.key
  sound := keptInv.sound
  wait x o h hs := (keptInv.wait x o h hs).elim (fun hq => by rw [keptQueue] at hq; cases hq) Or.inr
  idx := keptInv.idx
  nodup := keptInv.nodup
  stored := keptInv.stored

end Sized

open Sized in
theorem factStable : Sized.kept ≠ Sized.again ∧ Sized.again.status Sized.op.id = some (.valid 3) ∧
    ∀ f', Sized.again.status Sized.op.id = some (.valid f') → f' = 3 :=
  ⟨fun h => by have := congrArg DB.queue h; simp [Sized.again, Sized.keptQueue] at this,
   Sized.keptValid,
   fun _ h => (fact_stable Sized.keptInv Sized.againInv (g := Sized.kept.ops)
     (fun _ _ h => h) (fun _ _ h => h) Sized.keptValid h).symm⟩

end Vacuity.Query
