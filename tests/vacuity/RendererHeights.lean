import engine.renderer.Heights

namespace Vacuity.RendererHeights
open Heights Engine

-- Four message rows with varied heights; no zero-height leaves.
def tree : T := T.mk (T.mk (.leaf 48) (.leaf 72)) (T.mk (.leaf 96) (.leaf 40))
private theorem wellFormed : tree.WF :=
  T.wf_mk (T.wf_mk trivial trivial) (T.wf_mk trivial trivial)

theorem rowStart : tree.start 2 = (tree.toList.take 2).sum :=
  T.start_eq wellFormed 2
example : tree.start 2 = 120 := rfl

theorem findRow : tree.start (tree.find 130) ≤ 130 ∧ 130 < tree.start (tree.find 130 + 1) :=
  T.find_spec wellFormed (by decide)
example : tree.find 130 = 2 := rfl

theorem update : (tree.set 1 100).toList = tree.toList.set 1 100 :=
  (T.set_toList wellFormed (i := 1) (by decide) 100).1
example : (tree.set 1 100).toList = [48, 100, 96, 40] := rfl

theorem monotone : tree.start 1 ≤ tree.start 3 :=
  T.start_mono wellFormed (by decide)
theorem endOfContent : tree.start tree.size = tree.sum := T.start_size wellFormed

theorem below : tree.start (1 + 1) ≤ 130 :=
  T.below_window wellFormed (by decide) (by decide)
theorem above : 90 < tree.start 2 :=
  T.above_window wellFormed (by decide) (by decide)

theorem findCost : Counted.cost (T.findM (m := Counted) tree 130) ≤ { work := tree.depth } :=
  T.findM_cost tree 130

theorem startCost : Counted.cost (T.startM (m := Counted) tree 2) ≤ { work := tree.depth } :=
  T.startM_cost tree 2

theorem updateCost : Counted.cost (T.setM (m := Counted) tree 1 100) ≤ { work := tree.depth } :=
  T.setM_cost tree 1 100

def rows : Rows := Heights.rebuild [48, 72, 96, 40]
private theorem rowsOk : rows.Ok [48, 72, 96, 40] := Heights.rebuild_ok _
theorem pushed : (rows.push 60).Ok ([48, 72, 96, 40] ++ [60]) := Rows.push_ok rowsOk 60

theorem rowCosts :
    Counted.cost (T.findM (m := Counted) rows.t 130) ≤ { work := rows.d } ∧
    Counted.cost (T.startM (m := Counted) rows.t 2) ≤ { work := rows.d } ∧
    Counted.cost (T.setM (m := Counted) rows.t 1 100) ≤ { work := rows.d } :=
  Heights.rows_cost rowsOk 130 2 100

example : ¬ 300 < tree.sum := by decide
example : ¬ 4 < tree.size := by decide
example : tree.start 3 ≠ 121 := by decide

end Vacuity.RendererHeights
