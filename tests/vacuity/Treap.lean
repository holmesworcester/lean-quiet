import engine.sync.Conn

/-! Kernel witnesses for the room treap's laws (engine/sync/TreapAnswer.lean,
Conn.lean): a concrete room of three items under two claimed times, its
treap built by the running inserts, and each law applied to it. -/

namespace Vacuity.Treap
open Engine Engine.Sync

def room : Id := "treap-room".toUTF8
def a : Item := (⟨0, 7⟩, "a".toUTF8)
def b : Item := (⟨0, 9⟩, "b".toUTF8)
def c : Item := (⟨5, 3⟩, "c".toUTF8)
def xs : List Item := [a, b, c]
def ix : Index := { rooms := [(room, RoomTree.ofList [c, a, b])] }
def P : Params := { leaf := 1, fan := 2 }
def wide : Range := ⟨⟨0, 0⟩, none⟩
def claim : Claim := .fp wide 1 .empty

theorem sortedXs : Sorted Prod.fst xs := by unfold Sorted xs a b c; decide

-- The running answer and opening of a full round (floor 0) in a room built
-- by inserts, out of order, are the list functions' over its items in key
-- order.
theorem answerAgrees : ix.answer P room 0 claim =
    answer Prod.fst Prod.snd sha256 P (ix.items room) claim := by
  rw [Index.answer_eq, Index.over_full _ _ _ _ (by decide)]

theorem openingAgrees : ix.opening P room 0 wide =
    opening Prod.fst Prod.snd sha256 P (ix.items room) wide := by
  rw [Index.opening_eq, Index.over_full _ _ _ _ (by decide)]

-- The treap's answer over sorted items, cut into pieces (count 3 against
-- a claimed 1, more than a leaf of 1), is `answer`'s.
theorem treapAnswers : answerT Prod.fst Prod.snd sha256 P (canon Prod.fst Prod.snd sha256 xs) claim =
    answer Prod.fst Prod.snd sha256 P xs claim :=
  answerT_canon Prod.fst Prod.snd sha256 P sortedXs claim

-- The cost bounds, on this room's treap.
theorem answerCost :
    (Counted.cost (answerTM (m := Counted) Prod.fst Prod.snd sha256 P (canon Prod.fst Prod.snd sha256 xs) claim)).hashes ≤
      2 * (P.fan + 1) * (canon Prod.fst Prod.snd sha256 xs).height :=
  answerTM_hashes Prod.fst Prod.snd sha256 P _ claim

theorem openingCost :
    (Counted.cost (openingTM (m := Counted) Prod.fst Prod.snd sha256 P (canon Prod.fst Prod.snd sha256 xs) wide)).hashes ≤
      2 * (canon Prod.fst Prod.snd sha256 xs).height :=
  openingTM_hashes Prod.fst Prod.snd sha256 P _ wide

theorem insertCost :
    (Counted.cost (Treap.insertM (m := Counted) Prod.fst Prod.snd sha256 c
      (canon Prod.fst Prod.snd sha256 [a, b]))).hashes ≤ (canon Prod.fst Prod.snd sha256 [a, b]).height + 1 :=
  insert_hashes Prod.fst Prod.snd sha256 c _

theorem labels : (canon Prod.fst Prod.snd sha256 xs).label sha256 = lbl Prod.fst Prod.snd sha256 xs :=
  label_canon Prod.fst Prod.snd sha256 xs.length xs (Nat.le_refl _)

end Vacuity.Treap
