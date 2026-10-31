import engine.core.Core
import engine.core.Order
import engine.core.Union
import engine.core.CostErase
import ops.community.Link

/-! Nonempty synthetic wire payload, invite and interleaved list fixtures.
The opaque SHA is retained symbolically; no digest value or collision claim is
invented. All premises below are closed kernel proofs. -/
namespace Vacuity.Core
open Engine
set_option linter.defProp false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

def payload : UInt8 × List ByteArray × ByteArray :=
  (7, ["community-01".toUTF8, "admission-alice".toUTF8], "Hello, Quiet!".toUTF8)

theorem decoded : Codec.decode (Codec.encode payload) = some payload :=
  Codec.decode_encode payload

-- An independent wire image prevents the canonicality example being only a
-- roundtrip of an unexamined encoder.
def wire : ByteArray := ⟨#[7, 1, 12, 99, 111, 109, 109, 117, 110, 105, 116, 121, 45, 48, 49,
  1, 15, 97, 100, 109, 105, 115, 115, 105, 111, 110, 45, 97, 108, 105, 99, 101,
  0, 13, 72, 101, 108, 108, 111, 44, 32, 81, 117, 105, 101, 116, 33]⟩
theorem wireDecodes : Codec.decode wire = some payload := by decide +kernel
theorem canonical : Codec.encode payload = wire := Codec.encode_decode wireDecodes

def op : Op := Op.make payload.1 payload.2.1 payload.2.2

theorem opDecodes : Op.decode op.bytes = some op := Op.decode_bytes op

def exactBytes := Op.decode_exact opDecodes
def partsSmaller := Op.decode_parts opDecodes
def bundle := ["Hello Alice".toUTF8, "Hello Bob".toUTF8]
def bundleSmaller := Codec.decode_sum (Codec.decode_encode bundle)

theorem hashNamed : op.id = sha256 op.bytes := Op.id_decode opDecodes

example : (Codec.decode (Codec.encode payload ++ ⟨#[0]⟩) : Option (UInt8 × List ByteArray × ByteArray)) = none := by decide +kernel
example : payload.2.1.length = 2 ∧ payload.2.2.size = 13 := by decide +kernel

def a : Pos := (⟨#[1]⟩, ⟨#[11]⟩)
def b : Pos := (⟨#[1]⟩, ⟨#[12]⟩)
def c : Pos := (⟨#[2]⟩, ⟨#[10]⟩)
def rowA : Pos × String := (a, "Alice: hello")
def rowB : Pos × String := (b, "Bob: hello")
def rowC : Pos × String := (c, "Alice: reply")
def rows := [rowC, rowB, rowA]

theorem positionEquality : (Pos.cmp a a = .eq ↔ a = a) ∧
    (Pos.cmp a b = .eq ↔ a = b) := ⟨Pos.cmp_eq_iff a a, Pos.cmp_eq_iff a b⟩
example : Pos.cmp a b ≠ .eq ∧ a ≠ b := by decide +kernel

theorem transitive : Pos.cmp a c = .lt :=
  Pos.cmp_lt_trans (q := b) (by decide +kernel) (by decide +kernel)

theorem sorted : Sorted (sortPos rows) := sortPos_sorted rows

theorem fastSort : sortPos rows = sortPosFast rows := congrFun (congrFun sortPos_eq_fast String) rows

theorem permutation : (sortPos rows).Perm rows := perm_sortPos rows

def runs := [[rowA, rowC], [rowB]]
theorem runsOrdered : ∀ r ∈ runs, r.Pairwise (fun p q => posLE p q = true) := by decide +kernel

theorem merge : mergeRuns runs = sortPos runs.flatten := mergeRuns_eq_sortPos runs runsOrdered

theorem insertMerge : insertBy rowA (List.merge [rowC] [rowB] posLE) =
    List.merge [rowA, rowC] [rowB] posLE := insertBy_merge rowA [rowC] (by decide +kernel) [rowB]

theorem foldMerge : [rowA, rowC].foldr insertBy [rowB] = List.merge [rowA, rowC] [rowB] posLE :=
  foldr_insertBy [rowB] [rowA, rowC] (by decide +kernel)

def answers : List (Answer String) := [⟨[rowA, rowC], 2, 2⟩, ⟨[rowB], 1, 1⟩]
theorem union : (unionAnswers false (some 2) answers).rows =
    (orient false (sortPos (answers.map fun a => orient false a.rows).flatten)).take 2 :=
  union_rows (by decide +kernel)

example : sortPos rows = [rowA, rowB, rowC] := by decide +kernel
example : mergeRuns runs = [rowA, rowB, rowC] := by rw [merge]; decide +kernel
example : (unionAnswers false (some 2) answers).rows = [rowA, rowB] := by rw [union]; decide +kernel
example : ¬ Pos.cmp b a = .lt := by decide +kernel
example : ¬ [rowC, rowA].Pairwise (fun p q => posLE p q = true) := by decide +kernel

def charge : Meter := { reads := 2, writes := 1, copied := 13 }
def action : Counted Nat := CostT.charged charge (pure 42)
def continuation (n : Nat) : Counted Nat := CostT.charged { work := 3 } (pure (n + 1))

def eraseRun := CostT.erase_run action
def erasePure := CostT.erase_pure (m := Id) (42 : Nat)
def eraseBind := CostT.erase_bind action continuation
def eraseCharged := CostT.erase_charged (m := Id) charge (pure (42 : Nat))
def eraseChargedBy := CostT.erase_chargedBy (m := Id) (fun n : Nat => { work := n }) (pure 42)
def eraseLift := CostT.erase_lift (m := Id) (pure (42 : Nat))
def eraseTick := CostT.erase_tick (m := Id) charge
def valueErased := Counted.val_erase action
def costRun := Counted.cost_run action
example : Counted.val (CostT.bind action continuation) = 43 := by decide +kernel
example : (Counted.cost (CostT.bind action continuation)).reads = 2 ∧
    (Counted.cost (CostT.bind action continuation)).work = 3 := by decide +kernel

open Community
-- Seed/ids are deterministic 32-byte fixtures, not production credentials.
def bytes32 (n : UInt8) : ByteArray := ⟨Array.replicate 32 n⟩
def invite : Invite := ⟨bytes32 1, bytes32 2, bytes32 3, ["127.0.0.1:7447".toUTF8], bytes32 4⟩
theorem inviteValid : invite.Valid := by decide +kernel
theorem inviteRound : Invite.parse invite.text = some invite := parse_text inviteValid
theorem parsedValid : invite.Valid := parse_valid inviteRound
theorem base62Round : Base62.decode (Base62.encode [0, 1, 254, 255]) = some [0, 1, 254, 255] :=
  Base62.decode_encode _
example : ¬ ({ invite with secret := ⟨#[4]⟩ } : Invite).Valid := by decide +kernel
example : Base62.decode ['!'] = none := by decide +kernel

end Vacuity.Core
