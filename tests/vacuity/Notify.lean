import app.community.Screen
import app.community.notice.Proofs
import app.Proofs

/-
Notifications' laws, witnessed on concrete inputs of the running code: one
community, one post from another device and user above this device's
mark, at the default level, with nothing on screen. Each premise is
discharged by evaluation before the law is applied.
-/

namespace Vacuity.Notifications
open Engine Community _root_.Notify

def c : ByteArray := ⟨#[1]⟩
/-- This device, and the device that wrote the post. -/
def mine : ByteArray := ⟨#[2]⟩
def theirs : ByteArray := ⟨#[3]⟩
/-- This device's user, the author's, and the post. -/
def u : ByteArray := ⟨#[4]⟩
def author : ByteArray := ⟨#[5]⟩
def x : ByteArray := ⟨#[6]⟩

def row : Kinds.Notify.Row := { id := x, author, device := theirs, name := "Bea", text := "hi", time := 10 }

def input : Input :=
  { c, title := "#general (club)", device := mine, user := u, live := true,
    snap := { rows := [row], mark := some 5, read := [], settings := {} } }

/-- **own_silent**: a post this device wrote never alerts it. -/
theorem ownSilent : eligible {} { device := mine, authorDevice := mine } = false :=
  own_silent {} _ rfl

/-- The turn over that one community posts exactly that post's card. -/
theorem posts : (step {} [c] none [] [input]).2 = [.post (card input row)] := by rfl

/-- **step_post**: and that card is of a post the rule admits. -/
theorem posted : ∃ i ∈ [input], ∃ r ∈ i.snap.rows, card input row = card i r ∧ Rule i.snap.settings (facts i none r) :=
  step_post {} [c] none [] [input] _ (by rw [posts]; exact List.mem_singleton_self _)

/-- A card standing before a turn with nothing on screen, no read and no
community left: it still stands. -/
def standing : State := { seen := [x], active := [card input row] }

theorem standsEq : (step standing [c] none [] []).1.active = [card input row] := by rfl

theorem stands : card input row ∈ (step standing [c] none [] []).1.active := by
  rw [standsEq]; exact List.mem_singleton_self _

/-- **step_read**: the standing card is of no message read here. -/
theorem notRead : (card input row).id ∉ ([] : List Id) :=
  step_read standing [c] none [] [] _ stands

/-- **step_removed**: its community is held and this device a member there. -/
theorem held : (card input row).community ∈ [c] ∧ ∀ i ∈ ([] : List Input), i.c = (card input row).community → i.live = true :=
  step_removed standing [c] none [] [] _ stands

/-- **step_keeps**: a standing card the turn's `gone` does not name stays. -/
theorem kept : card input row ∈ (step standing [c] none [] []).1.active :=
  step_keeps standing [c] none [] [] _ (List.mem_singleton_self _) (by rfl)

/-- A community read for the first time: its first mark is now. -/
def first : Input := { input with snap := { input.snap with mark := none } }

theorem firstMark : (c, 7) ∈ marks 7 [first] := by
  show (c, 7) ∈ [(c, 7)]
  exact List.mem_singleton_self _

/-- **marks_le**: a mark never runs ahead of the clock. -/
theorem markLe : (c, 7).2 ≤ 7 := marks_le 7 [first] (c, 7) firstMark

/-- **noticeRecipients_own**: a read is sealed to the user's other device,
the node key of one of its admissions. -/
def other : ByteArray := ⟨#[7]⟩
def rows : List (Pos × Fact) := [((.empty, x), Fact.admission c u theirs other .empty)]

theorem sealedTo : other ∈ noticeRecipients mine false rows := by
  show other ∈ [other]
  exact List.mem_singleton_self _

theorem recipient : (∃ p c' u' d k, (p, Fact.admission c' u' d other k) ∈ rows) ∧ (false = true ∨ other ≠ mine) :=
  noticeRecipients_own mine false rows other sealedTo

/-- **target_roundtrip**: a link to a message, with 32-byte ids. -/
def id32 (b : UInt8) : ByteArray := ⟨Array.replicate 32 b⟩
def target : Target := ⟨id32 1, id32 1, id32 2, []⟩

theorem targetValid : target.Valid := by decide

theorem roundtrip : Target.parse target.uri = some target := target_roundtrip targetValid

/-- **targetOf_member**: this device's admitted entry in the link's community. -/
def entry : Kinds.Accepted.Me :=
  { dev := Device.ofSeed .empty, seed := .empty, dev_ok := rfl, c := id32 1, adm := id32 9, name := "club" }

theorem found : App.targetOf #[entry] target = some entry := by rfl

theorem member : entry.c = target.community ∧ entry.waiting = false ∧ entry.removed = false ∧ entry ∈ #[entry] :=
  App.targetOf_member #[entry] target entry found

end Vacuity.Notifications
