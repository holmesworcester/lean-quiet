/- Deterministic arbitration of authenticated sessions. The connection op is
shared verbatim by both ends; arrival times and local direction are irrelevant.
A live minimum is never displaced by a larger id. Transport failure removes it,
allowing a fresh handshake. -/
import engine.core.Order

namespace Engine.Winner
open Engine

/-- The same total byte order used by the engine's persisted lists. -/
def choose (a b : Id) : Id := if bcmp a b = .gt then b else a

theorem choose_self (a : Id) : choose a a = a := by simp [choose]

theorem choose_comm (a b : Id) : choose a b = choose b a := by
  have swap := Pos.cmp_swap (.empty, a) (.empty, b)
  have empty : bcmp ByteArray.empty ByteArray.empty = .eq := (bcmp_eq_iff _ _).2 rfl
  simp only [Pos.cmp, empty, Ordering.then] at swap
  cases h : bcmp a b <;> simp_all [choose, Ordering.swap]
  exact (bcmp_eq_iff _ _).1 h

theorem choose_member (a b : Id) : choose a b = a ∨ choose a b = b := by
  unfold choose; split <;> simp

/-- Reconsidering either losing attempt cannot flap the selected connection. -/
theorem choose_stable (a b : Id) : choose (choose a b) b = choose a b := by
  unfold choose; split <;> simp_all

/-- Exactly one of two distinct attempts survives, independent of which side
lists its outbound attempt first. -/
theorem exactly_one (a b : Id) (hne : a ≠ b) :
    (choose a b = a ∧ choose a b ≠ b) ∨ (choose a b = b ∧ choose a b ≠ a) := by
  rcases choose_member a b with h | h
  · exact Or.inl ⟨h, by simpa [h] using hne⟩
  · exact Or.inr ⟨h, by simpa [h] using Ne.symm hne⟩

/-- One winner per remote identity; duplicate reports of an id coalesce. -/
def select : List (Id × ByteArray) → List (ByteArray × Id)
  | [] => []
  | (cid, peer) :: rest =>
    let winners := select rest
    let previous := winners.find? (fun w => w.1 == peer)
    (peer, previous.map (fun w => choose cid w.2) |>.getD cid) ::
      winners.filter (fun w => w.1 != peer)

end Engine.Winner
