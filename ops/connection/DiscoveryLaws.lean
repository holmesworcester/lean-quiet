/- Laws about the selector and endpoint policy called by the application.
Concrete premise witnesses follow each conditional result. -/
import ops.connection.Discovery

namespace Connection.DiscoveryLaws
open Engine Engine.Sync

private theorem bytesBEq : LawfulBEq ByteArray where
  rfl := by intro a; change (a.data == a.data) = true; simp
  eq_of_beq := by intro a b h; change (a.data == b.data) = true at h; exact ByteArray.ext (by simpa using h)
attribute [local instance] bytesBEq

/-- The production `kept` selector uses the common connection id, regardless
of direction, observed address, order of arrival or local clock. -/
theorem kept_pair (a b peer addr1 addr2 : B) (dir1 dir2 : Bool) (t1 t2 : Nat) :
    kept [(a, peer, dir1, addr1, t1), (b, peer, dir2, addr2, t2)] =
      [Winner.choose a b] := by
  simp [kept, Winner.select]

/-- Opposite ends, with opposite directions and unrelated arrival clocks,
select the same single authenticated connection. -/
theorem both_choose_same (a b peerA peerB aa ab ba bb : B) (ta tb ua ub : Nat) :
    kept [(a, peerB, true, aa, ta), (b, peerB, false, ab, tb)] =
    kept [(b, peerA, true, ba, ua), (a, peerA, false, bb, ub)] := by
  simp only [kept_pair, Winner.choose_comm a b]

/-- With two distinct authenticated attempts exactly one survives selection.
The node's existing finish path retires the complement. Closing native sockets
still requires its writer/OS completion contract. -/
theorem single_survivor (a b peer aa ab : B) (ta tb : Nat) (hne : a ≠ b) :
    let survivors := kept [(a, peer, true, aa, ta), (b, peer, false, ab, tb)]
    survivors.length = 1 ∧ ((a ∈ survivors ∧ b ∉ survivors) ∨ (b ∈ survivors ∧ a ∉ survivors)) := by
  simp only [kept_pair, List.length_singleton, List.mem_singleton, true_and]
  rcases Winner.exactly_one a b hne with ⟨ha, hb⟩ | ⟨hb, ha⟩
  · exact Or.inl ⟨ha.symm, Ne.symm hb⟩
  · exact Or.inr ⟨hb.symm, Ne.symm ha⟩

/-- A duplicate losing report cannot displace the selected winner. -/
theorem no_flapping (a b peer addr : B) :
    kept [(Winner.choose a b, peer, true, addr, 100), (b, peer, false, addr, 999)] =
      [Winner.choose a b] := by
  rw [kept_pair, Winner.choose_stable]

-- Concrete simultaneous attempts, with reversed clocks and local directions.
example : (ByteArray.mk #[1]) ≠ ByteArray.mk #[2] := by decide
example : kept [(ByteArray.mk #[2], ByteArray.mk #[9], true, .empty, 3),
    (ByteArray.mk #[1], ByteArray.mk #[9], false, .empty, 1)] = [ByteArray.mk #[1]] := by
  rw [kept_pair]; simp [Winner.choose, bcmp_eq_lexCmp, lexCmp]
example : Winner.choose (ByteArray.mk #[1]) (ByteArray.mk #[2]) = ByteArray.mk #[1] := by
  simp [Winner.choose, bcmp_eq_lexCmp, lexCmp]

/-- The running endpoint validator binds publication to the admitting
node key and requires that device's signature and the address cap. -/
theorem publication_auth (C : Community.Crypto) (o : Op) (c u0 rootDevice rootPeer c1 u d peer : B)
    (ds os : List B) (issued expires : Nat) (sig : B) (f : Community.Fact)
    (h : Community.check C o (.addresses ds os issued expires sig)
      [.admission c u0 rootDevice rootPeer, .admission c1 u d peer] = some f) :
    C.verify d (Community.signed o (.addresses ds os issued expires sig)) sig = true ∧
      (ds ++ os).length ≤ Endpoint.cap ∧ f = .addresses c peer ds os issued expires := by
  simp only [Community.check] at h
  split at h <;> simp_all [Endpoint.valid]

/-- A hostile advertisement cannot enlarge the candidates passed to dialing. -/
theorem candidate_cap (a b c : List B) : (Discovery.candidates a b c).length ≤ 24 := by
  simp only [Discovery.candidates, List.length_take, Endpoint.dialCap, Endpoint.cap]; omega

/-- A due retry cannot be delayed indefinitely by the exponential backoff:
60 seconds after the last attempt every backoff state is eligible. -/
theorem retry_eventually_due (last attempts now : Nat) (h : last + 60000 ≤ now) :
    Discovery.canTry now (some (last, attempts)) = true := by
  simp only [Discovery.canTry, Endpoint.due, decide_eq_true_eq]
  have := Endpoint.delay_bounded attempts
  omega

example : 1000 + 60000 ≤ 61000 := by decide
example : Discovery.canTry 61000 (some (1000, 200)) = true := by decide
example : Discovery.canTry 1001 (some (1000, 200)) = false := by decide

/-- Every retained candidate is picked within one cycle. This is the actual
address choice used by `plan`, not an independent discovery model. -/
theorem candidate_visited (xs : List B) (i : Nat) (h : i < (xs.take Endpoint.dialCap).length) :
    Endpoint.pick xs i = (xs.take Endpoint.dialCap)[i]? := by
  rw [Endpoint.pick, Nat.mod_eq_of_lt h]

example : 1 < (["192.168.4.35:47100".toUTF8, "100.67.2.56:47100".toUTF8].take Endpoint.dialCap).length := by decide
example : Endpoint.pick ["192.168.4.35:47100".toUTF8, "100.67.2.56:47100".toUTF8] 1 =
    some "100.67.2.56:47100".toUTF8 := by decide
example : Endpoint.fresh 1000 900 1100 = true := by decide
example : Endpoint.fresh 1100 900 1100 = false := by decide

end Connection.DiscoveryLaws
