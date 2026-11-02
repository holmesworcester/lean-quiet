import engine.core.Order
import app.community.Family

namespace Community
open Engine Codec
variable {C : Crypto} {ops : Id → Option Op}

/-- A receipt's validator: it cites one message, saturated, and names
it with its community and key. -/
theorem check_received {clump : Option Id} {C : Crypto} {o : Op} {b : Body} {fs : List Fact} {c kid m : Id} {k : Nat}
    (h : check C o b fs = some (.received c kid m k clump)) :
    b = .receive k ∧ m = o.reqs.headD .empty ∧
      ∃ u d sealed n tm, fs = [.message c u d kid sealed n tm clump] ∧ countCap ≤ n := by
  unfold check at h
  split at h <;> (try (simp at h; done))
  rename_i b m
  rcases b with ⟨k'⟩; rcases m with ⟨c', u, d, kid', sealed, n, tm, clump'⟩
  simp only [Receive.check] at h
  split at h
  · rename_i hc
    simp only [Option.map_some, Option.some.injEq, Fact.ofReceived.injEq, Receive.Fact.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl, _, _, _, _, _, rfl, hc⟩
  · simp at h

/-- **A receipt is of a saturated message.** A Valid receipt of m in c
under kid cites only m, a Valid message of c sealed under kid that
claims the counter cap or more. -/
theorem received_of_message {clump : Option Id} {x c kid m : Id} {k : Nat} (h : V C ops x (.received c kid m k clump)) :
    ∃ o u d sealed n tm, ops x = some o ∧ o.reqs = [m] ∧ countCap ≤ n ∧
      V C ops m (.message c u d kid sealed n tm clump) := by
  obtain ⟨o, b, fs, hx, _, hr, hv⟩ := valid_inv h
  obtain ⟨rfl, hm, u, d, sealed, n, tm, rfl, hn⟩ := check_received hv
  have h1 : ∃ y, o.reqs = [y] ∧ V C ops y (.message c u d kid sealed n tm clump) := by
    generalize o.reqs = l at hr
    cases hr with | cons hy hrest => cases hrest; exact ⟨_, rfl, hy⟩
  obtain ⟨y, hreq, hy⟩ := h1
  rw [hreq] at hm; simp at hm; subst hm
  exact ⟨o, u, d, sealed, n, tm, hx, hreq, hn, hy⟩
open Engine Codec

theorem recKey_toList (k : Nat) (m : Id) :
    (recKey k m).data.toList = (be64 countCap).data.toList ++ ((be64 k).data.toList ++ m.data.toList) := by
  rw [recKey, toList_append, toList_append, List.append_assoc]

theorem bcmp_recKey {k k' : Nat} (hk : k < 2 ^ 64) (hk' : k' < 2 ^ 64) (m m' : Id) :
    bcmp (recKey k m) (recKey k' m') = (compare k k').then (bcmp m m') := by
  rw [bcmp_eq_lexCmp, bcmp_eq_lexCmp, recKey_toList, recKey_toList, lexCmp_append _ _ (be64_len_eq _ _),
    lexCmp_append _ _ (be64_len_eq _ _), lexCmp_be64 countCap_lt countCap_lt, lexCmp_be64 hk hk',
    Nat.compare_eq_eq.2 rfl]
  rfl

/-- Every message below the cap sorts before every receipt. -/
theorem bcmp_msg_rec {n : Nat} (hn : n < countCap) (tm k : Nat) (m : Id) :
    bcmp (msgKey n tm) (recKey k m) = .lt := by
  rw [bcmp_eq_lexCmp, msgKey, recKey_toList, toList_append, lexCmp_append _ _ (be64_len_eq _ _),
    lexCmp_be64 (min_lt countCap_lt) countCap_lt, Nat.min_eq_left (Nat.le_of_lt hn), Nat.compare_eq_lt.2 hn]
  rfl

/-- A receipt's sort key names its message. -/
theorem recKey_inj {k k' : Nat} {m m' : Id} (h : recKey k m = recKey k' m') : m = m' := by
  have h1 := congrArg (·.data.toList) h
  simp only [recKey_toList] at h1
  have h2 := List.append_cancel_left h1
  have h3 := (List.append_inj h2 (by rw [be64_length, be64_length])).2
  exact ByteArray.ext (Array.toList_inj.1 h3)
open Engine Codec
section
variable {s : DB Fact} {C : Crypto}

/-- Where message x of c sits in this device's list (`readable_held`):
below the counter cap at its own key, past it at a receipt of it this
device holds. -/
def Listed (C : Crypto) (ops : Id → Option Op) (c x : Id) (sk : ByteArray) : Prop :=
  (∃ u d kid sealed n tm clump, V C ops x (.message c u d kid sealed n tm clump) ∧ n < countCap ∧ sk = msgKey n tm) ∨
    ∃ z kid k clump, V C ops z (.received c kid x k clump) ∧ sk = recKey k x

/-- Post x claims counter n and time tm: its op's body says so. -/
def Posted (ops : Id → Option Op) (x : Id) (n tm : Nat) : Prop :=
  ∃ o kid sealed sig, ops x = some o ∧ (decode o.body : Option Body) = some (.post kid sealed n tm sig)

/-- A receipt's sort key names its message. -/
theorem recMsg_recKey (k : Nat) (m : Id) : recMsg (recKey k m) = m := by
  unfold recMsg
  rw [recKey_toList, ← List.append_assoc,
    List.drop_left' (by rw [List.length_append, be64_length, be64_length])]

end
end Community
