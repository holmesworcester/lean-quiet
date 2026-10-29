/- Sender-owned message groups. Receivers use signed references; this
five-minute rule is only the sender's choice when composing a new post. -/
import ops.community.Query

namespace Community.Clump
open Engine

/-- Quiet's time unit is wall-clock minutes. The total span from the
root is strictly below five minutes; a backwards clock starts a root. -/
def within (rootTime now : Nat) : Bool := decide (rootTime ≤ now ∧ now < rootTime + 5)

theorem within_iff (rootTime now : Nat) :
    within rootTime now = true ↔ rootTime ≤ now ∧ now < rootTime + 5 := by simp [within]

theorem expired (rootTime now : Nat) (h : rootTime + 5 ≤ now) : within rootTime now = false := by
  simp [within]; omega

theorem backwards (rootTime now : Nat) (h : now < rootTime) : within rootTime now = false := by
  simp [within]; omega

/-- An id lookup is the singleton list every valid op is filed in. -/
def fact (id : Id) : View Fact (Option Fact) := do
  let a ← View.read { key := opKey id, limit := some 1 }
  return a.rows.head?.map (·.2)

/-- Only the latest known author's own root can continue. Linked devices
of the same user can continue a clump. An intervening author starts a new
root even when an older clump of ours is still within the time window. -/
def choose (c myAdm : Id) (now : Nat) : View Fact (Option Id) := do
  let some (.admission ac me _ _) ← fact myAdm | return none
  if ac != c then return none
  let last ← message.all.read [c] (limit := some 1)
  let some ((_, id), .message lc author _ _ _ _ time parent) := last.rows.head? | return none
  if lc != c || author != me then return none
  match parent with
  | none => return if within time now then some id else none
  | some root =>
    let some (.message rc ru _ _ _ _ rootTime none) ← fact root | return none
    return if rc == c && ru == me && within rootTime now then some root else none

end Community.Clump
