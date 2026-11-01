import ops.community.Family
import ops.community.member.join.joining.abandon.Commands

/-!
`community.member.join.joining.abandon`: laws about the op types in this folder and below.
-/
namespace Community
open Engine

/-- **Stopping waiting is local.** -/
theorem stopWaiting_local (C : Crypto) (j : Id) : (stopWaiting j).ops.filter (family C).shared = [] := by
  simp [stopWaiting, abandon, shared_mkOp, Body.isLocal]

end Community
