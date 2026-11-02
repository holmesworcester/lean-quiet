import app.community.member.invite.request.approve.Op
import app.community.member.invite.request.Op

namespace Community
open Engine Codec

namespace Approve

/-- Whether q admitted the user a's device da with key ea in c: it
approves a request for exactly that admission. -/
def admits (c a : Id) (da ea : Key) (q : Fact) : Bool :=
  decide (q.c = c ∧ q.ru = a ∧ q.rd = da ∧ q.re = ea)

/-- Whether p is device da's own approval in c. -/
def mine (c : Id) (da : Key) (p : Fact) : Bool := decide (p.c = c ∧ p.dev = da)

/-- Its links, after the community, the request and its approver's
admission (user a, device da, key ea): the founder's device (`founder`:
its admission is the root's own) cites its previous approval, if any;
any other device cites the approval that admitted it (`up`), then its
previous approval, if any. The cited facts give the depth (up's + 1, or
0 for the founder's) and the place in the device's chain (prev's + 1,
or 0): up, depth, prev, n. -/
def links (o : Op) (c a : Id) (da ea : Key) (founder : Bool) : List Fact → Option (Id × Nat × Id × Nat)
  | [] => if founder then some (.empty, 0, .empty, 0) else none
  | [p] =>
    if founder then (if mine c da p then some (.empty, 0, o.reqs.getD 3 .empty, p.n + 1) else none)
    else if admits c a da ea p then some (o.reqs.getD 3 .empty, p.depth + 1, .empty, 0) else none
  | [q, p] =>
    if !founder && admits c a da ea q && mine c da p
    then some (o.reqs.getD 3 .empty, q.depth + 1, o.reqs.getD 4 .empty, p.n + 1) else none
  | _ => none

/-- It cites the community, the request it approves, and its author's
admission, by another device than the requester's; then its links (none
if one is not an approval). -/
def check (C : Crypto) (o : Op) : Body → Root.Fact → Request.Fact → Root.Fact → Option (List Fact) → Option Fact
  | ⟨s⟩, ⟨c, u0, d0, e0, _⟩, ⟨c1, u, d, e, l⟩, ⟨c2, a, da, ea, _⟩, ls =>
    if o.reqs.head? = some c ∧ u0 = c ∧ c1 = c ∧ c2 = c ∧ (l = true → a = u) ∧ da ≠ d ∧
      C.verify da (signedBy o (Body.unsigned ⟨s⟩)) s
    then (ls.bind (links o c a da ea (decide (a = c ∧ da = d0 ∧ ea = e0)))).map fun (up, depth, prev, n) =>
      ⟨c, o.reqs.getD 1 .empty, a, da, u, d, e, up, depth, prev, n⟩
    else none

end Approve

end Community
