import app.community.Op

/-
A member's signed yes to a request, by another device than the
requester's; a link request is approved by the issuer's user only. It
cites the request, so approvals come after it. It also cites the
approval that admitted its approver (`up`, but for the founder's
device) and its device's previous approval (`prev`, but for its first):
[c, req, adm] ++ [up] ++ [prev]. So an approval's chain to the founder,
and its device's chain, are in its requirements, fixed by hashes.
-/

namespace Community
open Engine Codec

namespace Approve

/-- What its author writes and signs. -/
structure Body where
  sig : ByteArray
  deriving DecidableEq, Inhabited

instance : Codec Body := Codec.tagged 10 (fun x => x.sig) (fun (p : B) => ⟨p⟩) (fun _ => rfl)

@[simp] theorem Body.enc_tag (x : Body) : Codec.enc x = 10 :: Codec.enc x.sig := rfl

/-- The body with its signatures blanked: what the signatures cover. -/
def Body.unsigned (b : Body) : Body := { b with sig := .empty }


/-- Its fact, `approval`: the request it approves and the admission
that gives (`ru`, `rd`, `re`), its approver's user and device, and its
two links. `up` is the approval that admitted the approver (none for the
founder's device: the root admitted it), so following `up` reaches the
founder in `depth` steps. `prev` is the same device's previous approval
(none for its first), so a device's approvals form a hash chain and `n`
is its place in it. All but the ids are read off the facts it cites; a
removal keeps the approvals at or behind each removed device's head
(`Behind`, docs/REMOVAL.md). -/
structure Fact where
  c : Id
  req : Id
  u : Id
  dev : Key
  ru : Id
  rd : Key
  re : Key
  up : Id
  depth : Nat
  prev : Id
  n : Nat
  deriving DecidableEq, Inhabited

instance : Codec Fact := Codec.tagged 10
  (fun x => (x.c, x.req, x.u, x.dev, x.ru, x.rd, x.re, x.up, x.depth, x.prev, x.n))
  (fun (p : B × B × B × B × B × B × B × B × Nat × B × Nat) =>
    ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.1,
      p.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2⟩) (fun _ => rfl)

@[simp] theorem Fact.enc_tag (x : Fact) : Codec.enc x =
    10 :: Codec.enc (x.c, x.req, x.u, x.dev, x.ru, x.rd, x.re, x.up, x.depth, x.prev, x.n) := rfl

/-- Where its fact sorts under its keys: by its place in its device's
chain, so a device's newest approval is its list's last. -/
@[simp] def sortKey (f : Fact) : ByteArray := be64 f.n

/-! ## The lists its fact is filed in (`approval.*`) -/
def byRequest : Rel Fact := ⟨"approval", "byRequest", fun f => some [f.c, f.req]⟩
@[simp] theorem byRequest_args (f : Fact) : byRequest.args f = (some [f.c, f.req]) := rfl
/-- A device's approvals, its chain: its head (the newest) is what a
removal of its user keeps up to. -/
def byDev : Rel Fact := ⟨"approval", "byDev", fun f => some [f.c, f.dev]⟩
@[simp] theorem byDev_args (f : Fact) : byDev.args f = (some [f.c, f.dev]) := rfl
/-- The approvals of a device's requests: what makes its admissions
trusted (`Trusted`). -/
def byRequester : Rel Fact := ⟨"approval", "byRequester", fun f => some [f.c, f.rd]⟩
@[simp] theorem byRequester_args (f : Fact) : byRequester.args f = (some [f.c, f.rd]) := rfl

end Approve

end Community
