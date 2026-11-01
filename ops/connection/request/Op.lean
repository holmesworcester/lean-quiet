import engine.wire.Noise
import engine.core.Engine

/-
`request` (conn scope: the bare wire, one peer, never synced): Noise
message 1 (`e, es, ss`), as poc-17's conn.request and tiny's
connection.request. It goes to the responder's node key from the
initiator's: the two statics, in the clear, as poc-17's are, so the
responder can decide to answer before it opens anything, and KK has
both in advance (the initiator has the responder's from the invite link,
or from the admissions that name it). It carries the message:
the initiator's ephemeral key, then the sealed hello.

The hello is the community the initiator dials for, the address it
listens on, and the ops it delivers. A joiner's request rides here, so
it reaches the inviter before anyone approves it, and it opens nothing:
"a request alone opens nothing and earns no reply". A hello delivers
nothing else: the responder takes from it only a join request of its
community (`react`, `bare_takes_only_join`).

Valid iff both keys are 32 bytes, they differ, and the message holds an
ephemeral key and a tag. This is structural, so every
holder judges it the same. Filed under `conn.request.byTo [to]` (how a
responder finds what is addressed to it) and `conn.request.byFrm [frm]`
(a dialer's own requests).

`connect` is the command: an `eph` (local), the request, and a `send`
courier carrying the request's bytes to the address. Redialing only
writes the courier again: the request is the same op, with the same
bytes and the same id.

This op type's body and fact, their bytes, and the lists its fact is
filed in. Its validator is Validate.lean; the registry is
ops/connection/Family.lean.
-/

namespace Connection
open Engine Codec

namespace Request

/-- What its author writes. -/
structure Body where
  to : B
  frm : B
  m1 : B
  deriving BEq

instance : Codec Body := Codec.tagged 33 (fun x => (x.to, x.frm, x.m1)) (fun (p : B × B × B) => ⟨p.1, p.2.1, p.2.2⟩) (fun _ => rfl)

@[simp] theorem Body.enc_tag (x : Body) : Codec.enc x = 33 :: Codec.enc (x.to, x.frm, x.m1) := rfl

/-- Its fact, `request`. -/
structure Fact where
  to : B
  frm : B
  m1 : B
  deriving Inhabited, BEq

instance : Codec Fact := Codec.tagged 1 (fun x => (x.to, x.frm, x.m1)) (fun (p : B × B × B) => ⟨p.1, p.2.1, p.2.2⟩) (fun _ => rfl)

@[simp] theorem Fact.enc_tag (x : Fact) : Codec.enc x = 1 :: Codec.enc (x.to, x.frm, x.m1) := rfl

/-! ## The lists its fact is filed in (`conn.request.*`) -/
def byTo : Rel Fact := ⟨"conn.request", "byTo", fun f => some [f.to]⟩
@[simp] theorem byTo_args (f : Fact) : byTo.args f = (some [f.to]) := rfl
def byFrm : Rel Fact := ⟨"conn.request", "byFrm", fun f => some [f.frm]⟩
@[simp] theorem byFrm_args (f : Fact) : byFrm.args f = (some [f.frm]) := rfl

end Request

end Connection
