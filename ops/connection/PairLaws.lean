/-
The pair's laws, over every execution of the two real nodes
(`Setup.Run`, ops/connection/World.lean) against the wire attacker
(ops/connection/Wiretap.lean). Each is stated here as a `Prop`, for review
before it is proven.

Every law takes the primitives' reading `Ideal` as a parameter and
assumes `Apart` (which bytes are plain, and that the pair's secrets are
distinct names). That the two users admit only each other is a
condition on each step of an execution (`Setup.Step`).
-/
import ops.connection.Wiretap

namespace Connection.Pair
open Engine Engine.Sync Noise Noise.Symbolic

namespace World

/-- The connection ids of the sessions node A (true) or B holds. -/
def sessionIds (w : World) (isA : Bool) : List Id :=
  (w.ests isA).filterMap fun (_, f) => match f with
    | .established cid .. => some cid
    | _ => none

/-- Node A's (true) or B's session `cid` was made with ephemeral secret
`e`: its `established` op for `cid` cites an `eph` op with secret `e`. -/
def EphOf (w : World) (isA : Bool) (cid e : B) : Prop :=
  ∃ o ∈ w.ops isA, ∃ q ∈ w.ops isA, (Codec.decode o.body : Option Body) = some .established ∧
    o.reqs.head? = some cid ∧ o.reqs[2]? = some q.id ∧ (Codec.decode q.body : Option Body) = some (.eph e)

/-- Node A (true) or B holds no session `cid`. -/
def Closed (w : World) (isA : Bool) (cid : B) : Prop :=
  ∀ o ∈ w.ops isA, (Codec.decode o.body : Option Body) = some .established → o.reqs.head? ≠ some cid

end World

namespace Setup
variable (P : Setup) (I : Ideal P.K)

/-- What every law assumes, besides `Ideal` itself: `Apart`, and that the
nodes keep sessions by the family's rule. -/
def Assumed : Prop := Apart P I ∧ P.keepRule = kept

/-- These bytes as a session frame, opened at node A (true) or B with
its own keys (`openFrame`, what `Node.onFrame` calls). -/
def opens (w : World) (isA : Bool) (b : B) : Option (Id × B) :=
  if (b[0]? : Option UInt8) = some sealedTag then w.at isA (openFrame P.K (b.extract 1 b.size)) else none

/-- **1. Secrecy.** At every world an execution reaches, the attacker
derives none of the pair's secrets (either device's seed or X25519
secret, any draw of either node's entropy, so any ephemeral), and no
session either node establishes has keys the attacker derives, then or
at any later world. -/
def secrecy_stmt : Prop :=
  P.Assumed I → ∀ w, P.Reach I w →
    (∀ v, P.Secret v → ¬ P.Derives I w v) ∧
    ∀ isA x cid c peer h sk rk d, (x, Fact.established cid c peer h sk rk d) ∈ w.ests isA →
      ∀ w', P.Run I w w' → ¬ P.Derives I w' sk ∧ ¬ P.Derives I w' rk

/-- **2. Authenticity.** Every frame a node opens is, byte for byte, one
the other node sent, and the session it names is, at this node, with the
other node's device. So the ops a node takes in over a session (its
frames' payloads) were sent by the device that session's handshake
authenticated, in that session. A bare delivery is taken in only if it
is a conn-scope op: anything else changes nothing and sends nothing. -/
def authentic_stmt : Prop :=
  P.Assumed I → ∀ w, P.Reach I w →
    (∀ isA b cid p, P.opens w isA b = some (cid, p) →
      (∃ to, (!isA, to, b) ∈ w.wire) ∧
      ∃ x c h sk rk d, (x, Fact.established cid c (P.endpointKey !isA) h sk rk d) ∈ w.ests isA) ∧
    ∀ isA src b now o, (b[0]? : Option UInt8) = some bareTag →
      Op.decode (b.extract 1 b.size) = some o → P.fam.scope o ≠ .conn →
        (w.step P (.deliver isA src b now)).side isA = w.side isA ∧
          (w.step P (.deliver isA src b now)).wire = w.wire

/-- **3a. A replayed frame is dropped.** A frame a node has opened once
(and so taken, or dropped as stale), delivered to it again, from any
address, at any later world, changes nothing at that node: neither its
store nor its node state (the session's return address included), and
it sends nothing.

**Needs the node's freshness check.** Today `Node.onFrame` rebinds the
session's address (`setAddr`) and runs the sync step for every frame
that opens, so a replayed frame from the attacker's address diverts the
session's frames to it until the peer's next frame
(tests/engine/PairWorld.lean's "FINDING" check). It holds once the node drops
a frame whose counter (`Frame.openAt`) is not above the session's mark
(`Frame.fresh`) before anything else. -/
def frameReplay_stmt : Prop :=
  P.Assumed I → ∀ w₀ w isA src₀ src b now₀ now cid p,
    P.Reach I w₀ → P.Step I w₀ (w₀.step P (.deliver isA src₀ b now₀)) →
    P.opens w₀ isA b = some (cid, p) → P.Run I (w₀.step P (.deliver isA src₀ b now₀)) w →
      (w.step P (.deliver isA src b now)).side isA = w.side isA ∧
        (w.step P (.deliver isA src b now)).wire = w.wire

/-- **3b. A replayed handshake op closes no session, and opens none
another node holds.** Delivering again a bare op a node was already
delivered closes none of its sessions (in particular it retires none
that has heard its peer: `kept_heard`), adds no Community op, and any
session it opens there is one the other node never holds, now or at any
later world. That session is a responder's answer to a request whose
own session was closed and purged; it never hears its peer, so patience
drops it (`deadDropped_stmt`). The replay may also add arrival records
and resend a connection to the address it came from. -/
def bareReplay_stmt : Prop :=
  P.Assumed I → ∀ w, P.Reach I w → ∀ isA src b now, (isA, b) ∈ w.delivered →
    (b[0]? : Option UInt8) = some bareTag →
    (∀ cid ∈ w.sessionIds isA, cid ∈ (w.step P (.deliver isA src b now)).sessionIds isA) ∧
    (∀ o ∈ (w.step P (.deliver isA src b now)).ops isA, o ∉ w.ops isA → owns o.kind = true) ∧
    ∀ cid ∈ (w.step P (.deliver isA src b now)).sessionIds isA, cid ∉ w.sessionIds isA →
      ∀ w', P.Run I (w.step P (.deliver isA src b now)) w' → cid ∉ w'.sessionIds (!isA)

/-- **3c. A session that never hears its peer is dropped by patience.**
If a node's connection for session `cid` has not heard the peer's hello
(`peerFloor` unknown) and was last heard from more than `patience` ago,
the node's next tick closes the session and purges it. With 3b, a
replayed request leaves nothing behind for long. -/
def deadDropped_stmt : Prop :=
  P.Assumed I → ∀ w, P.Reach I w → ∀ isA cid c now, (w.side isA).node.conn? cid = some c →
    c.peerFloor = none → c.heard + P.cfg.patience < now →
      cid ∉ (w.step P (.tick isA now)).sessionIds isA

/-- **4. Forward secrecy.** A session both nodes held, made with
ephemeral `e` at A and `f` at B, once both have closed it: neither store
holds `e` or `f` (`close_forgets`, over the real purge); and an attacker
that knows every value not built from `e` or `f` (both devices' seeds and
X25519 secrets, and everything else either store still holds, among
them) and all the wire derives neither end's keys, so it opens none of
the session's frames. -/
def forward_stmt : Prop :=
  P.Assumed I → ∀ w₀ w, P.Reach I w₀ → P.Run I w₀ w →
    ∀ cid e f, w₀.EphOf true cid e → w₀.EphOf false cid f → w.Closed true cid → w.Closed false cid →
      (∀ isA, ∀ o ∈ w.ops isA, (Codec.decode o.body : Option Body) ≠ some (.eph e) ∧
        (Codec.decode o.body : Option Body) ≠ some (.eph f)) ∧
      ∀ isA x c peer h sk rk d, (x, Fact.established cid c peer h sk rk d) ∈ w₀.ests isA →
        let K0 := fun t => Clean (fun n => I.rd e = .atom n ∨ I.rd f = .atom n) t ∨ t ∈ P.heard I w
        ¬ Dy K0 (I.rd sk) ∧ ¬ Dy K0 (I.rd rk)

/-- **5. Non-vacuity.** Some execution establishes one session at both
ends and carries an op each way: an op A's user wrote is held at B, and
one B's user wrote is held at A. -/
def live_stmt : Prop :=
  ∃ w, P.Reach I w ∧ (∃ cid, cid ∈ w.sessionIds true ∧ cid ∈ w.sessionIds false) ∧
    (∃ o, (true, o) ∈ w.wrote ∧ o ∈ w.ops false) ∧ ∃ o, (false, o) ∈ w.wrote ∧ o ∈ w.ops true

end Setup

end Connection.Pair
