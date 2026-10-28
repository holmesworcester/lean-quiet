/-
The pair's laws, over every execution of the two real nodes
(`Setup.Run`, Connection/World.lean) against the wire attacker
(Connection/Wiretap.lean). Each is stated here as a `Prop`, for review
before it is proven.

Every law takes the primitives' reading `Ideal` as a parameter and
assumes `Apart` (which bytes are plain, and that the pair's secrets are
distinct names). That the two users admit only each other is a
condition on each step of an execution (`Setup.Step`).
-/
import Connection.Wiretap

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

/-- The ops a session frame's bundle carries. -/
def carried (bundle : B) : List Op :=
  match (Codec.decode bundle : Option (List B)) with
  | some ps => ps.filterMap Op.decode
  | none => []

namespace Setup
variable (P : Setup) (I : Ideal P.K)

/-- What every law assumes, besides `Ideal` itself. -/
def Assumed : Prop := Apart P I

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
      ∃ x c h sk rk d, (x, Fact.established cid c (P.dev !isA) h sk rk d) ∈ w.ests isA) ∧
    ∀ isA src b now o, (b[0]? : Option UInt8) = some bareTag →
      Op.decode (b.extract 1 b.size) = some o → P.fam.scope o ≠ .conn →
        (w.step P (.deliver isA src b now)).side isA = w.side isA ∧
          (w.step P (.deliver isA src b now)).wire = w.wire

/-- **3. Replay.** Delivering again bytes a node was already delivered
adds, at that node, only arrival records (`recv`, kind 38, for an op it
holds with no arrival recorded) and ops the bytes' frame carries (which
the other node sent, by authenticity), and opens or closes no session.

**False today.** A request whose session was closed and purged, if
delivered again to its responder, is opened and answered afresh (a new
`eph`, connection and `established`), and the one-per-peer choice
(`kept`) then keeps that newest session, which no other node holds, and
retires the live one: Tests/PairWorld.lean's "FINDING" check. -/
def replay_stmt : Prop :=
  P.Assumed I → ∀ w, P.Reach I w → ∀ isA src b now, (isA, b) ∈ w.delivered →
    (∀ o ∈ (w.step P (.deliver isA src b now)).ops isA, o ∉ w.ops isA →
      o.kind = 38 ∨ ∃ cid p, P.opens w isA b = some (cid, p) ∧ o ∈ carried p) ∧
    ∀ cid, cid ∈ (w.step P (.deliver isA src b now)).sessionIds isA ↔ cid ∈ w.sessionIds isA

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
