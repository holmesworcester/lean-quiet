/-
The attacker on the pair's wire, what the pair laws assume of the
primitives, and the executions they are about.

**The attacker's knowledge is symbolic.** A closure over raw bytes
under the real functions holds every byte string: Noise's framing in
`Noise.suite` is `++` and a split at 32 bytes, a frame is bytes laid end
to end (`Frame.seal`), and Codec writes a ByteArray as its length then
its bytes, which are also the bytes of a list of UInt8. A split of any
33-byte string gives one byte, and appending bytes gives every string,
the secrets among them. So over bytes "the attacker cannot derive e" is
false for the real framing, and no Keys instance meets it; secrecy
without probability needs values the attacker cannot take apart. The
attacker therefore reads the wire as the protocol does, field by field
(`reads`), into the free algebra `T`, and knows the Dolev-Yao closure of
what it read (`Dy`, `Knows`). It may deliver any bytes whose fields it
knows (`Deliverable`): the fields are what the receiving code reads, so
any bytes with the same fields would act the same.

**The one assumption about the primitives (`Ideal`).** The Keys are the
free algebra, read off bytes: an injective reading `rd` of byte strings
as terms under which every Keys operation is its constructor (and DH is
defined on names only, and commutes). Injectivity is "no collisions";
free constructors are "no other equations". The per-primitive
properties then follow as theorems, not hypotheses: a DH value of two
secret names is not derivable, a ciphertext opens only under its key
(INT-CTXT) and hides its payload, HKDF and the hash are one-way.
`Apart` says which bytes are plain (read as constants), which are the
pair's secrets (names, all distinct), and how a node's wire key leads to
its endpoint secret's public key (today through the device key; E3
makes the endpoint its own key). The engine's SHA-256 (op ids)
and Ed25519 (device keys) are opaque in Lean, so that they never build a
value the Keys build is assumed here, as the engine assumes ids
distinct; it cannot be proven of any witness.

**Executions.** `Run` is every sequence of steps: a delivery of
attacker-derivable bytes, a tick, or a write by a node's user
(`HonestWrite`: Community ops only, containing no draw of either node's
entropy), after which both nodes still trust only each other
(`PairOnly`). That last condition is on the users (they admit, and
follow links to, only each other) and on Ed25519 (no forged admission is
accepted, since the attacker can put any op in a request's hello). It is
an assumption on each step, not on the reachable worlds, so it cannot
make the laws vacuous; deriving it from the users' writes and the
Community laws (`Unforgeable`) is future work.
-/
import Connection.World
import Connection.NoiseSymbolic

namespace Connection.Pair
open Engine Engine.Sync Noise Noise.Symbolic

/-- **The primitives are the free algebra.** `rd` reads bytes as terms. -/
structure Ideal (K : Keys) where
  rd : B → T
  /-- No collisions. -/
  inj : ∀ a b, rd a = rd b → a = b
  pub : ∀ x, rd (K.suite.pub x) = .pub (rd x)
  /-- DH succeeds only on a name and a name's public key, and commutes. -/
  dh : ∀ a b z, K.suite.dh a b = some z → sym.dh (rd a) (rd b) = some (rd z)
  enc : ∀ k n ad p, rd (K.suite.enc k n ad p) = .aead (rd k) n (rd ad) (rd p)
  /-- A ciphertext opens only as what was sealed under that key, nonce
  and associated data. -/
  dec : ∀ k n ad c p, K.suite.dec k n ad c = some p → rd c = .aead (rd k) n (rd ad) (rd p)
  hash : ∀ x, rd (K.suite.hash x) = .hash (rd x)
  hkdf₁ : ∀ a b, rd (K.suite.hkdf a b).1 = .hk1 (rd a) (rd b)
  hkdf₂ : ∀ a b, rd (K.suite.hkdf a b).2 = .hk2 (rd a) (rd b)
  pair : ∀ a b, rd (K.suite.pair a b) = .pair (rd a) (rd b)
  split : ∀ m a b, K.suite.split m = some (a, b) → rd m = .pair (rd a) (rd b)
  lit : ∀ b, rd (K.suite.lit b) = .lit b
  /-- The frames' AEAD, the same way. -/
  fenc : ∀ k n ad p, rd (K.fenc k n ad p) = .xaead (rd k) (rd n) (rd ad) (rd p)
  fdec : ∀ k n ad c p, K.fdec k n ad c = some p → rd c = .xaead (rd k) (rd n) (rd ad) (rd p)

namespace Setup
variable (P : Setup)

/-- The pair's secrets: both devices' seeds, both nodes' endpoint
secrets, and every draw of either node's entropy (ephemerals, and the
draws frame nonces take their random tails from). -/
def Secret (v : B) : Prop :=
  v = P.seedA ∨ v = P.seedB ∨ v = P.endpoint true ∨ v = P.endpoint false ∨
    ∃ i, v = P.entA i ∨ v = P.entB i

/-- The names of the pair's secrets. -/
def Honest (I : Ideal P.K) (n : Nat) : Prop := ∃ v, P.Secret v ∧ I.rd v = .atom n

end Setup

/-- Whether `v` occurs in `b`, byte for byte. -/
def Occurs (v b : B) : Prop := ∃ k, b.extract k (k + v.size) = v

/-- **What else is assumed**: which bytes are plain, and that the
pair's secrets are distinct names. -/
structure Apart (P : Setup) (I : Ideal P.K) : Prop where
  /-- Op ids and device keys (SHA-256 and Ed25519, opaque here). -/
  id : ∀ b, I.rd (sha256 b) = .lit (sha256 b)
  dev : ∀ seed, I.rd (Community.ed25519.pub seed) = .lit (Community.ed25519.pub seed)
  /-- What the code lays out itself: the prologue, the empty payload,
  hellos, frame plaintexts and headers, nonces. -/
  prologue : I.rd prologue = .lit prologue
  empty : I.rd .empty = .lit .empty
  hello : ∀ x : B × B × List B, I.rd (Codec.encode x) = .lit (Codec.encode x)
  bundle : ∀ g : List B, I.rd (Codec.encode g) = .lit (Codec.encode g)
  ad : ∀ cid, I.rd (Frame.ad cid) = .lit (Frame.ad cid)
  nonce : ∀ s i, I.rd ((P.ent s i).extract 0 24) = .lit ((P.ent s i).extract 0 24)
  /-- Every draw, both seeds and both endpoint secrets are names; the
static key the code takes a node's wire key to is its endpoint
secret's public key, and any wire key's is some public key. -/
  draw : ∀ s i, ∃ n, I.rd (P.ent s i) = .atom n
  seed : ∀ s, ∃ n, I.rd (P.seed s) = .atom n
  endpoint : ∀ s, ∃ n, I.rd (P.endpoint s) = .atom n
  endpointPub : ∀ s, P.staticOf (P.endpointKey s) = P.K.suite.pub (P.endpoint s)
  anyStatic : ∀ pk, ∃ x, I.rd (P.staticOf pk) = .pub x
  /-- All distinct: no draw repeats, or is a seed or an endpoint secret,
  and the two nodes differ. -/
  draws : ∀ s i s' i', P.ent s i = P.ent s' i' → s = s' ∧ i = i'
  apart : ∀ s i t, P.ent s i ≠ P.seed t ∧ P.ent s i ≠ P.endpoint t
  nodes : P.seedA ≠ P.seedB ∧ P.endpoint true ≠ P.endpoint false

/-- The attacker's Dolev-Yao closure of `K0`: constants, pairs, public
keys, DH of a name it knows with a public key, hashes and HKDFs, and
both AEADs, sealing and opening under keys it knows. -/
inductive Dy (K0 : T → Prop) : T → Prop
  | know {t} : K0 t → Dy K0 t
  | lit (b : B) : Dy K0 (.lit b)
  | pair {a b} : Dy K0 a → Dy K0 b → Dy K0 (.pair a b)
  | fst {a b} : Dy K0 (.pair a b) → Dy K0 a
  | snd {a b} : Dy K0 (.pair a b) → Dy K0 b
  | pub {x} : Dy K0 x → Dy K0 (.pub x)
  | dh {x y z} : Dy K0 x → Dy K0 y → sym.dh x y = some z → Dy K0 z
  | hash {x} : Dy K0 x → Dy K0 (.hash x)
  | hk1 {a b} : Dy K0 a → Dy K0 b → Dy K0 (.hk1 a b)
  | hk2 {a b} : Dy K0 a → Dy K0 b → Dy K0 (.hk2 a b)
  | encrypt {k ad p} (n : Nat) : Dy K0 k → Dy K0 ad → Dy K0 p → Dy K0 (.aead k n ad p)
  | decrypt {k n ad p} : Dy K0 (.aead k n ad p) → Dy K0 k → Dy K0 p
  | xencrypt {k n ad p} : Dy K0 k → Dy K0 n → Dy K0 ad → Dy K0 p → Dy K0 (.xaead k n ad p)
  | xdecrypt {k n ad p} : Dy K0 (.xaead k n ad p) → Dy K0 k → Dy K0 p

namespace Setup
variable (P : Setup) (I : Ideal P.K)

/-- What the receiving code reads of these bytes, each field through
`rd`: a bare op's requirements and its request's or connection's
fields; a frame's connection id, nonce and ciphertext. Anything else is
read whole. -/
def reads (b : B) : List T :=
  let body := b.extract 1 b.size
  match (b[0]? : Option UInt8) with
  | some 0 =>
    match Op.decode body with
    | some o => o.reqs.map I.rd ++
      match (Codec.decode o.body : Option Body) with
      | some (.request to frm m1) => [I.rd to, I.rd frm, I.rd m1]
      | some (.connection m2) => [I.rd m2]
      | _ => [I.rd o.body]
    | none => [I.rd b]
  | some 1 =>
    match Frame.cid body with
    | some cid => [I.rd cid, I.rd (body.extract 33 57), I.rd (body.extract 57 body.size)]
    | none => [I.rd b]
  | _ => [I.rd b]

/-- What the attacker starts with: every name that is not the pair's
secret (its own among them), and every public key. -/
def Base (t : T) : Prop := (∃ n, t = .atom n ∧ ¬ P.Honest I n) ∨ ∃ x, t = .pub x

/-- Everything read off the wire so far. -/
def heard (w : World) : List T := w.wire.flatMap fun e => P.reads I e.2.2

/-- **What the attacker knows** at a world. -/
def Knows (w : World) (t : T) : Prop := Dy (fun t => P.Base I t ∨ t ∈ P.heard I w) t

/-- The attacker derives these bytes. -/
def Derives (w : World) (v : B) : Prop := P.Knows I w (I.rd v)

/-- The attacker can deliver these bytes: it knows every field the
receiving code reads of them. -/
def Deliverable (w : World) (b : B) : Prop := ∀ t ∈ P.reads I b, P.Knows I w t

/-- What a device's user may write: Community ops only (the Connection
family writes its own), and nothing that contains a draw of either
node's entropy. -/
def HonestWrite (ops : List Op) : Prop :=
  ∀ o ∈ ops, owns o.kind = false ∧ ∀ s i, ¬ Occurs (P.ent s i) o.bytes

/-- The two users admit, and follow links to, only each other: each
node's `allowPeer` takes only the pair's endpoints, and every join it
waits on names one of them as the inviter. (The trust rule, `trusts`,
is `allowPeer` or a pending join's inviter.) -/
def PairOnly (w : World) : Prop :=
  ∀ isA,
    (∀ c peer, w.at isA ((Community.allowPeer c peer).liftL.run : NodeM Bool) = true →
      peer = P.endpointKey true ∨ peer = P.endpointKey false) ∧
    ∀ o ∈ w.ops isA, ∀ c inv hints req name d t,
      (Codec.decode o.body : Option Community.Body) = some (.joining c inv hints req name d t) →
        inv = P.endpointKey true ∨ inv = P.endpointKey false

/-- One step of an execution: what the act may be, and both nodes
still trusting only each other after it. -/
inductive Step : World → World → Prop
  | deliver {w : World} {isA : Bool} {src b : B} {now : Nat} :
      P.Deliverable I w b → P.PairOnly (w.step P (.deliver isA src b now)) →
        Step w (w.step P (.deliver isA src b now))
  | tick {w : World} {isA : Bool} {now : Nat} :
      P.PairOnly (w.step P (.tick isA now)) → Step w (w.step P (.tick isA now))
  | write {w : World} {isA : Bool} {ops : List Op} {now : Nat} :
      P.HonestWrite ops → P.PairOnly (w.step P (.write isA ops now)) →
        Step w (w.step P (.write isA ops now))

/-- Executions from `w`. -/
inductive Run : World → World → Prop
  | refl (w : World) : Run w w
  | step {w w' w'' : World} : Run w w' → Step P I w' w'' → Run w w''

/-- Every world an execution reaches, from both nodes booted. -/
def Reach (w : World) : Prop := P.Run I (World.init P) w

end Setup

end Connection.Pair
