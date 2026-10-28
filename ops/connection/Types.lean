/-
The connection family's ops and facts, and how they are written as
bytes. Each op type's meaning lives in its own file: Eph, Request,
Opened, Connection, Established, Send and Recv.

Keys: a node handshakes with its own key (Community's local
`endpoint`, an X25519 key pair), not with a device key. A session's two
statics are the two nodes' keys, and an `established` names its peer by
node key; the trust rule maps a node key to membership through the
admissions that name it (`Community.allowPeer`). Device keys only sign.

Kinds 32–39 until the registry names them.
-/
import ops.connection.Noise
import ops.community.Community

namespace Connection
open Engine Codec

abbrev B := ByteArray

/-- Noise, run on node keys, and the frames' AEAD. -/
structure Keys where
  suite : Noise.Suite B
  /-- The frames' AEAD (XChaCha20-Poly1305): key, 24-byte nonce,
  associated data, plaintext. -/
  fenc : B → B → B → B → B
  fdec : B → B → B → B → Option B

/-- What the laws assume: a good suite, and an AEAD that opens what it
seals. -/
def Keys.Good (K : Keys) : Prop :=
  K.suite.Good ∧ ∀ k n ad p, K.fdec k n ad (K.fenc k n ad p) = some p

/-- libsodium's (the Rust crates'). -/
def sodium : Keys where
  suite := Noise.suite
  fenc := Noise.xchachaSeal
  fdec := Noise.xchachaOpen

/-- The prologue both ends mix in. -/
def prologue : B := "quiet connection v1".toUTF8

inductive Body where
  | eph (sk : B)
  | request (to frm m1 : B)
  | opened
  | connection (m2 : B)
  | established
  | send (addr : B)
  | recv (onConn : Bool) (via addr : B) (at_ : Nat)
  | settled (room : B)

inductive Fact where
  | eph (of pk sk : B)
  | request (to frm m1 : B)
  | opened (req c frm addr : B) (ops : List B)
  | connection (req m2 : B)
  | established (cid c peer h sendKey recvKey : B) (dialer : Bool)
  | send (op addr : B)
  | recv (op : B) (onConn : Bool) (via addr : B) (at_ : Nat)
  | settled (conn room : B)
  deriving Inhabited, BEq

def Body.kind : Body → UInt8
  | .eph .. => 32 | .request .. => 33 | .opened => 34 | .connection .. => 35
  | .established => 36 | .send .. => 37 | .recv .. => 38 | .settled .. => 39

open Community (decAs decAs_enc)

def Body.enc : Body → List UInt8
  | .eph sk => 32 :: Codec.enc sk
  | .request t f m => 33 :: Codec.enc (t, f, m)
  | .opened => [34]
  | .connection m => 35 :: Codec.enc m
  | .established => [36]
  | .send a => 37 :: Codec.enc a
  | .recv c v a t => 38 :: Codec.enc (c, v, a, t)
  | .settled r => 39 :: Codec.enc r

def Body.dec : List UInt8 → Option (Body × List UInt8)
  | 32 :: r => decAs (fun (p : B) => Body.eph p) r
  | 33 :: r => decAs (fun (p : B × B × B) => Body.request p.1 p.2.1 p.2.2) r
  | 34 :: r => some (.opened, r)
  | 35 :: r => decAs (fun (p : B) => Body.connection p) r
  | 36 :: r => some (.established, r)
  | 37 :: r => decAs (fun (p : B) => Body.send p) r
  | 38 :: r => decAs (fun (p : Bool × B × B × Nat) => Body.recv p.1 p.2.1 p.2.2.1 p.2.2.2) r
  | 39 :: r => decAs (fun (p : B) => Body.settled p) r
  | _ => none

instance : Codec Body where
  enc := Body.enc
  dec := Body.dec
  round b rest := by
    cases b <;> simp only [Body.enc, Body.dec, List.cons_append] <;>
      first | rfl | exact decAs_enc _ _ _

def Fact.enc : Fact → List UInt8
  | .eph o p s => 0 :: Codec.enc (o, p, s)
  | .request t f m => 1 :: Codec.enc (t, f, m)
  | .opened r c f a os => 2 :: Codec.enc (r, c, f, a, os)
  | .connection r m => 3 :: Codec.enc (r, m)
  | .established i c p h s k d => 4 :: Codec.enc (i, c, p, h, s, k, d)
  | .send o a => 5 :: Codec.enc (o, a)
  | .recv o c v a t => 6 :: Codec.enc (o, c, v, a, t)
  | .settled c r => 7 :: Codec.enc (c, r)

def Fact.dec : List UInt8 → Option (Fact × List UInt8)
  | 0 :: r => decAs (fun (p : B × B × B) => Fact.eph p.1 p.2.1 p.2.2) r
  | 1 :: r => decAs (fun (p : B × B × B) => Fact.request p.1 p.2.1 p.2.2) r
  | 2 :: r => decAs (fun (p : B × B × B × B × List B) =>
      Fact.opened p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) r
  | 3 :: r => decAs (fun (p : B × B) => Fact.connection p.1 p.2) r
  | 4 :: r => decAs (fun (p : B × B × B × B × B × B × Bool) =>
      Fact.established p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2) r
  | 5 :: r => decAs (fun (p : B × B) => Fact.send p.1 p.2) r
  | 6 :: r => decAs (fun (p : B × Bool × B × B × Nat) =>
      Fact.recv p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) r
  | 7 :: r => decAs (fun (p : B × B) => Fact.settled p.1 p.2) r
  | _ => none

instance : Codec Fact where
  enc := Fact.enc
  dec := Fact.dec
  round f rest := by
    cases f <;> simp only [Fact.enc, Fact.dec, List.cons_append] <;> exact decAs_enc _ _ _

/-- Where a fact sorts under its keys: arrivals by time. -/
def sortOf : Fact → B
  | .recv _ _ _ _ t => Community.be64 t
  | _ => .empty

instance : SortKey Fact := ⟨sortOf⟩

/-- An op of this family, named by its bytes. -/
def mkOp (reqs : List Id) (b : Body) : Op := Op.make b.kind reqs (encode b)

/-- The node's facts: Community's and this family's. -/
abbrev F := Community.Fact ⊕ Fact

/-- What message 1 seals: the community dialed for, the address the
dialer listens on, and the ops it delivers (a joiner's request). -/
def hello (c addr : B) (ops : List Op) : B := encode (c, addr, ops.map (·.bytes))

end Connection
