/-
The connection family's ops and facts, and how they are written as
bytes. Each op type's meaning lives in its own file: Eph, Request,
Opened, Connection, Established, Send and Recv.

Keys: devices are named by their Ed25519 keys, as in Community. Noise
runs on the X25519 keys those convert to (`Keys`).

Kinds 32–38 until the registry names them.
-/
import ops.connection.Noise
import ops.community.Community

namespace Connection
open Engine Codec

abbrev B := ByteArray

/-- Noise, plus the conversion of Ed25519 device keys to the X25519
keys Noise runs on. -/
structure Keys where
  suite : Noise.Suite B
  /-- A device key's X25519 key; empty if it is not a point. -/
  xPub : B → B
  /-- The X25519 secret of a device seed. -/
  xSec : B → B
  /-- The frames' AEAD (XChaCha20-Poly1305): key, 24-byte nonce,
  associated data, plaintext. -/
  fenc : B → B → B → B → B
  fdec : B → B → B → B → Option B

/-- What the laws assume of the conversion: a seed's X25519 secret has
the X25519 key of the seed's device key. -/
def Keys.Good (K : Keys) (edPub : B → B) : Prop :=
  K.suite.Good ∧ (∀ seed, K.xPub (edPub seed) = K.suite.pub (K.xSec seed)) ∧
    ∀ k n ad p, K.fdec k n ad (K.fenc k n ad p) = some p

/-- libsodium's. -/
def sodium : Keys where
  suite := Noise.suite
  xPub := Noise.staticPubOf
  xSec seed := Noise.staticOf (Community.Device.ofSeed seed).sk
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

inductive Fact where
  | eph (of pk sk : B)
  | request (to frm m1 : B)
  | opened (req c frm addr : B) (ops : List B)
  | connection (req m2 : B)
  | established (cid c peer h sendKey recvKey : B) (dialer : Bool)
  | send (op addr : B)
  | recv (op : B) (onConn : Bool) (via addr : B) (at_ : Nat)
  deriving Inhabited, BEq

def Body.kind : Body → UInt8
  | .eph .. => 32 | .request .. => 33 | .opened => 34 | .connection .. => 35
  | .established => 36 | .send .. => 37 | .recv .. => 38

open Community (decAs decAs_enc)

def Body.enc : Body → List UInt8
  | .eph sk => 32 :: Codec.enc sk
  | .request t f m => 33 :: Codec.enc (t, f, m)
  | .opened => [34]
  | .connection m => 35 :: Codec.enc m
  | .established => [36]
  | .send a => 37 :: Codec.enc a
  | .recv c v a t => 38 :: Codec.enc (c, v, a, t)

def Body.dec : List UInt8 → Option (Body × List UInt8)
  | 32 :: r => decAs (fun (p : B) => Body.eph p) r
  | 33 :: r => decAs (fun (p : B × B × B) => Body.request p.1 p.2.1 p.2.2) r
  | 34 :: r => some (.opened, r)
  | 35 :: r => decAs (fun (p : B) => Body.connection p) r
  | 36 :: r => some (.established, r)
  | 37 :: r => decAs (fun (p : B) => Body.send p) r
  | 38 :: r => decAs (fun (p : Bool × B × B × Nat) => Body.recv p.1 p.2.1 p.2.2.1 p.2.2.2) r
  | _ => none

/-- `Body.enc`, as it runs: appended to a buffer (`Engine.Codec`). -/
def Body.encInto (buf : ByteArray) : Body → ByteArray
  | .eph sk => Codec.encInto (buf.push 32) sk
  | .request t f m => Codec.encInto (buf.push 33) (t, f, m)
  | .opened => buf.push 34
  | .connection m => Codec.encInto (buf.push 35) m
  | .established => buf.push 36
  | .send a => Codec.encInto (buf.push 37) a
  | .recv c v a t => Codec.encInto (buf.push 38) (c, v, a, t)

/-- `Body.dec`, as it runs: read at offset i of a byte array. -/
def Body.decFrom (b : ByteArray) (i : Nat) : Option (Body × Nat) :=
  match b[i]? with
  | some 32 => decFromAs (fun (p : B) => Body.eph p) b (i + 1)
  | some 33 => decFromAs (fun (p : B × B × B) => Body.request p.1 p.2.1 p.2.2) b (i + 1)
  | some 34 => some (.opened, i + 1)
  | some 35 => decFromAs (fun (p : B) => Body.connection p) b (i + 1)
  | some 36 => some (.established, i + 1)
  | some 37 => decFromAs (fun (p : B) => Body.send p) b (i + 1)
  | some 38 => decFromAs (fun (p : Bool × B × B × Nat) => Body.recv p.1 p.2.1 p.2.2.1 p.2.2.2) b (i + 1)
  | _ => none

instance : Codec Body where
  enc := Body.enc
  dec := Body.dec
  round b rest := by
    cases b <;> simp only [Body.enc, Body.dec, List.cons_append] <;>
      first | rfl | exact decAs_enc _ _ _
  encInto := Body.encInto
  encInto_eq buf x := by
    cases x <;> simp only [Body.encInto, Body.enc] <;> first | exact encInto_tag .. | exact push_toList ..
  decFrom := Body.decFrom
  decFrom_at x h := by
    cases x <;> simp only [Body.enc] at h <;> simp only [Body.decFrom, h.tag] <;>
      first | exact decFromAs_tag _ h | rfl

def Fact.enc : Fact → List UInt8
  | .eph o p s => 0 :: Codec.enc (o, p, s)
  | .request t f m => 1 :: Codec.enc (t, f, m)
  | .opened r c f a os => 2 :: Codec.enc (r, c, f, a, os)
  | .connection r m => 3 :: Codec.enc (r, m)
  | .established i c p h s k d => 4 :: Codec.enc (i, c, p, h, s, k, d)
  | .send o a => 5 :: Codec.enc (o, a)
  | .recv o c v a t => 6 :: Codec.enc (o, c, v, a, t)

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
  | _ => none

/-- `Fact.enc`, as it runs: appended to a buffer (`Engine.Codec`). -/
def Fact.encInto (buf : ByteArray) : Fact → ByteArray
  | .eph o p s => Codec.encInto (buf.push 0) (o, p, s)
  | .request t f m => Codec.encInto (buf.push 1) (t, f, m)
  | .opened r c f a os => Codec.encInto (buf.push 2) (r, c, f, a, os)
  | .connection r m => Codec.encInto (buf.push 3) (r, m)
  | .established i c p h s k d => Codec.encInto (buf.push 4) (i, c, p, h, s, k, d)
  | .send o a => Codec.encInto (buf.push 5) (o, a)
  | .recv o c v a t => Codec.encInto (buf.push 6) (o, c, v, a, t)

/-- `Fact.dec`, as it runs: read at offset i of a byte array. -/
def Fact.decFrom (b : ByteArray) (i : Nat) : Option (Fact × Nat) :=
  match b[i]? with
  | some 0 => decFromAs (fun (p : B × B × B) => Fact.eph p.1 p.2.1 p.2.2) b (i + 1)
  | some 1 => decFromAs (fun (p : B × B × B) => Fact.request p.1 p.2.1 p.2.2) b (i + 1)
  | some 2 => decFromAs (fun (p : B × B × B × B × List B) =>
      Fact.opened p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) b (i + 1)
  | some 3 => decFromAs (fun (p : B × B) => Fact.connection p.1 p.2) b (i + 1)
  | some 4 => decFromAs (fun (p : B × B × B × B × B × B × Bool) =>
      Fact.established p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2) b (i + 1)
  | some 5 => decFromAs (fun (p : B × B) => Fact.send p.1 p.2) b (i + 1)
  | some 6 => decFromAs (fun (p : B × Bool × B × B × Nat) =>
      Fact.recv p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) b (i + 1)
  | _ => none

instance : Codec Fact where
  enc := Fact.enc
  dec := Fact.dec
  round f rest := by
    cases f <;> simp only [Fact.enc, Fact.dec, List.cons_append] <;> exact decAs_enc _ _ _
  encInto := Fact.encInto
  encInto_eq buf x := by
    cases x <;> simp only [Fact.encInto, Fact.enc] <;> first | exact encInto_tag .. | exact push_toList ..
  decFrom := Fact.decFrom
  decFrom_at x h := by
    cases x <;> simp only [Fact.enc] at h <;> simp only [Fact.decFrom, h.tag] <;>
      first | exact decFromAs_tag _ h | rfl

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
