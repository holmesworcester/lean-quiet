import engine.core.Families
import engine.core.Project
import engine.wire.Node
import ops.community.Community
import ops.connection.connection.Op
import ops.connection.connection.Validate
import ops.connection.eph.Op
import ops.connection.eph.Validate
import ops.connection.established.Op
import ops.connection.established.Validate
import ops.connection.given.Op
import ops.connection.given.Validate
import ops.connection.opened.Op
import ops.connection.opened.Validate
import ops.connection.recv.Op
import ops.connection.recv.Validate
import ops.connection.request.Op
import ops.connection.request.Validate
import ops.connection.send.Op
import ops.connection.send.Validate
import ops.sync.Notice
import ops.sync.NoticeLaws

/-
The connection family: the handshake and sessions, made of ops. Each op
type is a folder below this one: its body and fact (Op.lean) and its
validator (Validate.lean). This file is the registry: the sum of them,
their bytes, which validator judges which op, and the lists the family
files facts in. The request and the connection travel on the bare wire
(conn scope); every other op is local. It reads Community's facts as
well as its own, for the node's key, so the node's one family is the two
composed (`Engine.Family.sum`).

Keys: a node handshakes with its own key (Community's local `endpoint`,
an X25519 key pair), not with a device key. A session's two statics are
the two nodes' keys, and an `established` names its peer by node key; the
trust rule maps a node key to membership through the admissions that
name it (`Community.allowPeer`). Device keys only sign. Kinds 32–39 until
the registry names them.
-/

namespace Connection
open Engine Codec
open Community (decAs decAs_enc)

/-- An op of the connection family: one op type's body. -/
inductive Body where
  | ofEph (b : Eph.Body)
  | ofRequest (b : Request.Body)
  | ofOpened (b : Opened.Body)
  | ofConnection (b : Reply.Body)
  | ofEstablished (b : Established.Body)
  | ofSend (b : Send.Body)
  | ofRecv (b : Recv.Body)
  | ofGiven (b : Given.Body)

/-- A fact of the connection family: one op type's fact. -/
inductive Fact where
  | ofEph (f : Eph.Fact)
  | ofRequest (f : Request.Fact)
  | ofOpened (f : Opened.Fact)
  | ofConnection (f : Reply.Fact)
  | ofEstablished (f : Established.Fact)
  | ofSend (f : Send.Fact)
  | ofRecv (f : Recv.Fact)
  | ofGiven (f : Given.Fact)
  deriving Inhabited, BEq

/-! ## Each op type's fact and body by its fields -/

@[match_pattern] abbrev Fact.eph (of : B) (pk : B) (sk : B) : Fact := .ofEph ⟨of, pk, sk⟩
@[match_pattern] abbrev Fact.request (to : B) (frm : B) (m1 : B) : Fact := .ofRequest ⟨to, frm, m1⟩
@[match_pattern] abbrev Fact.opened (req : B) (c : B) (frm : B) (addr : B) (ops : List B) : Fact := .ofOpened ⟨req, c, frm, addr, ops⟩
@[match_pattern] abbrev Fact.connection (req : B) (m2 : B) : Fact := .ofConnection ⟨req, m2⟩
@[match_pattern] abbrev Fact.established (cid : B) (c : B) (peer : B) (h : B) (sendKey : B) (recvKey : B) (dialer : Bool) : Fact := .ofEstablished ⟨cid, c, peer, h, sendKey, recvKey, dialer⟩
@[match_pattern] abbrev Fact.send (op : B) (addr : B) : Fact := .ofSend ⟨op, addr⟩
@[match_pattern] abbrev Fact.recv (op : B) (onConn : Bool) (via : B) (addr : B) (at_ : Nat) : Fact := .ofRecv ⟨op, onConn, via, addr, at_⟩
@[match_pattern] abbrev Fact.given (conn : B) (x : B) : Fact := .ofGiven ⟨conn, x⟩
@[match_pattern] abbrev Body.eph (sk : B) : Body := .ofEph ⟨sk⟩
@[match_pattern] abbrev Body.request (to : B) (frm : B) (m1 : B) : Body := .ofRequest ⟨to, frm, m1⟩
@[match_pattern] abbrev Body.opened : Body := .ofOpened {}
@[match_pattern] abbrev Body.connection (m2 : B) : Body := .ofConnection ⟨m2⟩
@[match_pattern] abbrev Body.established : Body := .ofEstablished {}
@[match_pattern] abbrev Body.send (addr : B) : Body := .ofSend ⟨addr⟩
@[match_pattern] abbrev Body.recv (onConn : Bool) (via : B) (addr : B) (at_ : Nat) : Body := .ofRecv ⟨onConn, via, addr, at_⟩
@[match_pattern] abbrev Body.given (x : B) : Body := .ofGiven ⟨x⟩

theorem Fact.eph.injEq (of : B) (pk : B) (sk : B) (of' : B) (pk' : B) (sk' : B) :
    (Fact.eph of pk sk = Fact.eph of' pk' sk') = (of = of' ∧ pk = pk' ∧ sk = sk') := by
  simp [Fact.eph]
theorem Fact.request.injEq (to : B) (frm : B) (m1 : B) (to' : B) (frm' : B) (m1' : B) :
    (Fact.request to frm m1 = Fact.request to' frm' m1') = (to = to' ∧ frm = frm' ∧ m1 = m1') := by
  simp [Fact.request]
theorem Fact.opened.injEq (req : B) (c : B) (frm : B) (addr : B) (ops : List B) (req' : B) (c' : B) (frm' : B) (addr' : B) (ops' : List B) :
    (Fact.opened req c frm addr ops = Fact.opened req' c' frm' addr' ops') = (req = req' ∧ c = c' ∧ frm = frm' ∧ addr = addr' ∧ ops = ops') := by
  simp [Fact.opened]
theorem Fact.connection.injEq (req : B) (m2 : B) (req' : B) (m2' : B) :
    (Fact.connection req m2 = Fact.connection req' m2') = (req = req' ∧ m2 = m2') := by
  simp [Fact.connection]
theorem Fact.established.injEq (cid : B) (c : B) (peer : B) (h : B) (sendKey : B) (recvKey : B) (dialer : Bool) (cid' : B) (c' : B) (peer' : B) (h' : B) (sendKey' : B) (recvKey' : B) (dialer' : Bool) :
    (Fact.established cid c peer h sendKey recvKey dialer = Fact.established cid' c' peer' h' sendKey' recvKey' dialer') = (cid = cid' ∧ c = c' ∧ peer = peer' ∧ h = h' ∧ sendKey = sendKey' ∧ recvKey = recvKey' ∧ dialer = dialer') := by
  simp [Fact.established]
theorem Fact.send.injEq (op : B) (addr : B) (op' : B) (addr' : B) :
    (Fact.send op addr = Fact.send op' addr') = (op = op' ∧ addr = addr') := by
  simp [Fact.send]
theorem Fact.recv.injEq (op : B) (onConn : Bool) (via : B) (addr : B) (at_ : Nat) (op' : B) (onConn' : Bool) (via' : B) (addr' : B) (at_' : Nat) :
    (Fact.recv op onConn via addr at_ = Fact.recv op' onConn' via' addr' at_') = (op = op' ∧ onConn = onConn' ∧ via = via' ∧ addr = addr' ∧ at_ = at_') := by
  simp [Fact.recv]
theorem Fact.given.injEq (conn : B) (x : B) (conn' : B) (x' : B) :
    (Fact.given conn x = Fact.given conn' x') = (conn = conn' ∧ x = x') := by
  simp [Fact.given]
theorem Body.eph.injEq (sk : B) (sk' : B) :
    (Body.eph sk = Body.eph sk') = (sk = sk') := by
  simp [Body.eph]
theorem Body.request.injEq (to : B) (frm : B) (m1 : B) (to' : B) (frm' : B) (m1' : B) :
    (Body.request to frm m1 = Body.request to' frm' m1') = (to = to' ∧ frm = frm' ∧ m1 = m1') := by
  simp [Body.request]
theorem Body.connection.injEq (m2 : B) (m2' : B) :
    (Body.connection m2 = Body.connection m2') = (m2 = m2') := by
  simp [Body.connection]
theorem Body.send.injEq (addr : B) (addr' : B) :
    (Body.send addr = Body.send addr') = (addr = addr') := by
  simp [Body.send]
theorem Body.recv.injEq (onConn : Bool) (via : B) (addr : B) (at_ : Nat) (onConn' : Bool) (via' : B) (addr' : B) (at_' : Nat) :
    (Body.recv onConn via addr at_ = Body.recv onConn' via' addr' at_') = (onConn = onConn' ∧ via = via' ∧ addr = addr' ∧ at_ = at_') := by
  simp [Body.recv]
theorem Body.given.injEq (x : B) (x' : B) :
    (Body.given x = Body.given x') = (x = x') := by
  simp [Body.given]

@[simp] def Fact.eph? : Fact → Option Eph.Fact
  | .ofEph x => some x
  | _ => none
@[simp] def Fact.request? : Fact → Option Request.Fact
  | .ofRequest x => some x
  | _ => none
@[simp] def Fact.opened? : Fact → Option Opened.Fact
  | .ofOpened x => some x
  | _ => none
@[simp] def Fact.connection? : Fact → Option Reply.Fact
  | .ofConnection x => some x
  | _ => none
@[simp] def Fact.established? : Fact → Option Established.Fact
  | .ofEstablished x => some x
  | _ => none
@[simp] def Fact.send? : Fact → Option Send.Fact
  | .ofSend x => some x
  | _ => none
@[simp] def Fact.recv? : Fact → Option Recv.Fact
  | .ofRecv x => some x
  | _ => none
@[simp] def Fact.given? : Fact → Option Given.Fact
  | .ofGiven x => some x
  | _ => none

/-- Each body's op type. -/
def Body.kind : Body → UInt8
  | .ofEph _ => 32
  | .ofRequest _ => 33
  | .ofOpened _ => 34
  | .ofConnection _ => 35
  | .ofEstablished _ => 36
  | .ofSend _ => 37
  | .ofRecv _ => 38
  | .ofGiven _ => 39

/-! ## Bytes: each op type writes its own, tag first -/

def decWith {α β} [Codec α] (f : α → β) (bs : List UInt8) : Option (β × List UInt8) :=
  (Codec.dec bs : Option (α × List UInt8)).map fun p => (f p.1, p.2)

def Body.enc : Body → List UInt8
  | .ofEph a => Codec.enc a
  | .ofRequest a => Codec.enc a
  | .ofOpened a => Codec.enc a
  | .ofConnection a => Codec.enc a
  | .ofEstablished a => Codec.enc a
  | .ofSend a => Codec.enc a
  | .ofRecv a => Codec.enc a
  | .ofGiven a => Codec.enc a

def Body.dec (bs : List UInt8) : Option (Body × List UInt8) :=
  match bs.head? with
  | some 32 => decWith Body.ofEph bs
  | some 33 => decWith Body.ofRequest bs
  | some 34 => decWith Body.ofOpened bs
  | some 35 => decWith Body.ofConnection bs
  | some 36 => decWith Body.ofEstablished bs
  | some 37 => decWith Body.ofSend bs
  | some 38 => decWith Body.ofRecv bs
  | some 39 => decWith Body.ofGiven bs
  | _ => none

def Body.encInto (buf : ByteArray) : Body → ByteArray
  | .ofEph a => Codec.encInto buf a
  | .ofRequest a => Codec.encInto buf a
  | .ofOpened a => Codec.encInto buf a
  | .ofConnection a => Codec.encInto buf a
  | .ofEstablished a => Codec.encInto buf a
  | .ofSend a => Codec.encInto buf a
  | .ofRecv a => Codec.encInto buf a
  | .ofGiven a => Codec.encInto buf a

def Body.decFrom (b : ByteArray) (i : Nat) : Option (Body × Nat) :=
  match b[i]? with
  | some 32 => decFromAs Body.ofEph b i
  | some 33 => decFromAs Body.ofRequest b i
  | some 34 => decFromAs Body.ofOpened b i
  | some 35 => decFromAs Body.ofConnection b i
  | some 36 => decFromAs Body.ofEstablished b i
  | some 37 => decFromAs Body.ofSend b i
  | some 38 => decFromAs Body.ofRecv b i
  | some 39 => decFromAs Body.ofGiven b i
  | _ => none

theorem Body.dec_of {α} [Codec α] {t : UInt8} (f : α → Body) (a : α) (rest : List UInt8)
    (ht : (Codec.enc a).head? = some t) (hd : ∀ bs : List UInt8, bs.head? = some t → Body.dec bs = decWith f bs) :
    Body.dec (Codec.enc a ++ rest) = some (f a, rest) := by
  have h1 : (Codec.enc a ++ rest).head? = some t := by
    cases h : Codec.enc a with
    | nil => simp [h] at ht
    | cons x l => simpa [h] using ht
  rw [hd _ h1]; simp [decWith, Codec.round]

theorem Body.decFrom_of {α} [Codec α] {t : UInt8} (f : α → Body) (a : α) {b : ByteArray} {i : Nat}
    (ht : (Codec.enc a).head? = some t) (hd : ∀ (b : ByteArray) (i : Nat), b[i]? = some t → Body.decFrom b i = decFromAs f b i)
    (h : Codec.At b i (Codec.enc a)) : Body.decFrom b i = some (f a, i + (Codec.enc a).length) := by
  have hb : b[i]? = some t := by
    cases he : Codec.enc a with
    | nil => simp [he] at ht
    | cons x l =>
      simp [he] at ht; subst ht; rw [he] at h; exact h.tag
  rw [hd b i hb]; exact decFromAs_at f h

instance : Codec Body where
  enc := Body.enc
  dec := Body.dec
  round x rest := by
    cases x with
    | ofEph a => exact Body.dec_of (t := 32) _ _ _ rfl (fun bs h => by simp only [Body.dec, h])
    | ofRequest a => exact Body.dec_of (t := 33) _ _ _ rfl (fun bs h => by simp only [Body.dec, h])
    | ofOpened a => exact Body.dec_of (t := 34) _ _ _ rfl (fun bs h => by simp only [Body.dec, h])
    | ofConnection a => exact Body.dec_of (t := 35) _ _ _ rfl (fun bs h => by simp only [Body.dec, h])
    | ofEstablished a => exact Body.dec_of (t := 36) _ _ _ rfl (fun bs h => by simp only [Body.dec, h])
    | ofSend a => exact Body.dec_of (t := 37) _ _ _ rfl (fun bs h => by simp only [Body.dec, h])
    | ofRecv a => exact Body.dec_of (t := 38) _ _ _ rfl (fun bs h => by simp only [Body.dec, h])
    | ofGiven a => exact Body.dec_of (t := 39) _ _ _ rfl (fun bs h => by simp only [Body.dec, h])
  encInto := Body.encInto
  encInto_eq buf x := by cases x <;> exact Codec.encInto_eq _ _
  decFrom := Body.decFrom
  decFrom_at x h := by
    cases x with
    | ofEph a => exact Body.decFrom_of (t := 32) _ _ rfl (fun b i h => by simp only [Body.decFrom, h]) h
    | ofRequest a => exact Body.decFrom_of (t := 33) _ _ rfl (fun b i h => by simp only [Body.decFrom, h]) h
    | ofOpened a => exact Body.decFrom_of (t := 34) _ _ rfl (fun b i h => by simp only [Body.decFrom, h]) h
    | ofConnection a => exact Body.decFrom_of (t := 35) _ _ rfl (fun b i h => by simp only [Body.decFrom, h]) h
    | ofEstablished a => exact Body.decFrom_of (t := 36) _ _ rfl (fun b i h => by simp only [Body.decFrom, h]) h
    | ofSend a => exact Body.decFrom_of (t := 37) _ _ rfl (fun b i h => by simp only [Body.decFrom, h]) h
    | ofRecv a => exact Body.decFrom_of (t := 38) _ _ rfl (fun b i h => by simp only [Body.decFrom, h]) h
    | ofGiven a => exact Body.decFrom_of (t := 39) _ _ rfl (fun b i h => by simp only [Body.decFrom, h]) h

def Fact.enc : Fact → List UInt8
  | .ofEph a => Codec.enc a
  | .ofRequest a => Codec.enc a
  | .ofOpened a => Codec.enc a
  | .ofConnection a => Codec.enc a
  | .ofEstablished a => Codec.enc a
  | .ofSend a => Codec.enc a
  | .ofRecv a => Codec.enc a
  | .ofGiven a => Codec.enc a

def Fact.dec (bs : List UInt8) : Option (Fact × List UInt8) :=
  match bs.head? with
  | some 0 => decWith Fact.ofEph bs
  | some 1 => decWith Fact.ofRequest bs
  | some 2 => decWith Fact.ofOpened bs
  | some 3 => decWith Fact.ofConnection bs
  | some 4 => decWith Fact.ofEstablished bs
  | some 5 => decWith Fact.ofSend bs
  | some 6 => decWith Fact.ofRecv bs
  | some 7 => decWith Fact.ofGiven bs
  | _ => none

def Fact.encInto (buf : ByteArray) : Fact → ByteArray
  | .ofEph a => Codec.encInto buf a
  | .ofRequest a => Codec.encInto buf a
  | .ofOpened a => Codec.encInto buf a
  | .ofConnection a => Codec.encInto buf a
  | .ofEstablished a => Codec.encInto buf a
  | .ofSend a => Codec.encInto buf a
  | .ofRecv a => Codec.encInto buf a
  | .ofGiven a => Codec.encInto buf a

def Fact.decFrom (b : ByteArray) (i : Nat) : Option (Fact × Nat) :=
  match b[i]? with
  | some 0 => decFromAs Fact.ofEph b i
  | some 1 => decFromAs Fact.ofRequest b i
  | some 2 => decFromAs Fact.ofOpened b i
  | some 3 => decFromAs Fact.ofConnection b i
  | some 4 => decFromAs Fact.ofEstablished b i
  | some 5 => decFromAs Fact.ofSend b i
  | some 6 => decFromAs Fact.ofRecv b i
  | some 7 => decFromAs Fact.ofGiven b i
  | _ => none

theorem Fact.dec_of {α} [Codec α] {t : UInt8} (f : α → Fact) (a : α) (rest : List UInt8)
    (ht : (Codec.enc a).head? = some t) (hd : ∀ bs : List UInt8, bs.head? = some t → Fact.dec bs = decWith f bs) :
    Fact.dec (Codec.enc a ++ rest) = some (f a, rest) := by
  have h1 : (Codec.enc a ++ rest).head? = some t := by
    cases h : Codec.enc a with
    | nil => simp [h] at ht
    | cons x l => simpa [h] using ht
  rw [hd _ h1]; simp [decWith, Codec.round]

theorem Fact.decFrom_of {α} [Codec α] {t : UInt8} (f : α → Fact) (a : α) {b : ByteArray} {i : Nat}
    (ht : (Codec.enc a).head? = some t) (hd : ∀ (b : ByteArray) (i : Nat), b[i]? = some t → Fact.decFrom b i = decFromAs f b i)
    (h : Codec.At b i (Codec.enc a)) : Fact.decFrom b i = some (f a, i + (Codec.enc a).length) := by
  have hb : b[i]? = some t := by
    cases he : Codec.enc a with
    | nil => simp [he] at ht
    | cons x l =>
      simp [he] at ht; subst ht; rw [he] at h; exact h.tag
  rw [hd b i hb]; exact decFromAs_at f h

instance : Codec Fact where
  enc := Fact.enc
  dec := Fact.dec
  round x rest := by
    cases x with
    | ofEph a => exact Fact.dec_of (t := 0) _ _ _ rfl (fun bs h => by simp only [Fact.dec, h])
    | ofRequest a => exact Fact.dec_of (t := 1) _ _ _ rfl (fun bs h => by simp only [Fact.dec, h])
    | ofOpened a => exact Fact.dec_of (t := 2) _ _ _ rfl (fun bs h => by simp only [Fact.dec, h])
    | ofConnection a => exact Fact.dec_of (t := 3) _ _ _ rfl (fun bs h => by simp only [Fact.dec, h])
    | ofEstablished a => exact Fact.dec_of (t := 4) _ _ _ rfl (fun bs h => by simp only [Fact.dec, h])
    | ofSend a => exact Fact.dec_of (t := 5) _ _ _ rfl (fun bs h => by simp only [Fact.dec, h])
    | ofRecv a => exact Fact.dec_of (t := 6) _ _ _ rfl (fun bs h => by simp only [Fact.dec, h])
    | ofGiven a => exact Fact.dec_of (t := 7) _ _ _ rfl (fun bs h => by simp only [Fact.dec, h])
  encInto := Fact.encInto
  encInto_eq buf x := by cases x <;> exact Codec.encInto_eq _ _
  decFrom := Fact.decFrom
  decFrom_at x h := by
    cases x with
    | ofEph a => exact Fact.decFrom_of (t := 0) _ _ rfl (fun b i h => by simp only [Fact.decFrom, h]) h
    | ofRequest a => exact Fact.decFrom_of (t := 1) _ _ rfl (fun b i h => by simp only [Fact.decFrom, h]) h
    | ofOpened a => exact Fact.decFrom_of (t := 2) _ _ rfl (fun b i h => by simp only [Fact.decFrom, h]) h
    | ofConnection a => exact Fact.decFrom_of (t := 3) _ _ rfl (fun b i h => by simp only [Fact.decFrom, h]) h
    | ofEstablished a => exact Fact.decFrom_of (t := 4) _ _ rfl (fun b i h => by simp only [Fact.decFrom, h]) h
    | ofSend a => exact Fact.decFrom_of (t := 5) _ _ rfl (fun b i h => by simp only [Fact.decFrom, h]) h
    | ofRecv a => exact Fact.decFrom_of (t := 6) _ _ rfl (fun b i h => by simp only [Fact.decFrom, h]) h
    | ofGiven a => exact Fact.decFrom_of (t := 7) _ _ rfl (fun b i h => by simp only [Fact.decFrom, h]) h

/-- Where a fact sorts under its keys: arrivals by time. -/
def sortOf : Fact → B
  | .ofRecv f => Recv.sortKey f
  | _ => .empty

instance : SortKey Fact := ⟨sortOf⟩

/-- An op of this family, named by its bytes. -/
def mkOp (reqs : List Id) (b : Body) : Op := Op.make b.kind reqs (encode b)

/-- The node's facts: Community's and this family's. -/
abbrev F := Community.Fact ⊕ Fact

/-- What message 1 seals: the community dialed for, the address the
dialer listens on, and the ops it delivers (a joiner's request). -/
def hello (c addr : B) (ops : List Op) : B := encode (c, addr, ops.map (·.bytes))

/-- An op's validator, by its body: its op type's (each folder's
Validate.lean), given the facts it cites, typed. -/
def check (K : Keys) (o : Op) : Body → List F → Option Fact
  | .ofEph b, [_] => (Eph.check K o b).map .ofEph
  | .ofRequest b, [] => (Request.check b).map .ofRequest
  | .ofOpened b, [.inr (.ofRequest r), .inl (.ofEndpoint e)] => (Opened.check K o b r e).map .ofOpened
  | .ofConnection b, [.inr (.ofRequest r)] => (Reply.check o b r).map .ofConnection
  | .ofEstablished b, [.inr (.ofConnection c), .inr (.ofRequest r), .inr (.ofEph e), .inl (.ofEndpoint n)] =>
    (Established.check K o b c r e n).map .ofEstablished
  | .ofSend b, [_] => (Send.check o b).map .ofSend
  | .ofRecv b, [_] => (Recv.check o b).map .ofRecv
  | .ofGiven b, [.inr (.ofConnection c)] => (Given.check o b c).map .ofGiven
  | _, _ => none

def validate (K : Keys) (o : Op) (fs : List F) : Option Fact :=
  match (decode o.body : Option Body) with
  | some b => if b.kind = o.kind then check K o b fs else none
  | none => none

/-! ## Relations: each op type's lists, read in the family (same names, so the same keys) -/

namespace eph
def byOf : Rel Fact := Eph.byOf.comap Fact.eph?
end eph

namespace request
def byTo : Rel Fact := Request.byTo.comap Fact.request?
def byFrm : Rel Fact := Request.byFrm.comap Fact.request?
end request

namespace opened
def all : Rel Fact := Opened.all.comap Fact.opened?
def byRequest : Rel Fact := Opened.byRequest.comap Fact.opened?
end opened

namespace connection
def byRequest : Rel Fact := Reply.byRequest.comap Fact.connection?
end connection

namespace established
def all : Rel Fact := Established.all.comap Fact.established?
def byConn : Rel Fact := Established.byConn.comap Fact.established?
end established

namespace send
def all : Rel Fact := Send.all.comap Fact.send?
end send

namespace recv
def byOp : Rel Fact := Recv.byOp.comap Fact.recv?
end recv

namespace given
def byConn : Rel Fact := Given.byConn.comap Fact.given?
end given

def rels : List (Rel Fact) :=
  [eph.byOf, request.byTo, request.byFrm, opened.all, opened.byRequest, connection.byRequest,
   established.all, established.byConn, send.all, recv.byOp, given.byConn]

def keys : Fact → List ByteArray := keysOf rels

/-- The request and the connection go on the bare wire; the rest is local. -/
def scopeOf (o : Op) : Scope := if o.kind = 33 ∨ o.kind = 35 then .conn else .local

def owns (k : UInt8) : Bool := 32 ≤ k && k ≤ 39

def family (K : Keys) : Family₂ Community.Fact Fact :=
  { validate := validate K, keys, scope := scopeOf, owns }

/-- The node's one family. -/
def node (C : Community.Crypto) (K : Keys) : Family F := Family.sum (Community.family C) (family K)

end Connection

namespace Connection
open Engine Engine.Sync Codec

/-- This node's key, while it is in community c: `Community.mine` names a
device of c whose secret it holds, live or waiting on a join. -/
def meV (c : B) : View F (Option B) := do
  let some _ ← ((Community.mine c).liftL : View F _) | return none
  let k ← ((Community.nodeKey).liftL : View F _)
  return k.map (·.1)
end Connection
namespace Connection
open Engine Engine.Sync Codec
section
variable {m : Type → Type} [Monad m] [Lists F m] [Store F m] [Fresh m]

/-- This family's rows of a relation: op id and fact. -/
def rows (r : Rel Fact) (args : List B) : m (List (Id × Fact)) := do
  let a : Answer F ← Lists.list (m := m) (r.query args)
  return a.rights.map fun ((_, x), f) => (x, f)

def count (r : Rel Fact) (args : List B) : m Nat := do
  let a : Answer F ← Lists.list (m := m) (r.query args (limit := some 0))
  return a.total

/-- Whether a hello delivers the op `req`. -/
def delivers (req : Id) : Option (B × B × List B) → Bool
  | some (_, _, ops) => ops.any fun b => (Op.decode b).any (·.id == req)
  | none => false
end
end Connection
namespace Connection
open Engine Engine.Sync Codec
section
variable [fr : Fresh (Model F)]

/-- An op of the Connection family: what open, answer and establish
write. -/
def ConnOp (o : Op) : Prop := ∃ (reqs : List Id) (b : Body), o = mkOp reqs b

theorem body_conn (reqs : List Id) (b : Body) : (decode (mkOp reqs b).body : Option Body) = some b :=
  Codec.decode_encode b
end
end Connection
namespace Community
open Engine

theorem reads_unremoved (c : Id) (rows : List (Pos × Fact)) : (unremoved c rows).Reads (RelKey rels) := by
  induction rows with
  | nil => exact .pure _
  | cons pf t ih =>
    obtain ⟨p, f⟩ := pf
    cases f with
    | ofAdmission x =>
      obtain ⟨c', u, d, e⟩ := x
      show View.Reads _ (if c' = c then _ else _)
      split
      · exact .list ⟨removal.byUser, by simp [rels], [c, u], rfl⟩ fun a => by
          show View.Reads _ (if a.total = 0 then _ else _)
          split
          · exact ih
          · exact .pure _
      · exact ih
    | _ => exact ih

theorem reads_deviceLive (c : Id) (d : Key) : (deviceLive c d).Reads (RelKey rels) :=
  (View.Reads.read ⟨admission.byDevice, by simp [rels], [c, d], rfl⟩).bind fun a => by
    show View.Reads _ (if a.rows.isEmpty then _ else _)
    split
    · exact .pure _
    · exact reads_unremoved c a.rows

theorem reads_live (c : Id) (rows : List (Pos × Fact)) : (live c rows).Reads (RelKey rels) := by
  induction rows with
  | nil => exact .pure _
  | cons pf t ih =>
    obtain ⟨p, f⟩ := pf
    cases f with
    | ofAdmission x =>
      obtain ⟨c', u, d, e⟩ := x
      show View.Reads _ (if c' = c then _ else _)
      split
      · exact (reads_deviceLive c d).bind fun _ => ih.bind fun _ => .pure _
      · exact ih
    | _ => exact ih

theorem reads_allowPeer (c : Id) (e : Key) : (allowPeer c e).Reads (RelKey rels) :=
  (View.Reads.read ⟨admission.byKey, by simp [rels], [c, e], rfl⟩).bind fun a =>
    (reads_live c a.rows).bind fun _ => .pure _

theorem reads_members (c : Id) : (members c).Reads (RelKey rels) :=
  (View.Reads.read ⟨admission.all, by simp [rels], [c], rfl⟩).bind fun a =>
    (reads_live c a.rows).bind fun _ => .pure _

theorem reads_recipients (c : Id) : (recipients c).Reads (RelKey rels) :=
  (View.Reads.read ⟨admission.all, by simp [rels], [c], rfl⟩).bind fun a =>
    (reads_live c a.rows).bind fun _ => .pure _
end Community
namespace Connection
open Engine

/-- The node's Community part: the Community ops its store holds, with
Community's own verdicts over them (`Engine.DB.proj`). -/
noncomputable abbrev community (C : Community.Crypto) (s : DB F) : DB Community.Fact :=
  s.proj (Community.family C) owns

/-- No Community relation shares its names with a Connection relation. -/
theorem rels_apart : ∀ r ∈ Community.rels, ∀ r' ∈ rels, ¬ (r'.kind = r.kind ∧ r'.name = r.name) := by
  decide
end Connection
namespace Connection
open Engine
variable {C : Community.Crypto} {K : Keys} {s : DB F}

/-- **`sum_project` for the running node.** At rest, the node's
Community part keeps Community's invariant and is at rest. It holds
exactly the node's Community ops (kinds Connection does not own), and an
op is Valid there with a Community fact exactly when it is in the node.
Every Community view reading only Community relations answers, lifted to
the node's store, as it does on the Community part. -/
theorem sum_project_node (h : Inv (node C K) s) (hq : s.queue = []) :
    Inv (Community.family C) (community C s) ∧ (community C s).queue = [] ∧
      (∀ x o, (community C s).ops x = some o ↔ s.ops x = some o ∧ owns o.kind = false) ∧
      (∀ x f, Community.V C (community C s).ops x f ↔ s.status x = some (.valid (.inl f))) ∧
      ∀ {α : Type} (v : View Community.Fact α), v.Reads (RelKey Community.rels) →
        (v.liftL : View F α).eval s = v.eval (community C s) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := sum_project (b := family K) h hq
  exact ⟨h1, h2, h3, h4, fun v hv =>
    h5 v (hv.mono fun _ => leftKey_rels h rfl Community.rels_short rels_apart)⟩

theorem community_inv (h : Inv (node C K) s) (hq : s.queue = []) :
    Inv (Community.family C) (community C s) :=
  (sum_project_node h hq).1

theorem view_node (h : Inv (node C K) s) (hq : s.queue = []) {α : Type}
    {v : View Community.Fact α} (hv : v.Reads (RelKey Community.rels)) :
    (v.liftL : View F α).eval s = v.eval (community C s) :=
  (sum_project_node h hq).2.2.2.2 v hv
end Connection
namespace Connection
open Engine
variable {C : Community.Crypto} {K : Keys} {s : DB F}
open Community (Admitted Removed)

/-- **Which nodes the node lets in.** At rest, the node's `allowPeer`
accepts node key e for c exactly when a device admitted under e is live
(admitted, into no removed user) among the Community ops it holds. -/
theorem connect_iff_node (h : Inv (node C K) s) (hq : s.queue = []) (c : Id) (e : Community.Key) :
    ((Community.allowPeer c e).liftL : View F Bool).eval s = true ↔
      ∃ u d, Admitted C (community C s).ops c u d e ∧ Community.Live C (community C s).ops c d := by
  rw [view_node h hq (Community.reads_allowPeer c e)]
  exact Community.connect_iff (community_inv h hq) hq c e

/-- **A removal, once the node holds it, cuts the removed user's
devices' node out of its trust rule.** -/
theorem removal_cuts_off_node (h : Inv (node C K) s) (hq : s.queue = []) {c u : Id}
    {e : Community.Key} (hr : Removed C (community C s).ops c u)
    (only : ∀ u' d, Admitted C (community C s).ops c u' d e → ∃ e', Admitted C (community C s).ops c u d e') :
    ((Community.allowPeer c e).liftL : View F Bool).eval s = false := by
  rw [view_node h hq (Community.reads_allowPeer c e)]
  exact Community.removal_cuts_off (community_inv h hq) hq hr only

end Connection
