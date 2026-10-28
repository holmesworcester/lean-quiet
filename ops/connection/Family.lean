/-
The connection family: each op type's validator by its body (the op
files hold their meaning), the relations, and where each op travels.
The request and the connection travel on the bare wire (conn scope);
every other op is local. It reads Community's facts as well as its
own, for the device secret, so the node's one family is the two
composed (`Engine.Family.sum`).
-/
import Connection.Recv
import Engine.Families

namespace Connection
open Engine Codec

def check (K : Keys) (o : Op) : Body → List F → Option Fact
  | .eph sk, fs => Eph.check K o sk fs
  | .request t f m, fs => Request.check K t f m fs
  | .opened, fs => Opened.check K o fs
  | .connection m, fs => Reply.check o m fs
  | .established, fs => Established.check K o fs
  | .send a, fs => Send.check o a fs
  | .recv c v a t, fs => Recv.check o c v a t fs

def validate (K : Keys) (o : Op) (fs : List F) : Option Fact :=
  match (decode o.body : Option Body) with
  | some b => if b.kind = o.kind then check K o b fs else none
  | none => none

def rels : List (Rel Fact) :=
  [eph.byOf, request.byTo, request.byFrm, opened.all, opened.byRequest, connection.byRequest,
   established.all, established.byConn, send.all, recv.byOp]

def keys : Fact → List ByteArray := keysOf rels

/-- The request and the connection go on the bare wire; the rest is local. -/
def scopeOf (o : Op) : Scope := if o.kind = 33 ∨ o.kind = 35 then .conn else .local

def owns (k : UInt8) : Bool := 32 ≤ k && k ≤ 38

def family (K : Keys) : Family₂ Community.Fact Fact :=
  { validate := validate K, keys, scope := scopeOf, owns }

/-- The node's one family. -/
def node (C : Community.Crypto) (K : Keys) : Family F := Family.sum (Community.family C) (family K)

end Connection
