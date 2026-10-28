/-
`opened` (local, the responder's): a request it has read. It cites the
request and this device's `secret` op (Community's), and its validator
runs Noise's `read1` with the static secret of that seed. Valid iff the
request opens. Its fact is the request, the initiator's static key,
the hello, and the handshake state after message 1, which `established`
continues from.

This is poc-17's `Keys`: a local op cites the secret, so the shared op
needs no secret to be judged. It is filed under `opened.all`. A close
purges it, and so does a dismissal of a request that was never answered.

SKELETON: signatures are the contract; bodies are unwritten.
-/
import Connection.Request

namespace Connection
open Engine

structure Opened where

def Opened.kind : UInt8 := 34

structure OpenedFact where
  request : Id
  frm : ByteArray
  hello : Hello
  st : Noise.Sym

def Opened.check (S : Noise.Suite) (o : Op) (req : Request) (seed : ByteArray) : Option OpenedFact :=
  sorry

/-- Open request `req`, with this device's secret op `secretOp`. -/
def Opened.op (req secretOp : Id) : Op := sorry

end Connection
