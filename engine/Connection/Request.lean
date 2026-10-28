/-
`request` (conn scope: the bare wire, one peer, never synced): Noise
message 1 (`e, es, ss`), as poc-17's conn.request and tiny's
connection.request. It is to the responder's static key, from the
initiator's (in the clear, as poc-17's, so the responder can decide to
answer before it opens anything), and carries the message: the
initiator's ephemeral key, then the sealed hello.

The hello is the community the initiator dials for, the address it
listens on, and ops it delivers. A joiner's request rides here, so it
reaches the inviter before anyone approves it and opens nothing ("a
request alone opens nothing and earns no reply").

Valid iff the keys are 32 bytes and the message holds an ephemeral key
and a tag: structural, so every holder judges it the same. Its fact is
filed under `request.byTo [to]`, which is how a responder finds what is
addressed to it.

`connect` is the command: an `eph` (local), the request, and a `send`
courier carrying the request's bytes to the address. Redialing writes
the courier again; the request is the same op (same bytes, same id)
until a new ephemeral is drawn.

SKELETON: signatures are the contract; bodies are unwritten.
-/
import Connection.Eph

namespace Connection
open Engine

structure Request where
  to : ByteArray
  frm : ByteArray
  m1 : ByteArray

def Request.kind : UInt8 := 33

/-- What message 1 seals. -/
structure Hello where
  community : Id
  addr : ByteArray
  ops : List ByteArray

/-- The prologue both ends mix in: the protocol's name and version. -/
def prologue : ByteArray := "quiet connection v1".toUTF8

def Request.check (b : Request) : Bool := sorry

/-- Dial `to` (an X25519 static key) at `addr`, from the device whose
seed is `seed`, with ephemeral secret `e`: the ops to write. -/
def connect (S : Noise.Suite) (seed to addr : ByteArray) (hello : Hello) (e : ByteArray) : List Op :=
  sorry

end Connection
