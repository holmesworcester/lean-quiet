/-
`eph` (local): one ephemeral X25519 secret for one handshake, drawn at
random from the OS by the side that uses it: the initiator's `e`, the
responder's `f`. The side's `established` op cites it, and a close
purges both, which is what leaves the session's traffic unreadable
afterwards: the transport keys depend on `ee`, and no other copy of
either secret exists.

Valid iff the secret is 32 bytes. Its fact is the public key and the
secret. It is filed under no relation: only the op that cites it reads it.

SKELETON: signatures are the contract; bodies are unwritten.
-/
import Connection.Noise

namespace Connection
open Engine

structure Eph where
  sk : ByteArray

def Eph.kind : UInt8 := 32

/-- The fact: the public key, then the secret. -/
def Eph.check (S : Noise.Suite) (b : Eph) : Option (ByteArray × ByteArray) := sorry

def Eph.op (sk : ByteArray) : Op := sorry

end Connection
