/-
`seen` (local): where a device was last heard from: its static key, an
address, a time. It is written from mDNS answers, an invite link's
hints and `recv` records. `dial` reads `seen.byPeer [peer]` for
addresses. Valid iff the key is 32 bytes.

SKELETON: signatures are the contract; bodies are unwritten.
-/
import Connection.Recv

namespace Connection
open Engine Engine.Sync

structure Seen where
  peer : ByteArray
  addr : ByteArray
  at_ : Nat

def Seen.kind : UInt8 := 39

def Seen.op (peer addr : ByteArray) (at_ : Nat) : Op := sorry

end Connection
