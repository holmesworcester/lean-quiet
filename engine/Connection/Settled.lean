/-
`settled` (local): a room first settled on a connection (sync agreed
with this peer once). It cites the connection, and a close purges it
with the session. A screen shows "joining" until some open connection
has settled the community, and afterwards reads admission and members.

SKELETON: signatures are the contract; bodies are unwritten.
-/
import Connection.Seen

namespace Connection
open Engine Engine.Sync

structure Settled where
  room : Id

def Settled.kind : UInt8 := 40

def Settled.op (cid room : Id) : Op := sorry

end Connection
