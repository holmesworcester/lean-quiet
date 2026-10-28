/-
`send` (local): a courier, the one way out (tiny's and poc-17's
egress door). It carries a route (a connection id, or a bare address
for the two handshake messages) and the bytes to send, which are an op's
own bytes. Commands write couriers; they never send anything themselves.

The node lists `send.all`, hands each courier's bytes to its route, and
purges the courier. A courier is content-addressed, so writing the same
send again is one op until the first is purged. Valid iff the route is
well formed.

SKELETON: signatures are the contract; bodies are unwritten.
-/
import Connection.Established
import Engine.Sync.Node

namespace Connection
open Engine Engine.Sync

structure Send where
  route : Route
  bytes : ByteArray

def Send.kind : UInt8 := 37

def Send.op (route : Route) (bytes : ByteArray) : Op := sorry

end Connection
