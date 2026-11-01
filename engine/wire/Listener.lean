/- The explicit close seam for the runner's listening socket. Called
only after the acceptor joins; the closed native object is never reused. -/
import Std.Async.TCP

namespace Engine.Sync

/-- Closes the runner's listening socket, after its acceptor has joined.
Contract: its effect is the OS's, which Lean does not state. -/
@[extern "lq_listener_close"]
opaque closeListener (s : @& Std.Internal.UV.TCP.Socket) : IO Unit

end Engine.Sync
