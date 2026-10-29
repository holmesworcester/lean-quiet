/- The explicit close seam for the runner's listening socket. Called
only after the acceptor joins; the closed native object is never reused. -/
import Std.Async.TCP

namespace Engine.Sync

@[extern "lq_listener_close"]
opaque closeListener (s : @& Std.Internal.UV.TCP.Socket) : IO Unit

end Engine.Sync
