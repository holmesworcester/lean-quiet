/-
The connection family's laws.

Proven:
- `wire_kinds`: only the request and the connection cross the bare
  wire; every other connection op is local, so `intake_local` keeps it
  off every wire.
- `Noise.handshake_agrees`, `Noise.sent1_write1` (Connection/Noise.lean).

To prove, over the world as a pure step relation (holmes-a3's generic
Node; see the README):
- `established_agrees`: an initiator's and a responder's Valid
  `established` facts for one connection hold the same handshake hash and
  community, each other's device keys, and crossed transport keys.
- `established_own`: an initiator's `established` cites a request this
  device wrote, because `sent1` re-derives its message 1 from this
  device's seed and the ephemeral.
- `answer_trusted` / `untrusted_silent`: `react` writes a connection
  only for an opened request whose initiator `trusts` admits; for any
  other it writes no connection and no courier. This is lean-net's
  `no_connection_before_approval`, at the level of the ops that run.
- `close_forgets`: after the node purges `closing cid`, no eph, opened,
  established or settled op of cid is stored.
-/
import Connection.Intents

namespace Connection
open Engine

/-- **Only the two handshake messages cross the bare wire.** -/
theorem wire_kinds (o : Op) (h : scopeOf o = .conn) : o.kind = 33 ∨ o.kind = 35 := by
  unfold scopeOf at h
  split at h
  · assumption
  · cases h

/-- Every other connection op is local. -/
theorem local_kinds (o : Op) (h : ¬ (o.kind = 33 ∨ o.kind = 35)) : scopeOf o = .local := by
  simp [scopeOf, h]

end Connection
