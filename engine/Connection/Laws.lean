/-
The connection family's laws. Statements only; each is proven before
the family is called done.

- `wire_kinds`: the request and the connection are the only ops that
  cross the bare wire; every other connection op is local, so
  `intake_local` keeps them off every wire.
- `established_agrees`: an initiator's and a responder's Valid
  `established` facts for one connection id hold the same handshake hash
  and community, each other's static keys, and crossed transport keys
  (from `Noise.handshake_agrees`).
- `established_own`: a Valid initiator `established` cites a request
  this device wrote: its message 1 is rebuilt from this device's seed.
- `answer_trusted`: `react` writes a connection only for an opened
  request whose initiator `trusts` admits for the hello's community.
- `untrusted_silent`: for any other opened request, `react` writes no
  connection and no courier. The request is delivered and nothing more,
  lean-net's `no_connection_before_approval` at the level of ops.
- `close_forgets`: after the node purges `closing cid`, no eph, opened,
  established or settled op of cid is stored (`Engine.purge_gone`).
- `outbox_couriers`: the node's outbox is exactly the Valid `send` facts.
-/
import Connection.Intents

namespace Connection
open Engine Engine.Sync

theorem wire_kinds (S : Noise.Suite) (o : Op) (h : scopeOf o = .conn) :
    o.kind = Request.kind ∨ o.kind = Reply.kind := sorry

theorem established_agrees (S : Noise.Suite) (G : S.Good) (si sr : Session)
    (hi : True) (hr : True) (hc : si.cid = sr.cid) :
    si.h = sr.h ∧ si.community = sr.community ∧ si.send = sr.recv ∧ si.recv = sr.send := sorry

end Connection
