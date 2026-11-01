/-
**A removal reaches a live session**, over the node's entry points
(`Node.onFrame`, `onTick`, `onWrite`, `onClose`), run on held data with
the Connection family's own hooks.

`entry_fresh` (engine/wire/EgressLaws.lean): every payload an entry point
seals for a session is an op a connection step sent at a store on the
way, on the session's connection as that store gave its rooms. Here the
hooks are the family's (`hooks`), which only read (`hooks_reads`), and
whose rooms are `roomsV` read afresh (`rooms_held`). Each step, run on
held data, answers as on the model's tables (ops/sync/SimLaws.lean), so
the per-step law `removed_gets_only_notice` (and `serveOwed_shown` for a
session's queue) applies at that store: there, if this node is live in c
and the trust rule refuses the peer, the op is a sync wire op, an op of
another community, or in the requirement closure of a removal owed to
the peer (`sent_mayGo`).

So `removal_reaches_session`: once a removal is stored, every later step
on the session reads it, and nothing of c but the removal's notice goes
out, whatever entry point runs. The fresh bytes the hooks draw are
assumed to leave the store as it is (`hfr`), as the OS's do.
-/
import ops.connection.HooksRead
import ops.connection.RemovalLaws
import ops.sync.SimLaws
import engine.wire.EgressLaws

namespace Connection
open Engine Engine.Sync Codec

/-- The family's hooks only read, so the node's laws of hooks that only
read hold of them. -/
theorem hooks_readOnly [Fresh (HeldM F)] (hfr : Reads (Fresh.fresh : HeldM F ByteArray))
    (x : Sync F (HeldM F)) (K : Keys) (listen : B) (hx : x.hooks = hooks x.fam K listen) : ReadOnly x := by
  obtain ⟨fam, cfg, hk, room⟩ := x
  simp only at hx
  subst hx
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hooks_reads hfr fam K listen
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

/-- What may go out on session cid at store h, as of community c: if
this node is live in c and the trust rule refuses cid's peer, only a sync
wire op, an op of another community, or an op in the requirement
closure of a removal owed to the peer (`NoticeOnly`). -/
def MayGo (fam : Family F) (h : Held F) (cid c : B) (o : Op) : Prop :=
  LiveIn h.db c → Refused h.db cid c → NoticeOnly fam h.db cid c o

/-- **Each fresh step's send may go** (`sent_mayGo`): every op a
connection step sends, run where the node runs it, on the connection as
the store gives its rooms, is one `MayGo` allows at that store. -/
theorem sent_mayGo [Fresh (HeldM F)] (x : Sync F (HeldM F)) (K : Keys) (listen : B) (hx : x.hooks = hooks x.fam K listen)
    {h : Held F} {cid : Id} {o : Op} (hs : Sent x h cid o) (c : B) : MayGo x.fam h cid c o := by
  intro hl hr
  have hR : ((x.hooks.rooms cid).run h).1 = (roomsV cid).eval h.db := by
    simp only [hx, hooks, rooms_held]
  have hrm := rooms_removed h.db hl hr
  rcases hs with ⟨conn, ix, bytes, now, ho⟩ | ⟨conn, ids, ho⟩ | ⟨conn, ix, now, ho⟩ |
      ⟨conn, budget, first, ho⟩ | ⟨dialer, floor, now, ho⟩
  · rw [hR, recv_held] at ho
    exact (removed_gets_only_notice x.fam x.cfg ix h.db cid c conn bytes [] now 0 false hl hr).2.1 o ho
  · rw [hR, filedGive_held] at ho
    exact (removed_gets_only_notice x.fam x.cfg {} h.db cid c conn .empty ids 0 0 false hl hr).2.2.2.1 o ho
  · rw [hR, tickGive_held] at ho
    exact (removed_gets_only_notice x.fam x.cfg ix h.db cid c conn .empty [] now 0 false hl hr).2.2.2.2 o ho
  · rw [hR] at ho
    have hsh := (serveOwed_shown x.fam x.cfg (conn.carry ((roomsV cid).eval h.db)) budget first h o ho).1
    refine Or.inr (Or.inl fun hc => ?_)
    simp only [Conn.shows, hc] at hsh
    exact hrm _ (mem_syncs ((Engine.has_iff _ _).1 hsh)) rfl
  · simp only [Conn.open, List.mem_singleton] at ho
    subst ho
    exact Or.inl (msg_wire _)

/-- **A removal reaches a live session** (`removal_reaches_session`).
Run with the Connection family's hooks, whatever entry point the node
runs (a frame, the clock, a write, a socket closing), from any store:
it changes the store only by write turns and purges, and every frame it
sends is a bare op or a bundle sealed for one session cid, each of whose
payloads is an op that, at the store a connection step sent it from,
`MayGo` allows for every community: where this node is live in c and the
trust rule refuses cid's peer, only a sync wire op, an op of another
community, or one in the requirement closure of a removal owed to the
peer. -/
theorem removal_reaches_session [Fresh (HeldM F)] (hfr : Reads (Fresh.fresh : HeldM F ByteArray))
    (x : Sync F (HeldM F)) (K : Keys) (listen : B) (hx : x.hooks = hooks x.fam K listen)
    {E : Engine.Sync.Node → HeldM F (Engine.Sync.Node × Effects)} (hE : Entry x E)
    (n : Engine.Sync.Node) (h : Held F) :
    Moves x.fam h ((E n).run h).2 ∧
      FramesBy x (fun h' cid o => ∀ c, MayGo x.fam h' cid c o) h ((E n).run h).2 ((E n).run h).1.2 := by
  obtain ⟨m, ok⟩ := entry_fresh (hooks_readOnly hfr x K listen hx) hE n h
  exact ⟨m, ok.mono fun _ _ _ hs c => sent_mayGo x K listen hx hs c⟩

end Connection
