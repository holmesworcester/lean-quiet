/-
One link of the plain World, step by step: what a delivery does at the
node it reaches, and what an entry point puts in flight, so the frame
laws (H3, H4, H2) lift to packets in an execution.

- **A packet sent is in flight** (`enter_sends`): whatever an entry
  point at node i sends to an address goes in flight as a packet from i,
  stamped with the step's time.
- **A delivery runs the receiver** (`deliver_box`, `deliver_node`): the
  node at the packet's address takes its bytes, as from its origin.
- **The hops, at a delivery** (`deliver_takes`, `deliver_wants`,
  `deliver_queues`): the frame laws, at the step a packet is delivered.
-/
import engine.world.Inv

namespace Engine.World
open Engine Engine.Sync

variable {F : Type}

/-! ## Packets -/

theorem mem_packets {n : Nat} (i : Fin n) (origin : ByteArray) (t : Nat) :
    ∀ (L : List (ByteArray × ByteArray)) (s : Nat) (a b : ByteArray), (a, b) ∈ L →
      ∃ s', (⟨s', some i, origin, a, b, t⟩ : Packet n) ∈ packets i origin t s L := by
  intro L
  induction L with
  | nil => intro s a b h; cases h
  | cons q rest ih =>
    intro s a b h
    obtain ⟨d, e⟩ := q
    rcases List.mem_cons.1 h with e' | h
    · cases e'; exact ⟨s, List.mem_cons_self ..⟩
    · obtain ⟨s', hs'⟩ := ih (s + 1) a b h
      exact ⟨s', List.mem_cons_of_mem _ hs'⟩

namespace Plain
variable {Q : Plain F}

/-- **What an entry point sends goes in flight**, from its node, at its
time. -/
theorem enter_sends (w : World (Held F) Q.n) (i : Fin Q.n) (t : Nat) (f : Node → HeldM F (Node × Effects))
    (a b : ByteArray) (h : (a, b) ∈ ((f (w.node i)).run (w.box i)).1.2.send) :
    ∃ s, (⟨s, some i, Q.addr i, a, b, t⟩ : Packet Q.n) ∈ (w.enter Q.setup i t f).flight := by
  obtain ⟨s, hs⟩ := mem_packets i (Q.addr i) t _ w.serial a b h
  exact ⟨s, List.mem_append_right _ hs⟩

/-- A delivery to the node at the packet's address runs its frame entry
point: the node's store after the step. -/
theorem deliver_box (w : World (Held F) Q.n) (idx t : Nat) (p : Packet Q.n) (j : Fin Q.n)
    (hp : w.flight[idx]? = some p) (hj : Q.setup.at? p.dst = some j) :
    (w.step Q.setup (.deliver idx t)).box j =
      (((w.node j).onFrame ((Q.two j).sync .a) p.origin p.bytes t).run (w.box j)).2 := by
  simp only [World.step, hp, hj, World.enter, upd_same]

/-- A delivery's node after the step. -/
theorem deliver_node (w : World (Held F) Q.n) (idx t : Nat) (p : Packet Q.n) (j : Fin Q.n)
    (hp : w.flight[idx]? = some p) (hj : Q.setup.at? p.dst = some j) :
    (w.step Q.setup (.deliver idx t)).node j =
      (((w.node j).onFrame ((Q.two j).sync .a) p.origin p.bytes t).run (w.box j)).1.1 := by
  simp only [World.step, hp, hj, World.enter, upd_same]

/-- What a delivery sends goes in flight, from the receiver, at the
delivery's time. -/
theorem deliver_sends (w : World (Held F) Q.n) (idx t : Nat) (p : Packet Q.n) (j : Fin Q.n)
    (hp : w.flight[idx]? = some p) (hj : Q.setup.at? p.dst = some j) (a b : ByteArray)
    (h : (a, b) ∈ (((w.node j).onFrame ((Q.two j).sync .a) p.origin p.bytes t).run (w.box j)).1.2.send) :
    ∃ s, (⟨s, some j, Q.addr j, a, b, t⟩ : Packet Q.n) ∈ (w.step Q.setup (.deliver idx t)).flight := by
  obtain ⟨s, hs⟩ := mem_packets j (Q.addr j) t _ w.serial a b h
  refine ⟨s, ?_⟩
  simp only [World.step, hp, hj, World.enter]
  exact List.mem_append_right _ hs

/-- A frame in the clear opens to its session and bundle. -/
theorem onFrame_plain (i : Fin Q.n) (n : Node) (src : ByteArray) (cid : Id) (inner : List ByteArray) (now : Nat) :
    n.onFrame ((Q.two i).sync .a) src (plainFrame cid inner) now =
      n.onSealed ((Q.two i).sync .a) src (some (cid, Codec.encode inner)) now := by
  simp only [Node.onFrame, plainFrame_head, plainFrame_body, sync_openFrame, plainOpen, Codec.decode_encode,
    HeldM.pure_bind]

/-- **H3 at a delivery:** a frame delivered on a session the receiver
has open, carrying an op of a room the session shows there, is stored. -/
theorem deliver_takes (w : World (Held F) Q.n) (idx t : Nat) (p : Packet Q.n) (j : Fin Q.n) (cid : Id)
    (inner : List ByteArray) (o : Op) (r : Id)
    (hp : w.flight[idx]? = some p) (hj : Q.setup.at? p.dst = some j) (hb : p.bytes = plainFrame cid inner)
    (ho : o.bytes ∈ inner) (hc : ((w.node j).conn? cid).isSome = true) (hw : isWire o.kind = false)
    (hr : Q.fam.room o = some r) (hs : r ∈ Q.rooms j cid)
    (hpre : ∀ o', (w.box j).db.ops o.id = some o' → o' = o)
    (hfr : ∀ b ∈ inner, ∀ o', Op.decode b = some o' → o'.id = o.id → o' = o) :
    ((w.step Q.setup (.deliver idx t)).box j).db.ops o.id = some o := by
  rw [deliver_box w idx t p j hp hj, hb]
  exact onFrame_takes (Q.two j) .a _ p.origin cid inner o r t _ hc ho hw hr hs hpre hfr

/-- **H4 at a delivery:** a frame delivered on a session the receiver has
open, carrying a have in a room it shows of an op it has not asked for,
leaves the receiver holding the op there, or puts a want naming it in
flight back to the frame's origin, from the receiver, at the delivery's
time. -/
theorem deliver_wants (w : World (Held F) Q.n) (idx t : Nat) (p : Packet Q.n) (j : Fin Q.n) (cid : Id)
    (inner : List ByteArray) (r x : Id) (l : List Id) (c0 : Conn)
    (hp : w.flight[idx]? = some p) (hj : Q.setup.at? p.dst = some j) (hb : p.bytes = plainFrame cid inner)
    (hh : (Msg.hold r l).op.bytes ∈ inner) (hx : x ∈ l) (hs : r ∈ Q.rooms j cid) (hl : l.length ≤ Q.cfg.maxIds)
    (hc : (w.node j).conn? cid = some c0) (hm : (w.node j).managed = []) (hq : x ∉ c0.asked)
    (hroom : c0.asked.size + (inner.map asksOf).sum ≤ Q.cfg.maxKnown) (hmax : 0 < Q.cfg.maxIds) :
    heldIn Q.fam ((w.step Q.setup (.deliver idx t)).box j).db r x = true ∨
      ∃ sr g L, x ∈ L ∧ (Msg.want L).op.bytes ∈ g ∧
        (⟨sr, some j, Q.addr j, p.origin, plainFrame cid g, t⟩ : Packet Q.n) ∈ (w.step Q.setup (.deliver idx t)).flight := by
  rcases onSealed_wants (Q.two j) .a (w.node j) p.origin cid inner r x l t (w.box j) c0 hc hm hh hx hs hl hq
    hroom hmax with e | ⟨g, L, hxL, hg, hf⟩
  · left; rw [deliver_box w idx t p j hp hj, hb, onFrame_plain]; exact e
  · right
    rw [← onFrame_plain, ← hb] at hf
    obtain ⟨sr, hsr⟩ := deliver_sends w idx t p j hp hj _ _ hf
    exact ⟨sr, g, L, hxL, hg, hsr⟩

/-- **H2 at a delivery:** a frame delivered on a session the receiver has
open, carrying a want of an op it holds in a room the session shows and
its index lists, leaves the id in the session's queue, or puts the op in
flight back to the frame's origin, at the delivery's time. -/
theorem deliver_queues (w : World (Held F) Q.n) (idx t : Nat) (p : Packet Q.n) (j : Fin Q.n) (cid : Id)
    (inner : List ByteArray) (x : Id) (o : Op) (r : Id) (L : List Id) (c0 : Conn)
    (hp : w.flight[idx]? = some p) (hj : Q.setup.at? p.dst = some j) (hb : p.bytes = plainFrame cid inner)
    (hw' : (Msg.want L).op.bytes ∈ inner) (hxL : x ∈ L) (hL : L.length ≤ Q.cfg.maxIds)
    (hg : (w.box j).db.ops x = some o) (hr : Q.fam.room o = some r) (hs : r ∈ Q.rooms j cid)
    (hix : ∃ a ∈ (w.node j).ix.items r, a.2 = x) (hc : (w.node j).conn? cid = some c0)
    (hm : (w.node j).managed = []) (hq0 : OwesQueued c0)
    (hroom : c0.owed.length + (inner.map wantsOf).sum ≤ Q.cfg.maxKnown) :
    (∃ c', ((w.step Q.setup (.deliver idx t)).node j).conn? cid = some c' ∧ x ∈ c'.owed) ∨
      ∃ sr g, o.bytes ∈ g ∧
        (⟨sr, some j, Q.addr j, p.origin, plainFrame cid g, t⟩ : Packet Q.n) ∈ (w.step Q.setup (.deliver idx t)).flight := by
  rcases onSealed_queues (Q.two j) .a (w.node j) p.origin cid inner x o r L t (w.box j) c0 hc hm hw' hxL hL hg hr hs
    hix hq0 hroom with e | ⟨g, hg', hf⟩
  · left; rw [deliver_node w idx t p j hp hj, hb, onFrame_plain]; exact e
  · right
    rw [← onFrame_plain, ← hb] at hf
    obtain ⟨sr, hsr⟩ := deliver_sends w idx t p j hp hj _ _ hf
    exact ⟨sr, g, hg', hsr⟩

end Plain

end Engine.World
