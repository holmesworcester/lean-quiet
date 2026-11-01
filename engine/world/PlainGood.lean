/-
**Every plain world is good** (`Plain.good_always`): the first instance
of the top theorem (engine/world/Good.lean, docs/GOOD.md), over the
running node, in every execution from empty stores against any attacker.

A good plain node (`NodeGood`) manages no session (`managed_local`), its
sessions owe only what they queue (`oq_pieces`) and queue at most
`maxKnown` ids (`bounded_pieces`), its index covers its store
(`ix_pieces`), its store is one the engine reaches from its log
(`store_reachable`), and judging has settled (`store_settled`): each
conjunct is kept by every entry point and restart, given all of them
before (`good_local`). A good plain world has good nodes and only packets
sent in the past (`sent_keeps`). Every step moves each store only by
write turns and purges (`moves_always`).

The laws that were proven one by one are its projections
(`owes_queued_start`, `ix_covers_start`, `owed_bounded_start`), and two
headline laws follow for every node at every step: verdicts are the
spec's (`verdicts_spec`), and nodes that received the same ops, in any
orders, agree on every verdict (`agree`).

Not covered here (docs/GOOD.md): the production hooks (sealed sessions,
the handshake, rooms from the store), lifecycle (suspend, resume, the
write journal), and world-level conjuncts beyond `Sent` (provenance of
injected bytes, secrecy).
-/
import engine.world.InvOwed
import engine.sync.StoreEvolution

namespace Engine.World
open Engine Engine.Sync

variable {F : Type}

namespace Plain

/-- **A good plain node.** -/
structure NodeGood (Q : Plain F) (n : Node) (h : Held F) : Prop where
  /-- It manages no session: the plain family establishes none. -/
  managed : n.managed = []
  /-- Every session owes only ids in its queue. -/
  owes : NodeOQ n
  /-- Every session's queue holds at most `maxKnown` ids. -/
  bounded : NodeBounded Q.cfg.maxKnown n
  /-- Its index covers its store and lists ops under their own keys; its
  store holds each op under its id and in its log. -/
  ix : IxInv Q.fam n h
  /-- Its store is one the engine reaches from the ops in its log. -/
  store : h.Reachable Q.fam
  /-- Judging has settled. -/
  settled : h.db.queue = []

/-- **A good plain world**: every node good, and every packet in flight
sent in the past. -/
def Good (Q : Plain F) : World (Held F) Q.n → Prop := Engine.World.Good Q.setup (fun _ => Q.NodeGood) Sent

variable {Q : Plain F}

/-- Everything the World runs at a plain node moves its store only by
write turns and purges (main's `entry_fresh`). -/
theorem runs_moves {i : Fin Q.n} {f : Node → HeldM F (Node × Effects)} (hf : Runs Q.setup i f) (nd : Node)
    (h : Held F) : Moves Q.fam h ((f nd).run h).2 := by
  cases hf with
  | frame addr bytes t => exact Q.enter_moves i _ (Or.inl ⟨_, .frame addr bytes t, rfl⟩) nd h
  | tick t => exact Q.enter_moves i _ (Or.inl ⟨_, .tick t, rfl⟩) nd h
  | write ops t _ => exact Q.enter_moves i _ (Or.inl ⟨_, .write ops t, rfl⟩) nd h
  | close addr t => exact Q.enter_moves i _ (Or.inl ⟨_, .close addr t, rfl⟩) nd h
  | connect j cid dialer t _ => exact Q.connect_moves i nd cid _ dialer t h

/-- Every step moves each plain store only by moves; a crash keeps it. -/
theorem moves_boxes : Boxes Q.setup (fun _ _ _ => True) (fun _ => Moves Q.fam) where
  refl _ h := .refl h
  runs _ _ hf nd h _ := runs_moves hf nd h
  crash _ _ h _ := .refl h

/-- The store stays one the engine reaches. -/
theorem store_local : Local Q.setup (fun _ _ h => h.Reachable Q.fam) (fun _ _ h => h.Reachable Q.fam) where
  runs _ _ hf nd h hr := (runs_moves hf nd h).store_reachable hr
  boot _ _ _ hr := hr

/-- Judging stays settled, given a reachable store. -/
theorem settled_local :
    Local Q.setup (fun _ _ h => h.Reachable Q.fam ∧ h.db.queue = []) (fun _ _ h => h.db.queue = []) where
  runs _ _ hf nd h g := (runs_moves hf nd h).store_settled g.1 g.2
  boot _ _ _ g := g.2

/-- **Everything the World runs at a plain node keeps it good**: each
conjunct under all of them. -/
theorem good_local : Local Q.setup (fun _ => Q.NodeGood) (fun _ => Q.NodeGood) := by
  have m : Local Q.setup (fun _ => Q.NodeGood) (fun _ n _ => n.managed = []) :=
    managed_local.mono fun _ _ _ g => g.managed
  have o : Local Q.setup (fun _ => Q.NodeGood) (fun _ n _ => NodeOQ n) :=
    (pieces_local (fun n _ => NodeOQ n) (fun i => oq_pieces (Q.two i) .a)
      (fun _ _ _ _ _ hc => by simp [Node.boot, Node.conn?] at hc)).mono fun _ _ _ g => g.owes
  have b : Local Q.setup (fun _ => Q.NodeGood) (fun _ n _ => NodeBounded Q.cfg.maxKnown n) :=
    (pieces_local (fun n _ => NodeBounded Q.cfg.maxKnown n) (fun i => bounded_pieces (Q.two i) .a)
      (fun _ _ _ _ _ hc => by simp [Node.boot, Node.conn?] at hc)).mono fun _ _ _ g => g.bounded
  have x : Local Q.setup (fun _ => Q.NodeGood) (fun _ => IxInv Q.fam) :=
    (pieces_local (IxInv Q.fam) (fun i => ix_pieces (Q.two i) .a)
      (fun _ h hi => boot_ixinv Q.fam h 0 hi.2.2)).mono fun _ _ _ g => g.ix
  have r : Local Q.setup (fun _ => Q.NodeGood) (fun _ _ h => h.Reachable Q.fam) :=
    store_local.mono fun _ _ _ g => g.store
  have q : Local Q.setup (fun _ => Q.NodeGood) (fun _ _ h => h.db.queue = []) :=
    settled_local.mono fun _ _ _ g => ⟨g.store, g.settled⟩
  exact ⟨fun i f hf nd h g => ⟨m.runs i f hf nd h g, o.runs i f hf nd h g, b.runs i f hf nd h g,
      x.runs i f hf nd h g, r.runs i f hf nd h g, q.runs i f hf nd h g⟩,
    fun i nd h g => ⟨m.boot i nd h g, o.boot i nd h g, b.boot i nd h g, x.boot i nd h g, r.boot i nd h g,
      q.boot i nd h g⟩⟩

/-- **A good plain world steps to a good plain world**, by any legal act,
against any attacker. -/
theorem good_keeps {adv : World (Held F) Q.n → ByteArray → Prop} : Keeps Q.setup adv Q.Good Q.Good :=
  Engine.World.good_keeps good_local (sent_keeps.mono fun _ g => g.2)

/-- Empty stores, nothing in flight: a good world. -/
theorem good_start : Q.Good Q.start :=
  ⟨fun _ =>
    { managed := rfl
      owes := fun _ _ hc => by simp [Plain.start, World.init, Node.boot, Node.conn?] at hc
      bounded := fun _ _ hc => by simp [Plain.start, World.init, Node.boot, Node.conn?] at hc
      ix := ⟨(fun _ _ _ hx => by cases hx),
        (fun _ _ ha => by simp [Plain.start, World.init, Node.boot, Index.ofOps, Index.items] at ha),
        (fun _ _ hx => by cases hx)⟩
      store := held_empty_reachable Q.fam
      settled := rfl },
   fun _ hp => by cases hp⟩

/-- **Every plain world is good**, at every step of every execution from
empty stores, against any attacker: the top theorem for the plain World. -/
theorem good_always {adv : World (Held F) Q.n → ByteArray → Prop} (E : Exec Q.setup adv Q.start) (k : Nat) :
    Q.Good (E.world k) :=
  good_keeps.always good_start E k

/-- **Every step moves each store only by write turns and purges**, in
every execution against any attacker. -/
theorem moves_always {adv : World (Held F) Q.n → ByteArray → Prop} {w₀ : World (Held F) Q.n}
    (E : Exec Q.setup adv w₀) (k : Nat) (i : Fin Q.n) :
    Moves Q.fam ((E.world k).box i) ((E.world (k + 1)).box i) :=
  Guar.always (G := Nodes Q.setup fun _ _ _ => True) (fun _ _ _ _ _ => trivial) moves_boxes.guar
    (fun _ => trivial) E k i

theorem good_node {adv : World (Held F) Q.n → ByteArray → Prop} (E : Exec Q.setup adv Q.start) (k : Nat)
    (i : Fin Q.n) : Q.NodeGood ((E.world k).node i) ((E.world k).box i) :=
  (good_always E k).1 i

/-! ## Projections: the laws proven one by one -/

/-- **Every session owes only ids in its queue**, at every node in every
execution from empty stores, against any attacker. -/
theorem owes_queued_start {adv : World (Held F) Q.n → ByteArray → Prop} (E : Exec Q.setup adv Q.start) :
    ∀ k i cid c, ((E.world k).node i).conn? cid = some c → OwesQueued c :=
  fun k i => (good_node E k i).owes

/-- **Every node's index covers its store**, in every execution from
empty stores, against any attacker. -/
theorem ix_covers_start {adv : World (Held F) Q.n → ByteArray → Prop} (E : Exec Q.setup adv Q.start) :
    ∀ k i, IxCovers Q.fam ((E.world k).node i) ((E.world k).box i) :=
  fun k i => (good_node E k i).ix.1

/-- **Every session's queue holds at most `maxKnown` ids**, at every node
in every execution from empty stores, against any attacker. -/
theorem owed_bounded_start {adv : World (Held F) Q.n → ByteArray → Prop} (E : Exec Q.setup adv Q.start) :
    ∀ k i cid c, ((E.world k).node i).conn? cid = some c → c.owed.length ≤ Q.cfg.maxKnown :=
  fun k i => (good_node E k i).bounded

/-! ## Corollaries: headline laws at every node, at every step -/

/-- **Every plain node's verdicts are the spec's**, at every step of
every execution from empty stores, against any attacker: a verdict is
stored iff the spec gives it over the stored ops. -/
theorem verdicts_spec {adv : World (Held F) Q.n → ByteArray → Prop} (E : Exec Q.setup adv Q.start) (k : Nat)
    (i : Fin Q.n) (x : Id) (v : Verdict F) :
    ((E.world k).box i).db.status x = some v ↔ Spec Q.fam ((E.world k).box i).db.ops x v := by
  have g := good_node E k i
  obtain ⟨_, hr, _⟩ := g.store
  exact status_iff_spec (reach_inv hr) g.settled x v

/-- **Honest plain nodes agree**: two nodes that received the same ops,
in any orders (their logs hold the same ops; no two of them share an
id), hold the same verdicts, at any steps of any execution from empty
stores, against any attacker (`order_free` at every node). -/
theorem agree {adv : World (Held F) Q.n → ByteArray → Prop} (E : Exec Q.setup adv Q.start) (k k' : Nat)
    (i j : Fin Q.n) (hd : Distinct (((E.world k).box i).log ++ ((E.world k').box j).log))
    (hsame : ∀ o, o ∈ ((E.world k).box i).log ↔ o ∈ ((E.world k').box j).log) :
    ((E.world k).box i).db.status = ((E.world k').box j).db.status := by
  have g := good_node E k i
  have g' := good_node E k' j
  obtain ⟨L, hL, eL⟩ := g.store
  obtain ⟨L', hL', eL'⟩ := g'.store
  have mem : ∀ o, o ∈ L ++ L' → o ∈ ((E.world k).box i).log ++ ((E.world k').box j).log := by
    intro o ho
    rcases List.mem_append.1 ho with ho | ho
    · exact List.mem_append_left _ ((eL o).1 ho)
    · exact List.mem_append_right _ ((eL' o).1 ho)
  exact order_free hL hL' (fun a ha b hb => hd a (mem a ha) b (mem b hb))
    (fun o => (eL o).trans ((hsame o).trans (eL' o).symm)) g.settled g'.settled

end Plain

end Engine.World
