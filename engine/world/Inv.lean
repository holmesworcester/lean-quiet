/-
Invariants of every plain node in every execution, proven of the running
node: what the per-link laws take of a node's state at a step.

- **No managed sessions** (`managed_nil`): a plain node's sessions all
  come from the harness's `connect`; the family establishes none, so
  `Node.follow` never adds one and every entry point ends with none.
- **A plain node's pieces** (`Plain.pieces`): the `Pieces` of
  engine/world/Pieces.lean for the plain hooks, from the few they reach;
  every plain node invariant is one of these (`managed_pieces`, and
  engine/world/InvIx.lean's).
-/
import engine.world.Owed
import engine.world.Pieces

namespace Engine.World
open Engine Engine.Sync

variable {F : Type}

/-- Serving a queue changes a node's sessions only. -/
theorem serveOwed_managed (x : Sync F (HeldM F)) (n : Node) (cid : Id) (now : Nat) (h : Held F) :
    ((n.serveOwed x cid now).run h).1.1.managed = n.managed := by
  unfold Node.serveOwed
  split
  · rfl
  · split
    · rfl
    · simp only [HeldM.run_bind, HeldM.run_pure]

/-- With no catalog, a sweep does nothing. -/
theorem sweep_none (x : Sync F (HeldM F)) (hx : x.catalog = none) (n : Node) (cid : Id) (h : Held F) :
    (n.sweep x cid).run h = ((n, {}), h) := by
  unfold Node.sweep; rw [hx]; rfl

theorem drop_managed (n : Node) (cid : Id) (hm : n.managed = []) : (n.drop cid).managed = [] := by
  simp [Node.drop, Node.close, hm]

section
variable (S : Engine.Sync.Setup F) (s : Who)

theorem apply_managed (n : Node) (cid : Id) (st : Step) (now : Nat) (h : Held F) (hm : n.managed = []) :
    ((n.apply (S.sync s) cid st now).run h).1.1.managed = [] := by
  have hfold : ∀ (L : List Op), L.foldl (fun b (_ : Op) => b) ([] : List Op) = [] := by
    intro L; induction L with
    | nil => rfl
    | cons _ _ ih => exact ih
  unfold Node.apply
  split
  · exact drop_managed n cid hm
  · simp only [HeldM.run_bind, recordGiven_run]
    rw [forIn_yield _ _ (fun _ acc => acc) _ (fun o _ acc => by
      simp only [sync_recv, HeldM.run_bind, HeldM.run_pure, List.append_nil]), hfold, store_nil]
    simp only [HeldM.run_pure]
    rw [(store_facts S s _ st.take false h).2.1]; exact hm


end

/-! ## A plain node's pieces -/

namespace Plain
variable {Q : Plain F}

/-- The plain setup's run is a run. -/
theorem lawful : Lawful Q.setup.run := ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

/-- A step that reads only is `MetaOnly` in the plain setup: the held
store is the whole box. -/
theorem reads_meta {α : Type} {p : HeldM F α} (hp : Reads p) : MetaOnly Q.setup.run Q.setup.held p := hp

/-- The plain hooks' calls, sealing and ending a session read only: no
secrets, no couriers to purge. -/
theorem calls_keep {i : Fin Q.n} {α : Type} {p : HeldM F α} (hp : Call (Q.setup.sync i) p) (h : Held F) :
    (p.run h).2 = h := by
  cases hp with
  | sealed n out => exact seal_reads (Q.two i) .a n out h
  | _ => rfl

/-- Following: the plain family establishes no session, so following
only drops the managed ones. -/
theorem follow_ok {i : Fin Q.n} {Φ : Node → Held F → Prop} (hd : ∀ n cid h, Φ n h → Φ (n.drop cid) h)
    (n : Node) (now : Nat) (h : Held F) (hn : Φ n h) : Ok Q.setup Φ ((n.follow (Q.setup.sync i) now).run h) := by
  unfold Node.follow
  simp only [HeldM.run_bind, sync_established, HeldM.run_pure]
  generalize hR1 : HeldM.run (forIn (m := HeldM F) n.managed ((n, {}) : Node × Acts) _) h = R1
  have p1 := forIn_inv hR1 (fun h' (st : Node × Acts) => Φ st.1 h') hn (fun a _ st h' hst => by
    simp only [List.any_nil, Bool.not_false, ↓reduceIte, HeldM.run_pure, ForInStep.value]
    exact hd _ _ _ hst)
  simp only [List.forIn_nil, HeldM.run_pure]
  exact p1

/-- **A plain node's pieces, from those its hooks reach**: following,
the outbox, the calls and the catalog sweep are the plain hooks' (no
session established, no outbox, calls that only read, no catalog), so a
node invariant that drops keep needs only the rest. -/
theorem pieces {i : Fin Q.n} {Φ : Node → Held F → Prop}
    (write : ∀ n ops h, Φ n h → Ok Q.setup Φ ((n.write (Q.setup.sync i) ops).run h))
    (store : ∀ n ops mine h, Φ n h → Ok Q.setup Φ ((n.store (Q.setup.sync i) ops mine).run h))
    (recv : ∀ n cid c rs b now h, n.conn? cid = some c → Φ n h →
      Ok Q.setup Φ ((n.apply (Q.setup.sync i) cid
        ((Conn.recv Q.fam Q.cfg n.ix (c.carry rs) b now : HeldM F Step).run h).1 now).run h))
    (tick : ∀ n cid c rs now h, n.conn? cid = some c → Φ n h →
      Ok Q.setup Φ ((n.apply (Q.setup.sync i) cid
        ((Conn.tickGive Q.fam Q.cfg n.ix (c.carry rs) now : HeldM F Step).run h).1 now).run h))
    (serve : ∀ (y : Sync F (HeldM F)), y.fam = Q.fam → y.hooks = (Q.setup.sync i).hooks →
      ∀ n cid now h, Φ n h → Ok Q.setup Φ ((n.serveOwed y cid now).run h))
    (opens : ∀ n cid a dialer now h, Φ n h → Ok Q.setup Φ ((n.open (Q.setup.sync i) cid a dialer now).run h))
    (setAddr : ∀ n cid a h, Φ n h → Φ (n.setAddr cid a) h)
    (heat : ∀ n ids now h, Φ n h → Φ (n.heat (Q.setup.sync i) ids now) h)
    (drop : ∀ n cid h, Φ n h → Φ (n.drop cid) h)
    (sent : ∀ n out now h, Φ n h → Φ (n.sent out now) h)
    (clear : ∀ n h, Φ n h → Φ { n with fresh := [], purged := [] } h)
    (retries : ∀ n l o h, Φ n h → Φ { n with sweeps := l, retryOrder := o } h)
    (idle : ∀ n h, Φ n h → Φ n ((Turn.turn (Q.setup.sync i).fam [] : HeldM F Unit).run h).2) :
    Pieces Q.setup i Φ where
  write := write
  store := store
  recv n cid c rs b now h hc hn := by
    show Ok Q.setup Φ ((Conn.recv Q.fam Q.cfg n.ix (c.carry rs) b now >>= fun st =>
      n.apply (Q.setup.sync i) cid st now).run h)
    rw [HeldM.run_bind, recv_reads Q.fam Q.cfg n.ix (c.carry rs) b now h]
    exact recv n cid c rs b now h hc hn
  tick n cid c rs now h hc hn := by
    show Ok Q.setup Φ ((Conn.tickGive Q.fam Q.cfg n.ix (c.carry rs) now >>= fun st =>
      n.apply (Q.setup.sync i) cid st now).run h)
    rw [HeldM.run_bind, tickGive_reads Q.fam Q.cfg n.ix (c.carry rs) now h]
    exact tick n cid c rs now h hc hn
  serve := serve
  sweep r rr n cid h hn := by
    show Ok Q.setup Φ ((n.sweep { Q.setup.sync i with room := r, retryRoom := rr } cid).run h)
    rw [sweep_none _ rfl]; exact hn
  opens := opens
  follow n now h hn := follow_ok drop n now h hn
  flush n out h hn := by
    show Ok Q.setup Φ ((n.flush (Q.setup.sync i) out).run h)
    simp only [Node.flush, HeldM.run_bind, sync_outbox, HeldM.run_pure, List.isEmpty_nil, ↓reduceIte]
    exact hn
  calls p hp n h hn := by
    show Φ n (p.run h).2
    rw [calls_keep hp]; exact hn
  setAddr := setAddr
  heat := heat
  drop := drop
  sent := sent
  clear := clear
  retries := retries
  idle := idle

/-- **Every piece of a plain node keeps it managing no session.** -/
theorem managed_pieces (i : Fin Q.n) : Pieces Q.setup i (fun n _ => n.managed = []) :=
  pieces (fun n ops h hm => (write_keeps _ n ops h).trans hm)
    (fun n ops mine h hm => (store_keeps (Q.two i) .a n ops mine h).trans hm)
    (fun n cid _ _ _ now h _ hm => apply_managed (Q.two i) .a n cid _ now h hm)
    (fun n cid _ _ now h _ hm => apply_managed (Q.two i) .a n cid _ now h hm)
    (fun y _ _ n cid now h hm => (serveOwed_managed y n cid now h).trans hm)
    (fun n cid a dialer now h hm => by
      show ((n.open ((Q.two i).sync .a) cid a dialer now).run h).1.1.managed = []
      unfold Node.open
      simp only [HeldM.run_bind, sync_rooms, HeldM.run_pure]
      simp [Node.close, Node.setAddr, hm])
    (fun _ _ _ _ hm => hm) (fun _ _ _ _ hm => hm) (fun n cid _ hm => drop_managed n cid hm)
    (fun _ _ _ _ hm => hm) (fun _ _ hm => hm) (fun _ _ _ _ hm => hm)
    (fun _ _ hm => hm)

/-- **Everything the World runs at a plain node keeps it managing no
session**: every entry point, and a restart, which boots with none. -/
theorem managed_local : Local Q.setup (fun _ n _ => n.managed = []) (fun _ n _ => n.managed = []) :=
  Pieces.local lawful (Φ := fun _ n _ => n.managed = []) managed_pieces fun _ _ _ _ => rfl

/-- **No plain node ever manages a session**, in any execution against
any attacker, from nodes that manage none. -/
theorem managed_nil {adv : World (Held F) Q.n → ByteArray → Prop} {w₀ : World (Held F) Q.n}
    (E : Exec Q.setup adv w₀) (h0 : ∀ i, (w₀.node i).managed = []) : ∀ k i, ((E.world k).node i).managed = [] :=
  managed_local.keeps.always h0 E

end Plain

end Engine.World
