/-
**A node invariant over every entry point, for any World setup**
(docs/GOOD.md, "The serial gate").

A node invariant Φ (of a node and its held store) holds across every
entry point the World runs at a node (`Runs`) if it survives each piece
of the node's code, under the node's own hooks (`Pieces`), whatever those
hooks are: the plain harness's, which do nothing, or the production
`Connection.hooks`, which open sessions, react, dial, sweep a catalog and
purge. The entry points are proven once from the pieces
(`onFrame_keeps`, `onTick_keeps`, `onWrite_keeps`, `onClose_keeps`,
`connect_keeps`, through `finish_keeps`), and `Pieces.local` makes a node
invariant of them (`Local`, engine/world/Good.lean).

What the proofs need of the setup is that its run is a run (`Lawful`: a
monad morphism into state passing). The held store and the node invariant
read only `P.held`, so whatever else a box holds (the entropy cursor,
per-peer retry cursors) a step may move freely: such a step is
`MetaOnly`, and every `Reads` step is one.

Each piece is stated over the piece's whole run result (`Ok`), so that a
relation between a piece's start and its result (a8's `Steps`) can take
the same skeletons.
-/
import engine.world.Good
import engine.wire.WorldLaws

namespace Engine.World
open Engine Engine.Sync

variable {F : Type} {M : Type → Type} {S : Type} [Monad M] [Store F M] [Turn F M]

/-! ## Runs that are runs -/

/-- **`run` is a monad morphism into state passing.** -/
structure Lawful (run : {α : Type} → M α → S → α × S) : Prop where
  pure : ∀ {α} (a : α) (s : S), run (pure a) s = (a, s)
  bind : ∀ {α β} (x : M α) (f : α → M β) (s : S), run (x >>= f) s = run (f (run x s).1) (run x s).2

/-- **A step that leaves the held store as it is**: it may move only what
a node invariant ignores (the entropy cursor, per-peer retry cursors). -/
def MetaOnly (run : {α : Type} → M α → S → α × S) (held : S → Held F) {α : Type} (p : M α) : Prop :=
  ∀ s, held (run p s).2 = held s

section
variable {run : {α : Type} → M α → S → α × S}

/-- **A loop keeps what each pass keeps.** -/
theorem Lawful.forIn_inv (L : Lawful run) {α β : Type} (l : List α) (b : β) (f : α → β → M (ForInStep β))
    (s : S) (I : β → S → Prop) (hb : I b s)
    (hf : ∀ a ∈ l, ∀ b s, I b s → I (run (f a b) s).1.value (run (f a b) s).2) :
    I (run (forIn l b f) s).1 (run (forIn l b f) s).2 := by
  induction l generalizing b s with
  | nil => rw [List.forIn_nil, L.pure]; exact hb
  | cons a t ih =>
    rw [List.forIn_cons, L.bind]
    have h1 := hf a (List.mem_cons_self ..) b s hb
    generalize run (f a b) s = r at h1 ⊢
    obtain ⟨st, s'⟩ := r
    cases st with
    | done b' => rw [L.pure]; exact h1
    | yield b' => exact ih b' s' h1 (fun a ha => hf a (List.mem_cons_of_mem _ ha))

theorem MetaOnly.pure' (L : Lawful run) (held : S → Held F) {α} (a : α) : MetaOnly run held (pure a : M α) :=
  fun s => by dsimp only; rw [L.pure]

theorem MetaOnly.bind' (L : Lawful run) {held : S → Held F} {α β} {p : M α} {k : α → M β}
    (hp : MetaOnly run held p) (hk : ∀ a, MetaOnly run held (k a)) : MetaOnly run held (p >>= k) := by
  intro s
  unfold MetaOnly at hp hk
  dsimp only at hp hk ⊢
  rw [L.bind, hk, hp]

end

/-- What a node invariant reads of a run's result: its node and store. -/
def Ok (P : Setup F M S) (Φ : Node → Held F → Prop) {α : Type} (r : (Node × α) × S) : Prop :=
  Φ r.1.1 (P.held r.2)

/-! ## The pieces -/

/-- **The steps an entry point makes that leave the node as it is**: the
hooks it calls directly, sealing what goes out, and ending a session (the
close-purge path: the family's `closing`, purged). They may move the store
(ending a session purges its local rows); the `calls` piece asks only that
the invariant survive. -/
inductive Call (x : Sync F M) : {α : Type} → M α → Prop
  | rooms (cid : Id) : Call x (x.hooks.rooms cid)
  | openFrame (b : ByteArray) : Call x (x.hooks.openFrame b)
  | recv (addr : ByteArray) (o : Op) (now : Nat) : Call x (x.hooks.recv none addr o now)
  | dial (now : Nat) : Call x (x.hooks.dial now)
  | retired : Call x x.hooks.retired
  | seal (n : Node) (out : Acts) : Call x (n.seal x out)
  | endSession (cid : Id) : Call x (Node.endSession x cid)

/-- **What a node invariant must survive, piece by piece, at node i**,
under node i's hooks, whatever they are. Each piece is stated over its
whole run result. -/
structure Pieces (P : Setup F M S) (i : Fin P.n) (Φ : Node → Held F → Prop) : Prop where
  write : ∀ n ops s, Φ n (P.held s) → Ok P Φ (P.run (n.write (P.sync i) ops) s)
  /-- Storing ops: the write turn, offering them on, and the family's
  reactions to a fixpoint. -/
  store : ∀ n ops mine s, Φ n (P.held s) → Ok P Φ (P.run (n.store (P.sync i) ops mine) s)
  /-- A payload on session cid, on its connection with the rooms the hook
  gave (any). -/
  recv : ∀ n cid c rs b now s, n.conn? cid = some c → Φ n (P.held s) →
    Ok P Φ (P.run (Conn.recv (P.sync i).fam (P.sync i).cfg n.ix (c.carry rs) b now >>= fun st =>
      n.apply (P.sync i) cid st now) s)
  /-- The clock on session cid, likewise. -/
  tick : ∀ n cid c rs now s, n.conn? cid = some c → Φ n (P.held s) →
    Ok P Φ (P.run (Conn.tickGive (P.sync i).fam (P.sync i).cfg n.ix (c.carry rs) now >>= fun st =>
      n.apply (P.sync i) cid st now) s)
  /-- Serving a queue, under any setting with the same family and hooks
  (the tick serves on `afterActs`). -/
  serve : ∀ (y : Sync F M), y.fam = (P.sync i).fam → y.hooks = (P.sync i).hooks →
    ∀ n cid now s, Φ n (P.held s) → Ok P Φ (P.run (n.serveOwed y cid now) s)
  /-- A catalog sweep, under the node's setting with any transport room. -/
  sweep : ∀ (r rr : ByteArray → Option Nat) n cid s, Φ n (P.held s) →
    Ok P Φ (P.run (n.sweep { P.sync i with room := r, retryRoom := rr } cid) s)
  opens : ∀ n cid a dialer now s, Φ n (P.held s) → Ok P Φ (P.run (n.open (P.sync i) cid a dialer now) s)
  /-- Following the family's sessions: open the established, drop the rest. -/
  follow : ∀ n now s, Φ n (P.held s) → Ok P Φ (P.run (n.follow (P.sync i) now) s)
  /-- Handing out the outbox, its couriers purged. -/
  flush : ∀ n out s, Φ n (P.held s) → Ok P Φ (P.run (n.flush (P.sync i) out) s)
  calls : ∀ {α} (p : M α), Call (P.sync i) p → ∀ n s, Φ n (P.held s) → Φ n (P.held (P.run p s).2)
  setAddr : ∀ n cid a h, Φ n h → Φ (n.setAddr cid a) h
  heat : ∀ n ids now h, Φ n h → Φ (n.heat (P.sync i) ids now) h
  drop : ∀ n cid h, Φ n h → Φ (n.drop cid) h
  sent : ∀ n out now h, Φ n h → Φ (n.sent out now) h
  clear : ∀ n h, Φ n h → Φ { n with fresh := [], purged := [] } h
  /-- Catalog bookkeeping: retry cursors and admission order. -/
  retries : ∀ n l o h, Φ n h → Φ { n with sweeps := l, retryOrder := o } h

/-! ## The entry points, from the pieces -/

section
variable {P : Setup F M S} {i : Fin P.n} {Φ : Node → Held F → Prop}

theorem foldl_drop (Pc : Pieces P i Φ) : ∀ (L : List Id) (n : Node) (h : Held F), Φ n h → Φ (L.foldl Node.drop n) h
  | [], _, _, hn => hn
  | a :: t, n, h, hn => foldl_drop Pc t _ h (Pc.drop n a h hn)

/-- A node step, then the rest from its result. -/
theorem Ok.bind (L : Lawful P.run) {α β : Type} {p : M (Node × α)} {k : Node × α → M (Node × β)} {s : S}
    (hp : Ok P Φ (P.run p s)) (hk : ∀ r s', Φ r.1 (P.held s') → Ok P Φ (P.run (k r) s')) :
    Ok P Φ (P.run (p >>= k) s) := by
  rw [L.bind]; exact hk _ _ hp

/-- A step that leaves node n as it is, then the rest. -/
theorem Ok.call (L : Lawful P.run) {α β : Type} {p : M α} {n : Node} {k : α → M (Node × β)} {s : S}
    (hp : Φ n (P.held (P.run p s).2)) (hk : ∀ a s', Φ n (P.held s') → Ok P Φ (P.run (k a) s')) :
    Ok P Φ (P.run (p >>= k) s) := by
  rw [L.bind]; exact hk _ _ hp

theorem Ok.pure (L : Lawful P.run) {β : Type} {n : Node} {b : β} {s : S} (hn : Φ n (P.held s)) :
    Ok P Φ (P.run (Pure.pure (n, b) : M (Node × β)) s) := by
  unfold Ok; rw [L.pure]; exact hn

/-- A step that keeps node n's invariant and returns no node, then the rest. -/
theorem keep_bind (L : Lawful P.run) {α β : Type} {p : M α} {n : Node} {k : α → M β} {s : S}
    (hp : Φ n (P.held (P.run p s).2)) (hk : ∀ a s', Φ n (P.held s') → Φ n (P.held (P.run (k a) s').2)) :
    Φ n (P.held (P.run (p >>= k) s).2) := by
  rw [L.bind]; exact hk _ _ hp

/-- Reserved payloads are sealed one by one. -/
theorem sealRetries_ok (L : Lawful P.run) (Pc : Pieces P i Φ) (n : Node) (rs : List RetryOffer) (s : S)
    (hn : Φ n (P.held s)) : Φ n (P.held (P.run (n.sealRetries (P.sync i) rs) s).2) := by
  unfold Node.sealRetries
  refine keep_bind L ?_ fun _ s' h => by rw [L.pure]; exact h
  exact L.forIn_inv _ _ _ _ (fun _ s => Φ n (P.held s)) hn fun r _ b s hs =>
    keep_bind L (Pc.calls _ (.seal n _) n s hs) fun _ s' h => by rw [L.pure]; exact h

/-- The end of `finish`: every ended session's purge, then the node with
its write report cleared. -/
theorem finish_tail (L : Lawful P.run) (Pc : Pieces P i Φ) {N : Node} {s : S} {β : Type} {l init : List Id}
    {body : Id → List Id → M (ForInStep (List Id))} {g : List Id → β} (hN : Φ N (P.held s))
    (hb : ∀ c b s, Φ N (P.held s) → Φ N (P.held (P.run (body c b) s).2)) :
    Ok P Φ (P.run (forIn l init body >>= fun purged =>
      (Pure.pure ({ N with fresh := [], purged := [] }, g purged) : M (Node × β))) s) :=
  Ok.call L (L.forIn_inv _ _ _ s (fun _ s => Φ N (P.held s)) hN fun c _ b s hs => hb c b s hs)
    fun _ _ h => Ok.pure L (Pc.clear _ _ h)

/-- **Every entry point's end** keeps the invariant: following the
family's sessions, the outbox, the retired, sealing, and the purge of
every session that ended. -/
theorem finish_keeps (L : Lawful P.run) (Pc : Pieces P i Φ) (n : Node) (out : Acts) (now : Nat) (s : S)
    (hn : Φ n (P.held s)) : Ok P Φ (P.run (n.finish (P.sync i) out now) s) := by
  unfold Node.finish
  refine Ok.bind L (Pc.follow n now s hn) fun ⟨n1, o1⟩ s1 h1 => ?_
  refine Ok.bind L (Pc.flush n1 out s1 h1) fun ⟨n2, out2⟩ s2 h2 => ?_
  refine Ok.call L (Pc.calls _ .retired n2 s2 h2) fun ret s3 h3 => ?_
  have h4 := foldl_drop Pc ret n2 _ h3
  refine Ok.call L (Pc.calls _ (.seal _ _) _ s3 h4) fun _ s5 h5 => ?_
  refine Ok.call L (Pc.calls _ (.seal _ _) _ s5 h5) fun _ s6 h6 => ?_
  refine Ok.call L (sealRetries_ok L Pc _ _ s6 h6) fun ⟨_, _⟩ s7 h7 => ?_
  refine finish_tail L Pc ?_ ?_
  · exact Pc.sent _ _ now _ h7
  · intro c b s hs
    exact keep_bind L (Pc.calls _ (.endSession c) _ s hs) fun _ s' h => by rw [L.pure]; exact h

theorem onClose_keeps (L : Lawful P.run) (Pc : Pieces P i Φ) (n : Node) (addr : ByteArray) (now : Nat) (s : S)
    (hn : Φ n (P.held s)) : Ok P Φ (P.run (n.onClose (P.sync i) addr now) s) := by
  unfold Node.onClose
  exact finish_keeps L Pc _ _ now s (foldl_drop Pc _ n _ hn)

theorem connect_keeps (L : Lawful P.run) (Pc : Pieces P i Φ) (n : Node) (cid : Id) (a : ByteArray)
    (dialer : Bool) (now : Nat) (s : S) (hn : Φ n (P.held s)) :
    Ok P Φ (P.run (n.connect (P.sync i) cid a dialer now) s) := by
  unfold Node.connect
  exact Ok.bind L (Pc.opens n cid a dialer now s hn) fun ⟨n1, o1⟩ s1 h1 => finish_keeps L Pc n1 o1 now s1 h1

theorem onWrite_keeps (L : Lawful P.run) (Pc : Pieces P i Φ) (n : Node) (ops : List Op) (now : Nat) (s : S)
    (hn : Φ n (P.held s)) : Ok P Φ (P.run (n.onWrite (P.sync i) ops now) s) := by
  unfold Node.onWrite
  exact Ok.bind L (Pc.store n ops true s hn) fun ⟨n1, o1⟩ s1 h1 =>
    finish_keeps L Pc _ o1 now s1 (Pc.heat n1 _ now _ h1)

/-- A refreshed connection is the connection with the rooms the hook
gave, after the hook's run. -/
theorem refresh_bind (L : Lawful P.run) (cid : Id) (c : Conn) {β : Type} (k : Conn → M β) (s : S) :
    P.run (Node.refresh (P.sync i) cid c >>= k) s =
      P.run (k (c.carry (P.run ((P.sync i).hooks.rooms cid) s).1)) (P.run ((P.sync i).hooks.rooms cid) s).2 := by
  unfold Node.refresh
  rw [L.bind, L.bind, L.pure]

/-- A payload on a session, on its connection refreshed by the rooms hook. -/
theorem recv_ok (L : Lawful P.run) (Pc : Pieces P i Φ) {n : Node} {cid : Id} {c : Conn}
    (hc : n.conn? cid = some c) (b : ByteArray) (now : Nat) (s : S) (hn : Φ n (P.held s)) :
    Ok P Φ (P.run (Conn.recv (P.sync i).fam (P.sync i).cfg n.ix
      (c.carry (P.run ((P.sync i).hooks.rooms cid) s).1) b now >>= fun st => n.apply (P.sync i) cid st now)
      (P.run ((P.sync i).hooks.rooms cid) s).2) :=
  Pc.recv n cid c _ b now _ hc (Pc.calls _ (.rooms cid) n s hn)

/-- The clock on a session, likewise. -/
theorem tick_ok (L : Lawful P.run) (Pc : Pieces P i Φ) {n : Node} {cid : Id} {c : Conn}
    (hc : n.conn? cid = some c) (now : Nat) (s : S) (hn : Φ n (P.held s)) :
    Ok P Φ (P.run (Conn.tickGive (P.sync i).fam (P.sync i).cfg n.ix
      (c.carry (P.run ((P.sync i).hooks.rooms cid) s).1) now >>= fun st => n.apply (P.sync i) cid st now)
      (P.run ((P.sync i).hooks.rooms cid) s).2) :=
  Pc.tick n cid c _ now _ hc (Pc.calls _ (.rooms cid) n s hn)

theorem onSealed_keeps (L : Lawful P.run) (Pc : Pieces P i Φ) (n : Node) (addr : ByteArray)
    (opened : Option (Id × ByteArray)) (now : Nat) (s : S) (hn : Φ n (P.held s)) :
    Ok P Φ (P.run (n.onSealed (P.sync i) addr opened now) s) := by
  unfold Node.onSealed
  split
  · exact Ok.pure L hn
  · split
    · refine Ok.bind L ?_ fun ⟨n1, o1⟩ s1 h1 =>
        Ok.bind L (Pc.serve (P.sync i) rfl rfl n1 _ now s1 h1) fun ⟨n2, o2⟩ s2 h2 => finish_keeps L Pc n2 _ now s2 h2
      refine L.forIn_inv _ _ _ s (fun (st : Node × Acts) s => Φ st.1 (P.held s)) (Pc.setAddr _ _ _ _ hn) ?_
      intro b _ st s hs
      try dsimp only
      split
      · rename_i c hc
        have g := recv_ok L Pc hc b now s hs
        rw [L.bind] at g
        rw [refresh_bind L, L.bind, L.bind, L.pure]
        exact g
      · rw [L.pure]; exact hs
    · exact Ok.pure L hn

theorem onFrame_keeps (L : Lawful P.run) (Pc : Pieces P i Φ) (n : Node) (addr bytes : ByteArray) (now : Nat)
    (s : S) (hn : Φ n (P.held s)) : Ok P Φ (P.run (n.onFrame (P.sync i) addr bytes now) s) := by
  unfold Node.onFrame
  split
  · dsimp only
    split
    · exact Ok.pure L hn
    · split
      · exact Ok.pure L hn
      · refine Ok.bind L (Pc.write n _ s hn) fun ⟨n1, _⟩ s1 h1 => ?_
        refine Ok.call L (Pc.calls _ (.recv addr _ now) n1 s1 h1) fun more s2 h2 => ?_
        exact Ok.bind L (Pc.store n1 more true s2 h2) fun ⟨n3, o3⟩ s3 h3 => finish_keeps L Pc n3 o3 now s3 h3
  · exact Ok.call L (Pc.calls _ (.openFrame _) n s hn) fun opened s1 h1 =>
      onSealed_keeps L Pc n addr opened now s1 h1
  · exact Ok.pure L hn

end

end Engine.World
