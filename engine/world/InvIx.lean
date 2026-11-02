/-
Two more invariants of every plain node in every execution, proven of
the running node (engine/world/Inv.lean has the first, `managed_nil`).

- **What a session owes is queued** (`owes_queued`): every id a session
  owes (`owing`) is in its queue (`owed`). A want adds to both alike
  (`recv_owed`); serving takes exactly the served ids out of both (main's
  `serveOwed_run` with `serve_rest`); a session opens owing nothing; every
  other step leaves both alone.
- **The index covers the store** (`ix_covers`): every op of a room a node
  holds is listed in its index under its id. A write turn adds each op it
  newly stores to the index (`Node.write`); nothing else changes the
  store (the plain hooks purge nothing, and every other step only
  reads); nothing takes from the index. Two more facts go along: the
  index lists each item under its own op's key (`IxKeyed`), so adding a
  newly stored op is never shadowed by an item of the same key under
  another id (`Index.add` keeps one item per key); and the store holds
  each op under its own id and in its log (`LogInv`), so a restart,
  which boots the index from the log, covers the store.

Both are proven once per piece of the node (`oq_pieces`, `ix_pieces`:
the `Pieces` of engine/world/Pieces.lean, from the few the plain hooks
reach, `Plain.pieces`); the entry points are Pieces.lean's, for any
setup; then over every execution (`Plain.always`, through `Pieces.local`
and `Local` of engine/world/Good.lean). From
empty stores they are conjuncts of `Plain.good_always`
(engine/world/PlainGood.lean: `owes_queued_start`, `ix_covers_start`).
-/
import engine.world.Inv

namespace Engine.World
open Engine Engine.Sync

variable {F : Type}

attribute [local instance] byteArray_lawfulBEq

/-! ## Invariant 1: what a session owes is queued -/

/-- Every session of the node owes only ids in its queue. -/
def NodeOQ (n : Node) : Prop := ∀ cid c, n.conn? cid = some c → OwesQueued c

/-- A connection that owes and queues what c did. -/
def SameQ (c c' : Conn) : Prop := c'.owed = c.owed ∧ c'.owing = c.owing

theorem SameQ.oq {c c' : Conn} (e : SameQ c c') (hq : OwesQueued c) : OwesQueued c' := by
  intro y hy; rw [e.2] at hy; rw [e.1]; exact hq y hy

theorem oq_conns {n n' : Node} (e : n'.conns = n.conns) (hn : NodeOQ n) : NodeOQ n' := by
  intro cid c hc; simp only [Node.conn?] at hc; rw [e] at hc; exact hn cid c hc

/-- Stepping each session in place, keeping its id and what it owes
within its queue. -/
theorem oq_map (n : Node) (g : Id × Conn → Id × Conn) (hk : ∀ q, (g q).1 = q.1)
    (hq : ∀ q, OwesQueued q.2 → OwesQueued (g q).2) (hn : NodeOQ n) : NodeOQ { n with conns := n.conns.map g } := by
  intro cid c hc
  simp only [Node.conn?, List.find?_map, Option.map_map] at hc
  have e : ((fun p : Id × Conn => Decidable.decide (p.1 = cid)) ∘ g) = fun p => Decidable.decide (p.1 = cid) := by
    funext p; simp [Function.comp, hk]
  rw [e] at hc
  cases e' : n.conns.find? (fun p => Decidable.decide (p.1 = cid)) with
  | none => rw [e'] at hc; cases hc
  | some p =>
    rw [e'] at hc
    simp only [Option.map_some, Option.some.injEq, Function.comp] at hc
    subst hc
    exact hq p (hn cid p.2 (by simp [Node.conn?, e']))

/-- Replacing session cid's connection by one that owes only what it queues. -/
theorem oq_replace (n : Node) (cid : Id) (c' : Conn) (hc' : OwesQueued c') (hn : NodeOQ n) :
    NodeOQ { n with conns := n.conns.map fun p => if p.1 = cid then (cid, c') else p } :=
  oq_map n _ (fun q => by split <;> simp_all) (fun q hq => by
    split
    · exact hc'
    · exact hq) hn

/-- Closing a session leaves the others as they were. -/
theorem find_close (L : List (Id × Conn)) (cid cid' : Id) (p : Id × Conn)
    (h : (L.filter fun q => !Decidable.decide (q.1 = cid)).find? (fun q => Decidable.decide (q.1 = cid')) = some p) :
    L.find? (fun q => Decidable.decide (q.1 = cid')) = some p := by
  induction L with
  | nil => cases h
  | cons q t ih =>
    by_cases e1 : q.1 = cid
    · rw [List.filter_cons_of_neg (by simp [e1])] at h
      have hq : ¬ q.1 = cid' := by
        intro e2
        have hp1 := List.find?_some h
        have hp2 := List.mem_of_find?_eq_some h
        simp only [List.mem_filter, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not] at hp1 hp2
        exact hp2.2 (hp1.trans (e2.symm.trans e1))
      rw [List.find?_cons_of_neg (by simp [hq])]; exact ih h
    · rw [List.filter_cons_of_pos (by simp [e1])] at h
      by_cases e2 : q.1 = cid'
      · rw [List.find?_cons_of_pos (by simp [e2])] at h ⊢; exact h
      · rw [List.find?_cons_of_neg (by simp [e2])] at h ⊢; exact ih h

theorem close_conn (n : Node) (cid cid' : Id) (c : Conn) (h : (n.close cid).conn? cid' = some c) :
    n.conn? cid' = some c := by
  simp only [Node.conn?, Node.close] at h ⊢
  cases e : (n.conns.filter fun q => !Decidable.decide (q.1 = cid)).find? (fun q => Decidable.decide (q.1 = cid')) with
  | none => rw [e] at h; cases h
  | some p => rw [e] at h; rw [find_close _ _ _ _ e]; exact h

theorem oq_drop (n : Node) (cid : Id) (hn : NodeOQ n) : NodeOQ (n.drop cid) :=
  fun cid' c hc => hn cid' c (close_conn n cid cid' c hc)

theorem oq_sent (n : Node) (out : Acts) (now : Nat) (hn : NodeOQ n) : NodeOQ (n.sent out now) := by
  unfold Node.sent
  exact oq_map n _ (fun q => by cases q; rfl) (fun q hq => by
    cases q; dsimp only; split
    · exact hq
    · exact hq) hn

/-! ### Each step of a connection keeps it -/

theorem start_q (cfg : Config) (ix : Index) (c : Conn) (now : Nat) : SameQ c (c.start cfg ix now).conn := by
  rcases Conn.start_conn cfg ix c now with e | ⟨k, a, rs, ss, es, e⟩ <;> rw [e] <;> exact ⟨rfl, rfl⟩

theorem ask_q (cfg : Config) (c : Conn) (now : Nat) : SameQ c (c.ask cfg now).conn := by
  obtain ⟨rs, ss, e⟩ := Conn.ask_conn cfg c now; rw [e]; exact ⟨rfl, rfl⟩

theorem tick_q (fam : Family F) (cfg : Config) (ix : Index) (c : Conn) (now : Nat) (h : Held F) :
    SameQ c ((c.tick fam cfg ix now : HeldM F Step) h).1.conn := by
  unfold Conn.tick Conn.work
  split
  · exact ⟨rfl, rfl⟩
  · simp only [HeldM.bind_apply, HeldM.pure_apply, Step.pulse_conn]
    split
    · obtain ⟨s1, s2⟩ := start_q cfg ix (c.expireAsks cfg now) now
      exact ⟨s1, s2⟩
    · obtain ⟨s1, s2⟩ := ask_q cfg (c.expireAsks cfg now) now
      exact ⟨s1, s2⟩

theorem give_q (fam : Family F) (cfg : Config) : ∀ (l : List (Id × Id)) (c : Conn) (h : Held F),
    SameQ c ((c.give fam cfg l : HeldM F Step) h).1.conn
  | [], _, _ => ⟨rfl, rfl⟩
  | (r, x) :: rest, c, h => by
    unfold Conn.give
    split
    · exact give_q fam cfg rest c h
    · simp only [HeldM.bind_apply, HeldM.pure_apply]
      exact give_q fam cfg rest _ _

/-- **The clock keeps the queue and what the session owes.** -/
theorem tickGive_q (fam : Family F) (cfg : Config) (ix : Index) (c : Conn) (now : Nat) (h : Held F) :
    SameQ c ((c.tickGive fam cfg ix now : HeldM F Step) h).1.conn := by
  simp only [Conn.tickGive, Conn.notify, HeldM.bind_apply, HeldM.pure_apply]
  obtain ⟨g1, g2⟩ := give_q fam cfg c.notices c h
  split
  · obtain ⟨t1, t2⟩ := tick_q fam cfg ix ((c.give fam cfg c.notices : HeldM F Step) h).1.conn now
      ((c.give fam cfg c.notices : HeldM F Step) h).2
    exact ⟨t1.trans g1, t2.trans g2⟩
  · obtain ⟨t1, t2⟩ := tick_q fam cfg ix ((c.give fam cfg c.notices : HeldM F Step) h).1.conn now
      ((c.give fam cfg c.notices : HeldM F Step) h).2
    exact ⟨t1.trans g1, t2.trans g2⟩

theorem foldl_erase_mem {y : Id} : ∀ (L : List Id) (A : Std.HashSet Id),
    y ∈ L.foldl (·.erase ·) A ↔ y ∈ A ∧ y ∉ L := by
  intro L
  induction L with
  | nil => intro A; simp
  | cons a t ih =>
    intro A
    rw [List.foldl_cons, ih, Std.HashSet.mem_erase]
    simp only [List.mem_cons, not_or, beq_eq_false_iff_ne, ne_eq]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h2, fun e => h1 e.symm, h3⟩
    · rintro ⟨h2, h1, h3⟩; exact ⟨⟨fun e => h1 e.symm, h2⟩, h3⟩

/-- **Serving the queue keeps what the session owes within it:** the ids
served leave the queue and the owing set alike (`serve_rest`: what stays
queued is the queue's tail). -/
theorem serveOwed_oq (fam : Family F) (cfg : Config) (c : Conn) (budget : Nat) (first : List Id) (h : Held F)
    (hq : OwesQueued c) : OwesQueued ((c.serveOwed fam cfg budget first : HeldM F _) h).1.1 := by
  rw [serveOwed_eq]
  dsimp only
  obtain ⟨pre, hpre⟩ := serve_rest (c.shows fam) h.db.ops (c.owedAfter first) budget
  generalize ((serve (c.shows fam) budget (c.owedAfter first)).trace h.db.ops).1 = t at hpre ⊢
  have e1 : ∀ gone rest sent, (c.served cfg gone rest sent).owed = rest := fun _ _ _ => rfl
  have e2 : ∀ gone rest sent, (c.served cfg gone rest sent).owing = gone.foldl (·.erase ·) c.owing :=
    fun _ _ _ => rfl
  intro y hy
  rw [e2] at hy; rw [e1]
  obtain ⟨hyc, hyg⟩ := (foldl_erase_mem _ _).1 hy
  have hyo := hq y hyc
  simp only [List.mem_append, not_or] at hyg
  obtain ⟨hh, hp⟩ := hyg
  have hya : y ∈ c.owedAfter first := by
    unfold Conn.owedAfter
    split
    · exact hyo
    · exact List.mem_filter.2 ⟨hyo, by simpa using hh⟩
  rw [hpre] at hya hp
  have ht : (pre ++ t.2).take ((pre ++ t.2).length - t.2.length) = pre := by
    rw [List.length_append, Nat.add_sub_cancel]; exact List.take_left
  rw [ht] at hp
  rcases List.mem_append.1 hya with h1 | h1
  · exact absurd h1 hp
  · exact h1

section
variable (S : Engine.Sync.Setup F) (s : Who)

/-- **Applying a step**, for any invariant that storing keeps: dropped,
or the session's connection replaced, then a store. -/
theorem apply_gen (Φ : Node → Held F → Prop)
    (hs : ∀ n ops mine h, Φ n h → Φ ((n.store (S.sync s) ops mine).run h).1.1 ((n.store (S.sync s) ops mine).run h).2)
    (n : Node) (cid : Id) (st : Step) (now : Nat) (h : Held F)
    (hd : st.drop = true → Φ (n.drop cid) h)
    (hr : st.drop = false → Φ { n with conns := n.conns.map fun p => if p.1 = cid then (cid, st.conn) else p } h) :
    Φ ((n.apply (S.sync s) cid st now).run h).1.1 ((n.apply (S.sync s) cid st now).run h).2 := by
  have hfold : ∀ (L : List Op), L.foldl (fun b (_ : Op) => b) ([] : List Op) = [] := by
    intro L; induction L with
    | nil => rfl
    | cons _ _ ih => exact ih
  unfold Node.apply
  split
  · rename_i hdr; exact hd hdr
  · rename_i hdr
    simp only [HeldM.run_bind, recordGiven_run]
    rw [forIn_yield _ _ (fun _ acc => acc) _ (fun o _ acc => by
      simp only [sync_recv, HeldM.run_bind, HeldM.run_pure, List.append_nil]), hfold, store_nil]
    simp only [HeldM.run_pure]
    exact hs _ _ _ _ (hr (by simpa using hdr))

theorem store_oq (n : Node) (ops : List Op) (mine : Bool) (h : Held F) (hn : NodeOQ n) :
    NodeOQ ((n.store (S.sync s) ops mine).run h).1.1 := by
  intro cid c' hc'
  obtain ⟨c, hc, -, e1, e2⟩ := (store_facts S s n ops mine h).2.2.2 cid c' hc'
  exact SameQ.oq ⟨e1, e2⟩ (hn cid c hc)

/-- Serving a session's queue, on any sync (the clock serves on
`afterActs`'s): the served session's connection is `serveOwed_oq`'s. -/
theorem serve_oq (y : Sync F (HeldM F)) (n : Node) (cid : Id) (now : Nat) (h : Held F) (hn : NodeOQ n) :
    NodeOQ ((n.serveOwed y cid now).run h).1.1 := by
  unfold Node.serveOwed
  split
  · exact hn
  · rename_i c hc
    split
    · exact hn
    · simp only [HeldM.run_bind, Node.refresh, HeldM.run_pure]
      exact oq_replace n cid _ (serveOwed_oq _ _ _ _ _ _ (hn cid c hc)) hn

end

/-! ## Invariant 2: the index covers the store -/

/-- Every op of a room the store holds is listed in the node's index,
in its room, under its id. -/
def IxCovers (fam : Family F) (n : Node) (h : Held F) : Prop :=
  ∀ r x o, h.db.ops x = some o → fam.room o = some r → ∃ a ∈ n.ix.items r, a.2 = x

/-- Every item of an index is an op's key and that op's id (what
`Index.add` lists), so an op's key names one id. -/
def IxKeyed (fam : Family F) (ix : Index) : Prop := ∀ r a, a ∈ ix.items r → ∃ p : Op, a = (keyOf fam p, p.id)

/-- The store holds each op under its own id, and in its log (what a
restart boots the index from). -/
def LogInv (h : Held F) : Prop := ∀ x o, h.db.ops x = some o → o.id = x ∧ o ∈ h.log

/-- What a node's index keeps of its store, across restarts too. -/
def IxInv (fam : Family F) (n : Node) (h : Held F) : Prop := IxCovers fam n h ∧ IxKeyed fam n.ix ∧ LogInv h

theorem ixinv_of_ix {fam : Family F} {m n : Node} {h : Held F} (e : m.ix = n.ix) (hi : IxInv fam n h) :
    IxInv fam m h := by
  unfold IxInv IxCovers; rw [e]; exact hi

theorem keyed_foldl (fam : Family F) {ix : Index} (hk : IxKeyed fam ix) (L : List Op) :
    IxKeyed fam (L.foldl (Index.add fam) ix) := by
  intro r a ha
  rcases mem_items_foldl fam ha with h | ⟨o, _, e, _⟩
  · exact hk r a h
  · exact ⟨o, e⟩

/-- An op added to a keyed index is listed under its id: no item of
another id has its key. -/
theorem covers_foldl (fam : Family F) {ix : Index} (hk : IxKeyed fam ix) {L : List Op} {o : Op} {r : Id}
    (ho : o ∈ L) (hr : fam.room o = some r) : ∃ a ∈ (L.foldl (Index.add fam) ix).items r, a.2 = o.id := by
  obtain ⟨a, ha, e⟩ := items_foldl_key fam (ix := ix) ho hr
  obtain ⟨p, rfl⟩ := keyed_foldl fam hk L r a ha
  exact ⟨_, ha, keyOf_id fam e⟩

/-- What a write turn's intake stores: what was stored, or an op of the
turn, under its own id. -/
theorem foldl_ingestS_ops : ∀ (L : List Op) (s : DB F) {x : Id} {o : Op},
    (L.foldl (fun s o => ingestS o s) s).ops x = some o → s.ops x = some o ∨ (o ∈ L ∧ o.id = x) := by
  intro L
  induction L with
  | nil => intro s x o h; exact Or.inl h
  | cons p t ih =>
    intro s x o h
    rcases ih (ingestS p s) h with h | ⟨hm, he⟩
    · unfold ingestS at h
      split at h
      · exact Or.inl h
      · change (if x = p.id then some p else s.ops x) = some o at h
        split at h
        · rename_i e; cases h; exact Or.inr ⟨List.mem_cons_self .., e.symm⟩
        · exact Or.inl h
    · exact Or.inr ⟨List.mem_cons_of_mem _ hm, he⟩

theorem foldl_ingestS_isSome : ∀ (L : List Op) (s : DB F) {o : Op}, o ∈ L →
    ((L.foldl (fun s o => ingestS o s) s).ops o.id).isSome = true := by
  intro L
  induction L with
  | nil => intro s o ho; cases ho
  | cons p t ih =>
    intro s o ho
    rcases List.mem_cons.1 ho with rfl | ho
    · have : ((ingestS o s).ops o.id).isSome = true := by
        unfold ingestS
        split
        · rename_i q hq; rw [hq]; rfl
        · show (if o.id = o.id then some o else s.ops o.id).isSome = true
          simp
      obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 this
      rw [List.foldl_cons, foldl_ingest_keep t hq]; rfl
    · rw [List.foldl_cons]; exact ih _ ho

/-- **A write keeps the index covering the store**: the ops it newly
stores join the index, each under its own id. -/
theorem write_ixinv (x : Sync F (HeldM F)) (n : Node) (ops : List Op) (h : Held F) (hi : IxInv x.fam n h) :
    IxInv x.fam ((n.write x ops).run h).1.1 ((n.write x ops).run h).2 := by
  show IxInv x.fam (n.write x ops h).1.1 (n.write x ops h).2
  obtain ⟨hc, hk, hl⟩ := hi
  unfold Node.write
  simp only [HeldM.bind_apply]
  rw [HeldM.forIn_reads (g := absentStep h.db)]
  · dsimp only
    generalize ops.foldl (absentStep h.db) [] = absent
    by_cases he : absent.isEmpty = true
    · rw [ite_eq_left he]; exact ⟨hc, hk, hl⟩
    · rw [ite_eq_right he]
      simp only [HeldM.bind_apply, turn_apply]
      generalize absent.reverse = news
      have hS := fun o (ho : o ∈ news) => foldl_ingestS_isSome news h.db ho
      generalize hT : List.foldl (fun s o => ingestS o s) h.db news = t at hS ⊢
      generalize budget (h.log ++ news) t = k
      have hS' : ∀ o ∈ news, ((drainS x.fam k t).ops o.id).isSome = true := by
        intro o ho; rw [drainS_ops]; exact hS o ho
      rw [HeldM.forIn_reads (g := fileStep x.fam (drainS x.fam k t))]
      · simp only [HeldM.pure_apply]
        show IxInv x.fam { n with ix := (news.foldl (fileStep x.fam (drainS x.fam k t)) (n.ix, [])).1, fresh := _ }
          (Held.mk (h.log ++ news) (drainS x.fam k t))
        rw [foldl_fileStep x.fam _ news _ hS']
        refine ⟨fun r y o hy hr => ?_, keyed_foldl x.fam hk news, fun y o hy => ?_⟩
        · change (drainS x.fam k t).ops y = some o at hy
          rw [drainS_ops, ← hT] at hy
          rcases foldl_ingestS_ops news h.db hy with hy | ⟨hm, he⟩
          · obtain ⟨a, ha, ea⟩ := hc r y o hy hr
            exact ⟨a, items_foldl_mono x.fam ha, ea⟩
          · subst he; exact covers_foldl x.fam hk hm hr
        · change (drainS x.fam k t).ops y = some o at hy
          rw [drainS_ops, ← hT] at hy
          rcases foldl_ingestS_ops news h.db hy with hy | ⟨hm, he⟩
          · obtain ⟨e, hlog⟩ := hl y o hy; exact ⟨e, List.mem_append_left _ hlog⟩
          · exact ⟨he, List.mem_append_right _ hm⟩
      · intro a b
        rw [HeldM.bind_apply, HeldM.getOp_apply]
        unfold fileStep
        by_cases h1 : ((drainS x.fam k t).ops a.id).isSome = true
        · rw [ite_eq_left h1, ite_eq_left h1]; rfl
        · rw [ite_eq_right h1, ite_eq_right h1]; rfl
  · intro a b
    unfold absentStep
    by_cases h1 : (!b.any fun p => p.id == a.id) = true
    · rw [ite_eq_left h1, ite_eq_left h1, HeldM.bind_apply, HeldM.getOp_apply]
      by_cases h2 : (h.db.ops a.id).isNone = true
      · rw [ite_eq_left h2, ite_eq_left h2]; rfl
      · rw [ite_eq_right h2, ite_eq_right h2]; rfl
    · rw [ite_eq_right h1, ite_eq_right h1]; rfl

/-- **Booting covers the store**: the index of the log lists every
stored op under its id. -/
theorem boot_ixinv (fam : Family F) (h : Held F) (floor : Nat) (hl : LogInv h) :
    IxInv fam (Node.boot fam h.log floor) h := by
  have h0 : IxKeyed fam ({} : Index) := fun r a ha => by simp [Index.items, Index.room?] at ha
  refine ⟨fun r x o hx hr => ?_, keyed_foldl fam h0 h.log, hl⟩
  obtain ⟨e, hlog⟩ := hl x o hx
  subst e
  exact covers_foldl fam h0 hlog hr

section
variable (S : Engine.Sync.Setup F) (s : Who)

theorem store_ixinv (n : Node) (ops : List Op) (mine : Bool) (h : Held F) (hi : IxInv S.fam n h) :
    IxInv S.fam ((n.store (S.sync s) ops mine).run h).1.1 ((n.store (S.sync s) ops mine).run h).2 := by
  rw [store_run]
  dsimp only
  have hw := write_ixinv (S.sync s) n (intake (S.sync s).fam mine ops) h hi
  split
  · exact hw
  · rw [fanout_reads]
    exact ixinv_of_ix (fanout_ix S s _ _ _) hw

/-- Serving a session's queue, on any sync with the plain node's hooks,
reads the store and keeps the index. -/
theorem serveOwed_ix (y : Sync F (HeldM F)) (hh : y.hooks = (S.sync s).hooks) (n : Node) (cid : Id) (now : Nat)
    (h : Held F) : ((n.serveOwed y cid now).run h).2 = h ∧ ((n.serveOwed y cid now).run h).1.1.ix = n.ix := by
  unfold Node.serveOwed
  split
  · exact ⟨rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl⟩
    · simp only [HeldM.run_bind, Node.refresh, hh, sync_rooms, HeldM.run_pure]
      constructor
      · exact (serveOwed_run y.fam y.cfg _ _ _ h).2.2
      · first | rfl | trivial

end

/-! ## Over every execution -/

namespace Plain
variable {Q : Plain F}

/-- **Every piece of a plain node keeps what its sessions owe queued.** -/
theorem oq_pieces (i : Fin Q.n) : Pieces Q.setup i (fun n _ => NodeOQ n) :=
  pieces (fun n ops h hn => oq_conns (write_conns _ n ops h) hn)
    (fun n ops mine h hn => store_oq (Q.two i) .a n ops mine h hn)
    (fun n cid c rs b now h hc hn => apply_gen (Q.two i) .a (fun n _ => NodeOQ n)
      (fun n ops mine h hn => store_oq (Q.two i) .a n ops mine h hn) n cid _ now h (fun _ => oq_drop n cid hn)
      (fun _ => oq_replace n cid _ (recv_owed Q.fam Q.cfg n.ix (c.carry rs) b now h (hn cid c hc)).1 hn))
    (fun n cid c rs now h hc hn => apply_gen (Q.two i) .a (fun n _ => NodeOQ n)
      (fun n ops mine h hn => store_oq (Q.two i) .a n ops mine h hn) n cid _ now h (fun _ => oq_drop n cid hn)
      (fun _ => oq_replace n cid _ (SameQ.oq (tickGive_q Q.fam Q.cfg n.ix (c.carry rs) now h) (hn cid c hc)) hn))
    (fun y _ _ n cid now h hn => serve_oq y n cid now h hn)
    (fun n cid a dialer now h hn => by
      show NodeOQ ((n.open ((Q.two i).sync .a) cid a dialer now).run h).1.1
      unfold Node.open
      simp only [HeldM.run_bind, sync_rooms, HeldM.run_pure]
      intro cid' c hc
      simp only [Node.conn?, List.find?_cons] at hc
      split at hc
      · simp only [Option.map_some, Option.some.injEq] at hc
        subst hc
        intro y hy
        simp [Conn.open] at hy
      · exact hn cid' c (close_conn n cid cid' c hc))
    (fun _ _ _ _ hn => oq_conns rfl hn) (fun _ _ _ _ hn => oq_conns rfl hn) (fun n cid _ hn => oq_drop n cid hn)
    (fun n o t _ hn => oq_sent n o t hn) (fun _ _ hn => oq_conns rfl hn) (fun _ _ _ _ hn => oq_conns rfl hn)

/-- **Every piece of a plain node keeps its index covering its store.** -/
theorem ix_pieces (i : Fin Q.n) : Pieces Q.setup i (IxInv Q.fam) :=
  pieces (fun n ops h hi => write_ixinv ((Q.two i).sync .a) n ops h hi)
    (fun n ops mine h hi => store_ixinv (Q.two i) .a n ops mine h hi)
    (fun n cid _ _ _ now h _ hi => apply_gen (Q.two i) .a (IxInv Q.fam) (store_ixinv (Q.two i) .a) n cid _ now h
      (fun _ => ixinv_of_ix rfl hi) (fun _ => ixinv_of_ix rfl hi))
    (fun n cid _ _ now h _ hi => apply_gen (Q.two i) .a (IxInv Q.fam) (store_ixinv (Q.two i) .a) n cid _ now h
      (fun _ => ixinv_of_ix rfl hi) (fun _ => ixinv_of_ix rfl hi))
    (fun y _ hh n cid now h hi => by
      obtain ⟨e1, e2⟩ := serveOwed_ix (Q.two i) .a y hh n cid now h
      show IxInv Q.fam ((n.serveOwed y cid now).run h).1.1 ((n.serveOwed y cid now).run h).2
      rw [e1]; exact ixinv_of_ix e2 hi)
    (fun n cid a dialer now h hi => by
      show IxInv Q.fam ((n.open ((Q.two i).sync .a) cid a dialer now).run h).1.1
        ((n.open ((Q.two i).sync .a) cid a dialer now).run h).2
      unfold Node.open
      simp only [HeldM.run_bind, sync_rooms, HeldM.run_pure]
      exact ixinv_of_ix rfl hi)
    (fun _ _ _ _ hi => ixinv_of_ix rfl hi) (fun _ _ _ _ hi => ixinv_of_ix rfl hi)
    (fun _ _ _ hi => ixinv_of_ix rfl hi) (fun _ _ _ _ hi => ixinv_of_ix rfl hi)
    (fun _ _ hi => ixinv_of_ix rfl hi) (fun _ _ _ _ hi => ixinv_of_ix rfl hi)

/-- **A node invariant that every piece of a plain node keeps, and that
a restart restores from the store, holds of every node in every
execution**, against any attacker (`Pieces.local`, engine/world/Pieces.lean). -/
theorem always {adv : World (Held F) Q.n → ByteArray → Prop} {w₀ : World (Held F) Q.n}
    (E : Exec Q.setup adv w₀) (Φ : Node → Held F → Prop) (P : ∀ i, Pieces Q.setup i Φ)
    (hboot : ∀ n h, Φ n h → Φ (Node.boot Q.fam h.log 0) h)
    (h0 : ∀ i, Φ (w₀.node i) (w₀.box i)) : ∀ k i, Φ ((E.world k).node i) ((E.world k).box i) :=
  (Pieces.local lawful (Φ := fun _ => Φ) P fun _ n h hn => hboot n h hn).keeps.always h0 E

/-- **Every session owes only ids in its queue**, at every node in every
execution against any attacker, from sessions that did. -/
theorem owes_queued {adv : World (Held F) Q.n → ByteArray → Prop} {w₀ : World (Held F) Q.n}
    (E : Exec Q.setup adv w₀) (h0 : ∀ i cid c, (w₀.node i).conn? cid = some c → OwesQueued c) :
    ∀ k i cid c, ((E.world k).node i).conn? cid = some c → OwesQueued c :=
  always E (fun n _ => NodeOQ n) oq_pieces
    (fun _ _ _ cid c hc => by simp [Node.boot, Node.conn?] at hc) h0

/-- **Every node's index covers its store**, in every execution against
any attacker: each op of a room a node holds is listed in its index, in
that room, under its id. From nodes whose index covers their store,
lists only ops' own keys and ids (`IxKeyed`), and whose store holds each
op under its id and in its log (`LogInv`); a restart needs these two. -/
theorem ix_covers {adv : World (Held F) Q.n → ByteArray → Prop} {w₀ : World (Held F) Q.n}
    (E : Exec Q.setup adv w₀) (h0 : ∀ i, IxCovers Q.fam (w₀.node i) (w₀.box i))
    (hk : ∀ i, IxKeyed Q.fam (w₀.node i).ix) (hl : ∀ i, LogInv (w₀.box i)) :
    ∀ k i, IxCovers Q.fam ((E.world k).node i) ((E.world k).box i) := fun k i =>
  (always E (IxInv Q.fam) ix_pieces (fun _ h hi => boot_ixinv Q.fam h 0 hi.2.2)
    (fun i => ⟨h0 i, hk i, hl i⟩) k i).1

end Plain

/-! ## Negative control: a hook that stores without indexing

The `calls` piece has teeth: a dial hook that stores an op with a write
turn of its own, bypassing `Node.write` (so the node's index never lists
it), breaks the index's cover, and no `Pieces` for `IxInv` exists for a
node with that hook. -/

/-- **A mutant dial hook**: it stores op o directly, never indexing it.
Meant never to run. -/
def dialStores (fam : Family F) (o : Op) : Nat → HeldM F (List Op) := fun _ => do
  Turn.turn fam [o]
  pure []

/-- One node on the one-room family whose dial hook is the mutant. -/
def dialMutant (r : Id) (o : Op) : Setup Unit (HeldM Unit) (Held Unit) where
  n := 1
  sync _ := { fam := oneRoom r,
              hooks := { rooms := fun _ => pure [], sealFor := plainSeal, openFrame := plainOpen,
                         dial := dialStores (oneRoom r) o } }
  addr _ := ByteArray.empty
  run m h := m.run h
  held h := h

/-- **The mutant breaks the index's cover, so its `Pieces` cannot be
proven**: from an empty store and a fresh node, the dial stores o, an op
of room r, which the node's index does not list. -/
theorem dial_mutant_unindexed (r : Id) (o : Op) : ¬ Pieces (dialMutant r o) ⟨0, Nat.zero_lt_one⟩ (IxInv (oneRoom r)) := by
  intro Pc
  have h0 : IxInv (oneRoom r) (Node.boot (oneRoom r) [] 0) ({} : Held Unit) :=
    ⟨(fun _ _ _ hx => by cases hx),
     (fun _ _ ha => by simp [Node.boot, Index.ofOps, Index.items, Index.room?] at ha),
     (fun _ _ hx => by cases hx)⟩
  have h1 := Pc.calls _ (.dial 0) _ {} h0
  have hs : ((dialStores (oneRoom r) o 0).run ({} : Held Unit)).2.db.ops o.id = some o := by
    obtain ⟨o', ho'⟩ := Option.isSome_iff_exists.1
      (foldl_ingestS_isSome [o] (DB.empty : DB Unit) (o := o) (List.mem_singleton_self o))
    rcases foldl_ingestS_ops [o] DB.empty ho' with h | ⟨hm, -⟩
    · cases h
    · rw [List.mem_singleton] at hm
      subst hm
      show (drainS _ _ _).ops o'.id = some o'
      rw [drainS_ops]
      exact ho'
  obtain ⟨a, ha, -⟩ := h1.1 r o.id o hs rfl
  simp [Node.boot, Index.ofOps, Index.items, Index.room?] at ha

end Engine.World
