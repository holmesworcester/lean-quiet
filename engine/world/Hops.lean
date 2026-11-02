/-
The hops an op takes across a session, proven of the running node over
frames of any payloads, at a node with any number of sessions
(docs/PROOFS.md, "The hops"). Each is about one entry point of a plain
node (a3's `Setup.sync`, fixed rooms, frames in the clear), so it holds
at node i of the n-node World whatever the other nodes do.

- **What a payload does to the store** (`recv_cases`, `apply_store`): a
  connection step never drops its session, and it takes nothing, or the
  payload's own op; so a payload leaves the store as it was, or adds
  exactly its op, if the store lacked it.
- **Sessions persist through a frame** (`apply_keeps`): taking payloads
  never closes the session, whatever they are.
- **H3, an op is taken** (`onSealed_takes`, `onFrame_takes`): a frame on
  a session the node has open, carrying an op of a room the session
  shows, stores that op, wherever it sits in the frame and whatever else
  the frame carries.
-/
import engine.world.Plain

namespace Engine.World
open Engine Engine.Sync

variable {F : Type}

/-! ## Loops -/

/-- A loop whose every turn yields: an invariant P every turn keeps, a Q
that the turn on a makes and every turn keeps under P, hold at the end
once a is in the list. -/
theorem forIn_after {α β} (f : α → β → HeldM F (ForInStep β)) (P Q : Held F → β → Prop) (a : α)
    (l : List α)
    (hy : ∀ a' ∈ l, ∀ b h, ∃ b', ((f a' b).run h).1 = .yield b')
    (hP : ∀ a' ∈ l, ∀ b h, P h b → P ((f a' b).run h).2 ((f a' b).run h).1.value)
    (hQ : ∀ a' ∈ l, ∀ b h, P h b → Q h b → Q ((f a' b).run h).2 ((f a' b).run h).1.value)
    (ha : ∀ b h, P h b → Q ((f a b).run h).2 ((f a b).run h).1.value) :
    a ∈ l → ∀ b h, P h b → Q ((forIn l b f).run h).2 ((forIn l b f).run h).1 := by
  have keep : ∀ (l' : List α), (∀ x ∈ l', x ∈ l) → ∀ b h, P h b → Q h b →
      P ((forIn l' b f).run h).2 ((forIn l' b f).run h).1 ∧ Q ((forIn l' b f).run h).2 ((forIn l' b f).run h).1 := by
    intro l'
    induction l' with
    | nil => intro _ b h hp hq; exact ⟨hp, hq⟩
    | cons a' t ih =>
      intro hl b h hp hq
      have ha' := hl a' (List.mem_cons_self ..)
      rw [List.forIn_cons, HeldM.run_bind]
      obtain ⟨b', e⟩ := hy a' ha' b h
      have hp' := hP a' ha' b h hp
      have hq' := hQ a' ha' b h hp hq
      rw [e] at hp' hq' ⊢
      exact ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)) b' _ hp' hq'
  have main : ∀ (l' : List α), (∀ x ∈ l', x ∈ l) → a ∈ l' → ∀ b h, P h b →
      Q ((forIn l' b f).run h).2 ((forIn l' b f).run h).1 := by
    intro l'
    induction l' with
    | nil => intro _ hm; cases hm
    | cons a' t ih =>
      intro hl hm b h hp
      have ha' := hl a' (List.mem_cons_self ..)
      have ht : ∀ x ∈ t, x ∈ l := fun x hx => hl x (List.mem_cons_of_mem _ hx)
      rw [List.forIn_cons, HeldM.run_bind]
      obtain ⟨b', e⟩ := hy a' ha' b h
      have hp' := hP a' ha' b h hp
      rw [e] at hp' ⊢
      rcases List.mem_cons.1 hm with rfl | hm
      · have hq' := ha b h hp
        rw [e] at hq'
        exact (keep t ht b' _ hp' hq').2
      · exact ih ht hm b' _ hp'
  exact main l (fun _ hx => hx)

/-! ## Write turns, read off the store -/

/-- A write turn keeps every op stored. -/
theorem turnH_some (fam : Family F) (ops : List Op) (h : Held F) {x : Id} {o : Op} (hx : h.db.ops x = some o) :
    (turnH fam ops h).db.ops x = some o := by
  show (drainS fam _ (ops.foldl (fun s o => ingestS o s) h.db)).ops x = some o
  rw [drainS_ops]; exact foldl_ingestS_some ops hx

/-- A write turn of one op the store lacks adds exactly that op. -/
theorem turnH_one_ops (fam : Family F) (o : Op) (h : Held F) (hn : h.db.ops o.id = none) (x : Id) :
    (turnH fam [o] h).db.ops x = if x = o.id then some o else h.db.ops x := by
  show (drainS fam _ (ingestS o h.db)).ops x = _
  rw [drainS_ops]; simp [ingestS, hn, DB.putOp, DB.push]

/-! ## What a connection step does with a payload -/

/-- **A payload's step:** it reads the store, never drops the session,
and takes nothing or the payload's own op, an op of a room the
connection shows. -/
theorem recv_cases (fam : Family F) (cfg : Config) (ix : Index) (c : Conn) (b : ByteArray) (now : Nat)
    (h : Held F) :
    ((Conn.recv fam cfg ix c b now : HeldM F Step).run h).2 = h ∧
      ((Conn.recv fam cfg ix c b now : HeldM F Step).run h).1.drop = false ∧
      (((Conn.recv fam cfg ix c b now : HeldM F Step).run h).1.take = [] ∨
        ∃ o, Op.decode b = some o ∧ ((Conn.recv fam cfg ix c b now : HeldM F Step).run h).1.take = [o] ∧
          fam.shared o = true) := by
  refine ⟨recv_reads fam cfg ix c b now h, ?_⟩
  unfold Conn.recv
  cases hd : Op.decode b with
  | none => exact ⟨rfl, Or.inl rfl⟩
  | some o =>
    simp only [HeldM.pure_bind]
    cases hm : Msg.ofOp o with
    | some m =>
      cases m with
      | hello f =>
        simp only [HeldM.run_pure]
        split
        · exact ⟨Conn.start_drop .., Or.inl (Conn.start_take ..)⟩
        · exact ⟨rfl, Or.inl rfl⟩
      | rbsr r k cs =>
        simp only [HeldM.run_pure]
        unfold Conn.onRbsr
        split
        · exact ⟨rfl, Or.inl rfl⟩
        · split
          · exact ⟨rfl, Or.inl rfl⟩
          · dsimp only; split <;> exact ⟨rfl, Or.inl rfl⟩
      | hold r ids =>
        dsimp only
        split
        · -- an empty have asks for a round (`Conn.onAsk`): no take, no drop
          exact ⟨rfl, Or.inl rfl⟩
        try simp only [HeldM.run_bind, HeldM.run_pure]
        refine ⟨?_, Or.inl (onHold_take fam _ cfg r ids h)⟩
        unfold Conn.onHold
        split
        · rfl
        · split
          · rfl
          · simp only [HeldM.run_bind, HeldM.run_pure]
      | want ids =>
        simp only [HeldM.run_pure, Conn.onWant]
        split <;> exact ⟨rfl, Or.inl rfl⟩
    | none =>
      simp only
      split
      · exact ⟨rfl, Or.inl rfl⟩
      · rename_i hn
        simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hn
        refine ⟨rfl, Or.inr ⟨o, rfl, rfl, ?_⟩⟩
        have hs := hn.2
        simp only [Conn.shows, Bool.not_eq_false] at hs
        unfold Family.shared
        revert hs; cases fam.room o <;> simp

/-! ## A plain node's pieces -/

section
variable (S : Engine.Sync.Setup F) (s : Who)

/-- A node's session is open: it holds a connection under that id. -/
theorem conn_isSome (n : Node) (cid : Id) : (n.conn? cid).isSome = true ↔ cid ∈ n.conns.map Prod.fst := by
  simp only [Node.conn?, Option.isSome_map, List.find?_isSome, List.mem_map, decide_eq_true_eq]

/-- A write turn changes a node's index and fresh ids only. -/
theorem write_shape (x : Sync F (HeldM F)) (n : Node) (ops : List Op) (h : Held F) :
    ∃ ix fr, ((n.write x ops).run h).1.1 = { n with ix := ix, fresh := fr } := by
  simp only [Node.write, HeldM.run_bind]
  rw [forIn_yield ops _ (fun o acc => writeAbsent h.db acc o) h (fun y _ acc => by
    simp only [writeAbsent]; split
    · simp only [HeldM.run_bind, HeldM.run_getOp]
      by_cases hc : (h.db.ops y.id).isNone = true <;> simp [hc]
    · rfl)]
  split
  · exact ⟨n.ix, n.fresh, rfl⟩
  · simp only [HeldM.run_bind, HeldM.run_turn]
    generalize (List.foldl (fun b a => writeAbsent h.db b a) [] ops).reverse = news
    rw [forIn_yield news _ (fun a b => if ((turnH x.fam news h).db.ops a.id).isSome then
      (b.1.add x.fam a, a.id :: b.2) else b) _ (fun y _ b => by
        simp only [HeldM.run_bind, HeldM.run_getOp]
        by_cases hc : ((turnH x.fam news h).db.ops y.id).isSome = true <;> simp [hc])]
    exact ⟨_, _, rfl⟩

/-- A write turn keeps a node's sessions. -/
theorem write_conns (x : Sync F (HeldM F)) (n : Node) (ops : List Op) (h : Held F) :
    ((n.write x ops).run h).1.1.conns = n.conns := by
  obtain ⟨ix, fr, e⟩ := write_shape x n ops h; rw [e]

/-- A write turn keeps a node's addresses. -/
theorem write_addrs (x : Sync F (HeldM F)) (n : Node) (ops : List Op) (h : Held F) :
    ((n.write x ops).run h).1.1.addrs = n.addrs := by
  obtain ⟨ix, fr, e⟩ := write_shape x n ops h; rw [e]

/-- A write of ops all stored already changes nothing. -/
theorem write_held (x : Sync F (HeldM F)) (n : Node) (ops : List Op) (h : Held F)
    (hh : ∀ o ∈ ops, (h.db.ops o.id).isSome = true) : (n.write x ops).run h = ((n, []), h) := by
  simp only [Node.write, HeldM.run_bind]
  rw [forIn_yield ops _ (fun o acc => writeAbsent h.db acc o) h (fun y _ acc => by
    simp only [writeAbsent]; split
    · simp only [HeldM.run_bind, HeldM.run_getOp]
      by_cases hc : (h.db.ops y.id).isNone = true <;> simp [hc]
    · rfl)]
  have : ∀ (L acc : List Op), (∀ o ∈ L, (h.db.ops o.id).isSome = true) →
      L.foldl (fun b a => writeAbsent h.db b a) acc = acc := by
    intro L
    induction L with
    | nil => intro acc _; rfl
    | cons a t ih =>
      intro acc hL
      simp only [List.foldl_cons]
      have ha := hL a (List.mem_cons_self ..)
      have : writeAbsent h.db acc a = acc := by
        simp only [writeAbsent]; split
        · have : (h.db.ops a.id).isNone = false := by revert ha; cases h.db.ops a.id <;> simp
          simp [this]
        · rfl
      rw [this]; exact ih acc (fun o ho => hL o (List.mem_cons_of_mem _ ho))
  rw [this ops [] hh]
  rfl

/-- The fanout keeps a node's sessions: it steps each in place. -/
theorem fanout_conns (n : Node) (ids : List Id) (h : Held F) :
    (((n.fanout (S.sync s) ids).run h).1.1.conns.map Prod.fst) = n.conns.map Prod.fst := by
  simp only [Node.fanout, HeldM.run_bind]
  rw [forIn_yield n.conns _ (fun p st => fanoutStep S s ids h p st) h (fun p _ st => by
    simp only [HeldM.run_bind, refresh_run, HeldM.run_pure, sync_fam, sync_cfg]
    rw [filedGive_quiet _ _ _ _ _ rfl, filed_reads _ _ _ _ h]; rfl)]
  simp only [recordGiven_run, HeldM.run_pure]
  have : ∀ (L : List (Id × Conn)) st, ((L.foldl (fun b a => fanoutStep S s ids h a b) st).1.map Prod.fst) =
      (L.map Prod.fst).reverse ++ st.1.map Prod.fst := by
    intro L
    induction L with
    | nil => intro st; simp
    | cons p t ih => intro st; rw [List.foldl_cons, ih]; simp [fanoutStep]
  rw [List.map_reverse, this]; simp

/-- Storing keeps a node's sessions. -/
theorem store_conns (n : Node) (ops : List Op) (mine : Bool) (h : Held F) :
    (((n.store (S.sync s) ops mine).run h).1.1.conns.map Prod.fst) = n.conns.map Prod.fst := by
  rw [store_run]
  dsimp only
  split
  · unfold Node.put; rw [write_conns]
  · rw [fanout_conns]; unfold Node.put; rw [write_conns]

/-- A put of one shared op the store holds already, or of one over the
intake cap, changes nothing. -/
theorem put_held (x : Sync F (HeldM F)) (n : Node) (o : Op) (h : Held F) (hsh : x.fam.shared o = true)
    (hh : (h.db.ops o.id).isSome = true ∨ o.capped = false) : (n.put x [o] false).run h = ((n, []), h) := by
  unfold Node.put
  rcases hh with hh | hcp
  · cases hcp : o.capped
    · simp only [intake, Bool.false_eq_true, ↓reduceIte, List.filter_cons, hsh, hcp, List.filter_nil]
      exact write_nil x n h
    · simp only [intake, Bool.false_eq_true, ↓reduceIte, List.filter_cons, hsh, hcp, List.filter_nil]
      exact write_held x n [o] h (fun o' ho' => by rw [List.mem_singleton.1 ho']; exact hh)
  · simp only [intake, Bool.false_eq_true, ↓reduceIte, List.filter_cons, hsh, hcp, List.filter_nil]
    exact write_nil x n h

/-- **What applying a payload's step does:** the session stays open, and
the store is as it was, or gains exactly the step's op, which it
lacked. -/
theorem apply_store (n : Node) (cid : Id) (st : Step) (now : Nat) (h : Held F) (hd : st.drop = false)
    (ht : st.take = [] ∨ ∃ o, st.take = [o] ∧ S.fam.shared o = true) :
    ((((n.apply (S.sync s) cid st now).run h).1.1.conns.map Prod.fst) =
        (n.conns.map fun p => if p.1 = cid then (cid, st.conn) else p).map Prod.fst) ∧
      (((n.apply (S.sync s) cid st now).run h).2 = h ∨
        ∃ o, st.take = [o] ∧ h.db.ops o.id = none ∧ ((n.apply (S.sync s) cid st now).run h).2 = turnH S.fam [o] h) := by
  have hfold : ∀ (L : List Op), L.foldl (fun b (_ : Op) => b) ([] : List Op) = [] := by
    intro L; induction L with
    | nil => rfl
    | cons _ _ ih => exact ih
  unfold Node.apply
  simp only [hd, Bool.false_eq_true, ↓reduceIte, HeldM.run_bind, recordGiven_run]
  rw [forIn_yield _ _ (fun _ acc => acc) _ (fun o _ acc => by
    simp only [sync_recv, HeldM.run_bind, HeldM.run_pure, List.append_nil]), hfold, store_nil]
  simp only [HeldM.run_pure]
  rcases ht with ht | ⟨o, ht, hsh⟩
  · rw [ht, store_nil]; exact ⟨rfl, Or.inl rfl⟩
  · rw [ht]
    refine ⟨by rw [store_conns], ?_⟩
    by_cases hn : h.db.ops o.id = none
    · cases hcp : o.capped
      · left
        rw [store_run, put_held _ _ o h hsh (Or.inr hcp)]
        rfl
      · exact Or.inr ⟨o, rfl, hn, store_one S s _ o false h hn (by simp [intake, hsh, hcp])⟩
    · left
      rw [store_run, put_held _ _ o h hsh (Or.inl (by revert hn; cases h.db.ops o.id <;> simp))]
      rfl

/-- Applying a step that takes one shared op the store holds already
changes nothing. -/
theorem apply_one_held (n : Node) (cid : Id) (st : Step) (now : Nat) (h : Held F) (o : Op)
    (hd : st.drop = false) (ht : st.take = [o]) (hsh : S.fam.shared o = true) (hn : ¬ h.db.ops o.id = none) :
    ((n.apply (S.sync s) cid st now).run h).2 = h := by
  rcases (apply_store S s n cid st now h hd (Or.inr ⟨o, ht, hsh⟩)).2 with e | ⟨o', ho', hn', _⟩
  · exact e
  · rw [ht] at ho'; cases List.cons.inj ho' |>.1; exact absurd hn' hn

/-- One payload of a frame at a node whose session is open: the session
stays open, and the store is as it was or gains the payload's own op. -/
theorem payload_run (n : Node) (cid : Id) (c : Conn) (b : ByteArray) (now : Nat) (h : Held F)
    (hc : n.conn? cid = some c) :
    let st := ((Conn.recv S.fam S.cfg n.ix { c.setRooms (S.rooms s cid) with notices := [] } b now :
      HeldM F Step).run h).1
    (((n.apply (S.sync s) cid st now).run h).1.1.conn? cid).isSome = true ∧
      (((n.apply (S.sync s) cid st now).run h).2 = h ∨
        ∃ o, Op.decode b = some o ∧ h.db.ops o.id = none ∧ ((n.apply (S.sync s) cid st now).run h).2 = turnH S.fam [o] h) := by
  dsimp only
  obtain ⟨-, hd, ht⟩ := recv_cases S.fam S.cfg n.ix { c.setRooms (S.rooms s cid) with notices := [] } b now h
  obtain ⟨hk, hs⟩ := apply_store S s n cid _ now h hd (ht.imp id fun ⟨o, _, e, hsh⟩ => ⟨o, e, hsh⟩)
  refine ⟨?_, ?_⟩
  · rw [conn_isSome, hk, List.map_map]
    have hc' : cid ∈ n.conns.map Prod.fst := (conn_isSome n cid).1 (by rw [hc]; rfl)
    obtain ⟨p, hp, e⟩ := List.mem_map.1 hc'
    exact List.mem_map.2 ⟨p, hp, by simp only [Function.comp_apply]; split <;> simp_all⟩
  · rcases hs with hs | ⟨o, ho, hn, e⟩
    · exact Or.inl hs
    · rcases ht with ht | ⟨o', hd', ht', _⟩
      · rw [ht] at ho; cases ho
      · rw [ht'] at ho; obtain rfl := (List.cons.inj ho).1
        exact Or.inr ⟨_, hd', hn, e⟩

/-- **A payload that is an op of a room the session shows is taken:**
after it the store holds that op, or held an op under its id already and
is unchanged. -/
theorem payload_takes (n : Node) (cid : Id) (c : Conn) (o : Op) (r : Id) (now : Nat) (h : Held F)
    (hw : isWire o.kind = false) (hr : S.fam.room o = some r) (hs : r ∈ S.rooms s cid)
    (hcp : o.capped = true) :
    let st := ((Conn.recv S.fam S.cfg n.ix { c.setRooms (S.rooms s cid) with notices := [] } o.bytes now :
      HeldM F Step).run h).1
    ((n.apply (S.sync s) cid st now).run h).2.db.ops o.id = some o ∨
      ((h.db.ops o.id).isSome = true ∧ ((n.apply (S.sync s) cid st now).run h).2 = h) := by
  dsimp only
  have hsh : ({ c.setRooms (S.rooms s cid) with notices := [] } : Conn).shows S.fam o = true := by
    simp [Conn.shows, Conn.setRooms, hr, has_of_mem hs]
  rw [recv_data _ _ _ _ _ _ _ hw hsh]
  have hshared : S.fam.shared o = true := by simp [Family.shared, hr]
  by_cases hn : h.db.ops o.id = none
  · left
    rw [apply_takes S s _ _ _ _ o h rfl rfl hn hshared hcp, turnH_one _ _ _ hn]
  · right
    have hh : (h.db.ops o.id).isSome = true := by revert hn; cases h.db.ops o.id <;> simp
    exact ⟨hh, apply_one_held S s n cid _ now h o rfl rfl hshared hn⟩

/-! ## H3: an op in a frame is taken -/

/-- **H3 at a session's frame.** A node whose session cid is open takes
a frame on it whose payloads include op o, a data op of a room the
session shows. Then the node holds o after the frame, wherever o sits in
the frame and whatever else the frame carries, provided no other op of
the frame or the store bears o's id (no hash collision). -/
theorem onSealed_takes (n : Node) (src : ByteArray) (cid : Id) (inner : List ByteArray) (o : Op) (r : Id)
    (now : Nat) (h : Held F) (hc : (n.conn? cid).isSome = true) (ho : o.bytes ∈ inner)
    (hw : isWire o.kind = false) (hr : S.fam.room o = some r) (hs : r ∈ S.rooms s cid)
    (hcp : o.capped = true)
    (hpre : ∀ o', h.db.ops o.id = some o' → o' = o)
    (hfr : ∀ b ∈ inner, ∀ o', Op.decode b = some o' → o'.id = o.id → o' = o) :
    ((n.onSealed (S.sync s) src (some (cid, Codec.encode inner)) now).run h).2.db.ops o.id = some o := by
  obtain ⟨c0, hc0⟩ := Option.isSome_iff_exists.1 hc
  unfold Node.onSealed
  simp only [hc0, Codec.decode_encode, HeldM.run_bind]
  generalize hR : HeldM.run (forIn (m := HeldM F) (_ : List ByteArray)
    ((n.setAddr cid src, {}) : Node × Acts) _) h = R
  have key : R.2.db.ops o.id = some o := by
    rw [← hR]
    refine forIn_after _ (fun h' (st : Node × Acts) => (st.1.conn? cid).isSome = true ∧
        ∀ o', h'.db.ops o.id = some o' → o' = o) (fun h' _ => h'.db.ops o.id = some o) o.bytes
      inner ?_ ?_ ?_ ?_ ho _ h ⟨hc, hpre⟩
    · intro a _ st h'
      split
      · simp only [HeldM.run_bind, HeldM.run_pure]; exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
    · intro a ha st h' ⟨hc', hu⟩
      split
      · rename_i c hcs
        simp only [HeldM.run_bind, refresh_run, sync_fam, sync_cfg, HeldM.run_pure, ForInStep.value]
        rw [recv_reads]
        obtain ⟨k1, k2⟩ := payload_run S s st.1 cid c a now h' hcs
        refine ⟨k1, ?_⟩
        rcases k2 with e | ⟨o', hd, hn, e⟩
        · rw [e]; exact hu
        · rw [e, turnH_one_ops _ _ _ hn]
          intro o'' ho''
          split at ho''
          · rename_i hid
            cases ho''
            exact hfr a ha o' hd hid.symm
          · exact hu o'' ho''
      · exact ⟨hc', hu⟩
    · intro a _ st h' ⟨_, _⟩ hq
      split
      · rename_i c hcs
        simp only [HeldM.run_bind, refresh_run, sync_fam, sync_cfg, HeldM.run_pure, ForInStep.value]
        rw [recv_reads]
        rcases (payload_run S s st.1 cid c a now h' hcs).2 with e | ⟨o', _, hn, e⟩
        · rw [e]; exact hq
        · rw [e]; exact turnH_some _ _ _ hq
      · exact hq
    · intro st h' ⟨hc', hu⟩
      split
      · rename_i c hcs
        simp only [HeldM.run_bind, refresh_run, sync_fam, sync_cfg, HeldM.run_pure, ForInStep.value]
        rw [recv_reads]
        rcases payload_takes S s st.1 cid c o r now h' hw hr hs hcp with e | ⟨hh, e⟩
        · exact e
        · rw [e]
          obtain ⟨o', ho'⟩ := Option.isSome_iff_exists.1 hh
          rw [ho', hu o' ho']
      · rename_i hcn
        obtain ⟨c, hcc⟩ := Option.isSome_iff_exists.1 hc'
        exact (hcn c hcc).elim
  have hS := serveOwed_reads S s R.1.1 cid now R.2
  generalize HeldM.run (Node.serveOwed (S.sync s) R.1.1 cid now) R.2 = B at hS ⊢
  rw [finish_reads S s B.1.1 _ now B.2, hS]
  exact key

/-- **H3 at a frame in the clear**: `onSealed_takes` for the frame a
plain node receives. -/
theorem onFrame_takes (n : Node) (src : ByteArray) (cid : Id) (inner : List ByteArray) (o : Op) (r : Id)
    (now : Nat) (h : Held F) (hc : (n.conn? cid).isSome = true) (ho : o.bytes ∈ inner)
    (hw : isWire o.kind = false) (hr : S.fam.room o = some r) (hs : r ∈ S.rooms s cid)
    (hcp : o.capped = true)
    (hpre : ∀ o', h.db.ops o.id = some o' → o' = o)
    (hfr : ∀ b ∈ inner, ∀ o', Op.decode b = some o' → o'.id = o.id → o' = o) :
    ((n.onFrame (S.sync s) src (plainFrame cid inner) now).run h).2.db.ops o.id = some o := by
  have e : n.onFrame (S.sync s) src (plainFrame cid inner) now =
      n.onSealed (S.sync s) src (some (cid, Codec.encode inner)) now := by
    simp only [Node.onFrame, plainFrame_head, plainFrame_body, sync_openFrame, plainOpen, Codec.decode_encode,
      HeldM.pure_bind]
  rw [e]
  exact onSealed_takes S s n src cid inner o r now h hc ho hw hr hs hcp hpre hfr

end

end Engine.World
