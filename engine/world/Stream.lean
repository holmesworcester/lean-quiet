/-
The stream offers every op a node stores, proven of the running code
(`stream_offers_stored_proof`, so `offered_proof`): an op of room r that a
step stores at node i for the first time, whether the node's own write or
relayed from a third peer, on a session that shows r throughout, is
offered at once in a frame to that session's address, unless i knew the
peer holds it, or the frame the step hands i on that session names it.

- At a connection: the stream's loop as a fold (`filed_run`), offering
  each new id of a shown room not known or offered (`filed_offers'`),
  under its room (`holds_cover`).
- At a store: each op it newly stores, on each session (`store_offers`):
  a write reports what it stores (`write_reports`), a fanout runs the
  stream on every session (`fanout_offers'`), and a connection never
  counts as offered an op its node did not hold (`NodeOk.offered`).
- Over a frame: since sync-harden, what a session knows its peer holds
  is a bounded hint (finding 9). After a payload it knows only what it
  knew, what the payload names, or what the step sends
  (`recv_known_sub`), and `KnownBy` carries that through the frame; the
  first payload that stores the op offers it (`frameStep_offers`,
  `frame_offers`).
- At the world: only a session frame or a local write stores an op of a
  room (`onFrame_new`, `write_from`; the clock and the harness store
  nothing, `onTick_store`, `connect_store`); every session has an
  address (`reach_addr`); and a packet an entry point sends is new, by
  its serial (`reach_serial`, `enter_names`).
-/
import engine.world.Offer
namespace Engine.World
open Engine Engine.Sync
variable {F : Type}

attribute [local instance] byteArray_lawfulBEq

/-! ## The stream's loop -/

theorem foldl_ins_mem {y : Id} : ∀ (L acc : List Id), (y ∈ acc ∨ y ∈ L) → y ∈ L.foldl Engine.ins acc := by
  intro L
  induction L with
  | nil => intro acc h; rcases h with h | h; exact h; cases h
  | cons x L ih =>
    intro acc h
    simp only [List.foldl_cons]
    apply ih
    rcases h with h | h
    · exact Or.inl ((Engine.mem_ins _ _ _).2 (Or.inl h))
    · rcases List.mem_cons.1 h with rfl | h
      · exact Or.inl ((Engine.mem_ins _ _ _).2 (Or.inr rfl))
      · exact Or.inr h

/-- **Every offer goes out in a have of its room.** -/
theorem holds_cover (cfg : Config) (offer : List (Id × Id)) (hmax : 0 < cfg.maxIds) {r x : Id}
    (hx : (r, x) ∈ offer) : ∃ L, x ∈ L ∧ (Msg.hold r L).op ∈ holdsOf cfg offer := by
  have hr : r ∈ (offer.map (·.1)).foldl Engine.ins [] :=
    foldl_ins_mem _ _ (Or.inr (List.mem_map.2 ⟨(r, x), hx, rfl⟩))
  obtain ⟨l, hxl, -, hl⟩ := chunks_cover cfg (offer.filterMap fun p => if p.1 = r then some p.2 else none)
    (.hold r) hmax (x := x) (List.mem_filterMap.2 ⟨(r, x), hx, by simp⟩)
  exact ⟨l, hxl, List.mem_flatMap.2 ⟨r, hr, hl⟩⟩

/-- One turn of the stream's loop (`Conn.filed`) on a store. -/
def fileStep' (fam : Family F) (db : DB F) (st : List (Id × Id) × Conn) (i : Id) : List (Id × Id) × Conn :=
  if (!st.2.known.contains i && !st.2.offered.contains i) = true then
    match db.ops i with
    | some o => if st.2.shows fam o = true then
        (((fam.room o).getD .empty, i) :: st.1, { st.2 with offered := st.2.offered.insert i })
      else (st.1, st.2)
    | none => (st.1, st.2)
  else (st.1, st.2)

theorem filed_run (fam : Family F) (cfg : Config) (c : Conn) (ids : List Id) (h : Held F) :
    (c.filed fam cfg ids : HeldM F Step).run h =
      (Conn.finish (Step.mk (ids.foldl (fileStep' fam h.db) ([], c)).2
        (holdsOf cfg (ids.foldl (fileStep' fam h.db) ([], c)).1.reverse) [] [] false), h) := by
  unfold Conn.filed
  rw [HeldM.run_bind, forIn_yield _ _ (fileStep' fam h.db) h (fun i st => by
    obtain ⟨off, c'⟩ := st
    unfold fileStep'
    dsimp only
    split
    · simp only [HeldM.run_bind, HeldM.run_getOp]
      cases h.db.ops i with
      | none => rfl
      | some o => dsimp only; split <;> rfl
    · rfl)]
  rfl

theorem fileStep_known (fam : Family F) (db : DB F) : ∀ (l : List Id) st, (l.foldl (fileStep' fam db) st).2.known = st.2.known := by
  intro l
  induction l with
  | nil => intro st; rfl
  | cons a t ih =>
    intro st
    rw [List.foldl_cons, ih]
    unfold fileStep'
    split
    · split
      · split <;> rfl
      · rfl
    · rfl

theorem fileStep_grows (fam : Family F) (db : DB F) : ∀ (l : List Id) st, ∀ p ∈ st.1, p ∈ (l.foldl (fileStep' fam db) st).1 := by
  intro l
  induction l with
  | nil => intro st p h; exact h
  | cons a t ih =>
    intro st p hp
    rw [List.foldl_cons]
    apply ih
    unfold fileStep'
    split
    · split
      · split
        · exact List.mem_cons_of_mem _ hp
        · exact hp
      · exact hp
    · exact hp

/-- **The stream offers each id it is given that its peer may see, is not
known to hold and was not offered**, under the op's room. -/
theorem fileStep_offers (fam : Family F) (db : DB F) (x : Id) (o : Op) (r : Id) (ho : db.ops x = some o)
    (hr : fam.room o = some r) : ∀ (l : List Id) st, x ∈ l → x ∉ st.2.offered → x ∉ st.2.known →
      st.2.shows fam o = true → (r, x) ∈ (l.foldl (fileStep' fam db) st).1 := by
  intro l
  induction l with
  | nil => intro st h; cases h
  | cons a t ih =>
    intro st hx hof hkn hsh
    rw [List.foldl_cons]
    by_cases e : a = x
    · subst e
      apply fileStep_grows
      have hk : st.2.known.contains a = false := Bool.eq_false_iff.2 fun e => hkn (Std.HashSet.mem_iff_contains.2 e)
      have ho' : st.2.offered.contains a = false := Bool.eq_false_iff.2 fun e => hof (Std.HashSet.mem_iff_contains.2 e)
      simp [fileStep', hk, ho', ho, hsh, hr]
    · rcases List.mem_cons.1 hx with h | h
      · exact absurd h.symm e
      · apply ih _ h
        · unfold fileStep'
          split
          · split
            · split
              · intro hm
                rw [Std.HashSet.mem_insert] at hm
                rcases hm with e2 | hm
                · exact e (eq_of_beq e2)
                · exact hof hm
              · exact hof
            · exact hof
          · exact hof
        · rw [show (fileStep' fam db st a).2.known = st.2.known from fileStep_known fam db [a] st]; exact hkn
        · unfold fileStep'
          split
          · split
            · split
              · exact hsh
              · exact hsh
            · exact hsh
          · exact hsh

/-- **The stream, at a connection: a newly stored op of a shown room goes
out in a have of its room**, unless the peer is known to hold it. -/
theorem filed_offers' (fam : Family F) (cfg : Config) (c : Conn) (ids : List Id) (h : Held F) (x : Id) (o : Op)
    (r : Id) (hx : x ∈ ids) (ho : h.db.ops x = some o) (hr : fam.room o = some r) (hsh : c.shows fam o = true)
    (hof : x ∉ c.offered) (hmax : 0 < cfg.maxIds) :
    x ∈ c.known ∨ ∃ L, x ∈ L ∧ (Msg.hold r L).op ∈ ((c.filed fam cfg ids : HeldM F Step).run h).1.send := by
  by_cases hk : x ∈ c.known
  · exact Or.inl hk
  · right
    rw [filed_run, Conn.finish_send]
    exact holds_cover cfg _ hmax (List.mem_reverse.2 (fileStep_offers fam h.db x o r ho hr ids ([], c) hx hof hk hsh))

/-! ## Through a write and a fanout -/

/-- The first step of a fold at which a property starts to hold. -/
theorem fold_first {α β : Type} (f : α → β → α) (P : α → Prop) : ∀ (l : List β) (st : α), ¬ P st →
    P (l.foldl f st) → ∃ pre b post, l = pre ++ b :: post ∧ ¬ P (pre.foldl f st) ∧ P (f (pre.foldl f st) b) := by
  intro l
  induction l with
  | nil => intro st h1 h2; exact absurd h2 h1
  | cons a t ih =>
    intro st h1 h2
    by_cases ha : P (f st a)
    · exact ⟨[], a, t, rfl, h1, ha⟩
    · obtain ⟨pre, b, post, e, h3, h4⟩ := ih (f st a) ha h2
      exact ⟨a :: pre, b, post, by rw [e]; rfl, h3, h4⟩

theorem addStep_ids (fam : Family F) (db : DB F) : ∀ (l : List Op) (st : Index × List Id) (o : Op),
    o ∈ l → (db.ops o.id).isSome = true → o.id ∈ (l.foldl (addStep fam db) st).2 := by
  have keep : ∀ (l : List Op) (st : Index × List Id) y, y ∈ st.2 → y ∈ (l.foldl (addStep fam db) st).2 := by
    intro l
    induction l with
    | nil => intro st y h; exact h
    | cons a t ih =>
      intro st y h
      apply ih
      unfold addStep; split
      · exact List.mem_cons_of_mem _ h
      · exact h
  intro l
  induction l with
  | nil => intro st o h; cases h
  | cons a t ih =>
    intro st o ho hs
    rcases List.mem_cons.1 ho with rfl | ho
    · rw [List.foldl_cons]; apply keep; unfold addStep; rw [if_pos hs]; exact List.mem_cons_self ..
    · exact ih _ o ho hs

section
variable (fam : Family F) (cfg : Config) (rms : Held F → Id → List Id)

/-- **A write reports each op it newly stores.** -/
theorem write_reports (n : Node) (ops : List Op) (h : Held F) (x : Id) (hn : h.db.ops x = none)
    (hs : (((n.write (psync fam cfg rms) ops).run h).2.db.ops x).isSome = true) :
    x ∈ ((n.write (psync fam cfg rms) ops).run h).1.2 := by
  rw [write_run] at hs ⊢
  simp only [psync_fam] at hs ⊢
  split at hs
  · rw [hn] at hs; cases hs
  · rename_i he
    rw [if_neg he]
    obtain ⟨o', ho'⟩ := Option.isSome_iff_exists.1 hs
    simp only [turnH, drainS_ops] at ho'
    rcases ingest_from _ h.db x o' ho' with h1 | ⟨hm, e⟩
    · rw [hn] at h1; cases h1
    · rw [List.mem_reverse, ← e]
      apply addStep_ids _ _ _ _ o' hm
      rw [e]; exact hs

theorem fanStep_out (h : Held F) (ids : List Id) : ∀ (l : List (Id × Conn)) st, ∀ p ∈ l, ∀ y ∈ (sends p.1
    ((Conn.filed fam cfg (p.2.setRooms (rms h p.1)) ids : HeldM F Step).run h).1.send).send,
    y ∈ (l.foldl (fanStep fam cfg rms h ids) st).2.1.send := by
  have keep : ∀ (l : List (Id × Conn)) st y, y ∈ st.2.1.send → y ∈ (l.foldl (fanStep fam cfg rms h ids) st).2.1.send := by
    intro l
    induction l with
    | nil => intro st y h; exact h
    | cons a t ih => intro st y hy; apply ih; exact List.mem_append_left _ hy
  intro l
  induction l with
  | nil => intro st p h; cases h
  | cons a t ih =>
    intro st p hp y hy
    rcases List.mem_cons.1 hp with rfl | hp
    · rw [List.foldl_cons]; apply keep; exact List.mem_append_right _ hy
    · exact ih _ p hp y hy

/-- **A fanout offers on each session** what that session's stream step
offers. -/
theorem fanout_offers' (n : Node) (ids : List Id) (h : Held F) (cid : Id) (c : Conn) (hc : n.conn? cid = some c)
    (y : ByteArray) (hy : y ∈ ((Conn.filed fam cfg (c.setRooms (rms h cid)) ids : HeldM F Step).run h).1.send.map Op.bytes) :
    (Route.conn cid, y) ∈ ((n.fanout (psync fam cfg rms) ids).run h).1.2.send := by
  rw [fanout_run]
  apply fanStep_out fam cfg rms h ids _ _ (cid, c) (conn_mem hc)
  simp only [sends, List.mem_map] at hy ⊢
  obtain ⟨o, ho, rfl⟩ := hy
  exact ⟨o, ho, rfl⟩

end

section
variable (fam : Family F) (cfg : Config) (rms : Held F → Id → List Id)

/-- **The stream, at a node: storing an op offers it at once on each
session that shows its room**, unless the peer is known to hold it. -/
theorem store_offers (n : Node) (ops : List Op) (mine : Bool) (h : Held F) (ok : NodeOk fam n h) (cid : Id)
    (c : Conn) (hc : n.conn? cid = some c) (x : Id) (o : Op) (r : Id) (hn : h.db.ops x = none)
    (hs : ((n.store (psync fam cfg rms) ops mine).run h).2.db.ops x = some o) (hor : fam.room o = some r)
    (hrooms : ∀ h', Kept h h' → Kept h' ((n.store (psync fam cfg rms) ops mine).run h).2 → r ∈ rms h' cid)
    (hmax : 0 < cfg.maxIds) :
    x ∈ c.known ∨ ∃ L, x ∈ L ∧
      (Route.conn cid, (Msg.hold r L).op.bytes) ∈ ((n.store (psync fam cfg rms) ops mine).run h).1.2.send := by
  rw [store_run] at hs hrooms ⊢
  simp only [Node.put, psync_fam] at hs hrooms ⊢
  have wn := write_node fam cfg rms n (intake fam mine ops) h
  have we := write_grows fam cfg rms n (intake fam mine ops) h
  have hrep0 := write_reports fam cfg rms n (intake fam mine ops) h x hn
  by_cases he : ((n.write (psync fam cfg rms) (intake fam mine ops)).run h).1.2.isEmpty = true
  · exfalso
    simp only [he, ↓reduceIte] at hs
    have := hrep0 (by rw [hs]; rfl)
    rw [List.isEmpty_iff] at he; rw [he] at this; cases this
  · simp only [he, ↓reduceIte, Bool.false_eq_true] at hs hrooms ⊢
    rw [(fanout_node fam cfg rms _ _ _).1] at hs hrooms
    have hrep := hrep0 (by rw [hs]; rfl)
    have hcW : ((n.write (psync fam cfg rms) (intake fam mine ops)).run h).1.1.conn? cid = some c := by
      unfold Node.conn?; rw [wn.1]; exact hc
    have hr : r ∈ rms ((n.write (psync fam cfg rms) (intake fam mine ops)).run h).2 cid :=
      hrooms _ (fun y p hp => we.1 y p hp) (fun _ _ e => e)
    have hof : x ∉ (c.setRooms (rms ((n.write (psync fam cfg rms) (intake fam mine ops)).run h).2 cid)).offered := by
      intro hx
      have := ok.offered _ (conn_mem hc) x hx
      unfold Named at this; rw [hn] at this; cases this
    have hsh : (c.setRooms (rms ((n.write (psync fam cfg rms) (intake fam mine ops)).run h).2 cid)).shows fam o = true := by
      simp [Conn.shows, Conn.setRooms, hor, has_of_mem hr]
    rcases filed_offers' fam cfg _ _ _ x o r hrep hs hor hsh hof hmax with hk | ⟨L, hxL, hL⟩
    · exact Or.inl hk
    · right
      exact ⟨L, hxL, fanout_offers' fam cfg rms _ _ _ cid c hcW _ (List.mem_map.2 ⟨_, hL, rfl⟩)⟩

end

/-! ## What a store keeps -/

theorem finish_known (st : Step) : (Conn.finish st).conn.known = st.conn.known := by
  unfold Conn.finish Conn.report
  by_cases h : st.conn.asked.isEmpty = true <;> simp [h]

theorem filed_known (fam : Family F) (cfg : Config) (c : Conn) (ids : List Id) (h : Held F) :
    ((c.filed fam cfg ids : HeldM F Step).run h).1.conn.known = c.known := by
  rw [filed_run, finish_known]; exact fileStep_known fam h.db ids ([], c)

theorem setConn_eq (n : Node) (cid : Id) (c' : Conn) :
    setConn n cid c' = { n with conns := n.conns.map fun p => (p.1, if p.1 = cid then c' else p.2) } := by
  unfold setConn
  congr 2
  funext p
  split <;> simp_all

theorem setConn_conn (n : Node) (cid : Id) (c' : Conn) (d : Id) (c : Conn) (hd : n.conn? d = some c) :
    (setConn n cid c').conn? d = some (if d = cid then c' else c) := by
  rw [setConn_eq]
  exact conn_map n d (fun p => if p.1 = cid then c' else p.2) c hd

section
variable (fam : Family F) (cfg : Config) (rms : Held F → Id → List Id)

theorem setConn_ok (n : Node) (cid : Id) (c' : Conn) (h : Held F) (ok : NodeOk fam n h) (hs : SnapsIn c' h)
    (ho : ∀ x ∈ c'.offered, Named h x) : NodeOk fam (setConn n cid c') h := by
  refine ⟨⟨ok.sub.1, ?_⟩, ok.managed, ok.ids, ok.log, ok.wf, ok.exact, ok.logx, ok.stored, ?_⟩
  · intro p hp
    simp only [setConn, List.mem_map] at hp
    obtain ⟨q, hq, e⟩ := hp
    split at e
    · rw [← e]; exact hs
    · rw [← e]; exact ok.sub.2 q hq
  · intro p hp
    simp only [setConn, List.mem_map] at hp
    obtain ⟨q, hq, e⟩ := hp
    split at e
    · rw [← e]; exact ho
    · rw [← e]; exact ok.offered q hq

/-- A store keeps every session, and what each knows its peer holds. -/
theorem store_known (n : Node) (ops : List Op) (mine : Bool) (h : Held F) (d : Id) (c : Conn)
    (hd : n.conn? d = some c) :
    ∃ c', ((n.store (psync fam cfg rms) ops mine).run h).1.1.conn? d = some c' ∧ c'.known = c.known := by
  rw [store_run]
  simp only [Node.put, psync_fam]
  have wn := write_node fam cfg rms n (intake fam mine ops) h
  have hw : ((n.write (psync fam cfg rms) (intake fam mine ops)).run h).1.1.conn? d = some c := by
    unfold Node.conn?; rw [wn.1]; exact hd
  by_cases he : ((n.write (psync fam cfg rms) (intake fam mine ops)).run h).1.2.isEmpty = true
  · simp only [he, ↓reduceIte]; exact ⟨c, hw, rfl⟩
  · simp only [he, ↓reduceIte, Bool.false_eq_true]
    obtain ⟨-, -, -, -, e5⟩ := fanout_node fam cfg rms ((n.write (psync fam cfg rms) (intake fam mine ops)).run h).1.1
      ((n.write (psync fam cfg rms) (intake fam mine ops)).run h).1.2
      ((n.write (psync fam cfg rms) (intake fam mine ops)).run h).2
    have := conn_map _ d (fun p => ((Conn.filed fam cfg (p.2.setRooms (rms ((n.write (psync fam cfg rms)
      (intake fam mine ops)).run h).2 p.1)) ((n.write (psync fam cfg rms) (intake fam mine ops)).run h).1.2 :
        HeldM F Step).run ((n.write (psync fam cfg rms) (intake fam mine ops)).run h).2).1.conn) c hw
    refine ⟨_, by unfold Node.conn? at this ⊢; rw [e5]; exact this, ?_⟩
    rw [filed_known]; rfl

end


/-! ## What a session knows, within a frame: what the frame names, or what it sent -/

theorem remember_mem {cap : Nat} {k : Std.HashSet Id} {i y : Id} (h : y ∈ remember cap k i) : y ∈ k ∨ y = i := by
  unfold remember at h
  split at h
  · simp at h
  · dsimp only at h
    split at h
    · rcases Std.HashSet.mem_insert.1 h with e | h
      · exact Or.inr (eq_of_beq e).symm
      · exact Or.inl h
    · rcases Std.HashSet.mem_insert.1 h with e | h
      · exact Or.inr (eq_of_beq e).symm
      · simp at h

theorem foldl_remember_mem {cap : Nat} {y : Id} : ∀ (l : List Id) (k : Std.HashSet Id),
    y ∈ l.foldl (remember cap) k → y ∈ k ∨ y ∈ l := by
  intro l
  induction l with
  | nil => intro k h; exact Or.inl h
  | cons a t ih =>
    intro k h
    rcases ih _ h with h | h
    · rcases remember_mem h with h | rfl
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_self ..)
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem foldl_remember_ids {cap : Nat} {y : Id} : ∀ (l : List Op) (k : Std.HashSet Id),
    y ∈ l.foldl (fun (k : Std.HashSet Id) (o : Op) => remember cap k o.id) k → y ∈ k ∨ ∃ o ∈ l, o.id = y := by
  intro l
  induction l with
  | nil => intro k h; exact Or.inl h
  | cons a t ih =>
    intro k h
    rcases ih _ h with h | ⟨o, ho, e⟩
    · rcases remember_mem h with h | rfl
      · exact Or.inl h
      · exact Or.inr ⟨a, List.mem_cons_self .., rfl⟩
    · exact Or.inr ⟨o, List.mem_cons_of_mem _ ho, e⟩

section
variable (fam : Family F) (cfg : Config)

/-- **What a connection knows after a payload**: it knew it, or the
payload names it (the op itself, or a have of it), or the step sends it. -/
theorem recv_known_sub (ix : Index) (c : Conn) (b : ByteArray) (now : Nat) (h : Held F) (y : Id)
    (hy : y ∈ ((Conn.recv fam cfg ix c b now : HeldM F Step).run h).1.conn.known) :
    y ∈ c.known ∨ Names b y ∨ ∃ o ∈ ((Conn.recv fam cfg ix c b now : HeldM F Step).run h).1.send, o.id = y := by
  unfold Conn.recv at hy ⊢
  cases hd : Op.decode b with
  | none => simp only [hd, HeldM.run_pure] at hy; exact Or.inl hy
  | some o =>
    simp only [hd] at hy ⊢
    cases hm : Msg.ofOp o with
    | none =>
      simp only [hm] at hy ⊢
      split at hy
      · exact Or.inl hy
      · simp only [HeldM.run_pure, finish_known] at hy
        rcases remember_mem (Step.limit_known cfg _ hy) with hy | rfl
        · exact Or.inl hy
        · exact Or.inr (Or.inl ⟨o, hd, Or.inl rfl⟩)
    | some m =>
      simp only [hm] at hy ⊢
      cases m with
      | hello f =>
        simp only [HeldM.run_pure, finish_known] at hy
        left
        split at hy
        · unfold Conn.start at hy; split at hy <;> exact hy
        · exact hy
      | rbsr r k cs =>
        simp only [HeldM.run_pure, finish_known] at hy
        left
        unfold Conn.onRbsr at hy
        split at hy
        · exact hy
        · dsimp only at hy
          split at hy
          · exact hy
          · have hy := Step.limit_known cfg _ hy
            split at hy <;> exact hy
      | hold r ids =>
        simp only [HeldM.run_bind, HeldM.run_pure, finish_known] at hy
        change y ∈ ((Conn.onHold fam cfg _ r ids : HeldM F Step) h).1.conn.known at hy
        rw [onHold_apply] at hy
        split at hy
        · exact Or.inl hy
        · split at hy
          · exact Or.inl hy
          · rcases foldl_remember_mem _ _ (Step.limit_known cfg _ hy) with hy | hy
            · exact Or.inl hy
            · exact Or.inr (Or.inl ⟨o, hd, Or.inr ⟨r, ids, hm, (List.mem_filter.1 hy).1⟩⟩)
      | want ids =>
        simp only [HeldM.run_bind, HeldM.run_pure, finish_known, Conn.finish_send] at hy ⊢
        unfold Conn.onWant at hy ⊢
        split at hy
        · exact Or.inl hy
        · rename_i hl
          simp only [hl, ↓reduceIte, HeldM.run_bind, Read.run_heldW, HeldM.run_pure, Step.limit_send] at hy ⊢
          rcases foldl_remember_ids _ _ (Step.limit_known cfg _ hy) with hy | ⟨o', ho', e⟩
          · exact Or.inl hy
          · exact Or.inr (Or.inr ⟨o', ho', e⟩)

end


theorem names_bytes (o : Op) : Names o.bytes o.id := ⟨o, Op.decode_bytes o, Or.inl rfl⟩

theorem names_hold (r : Id) (L : List Id) (x : Id) (hx : x ∈ L) : Names (Msg.hold r L).op.bytes x :=
  ⟨(Msg.hold r L).op, Op.decode_bytes _, Or.inr ⟨r, L, ofOp_have r L, hx⟩⟩

/-- What session d knows at a point of a frame on session cid': it knew it
when the frame came, or the frame so far (on d) names it, or the entry
point has sent on d a payload naming it. -/
def KnownBy (d cid' : Id) (c₀ : Conn) (pre : List ByteArray) (st : (Node × Acts) × Held F) : Prop :=
  ∃ c, st.1.1.conn? d = some c ∧ ∀ y ∈ c.known,
    y ∈ c₀.known ∨ (d = cid' ∧ ∃ b ∈ pre, Names b y) ∨ ∃ b, Names b y ∧ (Route.conn d, b) ∈ st.1.2.send

section
variable (fam : Family F) (cfg : Config) (rms : Held F → Id → List Id)

/-- After session cid''s payload b, from st: session d's connection, and
what is sent. -/
theorem frameStep_at (cid' d : Id) (now : Nat) (st : (Node × Acts) × Held F) (b : ByteArray) (c' c : Conn)
    (hc' : st.1.1.conn? cid' = some c') (hc : st.1.1.conn? d = some c) :
    ∃ c2, (frameStep fam cfg rms cid' now st b).1.1.conn? d = some c2 ∧
      c2.known = (if d = cid' then ((Conn.recv fam cfg st.1.1.ix (c'.setRooms (rms st.2 cid')) b now :
        HeldM F Step).run st.2).1.conn else c).known ∧
      ∀ o ∈ ((Conn.recv fam cfg st.1.1.ix (c'.setRooms (rms st.2 cid')) b now : HeldM F Step).run st.2).1.send,
        (Route.conn cid', o.bytes) ∈ (frameStep fam cfg rms cid' now st b).1.2.send := by
  unfold frameStep
  rw [hc']; dsimp only
  have hdr := recv_drop fam cfg st.1.1.ix (c'.setRooms (rms st.2 cid')) b now st.2
  rw [apply_run fam cfg rms _ _ _ _ _ hdr]
  have hs := setConn_conn st.1.1 cid'
    ((Conn.recv fam cfg st.1.1.ix (c'.setRooms (rms st.2 cid')) b now : HeldM F Step).run st.2).1.conn d c hc
  obtain ⟨c2, hc2, e2⟩ := store_known fam cfg rms _ _ false st.2 d _ hs
  refine ⟨c2, hc2, e2, fun o ho => ?_⟩
  apply List.mem_append_right
  apply List.mem_append_left
  exact List.mem_map.2 ⟨o, ho, rfl⟩

/-- **One payload keeps `KnownBy`.** -/
theorem frameStep_knownBy (d cid' : Id) (now : Nat) (c₀ : Conn) (pre : List ByteArray)
    (st : (Node × Acts) × Held F) (b : ByteArray) (hk : KnownBy d cid' c₀ pre st) :
    KnownBy d cid' c₀ (pre ++ [b]) (frameStep fam cfg rms cid' now st b) := by
  obtain ⟨c, hc, hy⟩ := hk
  have hsend : ∀ y ∈ st.1.2.send, y ∈ (frameStep fam cfg rms cid' now st b).1.2.send := by
    intro y hy
    unfold frameStep
    split
    · exact List.mem_append_left _ hy
    · exact hy
  have weak : ∀ y, (y ∈ c₀.known ∨ (d = cid' ∧ ∃ b' ∈ pre, Names b' y) ∨
      ∃ b', Names b' y ∧ (Route.conn d, b') ∈ st.1.2.send) →
      y ∈ c₀.known ∨ (d = cid' ∧ ∃ b' ∈ pre ++ [b], Names b' y) ∨
        ∃ b', Names b' y ∧ (Route.conn d, b') ∈ (frameStep fam cfg rms cid' now st b).1.2.send := by
    intro y h
    rcases h with h | ⟨e, b', hb', hn⟩ | ⟨b', hn, hm⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨e, b', List.mem_append_left _ hb', hn⟩)
    · exact Or.inr (Or.inr ⟨b', hn, hsend _ hm⟩)
  cases hc' : st.1.1.conn? cid' with
  | none =>
    have e : frameStep fam cfg rms cid' now st b = st := by unfold frameStep; rw [hc']
    rw [e]
    exact ⟨c, hc, fun y h => by rw [← e]; exact weak y (hy y h)⟩
  | some c' =>
    obtain ⟨c2, hc2, e2, hsent⟩ := frameStep_at fam cfg rms cid' d now st b c' c hc' hc
    refine ⟨c2, hc2, fun y hy2 => ?_⟩
    rw [e2] at hy2
    split at hy2
    · rename_i hdc
      subst hdc
      rw [hc] at hc'; cases hc'
      rcases recv_known_sub fam cfg _ _ b now st.2 y hy2 with h | h | ⟨o, ho, e⟩
      · exact weak y (hy y (by simpa [Conn.setRooms] using h))
      · exact Or.inr (Or.inl ⟨rfl, b, List.mem_append_right _ (List.mem_singleton_self _), h⟩)
      · exact Or.inr (Or.inr ⟨o.bytes, e ▸ names_bytes o, hsent o ho⟩)
    · exact weak y (hy y hy2)

theorem frame_fold_knownBy (d cid' : Id) (now : Nat) (c₀ : Conn) : ∀ (l pre : List ByteArray)
    (st : (Node × Acts) × Held F), KnownBy d cid' c₀ pre st →
    KnownBy d cid' c₀ (pre ++ l) (l.foldl (frameStep fam cfg rms cid' now) st) := by
  intro l
  induction l with
  | nil => intro pre st h; simpa using h
  | cons b t ih =>
    intro pre st h
    have := ih (pre ++ [b]) _ (frameStep_knownBy fam cfg rms d cid' now c₀ pre st b h)
    simpa using this

variable (hw : WalkLaws (F := F) fam cfg)
include hw

/-- **The stream, one payload:** a payload that stores an op of room r for
the first time offers it on every session d that shows r throughout,
unless d knew its peer holds it when the frame came, or the frame names
it on d, or the entry point sends on d a payload naming it. -/
theorem frameStep_offers (cid' : Id) (now : Nat) (st : (Node × Acts) × Held F) (b : ByteArray)
    (ok : NodeOk fam st.1.1 st.2) (d : Id) (c₀ : Conn) (pre : List ByteArray) (hk : KnownBy d cid' c₀ pre st)
    (x : Id) (o : Op) (r : Id)
    (hn : st.2.db.ops x = none) (hs : (frameStep fam cfg rms cid' now st b).2.db.ops x = some o)
    (hor : fam.room o = some r)
    (hrooms : ∀ h', Kept st.2 h' → Kept h' (frameStep fam cfg rms cid' now st b).2 → r ∈ rms h' d)
    (hmax : 0 < cfg.maxIds) :
    x ∈ c₀.known ∨ (d = cid' ∧ ∃ b' ∈ pre ++ [b], Names b' x) ∨
      ∃ b', Names b' x ∧ (Route.conn d, b') ∈ (frameStep fam cfg rms cid' now st b).1.2.send := by
  have hk' := frameStep_knownBy fam cfg rms d cid' now c₀ pre st b hk
  obtain ⟨c, hc, hy⟩ := hk
  cases hc' : st.1.1.conn? cid' with
  | none =>
    unfold frameStep at hs; rw [hc'] at hs; rw [hn] at hs; cases hs
  | some c' =>
    obtain ⟨c2, hc2, hy2⟩ := hk'
    unfold frameStep at hs hrooms hc2 hy2 ⊢
    simp only [hc'] at hs hrooms hc2 hy2 ⊢
    have hdr := recv_drop fam cfg st.1.1.ix (c'.setRooms (rms st.2 cid')) b now st.2
    have hSs := recv_snaps fam cfg hw st.1.1.ix (c'.setRooms (rms st.2 cid')) b now st.2 ok.sub.1
      ((ok.sub.2 _ (conn_mem hc')).setRooms (rms st.2 cid'))
    have hSo : ∀ y ∈ ((Conn.recv fam cfg st.1.1.ix (c'.setRooms (rms st.2 cid')) b now : HeldM F Step).run st.2).1.conn.offered,
        Named st.2 y := fun y hy => by
      rcases recv_offered fam cfg hw st.1.1.ix (c'.setRooms (rms st.2 cid')) b now st.2 ok.sub.1
        ((ok.sub.2 _ (conn_mem hc')).setRooms (rms st.2 cid')) ok.ids y hy with hy | hy
      · exact ok.offered _ (conn_mem hc') y hy
      · exact hy
    rw [apply_run fam cfg rms _ _ _ _ _ hdr] at hs hrooms hc2 hy2 ⊢
    have okm := setConn_ok fam _ cid' _ st.2 ok hSs hSo
    have hcm := setConn_conn st.1.1 cid'
      ((Conn.recv fam cfg st.1.1.ix (c'.setRooms (rms st.2 cid')) b now : HeldM F Step).run st.2).1.conn d c hc
    rcases store_offers fam cfg rms _ _ false st.2 okm d _ hcm x o r hn hs hor hrooms hmax with hk | ⟨L, hxL, hL⟩
    · obtain ⟨c3, hc3, e3⟩ := store_known fam cfg rms _ _ false st.2 d _ hcm
      rw [hc3] at hc2; cases hc2
      exact hy2 x (by rw [e3]; exact hk)
    · right; right
      exact ⟨_, names_hold r L x hxL, List.mem_append_right _ (List.mem_append_right _ hL)⟩

end


section
variable (fam : Family F) (cfg : Config) (rms : Held F → Id → List Id) (hw : WalkLaws (F := F) fam cfg)
include hw

/-- **The stream, over a session's frame:** an op of room r that a frame
on session cid' stores for the first time is offered on every session d
that shows r throughout, in a frame to d's address, unless d knew its
peer holds it when the frame came, or the frame (on d) names it, or the
entry point sends on d a payload naming it. -/
theorem frame_offers (n : Node) (h : Held F) (ok : NodeOk fam n h) (a bytes : ByteArray) (now : Nat) (cid' : Id)
    (inner : List ByteArray) (hp : plainPeek bytes = some (cid', inner)) (c' : Conn) (hc' : n.conn? cid' = some c')
    (d : Id) (c₀ : Conn) (hc₀ : n.conn? d = some c₀) (x : Id) (o : Op) (r : Id) (hn : h.db.ops x = none)
    (hs : ((n.onFrame (psync fam cfg rms) a bytes now).run h).2.db.ops x = some o) (hor : fam.room o = some r)
    (hrooms : ∀ h', Kept h h' → Kept h' ((n.onFrame (psync fam cfg rms) a bytes now).run h).2 → r ∈ rms h' d)
    (hmax : 0 < cfg.maxIds) :
    x ∈ c₀.known ∨ (d = cid' ∧ ∃ b ∈ inner, Names b x) ∨
      ∃ g, (∃ b ∈ g, Names b x) ∧ ∀ a', ((n.onFrame (psync fam cfg rms) a bytes now).run h).1.1.addr? d = some a' →
        (a', plainFrame d g) ∈ ((n.onFrame (psync fam cfg rms) a bytes now).run h).1.2.send := by
  obtain ⟨h0, bundle, hb', hi⟩ := plainFrame_of_peek hp
  rw [onFrame_fold fam cfg rms hw n a bytes now h cid' bundle inner c' h0 hb' hi hc'] at hs hrooms ⊢
  have ok0 := setAddr_ok fam n cid' a h ok
  obtain ⟨okE, -, -, -, -⟩ := frame_fold fam cfg rms hw cid' now inner (((n.setAddr cid' a, ({} : Acts)), h)) ok0
  rw [frame_end_store fam cfg rms now _ okE] at hs hrooms
  rw [finish_run fam cfg rms _ _ _ _ okE.managed]
  have h0P : ¬ ((((n.setAddr cid' a, ({} : Acts)), h) : (Node × Acts) × Held F).2.db.ops x).isSome = true := by
    simp [hn]
  obtain ⟨pre, b, post, el, hP1, hP2⟩ := fold_first (frameStep fam cfg rms cid' now)
    (fun st => (st.2.db.ops x).isSome = true) inner _ h0P (by rw [hs]; rfl)
  have hk0 : KnownBy d cid' c₀ [] (((n.setAddr cid' a, ({} : Acts)), h) : (Node × Acts) × Held F) :=
    ⟨c₀, hc₀, fun y hy => Or.inl hy⟩
  have hk1 := frame_fold_knownBy fam cfg rms d cid' now c₀ pre [] _ hk0
  simp only [List.nil_append] at hk1
  rw [el, List.foldl_append, List.foldl_cons] at hs hrooms okE ⊢
  obtain ⟨ok1, e1, -, -, -⟩ := frame_fold fam cfg rms hw cid' now pre (((n.setAddr cid' a, ({} : Acts)), h)) ok0
  generalize pre.foldl (frameStep fam cfg rms cid' now) (((n.setAddr cid' a, ({} : Acts)), h)) = st1
    at ok1 e1 hP1 hP2 hs hrooms okE hk1 ⊢
  obtain ⟨ok2, -, -, -, -⟩ := frameStep_ok fam cfg rms hw cid' now st1 b ok1
  obtain ⟨-, e3, -, -, s3⟩ := frame_fold fam cfg rms hw cid' now post _ ok2
  have hn1 : st1.2.db.ops x = none := by
    cases e : st1.2.db.ops x with
    | none => rfl
    | some _ => exact absurd (by rw [e]; rfl) hP1
  have hso : (frameStep fam cfg rms cid' now st1 b).2.db.ops x = some o := by
    obtain ⟨o', ho'⟩ := Option.isSome_iff_exists.1 hP2
    have := e3.1 x o' ho'
    rw [hs] at this; cases this; exact ho'
  have hrm : ∀ h', Kept st1.2 h' → Kept h' (frameStep fam cfg rms cid' now st1 b).2 → r ∈ rms h' d :=
    fun h' k1 k2 => hrooms h' (fun y q hq => k1 y q (e1.1 y q hq)) (fun y q hq => e3.1 y q (k2 y q hq))
  rcases frameStep_offers fam cfg rms hw cid' now st1 b ok1 d c₀ pre hk1 x o r hn1 hso hor hrm hmax with
    hk | ⟨e, b', hb', hnm⟩ | ⟨b', hnm, hm⟩
  · exact Or.inl hk
  · right; left
    refine ⟨e, b', ?_, hnm⟩
    rcases List.mem_append.1 hb' with hb' | hb'
    · exact List.mem_append_left _ hb'
    · rw [List.mem_singleton.1 hb']; exact List.mem_append_right _ (List.mem_cons_self ..)
  · right; right
    have hE := s3 _ hm
    generalize post.foldl (frameStep fam cfg rms cid' now) (frameStep fam cfg rms cid' now st1 b) = fin at hE okE ⊢
    cases hd0 : fin.1.1.addr? d with
    | none =>
      exact ⟨[b'], ⟨b', List.mem_singleton_self _, hnm⟩, fun a' ha' => by
        simp only [Node.addr?] at ha' hd0; rw [hd0] at ha'; cases ha'⟩
    | some d0 =>
      obtain ⟨g, hg, hf⟩ := seal_mem fam cfg rms fin.1.1 fin.1.2 fin.2 d _ d0 hE hd0
      refine ⟨g, ⟨b', hg, hnm⟩, fun a' ha' => ?_⟩
      have : a' = d0 := by simp only [Node.addr?] at ha' hd0; rw [hd0] at ha'; cases ha'; rfl
      subst this; exact hf

end


/-! ## Which entry points store ops of a room -/

theorem absentStep_sub (db : DB F) {y : Op} : ∀ (l acc : List Op), y ∈ l.foldl (absentStep db) acc → y ∈ acc ∨ y ∈ l := by
  intro l
  induction l with
  | nil => intro acc h; exact Or.inl h
  | cons a t ih =>
    intro acc h
    rcases ih _ h with h | h
    · unfold absentStep at h
      split at h
      · rcases List.mem_cons.1 h with rfl | h
        · exact Or.inr (List.mem_cons_self ..)
        · exact Or.inl h
      · exact Or.inl h
    · exact Or.inr (List.mem_cons_of_mem _ h)

/-- **A write stores nothing but what it writes.** -/
theorem write_from (x : Sync F (HeldM F)) (n : Node) (ops : List Op) (h : Held F) (y : Id) (o : Op)
    (hy : ((n.write x ops).run h).2.db.ops y = some o) : h.db.ops y = some o ∨ o ∈ ops := by
  rw [write_run] at hy
  dsimp only at hy
  split at hy
  · exact Or.inl hy
  · simp only [turnH, drainS_ops] at hy
    rcases ingest_from _ h.db y o hy with hy | ⟨ho, -⟩
    · exact Or.inl hy
    · rcases absentStep_sub h.db _ [] (List.mem_reverse.1 ho) with ho | ho
      · cases ho
      · exact Or.inr ho

theorem peek_of_parts {b : ByteArray} {cid : Id} {bundle : ByteArray} {inner : List ByteArray}
    (h0 : b[0]? = some 1) (hd : Codec.decode (b.extract 1 b.size) = some (cid, bundle))
    (hi : (Codec.decode bundle : Option (List ByteArray)) = some inner) : plainPeek b = some (cid, inner) := by
  unfold plainPeek
  rw [if_pos (by rw [h0]; rfl)]
  simp [hd, hi]

section
variable (fam : Family F) (cfg : Config) (rms : Held F → Id → List Id) (hw : WalkLaws (F := F) fam cfg)
include hw

/-- **Only a session's frame stores an op of a room.** A delivery that
stores op x of room r for the first time is a session frame in the clear,
on a session the node holds; a bare frame stores only connection ops. -/
theorem onFrame_new (n : Node) (a b : ByteArray) (now : Nat) (h : Held F) (ok : NodeOk fam n h) (x : Id) (o : Op)
    (r : Id) (hn : h.db.ops x = none) (hs : ((n.onFrame (psync fam cfg rms) a b now).run h).2.db.ops x = some o)
    (hor : fam.room o = some r) :
    ∃ cid' inner c', plainPeek b = some (cid', inner) ∧ n.conn? cid' = some c' := by
  have same : ∀ h', h' = h → h'.db.ops x = some o → False := fun h' e hs' => by rw [e, hn] at hs'; cases hs'
  cases h0 : b[0]? with
  | none => exact (same _ (by simp only [Node.onFrame, h0, HeldM.run_pure]) hs).elim
  | some t =>
    by_cases t1 : t = 1
    · subst t1
      cases hd : (Codec.decode (b.extract 1 b.size) : Option (Id × ByteArray)) with
      | none => exact (same _ (by simp only [Node.onFrame, h0, psync_openFrame, HeldM.pure_bind, hd, Node.onSealed,
          HeldM.run_pure]) hs).elim
      | some q =>
        obtain ⟨cid, bundle⟩ := q
        cases hc : n.conn? cid with
        | none => exact (same _ (by simp only [Node.onFrame, h0, psync_openFrame, HeldM.pure_bind, hd, Node.onSealed,
            hc, HeldM.run_pure]) hs).elim
        | some c =>
          cases hi : (Codec.decode bundle : Option (List ByteArray)) with
          | none => exact (same _ (by simp only [Node.onFrame, h0, psync_openFrame, HeldM.pure_bind, hd,
              Node.onSealed, hc, hi, HeldM.run_pure]) hs).elim
          | some inner => exact ⟨cid, inner, c, peek_of_parts h0 hd hi, hc⟩
    · by_cases t0 : t = 0
      · subst t0
        exfalso
        cases hd : Op.decode (b.extract 1 b.size) with
        | none => exact same _ (by simp only [Node.onFrame, h0, hd, HeldM.run_pure]) hs
        | some o' =>
          by_cases he : (intakeConn fam [o']).isEmpty = true
          · exact same _ (by simp only [Node.onFrame, h0, hd, psync_fam, he, ↓reduceIte, HeldM.run_pure]) hs
          · simp only [Node.onFrame, h0, hd, psync_fam, he, ↓reduceIte, Bool.false_eq_true, HeldM.run_bind,
              psync_recv, HeldM.pure_bind, store_nil] at hs
            rw [finish_run fam cfg rms _ _ _ _ (by rw [(write_node fam cfg rms _ _ _).2.2]; exact ok.managed)] at hs
            rcases write_from (psync fam cfg rms) n _ h x o hs with hs | ho
            · rw [hn] at hs; cases hs
            · have := (intakeConn_conn fam ho).1
              simp [Family.room, this] at hor
      · exfalso
        apply same _ _ hs
        unfold Node.onFrame
        rw [h0]
        split
        · rename_i e; cases e; exact absurd rfl t0
        · rename_i e; cases e; exact absurd rfl t1
        · rfl

end

theorem tick_take (fam : Family F) (cfg : Config) (ix : Index) (c : Conn) (now : Nat) (h : Held F) :
    ((c.tick fam cfg ix now : HeldM F Step).run h).1.take = [] := by
  unfold Conn.tick
  split
  · rfl
  · simp only [HeldM.run_bind, HeldM.run_pure, Conn.finish_take]
    split
    · unfold Conn.start; split <;> rfl
    · rfl

section
variable (fam : Family F) (cfg : Config) (rms : Held F → Id → List Id)

theorem tickStep_store (now : Nat) (st : (Node × Acts) × Held F) (p : Id × Conn) :
    (tickStep fam cfg rms now st p).2 = st.2 := by
  unfold tickStep
  split
  · rename_i c _
    dsimp only
    by_cases hd : ((Conn.tick fam cfg st.1.1.ix (c.setRooms (rms st.2 p.1)) now : HeldM F Step).run st.2).1.drop = true
    · simp only [Node.apply, hd, ↓reduceIte, HeldM.run_pure]
    · rw [apply_run fam cfg rms _ _ _ _ _ (by simpa using hd), tick_take, store_nil]
  · rfl

theorem tick_fold_store (now : Nat) : ∀ (l : List (Id × Conn)) (st : (Node × Acts) × Held F),
    (l.foldl (tickStep fam cfg rms now) st).2 = st.2 := by
  intro l
  induction l with
  | nil => intro st; rfl
  | cons p t ih => intro st; rw [List.foldl_cons, ih, tickStep_store]

theorem connect_store (n : Node) (cid : Id) (a : ByteArray) (d : Bool) (now : Nat) (h : Held F) (hm : n.managed = []) :
    ((n.connect (psync fam cfg rms) cid a d now).run h).2 = h := by
  unfold Node.connect Node.open
  simp only [HeldM.run_bind, psync_rooms, readH_run, HeldM.run_pure]
  rw [finish_run fam cfg rms _ _ _ _ (by simp [Node.setAddr, Node.close, hm])]

variable (hw : WalkLaws (F := F) fam cfg)
include hw

theorem tick_fold_ok (now : Nat) : ∀ (l : List (Id × Conn)) st, NodeOk fam st.1.1 st.2 →
    NodeOk fam (l.foldl (tickStep fam cfg rms now) st).1.1 (l.foldl (tickStep fam cfg rms now) st).2 := by
  intro l
  induction l with
  | nil => intro st h; exact h
  | cons p t ih => intro st h; exact ih _ (tickStep_ok fam cfg rms hw now st p h)

/-- **The clock stores nothing.** -/
theorem onTick_store (n : Node) (now : Nat) (h : Held F) (ok : NodeOk fam n h) :
    ((n.onTick (psync fam cfg rms) now).run h).2 = h := by
  rw [onTick_run fam cfg rms hw]
  have okf := tick_fold_ok fam cfg rms hw now n.conns ((n, {}), h) ok
  rw [finish_run fam cfg rms _ _ _ _ okf.managed]
  exact tick_fold_store fam cfg rms now _ _

end


/-! ## Every session a node holds has an address -/

/-- Every session a node holds has an address. -/
def AddrOk (n : Node) : Prop := ∀ cid ∈ cids n, ∃ a, n.addr? cid = some a

/-- n' keeps an address for every session n has one for. -/
def AddrKeep (n n' : Node) : Prop := ∀ d a, n.addr? d = some a → ∃ a', n'.addr? d = some a'

theorem addrOk_of {n n' : Node} (ok : AddrOk n) (hk : AddrKeep n n') (hc : ∀ d ∈ cids n', d ∈ cids n) :
    AddrOk n' := fun d hd => let ⟨a, ha⟩ := ok d (hc d hd); hk d a ha

theorem addrKeep_eq {n n' : Node} (e : n'.addrs = n.addrs) : AddrKeep n n' :=
  fun d a h => ⟨a, by unfold Node.addr? at h ⊢; rw [e]; exact h⟩

theorem find_filter_ne {d cid : Id} (hne : d ≠ cid) : ∀ l : List (Id × ByteArray),
    (l.filter fun p => !Decidable.decide (p.1 = cid)).find? (fun p => Decidable.decide (p.1 = d)) =
      l.find? (fun p => Decidable.decide (p.1 = d)) := by
  intro l
  induction l with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨k, v⟩ := p
    by_cases e : k = d
    · subst e
      simp [List.filter_cons, hne]
    · by_cases e' : k = cid
      · subst e'
        simp [List.filter_cons, List.find?_cons, e, ih]
      · simp [List.filter_cons, List.find?_cons, e', e, ih]

theorem setAddr_keep (n : Node) (cid : Id) (a : ByteArray) : AddrKeep n (n.setAddr cid a) := by
  intro d a0 h
  by_cases e : d = cid
  · subst e; exact ⟨a, setAddr_addr n d a⟩
  · refine ⟨a0, ?_⟩
    unfold Node.setAddr Node.addr? at *
    simp only [List.find?_cons, show (cid = d) = False from propext ⟨fun h => e h.symm, False.elim⟩,
      decide_false, Bool.false_eq_true, ↓reduceIte] at h ⊢
    rw [find_filter_ne e]; exact h

theorem AddrKeep.trans {a b c : Node} (h1 : AddrKeep a b) (h2 : AddrKeep b c) : AddrKeep a c :=
  fun d x h => let ⟨y, hy⟩ := h1 d x h; h2 d y hy

section
variable (fam : Family F) (cfg : Config) (rms : Held F → Id → List Id)

theorem drop_cids (n : Node) (cid : Id) : ∀ d ∈ cids (n.drop cid), d ∈ cids n := by
  intro d hd
  simp only [cids, Node.drop, Node.close, List.mem_map, List.mem_filter] at hd ⊢
  obtain ⟨p, ⟨hp, -⟩, e⟩ := hd
  exact ⟨p, hp, e⟩

theorem tickStep_addr (now : Nat) (st : (Node × Acts) × Held F) (p : Id × Conn) :
    (tickStep fam cfg rms now st p).1.1.addrs = st.1.1.addrs ∧
    ∀ d ∈ cids (tickStep fam cfg rms now st p).1.1, d ∈ cids st.1.1 := by
  unfold tickStep
  split
  · rename_i c _
    dsimp only
    by_cases hd : ((Conn.tick fam cfg st.1.1.ix (c.setRooms (rms st.2 p.1)) now : HeldM F Step).run st.2).1.drop = true
    · simp only [Node.apply, hd, ↓reduceIte, HeldM.run_pure]
      exact ⟨rfl, drop_cids _ _⟩
    · rw [apply_run fam cfg rms _ _ _ _ _ (by simpa using hd)]
      have := store_node fam cfg rms (setConn st.1.1 p.1
        ((Conn.tick fam cfg st.1.1.ix (c.setRooms (rms st.2 p.1)) now : HeldM F Step).run st.2).1.conn)
        ((Conn.tick fam cfg st.1.1.ix (c.setRooms (rms st.2 p.1)) now : HeldM F Step).run st.2).1.take false st.2
      refine ⟨this.1, fun d h => ?_⟩
      rw [this.2, setConn_cids] at h; exact h
  · exact ⟨rfl, fun d h => h⟩

theorem tick_fold_addr (now : Nat) : ∀ (l : List (Id × Conn)) (st : (Node × Acts) × Held F),
    (l.foldl (tickStep fam cfg rms now) st).1.1.addrs = st.1.1.addrs ∧
    ∀ d ∈ cids (l.foldl (tickStep fam cfg rms now) st).1.1, d ∈ cids st.1.1 := by
  intro l
  induction l with
  | nil => intro st; exact ⟨rfl, fun d h => h⟩
  | cons p t ih =>
    intro st
    obtain ⟨a1, c1⟩ := tickStep_addr fam cfg rms now st p
    obtain ⟨a2, c2⟩ := ih (tickStep fam cfg rms now st p)
    exact ⟨a2.trans a1, fun d h => c1 d (c2 d h)⟩

theorem onWrite_addr (n : Node) (ops : List Op) (now : Nat) (h : Held F) (ok : NodeOk fam n h) (ha : AddrOk n) :
    AddrOk ((n.onWrite (psync fam cfg rms) ops now).run h).1.1 := by
  unfold Node.onWrite
  simp only [HeldM.run_bind]
  rw [finish_run fam cfg rms _ _ _ _ (store_ok fam cfg rms n ops true h ok).managed]
  have := store_node fam cfg rms n ops true h
  exact addrOk_of ha (addrKeep_eq this.1) (fun d hd => by rw [← this.2]; exact hd)

theorem connect_addr (n : Node) (cid : Id) (a : ByteArray) (dl : Bool) (now : Nat) (h : Held F) (ok : NodeOk fam n h)
    (ha : AddrOk n) : AddrOk ((n.connect (psync fam cfg rms) cid a dl now).run h).1.1 := by
  unfold Node.connect Node.open
  simp only [HeldM.run_bind, psync_rooms, readH_run, HeldM.run_pure]
  rw [finish_run fam cfg rms _ _ _ _ (by simp [Node.setAddr, Node.close, ok.managed])]
  intro d hd
  simp only [cids, List.map_cons, List.mem_cons] at hd
  by_cases e : d = cid
  · subst e; exact ⟨a, setAddr_addr _ d a⟩
  · rcases hd with hd | hd
    · exact absurd hd e
    · have hd' : d ∈ cids n := by
        have hd2 : d ∈ (n.close cid).conns.map (·.1) := hd
        simp only [Node.close] at hd2
        obtain ⟨p, hp, e'⟩ := List.mem_map.1 hd2
        exact List.mem_map.2 ⟨p, (List.mem_filter.1 hp).1, e'⟩
      obtain ⟨a0, ha0⟩ := ha d hd'
      have : (n.close cid).addr? d = some a0 := ha0
      exact setAddr_keep (n.close cid) cid a d a0 this

variable (hw : WalkLaws (F := F) fam cfg)
include hw

theorem onTick_addr (n : Node) (now : Nat) (h : Held F) (ok : NodeOk fam n h) (ha : AddrOk n) :
    AddrOk ((n.onTick (psync fam cfg rms) now).run h).1.1 := by
  rw [onTick_run fam cfg rms hw]
  have okf := tick_fold_ok fam cfg rms hw now n.conns ((n, {}), h) ok
  rw [finish_run fam cfg rms _ _ _ _ okf.managed]
  obtain ⟨a1, c1⟩ := tick_fold_addr fam cfg rms now n.conns ((n, {}), h)
  exact addrOk_of ha (addrKeep_eq a1) c1

theorem onFrame_addr (n : Node) (a b : ByteArray) (now : Nat) (h : Held F) (ok : NodeOk fam n h) (ha : AddrOk n) :
    AddrOk ((n.onFrame (psync fam cfg rms) a b now).run h).1.1 := by
  have hc := onFrame_cids fam cfg rms hw n a b now h ok
  refine addrOk_of ha ?_ (fun d hd => by rw [← hc]; exact hd)
  cases h0 : b[0]? with
  | none => simp only [Node.onFrame, h0, HeldM.run_pure]; exact fun d x h => ⟨x, h⟩
  | some t =>
    by_cases t1 : t = 1
    · subst t1
      cases hd : (Codec.decode (b.extract 1 b.size) : Option (Id × ByteArray)) with
      | none => simp only [Node.onFrame, h0, psync_openFrame, HeldM.pure_bind, hd, Node.onSealed, HeldM.run_pure]
                exact fun d x h => ⟨x, h⟩
      | some q =>
        obtain ⟨cid, bundle⟩ := q
        cases hc : n.conn? cid with
        | none => simp only [Node.onFrame, h0, psync_openFrame, HeldM.pure_bind, hd, Node.onSealed, hc, HeldM.run_pure]
                  exact fun d x h => ⟨x, h⟩
        | some c =>
          cases hi : (Codec.decode bundle : Option (List ByteArray)) with
          | none => simp only [Node.onFrame, h0, psync_openFrame, HeldM.pure_bind, hd, Node.onSealed, hc, hi,
                      HeldM.run_pure]
                    exact fun d x h => ⟨x, h⟩
          | some inner =>
            rw [onFrame_fold fam cfg rms hw n a b now h cid bundle inner c h0 hd hi hc]
            obtain ⟨ok1, -, -, a1, -⟩ := frame_fold fam cfg rms hw cid now inner ((n.setAddr cid a, {}), h)
              (setAddr_ok fam n cid a h ok)
            rw [finish_run fam cfg rms _ _ _ _ ok1.managed]
            exact (setAddr_keep n cid a).trans (addrKeep_eq a1)
    · by_cases t0 : t = 0
      · subst t0
        cases hd : Op.decode (b.extract 1 b.size) with
        | none => simp only [Node.onFrame, h0, hd, HeldM.run_pure]; exact fun d x h => ⟨x, h⟩
        | some o =>
          by_cases he : (intakeConn fam [o]).isEmpty = true
          · simp only [Node.onFrame, h0, hd, psync_fam, he, ↓reduceIte, HeldM.run_pure]; exact fun d x h => ⟨x, h⟩
          · simp only [Node.onFrame, h0, hd, psync_fam, he, ↓reduceIte, Bool.false_eq_true, HeldM.run_bind,
              psync_recv, HeldM.pure_bind, store_nil]
            rw [finish_run fam cfg rms _ _ _ _ (write_ok fam cfg rms _ _ _ ok).managed]
            exact addrKeep_eq (write_node fam cfg rms _ _ _).2.1
      · unfold Node.onFrame
        rw [h0]
        split
        · rename_i e; cases e; exact absurd rfl t0
        · rename_i e; cases e; exact absurd rfl t1
        · exact fun d x h => ⟨x, h⟩

end


/-! ## New packets are new: serials -/

/-- Every packet in flight has a serial below the next one's. -/
def SerialOk {S : Type} {n : Nat} (w : World S n) : Prop := ∀ q ∈ w.flight, q.serial < w.serial

theorem packets_serial {n : Nat} (i : Fin n) (o : ByteArray) (t : Nat) : ∀ (s : Nat) (l : List (ByteArray × ByteArray)) q,
    q ∈ packets i o t s l → s ≤ q.serial ∧ q.serial < s + l.length := by
  intro s l
  induction l generalizing s with
  | nil => intro q h; cases h
  | cons x t' ih =>
    intro q h
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · have := ih (s + 1) q h
      simp only [List.length_cons]; omega

theorem packets_length {n : Nat} (i : Fin n) (o : ByteArray) (t : Nat) : ∀ (s : Nat) (l : List (ByteArray × ByteArray)),
    (packets i o t s l).length = l.length := by
  intro s l
  induction l generalizing s with
  | nil => rfl
  | cons x t' ih => simp [packets, ih]

/-- What an entry point sends goes in flight as new packets, from its node. -/
theorem enter_new {M : Type → Type} {S' : Type} [Monad M] [Store F M] [Turn F M] (P : Setup F M S')
    (w : World S' P.n) (i : Fin P.n) (t : Nat) (f : Node → M (Node × Effects)) (d b : ByteArray)
    (hm : (d, b) ∈ (P.run (f (w.node i)) (w.box i)).1.2.send) :
    ∃ q ∈ (w.enter P i t f).flight, w.serial ≤ q.serial ∧ q.src = some i ∧ q.dst = d ∧ q.bytes = b := by
  obtain ⟨s', hs'⟩ := mem_packets i (P.addr i) t w.serial _ d b hm
  refine ⟨_, List.mem_append_right _ hs', (packets_serial i _ t w.serial _ _ hs').1, rfl, rfl, rfl⟩

theorem fresh_not_mem {S : Type} {n : Nat} {w : World S n} (hs : SerialOk w) {q : Packet n} (hq : w.serial ≤ q.serial) :
    q ∉ w.flight := fun h => by have := hs q h; omega

theorem enter_serial {M : Type → Type} {S' : Type} [Monad M] [Store F M] [Turn F M] (P : Setup F M S')
    (w : World S' P.n) (i : Fin P.n) (t : Nat) (f : Node → M (Node × Effects)) (hs : SerialOk w) :
    SerialOk (w.enter P i t f) := by
  intro q hq
  simp only [World.enter] at hq ⊢
  rcases List.mem_append.1 hq with hq | hq
  · have := hs q hq; omega
  · have := packets_serial i _ t w.serial _ q hq
    rw [packets_length]; omega

theorem reach_serial' (Q : Plain F) (adv : World (Held F) Q.setup.n → ByteArray → Prop) (w₀ w : World (Held F) Q.setup.n)
    (h0 : SerialOk w₀) (hr : Reachable Q.setup adv w₀ w) : SerialOk w := by
  induction hr with
  | init => exact h0
  | @step w a _ _ ih =>
    cases a with
    | deliver k t =>
      simp only [World.step]
      split
      · exact ih
      · rename_i p _
        have h' : SerialOk ({ w with flight := w.flight.eraseIdx k } : World (Held F) Q.setup.n) :=
          fun q hq => ih q (List.mem_of_mem_eraseIdx hq)
        split
        · exact h'
        · rename_i j' _
          intro q hq
          exact enter_serial Q.setup { w with flight := w.flight.eraseIdx k } j' t
            (fun nd => Node.onFrame (Q.setup.sync j') nd p.origin p.bytes t) h' q hq
    | dup k =>
      simp only [World.step]
      split
      · exact ih
      · intro q hq
        simp only at hq ⊢
        rcases List.mem_append.1 hq with hq | hq
        · have := ih q hq; omega
        · rw [List.mem_singleton.1 hq]; simp
    | drop k => exact fun q hq => ih q (List.mem_of_mem_eraseIdx hq)
    | tick i t => exact enter_serial Q.setup w i t (fun nd => nd.onTick (Q.setup.sync i) t) ih
    | write i ops t =>
      intro q hq
      exact enter_serial Q.setup w i t (fun nd => nd.onWrite (Q.setup.sync i) ops t) ih q hq
    | restart i t => exact ih
    | connect i j cid d t =>
      exact enter_serial Q.setup w i t (fun nd => nd.connect (Q.setup.sync i) cid (Q.setup.addr j) d t) ih
    | inject i o b t =>
      intro q hq
      exact enter_serial Q.setup w i t (fun nd => nd.onFrame (Q.setup.sync i) o b t) ih q hq

theorem reach_serial (Q : Plain F) (adv : World (Held F) Q.n → ByteArray → Prop) (w : World (Held F) Q.n)
    (hr : Q.Reach adv w) : SerialOk w :=
  reach_serial' Q adv Q.start w (fun q hq => by cases hq) hr

/-! ## Every session a node holds has an address, in every reachable world -/

theorem enter_addr (Q : Plain F) (w : World (Held F) Q.n) (i : Fin Q.n) (t : Nat) (f : Node → HeldM F (Node × Effects))
    (hf : AddrOk ((f (w.node i)).run (w.box i)).1.1) (ha : ∀ j, AddrOk (w.node j)) :
    ∀ j, AddrOk ((w.enter Q.setup i t f).node j) := by
  intro j
  simp only [World.enter, upd]
  by_cases e : j = i
  · subst e; simp only [ite_true]; exact hf
  · simp only [e, ite_false]; exact ha j

theorem boot_addr (fam : Family F) (ops : List Op) (floor : Nat) : AddrOk (Node.boot fam ops floor) :=
  fun d hd => by simp [cids, Node.boot] at hd

theorem reach_addr' (Q : Plain F) (hw : WalkLaws (F := F) Q.fam Q.cfg)
    (adv : World (Held F) Q.setup.n → ByteArray → Prop) (w₀ w : World (Held F) Q.setup.n)
    (h0ok : ∀ i, NodeOk Q.fam (w₀.node i) (w₀.box i)) (h0 : ∀ i, AddrOk (w₀.node i))
    (hr : Reachable Q.setup adv w₀ w) : ∀ i, AddrOk (w.node i) := by
  induction hr with
  | init => exact h0
  | @step w a hr' _ ih =>
    have ok := reach_ok' Q hw adv w₀ w h0ok hr'
    cases a with
    | deliver k t =>
      simp only [World.step]
      split
      · exact ih
      · rename_i p _
        split
        · exact ih
        · rename_i j' _
          exact enter_addr Q { w with flight := w.flight.eraseIdx k } j' t
            (fun nd => nd.onFrame (psync Q.fam Q.cfg (Q.rooms j')) p.origin p.bytes t)
            (onFrame_addr Q.fam Q.cfg (Q.rooms j') hw _ _ _ _ _ (ok j') (ih j')) ih
    | dup k => simp only [World.step]; split <;> exact ih
    | drop k => exact ih
    | tick i t =>
      exact enter_addr Q w i t (fun nd => nd.onTick (psync Q.fam Q.cfg (Q.rooms i)) t)
        (onTick_addr Q.fam Q.cfg (Q.rooms i) hw _ _ _ (ok i) (ih i)) ih
    | write i ops t =>
      exact enter_addr Q w i t (fun nd => nd.onWrite (psync Q.fam Q.cfg (Q.rooms i)) ops t)
        (onWrite_addr Q.fam Q.cfg (Q.rooms i) _ _ _ _ (ok i) (ih i)) ih
    | restart i t =>
      intro j
      simp only [World.step, upd]
      by_cases e : j = i
      · subst e; simp only [ite_true]; exact boot_addr _ _ _
      · simp only [e, ite_false]; exact ih j
    | connect i j cid d t =>
      exact enter_addr Q w i t (fun nd => nd.connect (psync Q.fam Q.cfg (Q.rooms i)) cid (Q.setup.addr j) d t)
        (connect_addr Q.fam Q.cfg (Q.rooms i) _ _ _ _ _ _ (ok i) (ih i)) ih
    | inject i o b t =>
      exact enter_addr Q w i t (fun nd => nd.onFrame (psync Q.fam Q.cfg (Q.rooms i)) o b t)
        (onFrame_addr Q.fam Q.cfg (Q.rooms i) hw _ _ _ _ _ (ok i) (ih i)) ih

theorem reach_addr (Q : Plain F) (hw : WalkLaws (F := F) Q.fam Q.cfg) (adv : World (Held F) Q.n → ByteArray → Prop)
    (w : World (Held F) Q.n) (hr : Q.Reach adv w) : ∀ i, AddrOk (w.node i) :=
  reach_addr' Q hw adv Q.start w (fun _ => boot_ok Q.fam {} (fun x o h => by cases h) (fun o ho => by cases ho)
    (fun o ho => by cases ho) (fun x o h => by cases h) _) (fun _ => boot_addr _ _ _) hr


/-! ## The stream law, over every reachable world -/

section
variable (fam : Family F) (cfg : Config) (rms : Held F → Id → List Id)

/-- **The stream at a node, for a local write.** -/
theorem write_stream (n : Node) (h : Held F) (ok : NodeOk fam n h) (ha : AddrOk n) (ops : List Op) (t : Nat)
    (cid x r : Id) (o : Op) (c₀ : Conn) (hmax : 0 < cfg.maxIds) (hn : h.db.ops x = none)
    (hs : ((n.onWrite (psync fam cfg rms) ops t).run h).2.db.ops x = some o) (hor : fam.room o = some r)
    (hrooms : ∀ h', Kept h h' → Kept h' ((n.onWrite (psync fam cfg rms) ops t).run h).2 → r ∈ rms h' cid)
    (hc₀ : n.conn? cid = some c₀) :
    x ∈ c₀.known ∨ ∃ a' g, (∃ b ∈ g, Names b x) ∧
      ((n.onWrite (psync fam cfg rms) ops t).run h).1.1.addr? cid = some a' ∧
      (a', plainFrame cid g) ∈ ((n.onWrite (psync fam cfg rms) ops t).run h).1.2.send := by
  unfold Node.onWrite at hs hrooms ⊢
  simp only [HeldM.run_bind] at hs hrooms ⊢
  have okS := store_ok fam cfg rms n ops true h ok
  rw [finish_run fam cfg rms _ _ _ _ okS.managed] at hs hrooms ⊢
  rcases store_offers fam cfg rms n ops true h ok cid c₀ hc₀ x o r hn hs hor hrooms hmax with hk | ⟨L, hxL, hL⟩
  · exact Or.inl hk
  · right
    obtain ⟨a', ha'⟩ := ha cid ((conn_iff n cid).1 ⟨c₀, hc₀⟩)
    have ha2 : ((n.store (psync fam cfg rms) ops true).run h).1.1.addr? cid = some a' := by
      unfold Node.addr? at ha' ⊢; rw [(store_node fam cfg rms n ops true h).1]; exact ha'
    obtain ⟨g, hg, hf⟩ := seal_mem fam cfg rms _ _ ((n.store (psync fam cfg rms) ops true).run h).2 cid _ a' hL ha2
    exact ⟨a', g, ⟨_, hg, names_hold r L x hxL⟩, ha2, hf⟩

variable (hw : WalkLaws (F := F) fam cfg)
include hw

/-- **The stream at a node, for a frame it takes.** -/
theorem frame_stream (n : Node) (h : Held F) (ok : NodeOk fam n h) (ha : AddrOk n) (origin bytes : ByteArray)
    (t : Nat) (cid x r : Id) (o : Op) (c₀ c : Conn) (hmax : 0 < cfg.maxIds) (hn : h.db.ops x = none)
    (hs : ((n.onFrame (psync fam cfg rms) origin bytes t).run h).2.db.ops x = some o) (hor : fam.room o = some r)
    (hrooms : ∀ h', Kept h h' → Kept h' ((n.onFrame (psync fam cfg rms) origin bytes t).run h).2 → r ∈ rms h' cid)
    (hc₀ : n.conn? cid = some c₀) (hc : ((n.onFrame (psync fam cfg rms) origin bytes t).run h).1.1.conn? cid = some c) :
    x ∈ c₀.known ∨ (∃ ps, plainPeek bytes = some (cid, ps) ∧ ∃ b ∈ ps, Names b x) ∨
      ∃ a' g, (∃ b ∈ g, Names b x) ∧
        ((n.onFrame (psync fam cfg rms) origin bytes t).run h).1.1.addr? cid = some a' ∧
        (a', plainFrame cid g) ∈ ((n.onFrame (psync fam cfg rms) origin bytes t).run h).1.2.send := by
  obtain ⟨cid', inner, c', hp, hc'⟩ := onFrame_new fam cfg rms hw n origin bytes t h ok x o r hn hs hor
  rcases frame_offers fam cfg rms hw n h ok origin bytes t cid' inner hp c' hc' cid c₀ hc₀ x o r hn hs hor hrooms hmax with
    hk | ⟨e, b, hb, hnm⟩ | ⟨g, hg, hf⟩
  · exact Or.inl hk
  · subst e; exact Or.inr (Or.inl ⟨inner, hp, b, hb, hnm⟩)
  · right; right
    obtain ⟨a', ha'⟩ := onFrame_addr fam cfg rms hw n origin bytes t h ok ha cid
      ((conn_iff _ cid).1 ⟨c, hc⟩)
    exact ⟨a', g, hg, ha', hf a' ha'⟩

end

/-- What an entry point at node i sends to session cid's address is a new
packet in flight. -/
theorem enter_names (Q : Plain F) (w : World (Held F) Q.n) (i : Fin Q.n) (t : Nat)
    (f : Node → HeldM F (Node × Effects)) (cid x : Id) (g : List ByteArray) (hg : ∃ b ∈ g, Names b x)
    (a' : ByteArray) (ha : ((f (w.node i)).run (w.box i)).1.1.addr? cid = some a')
    (hm : (a', plainFrame cid g) ∈ ((f (w.node i)).run (w.box i)).1.2.send) :
    ∃ p ∈ (w.enter Q.setup i t f).flight, w.serial ≤ p.serial ∧ p.src = some i ∧
      some p.dst = ((w.enter Q.setup i t f).node i).addr? cid ∧
      ∃ ps, plainPeek p.bytes = some (cid, ps) ∧ ∃ b ∈ ps, Names b x := by
  obtain ⟨q, hq, hser, hsrc, hdst, hb⟩ := enter_new Q.setup w i t f a' _ hm
  refine ⟨q, hq, hser, hsrc, ?_, g, by rw [hb]; exact peek_plainFrame cid g, hg⟩
  simp only [World.enter, upd_same]
  rw [hdst]; exact ha.symm

/-- **The stream offers every op a node stores, proven of the running
code.** An op of room r that a step stores at node i for the first time,
its own write or relayed, on a session that shows r throughout: i knew
the peer holds it, or the frame the step hands i on the session names
it, or the step puts in flight to the session's address a new frame of
i's naming it. -/
theorem stream_offers_stored_proof : stream_offers_stored_stmt := by
  intro F Q adv w a i r x cid c₀ c hr _ hok hnot hhold hrooms hc₀ hc
  have wl := walk_proof F Q.fam Q.cfg
  have okw := reach_ok Q wl adv w hr
  have haw := reach_addr Q wl adv w hr
  have hsw := reach_serial Q adv w hr
  have hext := step_ext Q wl w a i
  obtain ⟨o, hso, hor⟩ := hhold
  have hor' : Q.fam.room o = some r := hor
  have hso' : ((w.step Q.setup a).box i).db.ops x = some o := hso
  have hn : (w.box i).db.ops x = none := by
    cases e : (w.box i).db.ops x with
    | none => rfl
    | some o' =>
      exfalso
      have e2 := hext.1 x o' e
      rw [hso'] at e2; cases e2
      exact hnot ⟨o, e, hor⟩
  have same : (w.step Q.setup a).box i = w.box i → False := fun e => by rw [e, hn] at hso'; cases hso'
  have hmax := hok.maxIds
  cases a with
  | deliver k t =>
    cases hk : w.flight[k]? with
    | none => exact (same (by simp only [World.step, hk])).elim
    | some p =>
      cases hj : Q.setup.at? p.dst with
      | none => exact (same (by simp only [World.step, hk, hj])).elim
      | some j =>
        by_cases eij : j = i
        · subst eij
          have e : w.step Q.setup (.deliver k t) =
              { ({ w with flight := w.flight.eraseIdx k } : World (Held F) Q.n).enter Q.setup j t
                  (fun nd => nd.onFrame (psync Q.fam Q.cfg (Q.rooms j)) p.origin p.bytes t) with
                delivered := w.delivered ++ [(j, p.bytes)] } := by
            simp only [World.step, hk, hj]
          rw [e] at hso' hrooms hc ⊢
          simp only [World.enter, upd_same] at hso' hrooms hc
          rcases frame_stream Q.fam Q.cfg (Q.rooms j) wl (w.node j) (w.box j) (okw j) (haw j) p.origin p.bytes t
              cid x r o c₀ c hmax hn hso' hor' hrooms hc₀ hc with hk' | ⟨ps, hp, hb⟩ | ⟨a', g, hg, ha', hf⟩
          · exact Or.inl hk'
          · exact Or.inr (Or.inl ⟨p.bytes, ps, rfl, hp, hb⟩)
          · right; right
            obtain ⟨q, hq, hser, hsrc, hdst, hpk⟩ := enter_names Q { w with flight := w.flight.eraseIdx k } j t
              (fun nd => nd.onFrame (psync Q.fam Q.cfg (Q.rooms j)) p.origin p.bytes t) cid x g hg a' ha' hf
            exact ⟨q, hq, fresh_not_mem hsw hser, hsrc, hdst, hpk⟩
        · exact (same (by simp only [World.step, hk, hj, World.enter, upd_other _ _ (Ne.symm eij)])).elim
  | dup k => exact (same (by simp only [World.step]; split <;> rfl)).elim
  | drop k => exact (same rfl).elim
  | tick j t =>
    exfalso; apply same
    by_cases eij : j = i
    · subst eij
      simp only [World.step, World.enter, upd_same]
      exact onTick_store Q.fam Q.cfg (Q.rooms j) wl _ _ _ (okw j)
    · simp only [World.step, World.enter, upd_other _ _ (Ne.symm eij)]
  | write j ops t =>
    by_cases eij : j = i
    · subst eij
      simp only [World.step, World.enter, upd_same] at hso' hrooms hc ⊢
      rcases write_stream Q.fam Q.cfg (Q.rooms j) (w.node j) (w.box j) (okw j) (haw j) ops t cid x r o c₀ hmax hn
          hso' hor' hrooms hc₀ with hk' | ⟨a', g, hg, ha', hf⟩
      · exact Or.inl hk'
      · right; right
        obtain ⟨q, hq, hser, hsrc, hdst, hpk⟩ := enter_names Q w j t
          (fun nd => nd.onWrite (psync Q.fam Q.cfg (Q.rooms j)) ops t) cid x g hg a' ha' hf
        exact ⟨q, hq, fresh_not_mem hsw hser, hsrc, by simpa only [World.enter, upd_same] using hdst, hpk⟩
    · exact (same (by simp only [World.step, World.enter, upd_other _ _ (Ne.symm eij)])).elim
  | restart j t =>
    by_cases eij : j = i
    · subst eij
      exfalso
      simp only [World.step, upd_same] at hc
      simp [Node.conn?, Node.boot] at hc
    · exact (same (by simp only [World.step, upd_other _ _ (Ne.symm eij)])).elim
  | connect j j' cid' d t =>
    exfalso; apply same
    by_cases eij : j = i
    · subst eij
      simp only [World.step, World.enter, upd_same]
      exact connect_store Q.fam Q.cfg (Q.rooms j) _ _ _ _ _ _ (okw j).managed
    · simp only [World.step, World.enter, upd_other _ _ (Ne.symm eij)]
  | inject j origin b t =>
    by_cases eij : j = i
    · subst eij
      simp only [World.step, World.enter, upd_same] at hso' hrooms hc ⊢
      rcases frame_stream Q.fam Q.cfg (Q.rooms j) wl (w.node j) (w.box j) (okw j) (haw j) origin b t
          cid x r o c₀ c hmax hn hso' hor' hrooms hc₀ hc with hk' | ⟨ps, hp, hb⟩ | ⟨a', g, hg, ha', hf⟩
      · exact Or.inl hk'
      · exact Or.inr (Or.inl ⟨b, ps, rfl, hp, hb⟩)
      · right; right
        obtain ⟨q, hq, hser, hsrc, hdst, hpk⟩ := enter_names Q w j t
          (fun nd => nd.onFrame (psync Q.fam Q.cfg (Q.rooms j)) origin b t) cid x g hg a' ha' hf
        exact ⟨q, hq, fresh_not_mem hsw hser, hsrc, by simpa only [World.enter, upd_same] using hdst, hpk⟩
    · exact (same (by simp only [World.step, World.enter, upd_other _ _ (Ne.symm eij)])).elim


/-- **L-offered, both halves:** every node's index is its store, and the
stream offers every op a node stores. -/
theorem offered_proof : offered_stmt := ⟨index_store_proof, stream_offers_stored_proof⟩

end Engine.World
