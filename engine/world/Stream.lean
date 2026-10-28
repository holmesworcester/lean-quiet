/-
The stream offers every op a node stores, proven of the running code: an
op of room r that an entry point stores for the first time, whether the
node's own write or relayed from a third peer, is offered at once on
every session that shows r throughout, in a frame to that session's
address, unless the session knows its peer holds it
(`stream_offers_stored_proof`).

- The stream's loop as a fold (`filed_run`): it offers each new id of a
  shown room not known or offered (`filed_offers'`), under its room
  (`holds_cover`).
- A store offers each op it newly stores on each session
  (`store_offers`), since a write reports what it stores
  (`write_reports`) and a fanout runs the stream on every session
  (`fanout_offers'`); a connection never counts as offered an op its
  node did not hold (`NodeOk.offered`).
- Over a frame, the first payload that stores the op does it
  (`fold_first`, `frameStep_offers`, `frame_offers`); what a session
  knows its peer holds only grows (`recv_known`, `frame_fold_known`).
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

/-! ## What a connection knows its peer holds only grows within a frame -/

theorem finish_known (st : Step) : (Conn.finish st).conn.known = st.conn.known := by
  unfold Conn.finish Conn.report
  by_cases h : st.conn.asked.isEmpty = true <;> simp [h]

theorem filed_known (fam : Family F) (cfg : Config) (c : Conn) (ids : List Id) (h : Held F) :
    ((c.filed fam cfg ids : HeldM F Step).run h).1.conn.known = c.known := by
  rw [filed_run, finish_known]; exact fileStep_known fam h.db ids ([], c)

theorem mem_foldl_insert_keep {y : Id} : ∀ (l : List Id) (s : Std.HashSet Id), y ∈ s → y ∈ l.foldl (·.insert ·) s := by
  intro l
  induction l with
  | nil => intro s h; exact h
  | cons a t ih => intro s h; exact ih _ (Std.HashSet.mem_insert.2 (Or.inr h))

theorem mem_foldl_insert_ids_keep {y : Id} : ∀ (l : List Op) (s : Std.HashSet Id), y ∈ s →
    y ∈ l.foldl (fun (k : Std.HashSet Id) (o : Op) => k.insert o.id) s := by
  intro l
  induction l with
  | nil => intro s h; exact h
  | cons a t ih => intro s h; exact ih _ (Std.HashSet.mem_insert.2 (Or.inr h))

section
variable (fam : Family F) (cfg : Config) (hw : WalkLaws (F := F) fam cfg)
include hw

theorem recv_known (ix : Index) (c : Conn) (b : ByteArray) (now : Nat) (h : Held F) (y : Id) (hy : y ∈ c.known) :
    y ∈ ((Conn.recv fam cfg ix c b now : HeldM F Step).run h).1.conn.known := by
  unfold Conn.recv
  cases hd : Op.decode b with
  | none => exact hy
  | some o =>
    try simp only [hd]
    cases hm : Msg.ofOp o with
    | none =>
      try simp only [hm]
      split
      · exact hy
      · show y ∈ (Conn.finish _).conn.known
        rw [finish_known]
        exact Std.HashSet.mem_insert.2 (Or.inr hy)
    | some m =>
      try simp only [hm]
      cases m with
      | hello f =>
        simp only [HeldM.run_pure, finish_known]
        split
        · unfold Conn.start; split <;> exact hy
        · exact hy
      | rbsr r k cs =>
        simp only [HeldM.run_pure, finish_known]
        unfold Conn.onRbsr
        split
        · exact hy
        · dsimp only
          split
          · exact hy
          · split <;> exact hy
      | hold r ids =>
        simp only [HeldM.run_bind, HeldM.run_pure, finish_known]
        unfold Conn.onHold
        split
        · exact hy
        · simp only [HeldM.run_bind, HeldM.run_pure]
          exact mem_foldl_insert_keep _ _ hy
      | want ids =>
        simp only [HeldM.run_bind, HeldM.run_pure, finish_known]
        unfold Conn.onWant
        split
        · exact hy
        · simp only [HeldM.run_bind, HeldM.run_pure, filterMapM_getOp]
          rw [(hw.same _ _).known]
          exact mem_foldl_insert_ids_keep _ _ hy

end

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

variable (hw : WalkLaws (F := F) fam cfg)
include hw

/-- **One payload keeps every session, and what each knows its peer holds
only grows.** -/
theorem frameStep_known (cid : Id) (now : Nat) (st : (Node × Acts) × Held F) (b : ByteArray) (d : Id) (c : Conn)
    (hd : st.1.1.conn? d = some c) :
    ∃ c', (frameStep fam cfg rms cid now st b).1.1.conn? d = some c' ∧ ∀ y ∈ c.known, y ∈ c'.known := by
  unfold frameStep
  cases hc : st.1.1.conn? cid with
  | none => exact ⟨c, hd, fun y h => h⟩
  | some c0 =>
    dsimp only
    have hdr := recv_drop fam cfg st.1.1.ix (c0.setRooms (rms st.2 cid)) b now st.2
    rw [apply_run fam cfg rms _ _ _ _ _ hdr]
    have hs := setConn_conn st.1.1 cid
      ((Conn.recv fam cfg st.1.1.ix (c0.setRooms (rms st.2 cid)) b now : HeldM F Step).run st.2).1.conn d c hd
    obtain ⟨c', hc', e⟩ := store_known fam cfg rms _ _ false st.2 d _ hs
    refine ⟨c', hc', fun y hy => ?_⟩
    rw [e]
    split
    · rename_i hdc
      subst hdc
      rw [hc] at hd; cases hd
      exact recv_known fam cfg hw _ _ b now st.2 y hy
    · exact hy

theorem frame_fold_known (cid : Id) (now : Nat) : ∀ (l : List ByteArray) (st : (Node × Acts) × Held F) (d : Id)
    (c : Conn), st.1.1.conn? d = some c →
    ∃ c', (l.foldl (frameStep fam cfg rms cid now) st).1.1.conn? d = some c' ∧ ∀ y ∈ c.known, y ∈ c'.known := by
  intro l
  induction l with
  | nil => intro st d c hd; exact ⟨c, hd, fun y h => h⟩
  | cons b t ih =>
    intro st d c hd
    obtain ⟨c1, hc1, k1⟩ := frameStep_known fam cfg rms hw cid now st b d c hd
    obtain ⟨c2, hc2, k2⟩ := ih _ d c1 hc1
    exact ⟨c2, hc2, fun y hy => k2 y (k1 y hy)⟩

end

/-! ## The stream, over a whole entry point -/

section
variable (fam : Family F) (cfg : Config) (rms : Held F → Id → List Id) (hw : WalkLaws (F := F) fam cfg)
include hw

/-- **The stream, one payload:** a payload that stores an op of room r for
the first time offers it on every session that shows r throughout,
unless the session knows its peer holds it. -/
theorem frameStep_offers (cid' : Id) (now : Nat) (st : (Node × Acts) × Held F) (b : ByteArray)
    (ok : NodeOk fam st.1.1 st.2) (cid : Id) (c₀ : Conn) (hc₀ : st.1.1.conn? cid = some c₀) (x : Id) (o : Op) (r : Id)
    (hn : st.2.db.ops x = none) (hs : (frameStep fam cfg rms cid' now st b).2.db.ops x = some o)
    (hor : fam.room o = some r)
    (hrooms : ∀ h', Kept st.2 h' → Kept h' (frameStep fam cfg rms cid' now st b).2 → r ∈ rms h' cid)
    (hmax : 0 < cfg.maxIds) :
    (∃ c, (frameStep fam cfg rms cid' now st b).1.1.conn? cid = some c ∧ x ∈ c.known) ∨
      ∃ L, x ∈ L ∧ (Route.conn cid, (Msg.hold r L).op.bytes) ∈ (frameStep fam cfg rms cid' now st b).1.2.send := by
  unfold frameStep at hs hrooms ⊢
  cases hc' : st.1.1.conn? cid' with
  | none => simp only [hc'] at hs; rw [hn] at hs; cases hs
  | some c' =>
    simp only [hc'] at hs hrooms ⊢
    have hdr := recv_drop fam cfg st.1.1.ix (c'.setRooms (rms st.2 cid')) b now st.2
    have hSs := recv_snaps fam cfg hw st.1.1.ix (c'.setRooms (rms st.2 cid')) b now st.2 ok.sub.1
      ((ok.sub.2 _ (conn_mem hc')).setRooms (rms st.2 cid'))
    have hSo : ∀ y ∈ ((Conn.recv fam cfg st.1.1.ix (c'.setRooms (rms st.2 cid')) b now : HeldM F Step).run st.2).1.conn.offered,
        Named st.2 y := fun y hy => by
      rcases recv_offered fam cfg hw st.1.1.ix (c'.setRooms (rms st.2 cid')) b now st.2 ok.sub.1
        ((ok.sub.2 _ (conn_mem hc')).setRooms (rms st.2 cid')) ok.ids y hy with hy | hy
      · exact ok.offered _ (conn_mem hc') y hy
      · exact hy
    rw [apply_run fam cfg rms _ _ _ _ _ hdr] at hs hrooms ⊢
    have okm := setConn_ok fam _ cid' _ st.2 ok hSs hSo
    have hcm := setConn_conn st.1.1 cid'
      ((Conn.recv fam cfg st.1.1.ix (c'.setRooms (rms st.2 cid')) b now : HeldM F Step).run st.2).1.conn cid c₀ hc₀
    rcases store_offers fam cfg rms _ _ false st.2 okm cid _ hcm x o r hn hs hor hrooms hmax with hk | ⟨L, hxL, hL⟩
    · left
      obtain ⟨cs, hcs, ks⟩ := store_known fam cfg rms _ _ false st.2 cid _ hcm
      exact ⟨cs, hcs, by rw [ks]; exact hk⟩
    · right
      exact ⟨L, hxL, List.mem_append_right _ (List.mem_append_right _ hL)⟩

/-- **The stream, over a session's frame:** an op of room r the frame
stores for the first time is offered on every session that shows r
throughout, in a frame to that session's address, unless the session
knows its peer holds it. -/
theorem frame_offers (n : Node) (h : Held F) (ok : NodeOk fam n h) (a bytes : ByteArray) (now : Nat) (cid' : Id)
    (inner : List ByteArray) (hp : plainPeek bytes = some (cid', inner)) (c' : Conn) (hc' : n.conn? cid' = some c')
    (cid : Id) (c₀ : Conn) (hc₀ : n.conn? cid = some c₀) (x : Id) (o : Op) (r : Id) (hn : h.db.ops x = none)
    (hs : ((n.onFrame (psync fam cfg rms) a bytes now).run h).2.db.ops x = some o) (hor : fam.room o = some r)
    (hrooms : ∀ h', Kept h h' → Kept h' ((n.onFrame (psync fam cfg rms) a bytes now).run h).2 → r ∈ rms h' cid)
    (hmax : 0 < cfg.maxIds) :
    (∃ c, ((n.onFrame (psync fam cfg rms) a bytes now).run h).1.1.conn? cid = some c ∧ x ∈ c.known) ∨
      ∃ g L, x ∈ L ∧ (Msg.hold r L).op.bytes ∈ g ∧ ∀ d, ((n.onFrame (psync fam cfg rms) a bytes now).run h).1.1.addr? cid = some d →
        (d, plainFrame cid g) ∈ ((n.onFrame (psync fam cfg rms) a bytes now).run h).1.2.send := by
  obtain ⟨h0, bundle, hb', hi⟩ := plainFrame_of_peek hp
  rw [onFrame_sealed fam cfg rms hw n a bytes now h cid' bundle inner c' h0 hb' hi hc'] at hs hrooms ⊢
  have ok0 := setAddr_ok fam n cid' a h ok
  have hcids0 : cids (n.setAddr cid' a) = cids n := rfl
  obtain ⟨okE, eE, cE, aE, -⟩ := frame_fold fam cfg rms hw cid' now inner (((n.setAddr cid' a, ({} : Acts)), h)) ok0
  rw [frame_end_store fam cfg rms now _ okE] at hs hrooms
  rw [finish_run fam cfg rms _ _ _ _ okE.managed]
  have h0P : ¬ ((((n.setAddr cid' a, ({} : Acts)), h) : (Node × Acts) × Held F).2.db.ops x).isSome = true := by
    simp [hn]
  obtain ⟨pre, b, post, el, hP1, hP2⟩ := fold_first (frameStep fam cfg rms cid' now)
    (fun st => (st.2.db.ops x).isSome = true) inner _ h0P (by rw [hs]; rfl)
  rw [el, List.foldl_append, List.foldl_cons] at hs hrooms ⊢
  rw [el, List.foldl_append, List.foldl_cons] at okE
  obtain ⟨ok1, e1, c1, -, -⟩ := frame_fold fam cfg rms hw cid' now pre (((n.setAddr cid' a, ({} : Acts)), h)) ok0
  generalize pre.foldl (frameStep fam cfg rms cid' now) (((n.setAddr cid' a, ({} : Acts)), h)) = st1
    at ok1 e1 c1 hP1 hP2 hs hrooms okE ⊢
  obtain ⟨c1c, hc1c⟩ := (conn_iff _ _).2 (by rw [c1, hcids0]; exact (conn_iff _ _).1 ⟨c₀, hc₀⟩)
  obtain ⟨ok2, e2, -, a2, s2⟩ := frameStep_ok fam cfg rms hw cid' now st1 b ok1
  obtain ⟨-, e3, -, a3, s3⟩ := frame_fold fam cfg rms hw cid' now post _ ok2
  have hn1 : st1.2.db.ops x = none := by
    cases e : st1.2.db.ops x with
    | none => rfl
    | some _ => exact absurd (by rw [e]; rfl) hP1
  have hso : (frameStep fam cfg rms cid' now st1 b).2.db.ops x = some o := by
    obtain ⟨o', ho'⟩ := Option.isSome_iff_exists.1 hP2
    have := e3.1 x o' ho'
    rw [hs] at this; cases this; exact ho'
  have hrm : ∀ h', Kept st1.2 h' → Kept h' (frameStep fam cfg rms cid' now st1 b).2 → r ∈ rms h' cid :=
    fun h' k1 k2 => hrooms h' (fun y q hq => k1 y q (e1.1 y q hq)) (fun y q hq => e3.1 y q (k2 y q hq))
  rcases frameStep_offers fam cfg rms hw cid' now st1 b ok1 cid c1c hc1c x o r hn1 hso hor hrm hmax with
    ⟨cs, hcs, hk⟩ | ⟨L, hxL, hL⟩
  · left
    obtain ⟨cE', hcE', kE⟩ := frame_fold_known fam cfg rms hw cid' now post _ cid cs hcs
    exact ⟨cE', hcE', kE x hk⟩
  · right
    have hE := s3 _ hL
    generalize hfin : post.foldl (frameStep fam cfg rms cid' now) (frameStep fam cfg rms cid' now st1 b) = fin at hE okE ⊢
    cases hd0 : fin.1.1.addr? cid with
    | none => exact ⟨[(Msg.hold r L).op.bytes], L, hxL, List.mem_singleton_self _, fun d hd => by
        simp only [Node.addr?] at hd hd0; rw [hd0] at hd; cases hd⟩
    | some d0 =>
      obtain ⟨g, hg, hf⟩ := seal_mem fam cfg rms fin.1.1 fin.1.2 fin.2 cid _ d0 hE hd0
      refine ⟨g, L, hxL, hg, fun d hd => ?_⟩
      have : d = d0 := by simp only [Node.addr?] at hd hd0; rw [hd0] at hd; cases hd; rfl
      subst this; exact hf

end

end Engine.World

