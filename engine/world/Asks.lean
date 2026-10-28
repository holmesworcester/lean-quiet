/-
What a session asks, proven of the running code: everything it asks it
asked before or wanted on the wire in the same frame, and a frame grows
its asks by at most the ids the frame offers. So a have (H4) or a claim
of ids (H1) for an op the node lacks, not asked on the session when the
frame came, is answered with a want in the frame back, when the asks
have room (`have_wants`, `claim_wants`; finding 7).

- `onHold` is read through holmes-a3's `onHold_apply` (OfferLaws).
- **Asks are wants on the wire** (`recv_asked`, `frameStep_asked`,
  `frame_fold_asked`).
- **Asks grow by what is offered** (`recv_asked_size`,
  `frame_fold_asked_size`): a have by its ids, a round by its id claims'
  (`asksOf`).
-/
import engine.world.Hops
import ops.sync.OfferLaws
namespace Engine.World
open Engine Engine.Sync
variable {F : Type}

attribute [local instance] byteArray_lawfulBEq

/-! ## Asks: what a connection has wanted -/

theorem wantStep_mem (fam : Family F) (s : DB F) (c : Conn) (r y : Id) (hy : c.asked.contains y = false)
    (hh : heldIn fam s r y = false) : ∀ (ids acc : List Id), (y ∈ ids ∨ y ∈ acc) →
      y ∈ ids.foldl (wantStep fam s c r) acc := by
  intro ids
  induction ids with
  | nil => intro acc h; rcases h with h | h; cases h; exact h
  | cons a t ih =>
    intro acc h
    apply ih
    rcases h with h | h
    · rcases List.mem_cons.1 h with rfl | h
      · right; simp [wantStep, hy, hh]
      · exact Or.inl h
    · right; unfold wantStep; split <;> (try split) <;> simp [h]

theorem wantStep_sub (fam : Family F) (s : DB F) (c : Conn) (r : Id) : ∀ (ids acc : List Id) y,
    y ∈ ids.foldl (wantStep fam s c r) acc → y ∈ acc ∨ y ∈ ids := by
  intro ids
  induction ids with
  | nil => intro acc y h; exact Or.inl h
  | cons a t ih =>
    intro acc y h
    rcases ih _ y h with h | h
    · unfold wantStep at h
      split at h
      · split at h
        · rcases List.mem_cons.1 h with rfl | h
          · exact Or.inr (List.mem_cons_self ..)
          · exact Or.inl h
        · exact Or.inl h
      · exact Or.inl h
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem wantStep_len (fam : Family F) (s : DB F) (c : Conn) (r : Id) : ∀ (ids acc : List Id),
    (ids.foldl (wantStep fam s c r) acc).length ≤ acc.length + ids.length := by
  intro ids
  induction ids with
  | nil => intro acc; simp
  | cons a t ih =>
    intro acc
    simp only [List.foldl_cons, List.length_cons]
    have h1 := ih (wantStep fam s c r acc a)
    have h2 : (wantStep fam s c r acc a).length ≤ acc.length + 1 := by
      unfold wantStep; split <;> (try split) <;> simp
    omega

/-- **H4, at a connection: a have of an op this side lacks, not yet asked,
is answered with a want for it**, when the have is of at most `maxIds`
ids and the asks have room for them all (finding 7). -/
theorem onHold_wants (fam : Family F) (cfg : Config) (c : Conn) (r : Id) (ids : List Id) (h : Held F) (y : Id)
    (hr : r ∈ c.rooms) (hy : y ∈ ids) (ha : y ∉ c.asked) (hn : h.db.ops y = none) (hmax : 0 < cfg.maxIds)
    (hH : ids.length ≤ cfg.maxIds) (hroom : c.asked.size + ids.length ≤ cfg.maxKnown) :
    ∃ W, y ∈ W ∧ W.length ≤ cfg.maxIds ∧ (Msg.want W).op ∈ ((c.onHold fam cfg r ids : HeldM F Step).run h).1.send := by
  have hc : c.asked.contains y = false := Bool.eq_false_iff.2 fun e => ha (Std.HashSet.mem_iff_contains.2 e)
  have hh : heldIn fam h.db r y = false := by simp [heldIn, hn]
  have hm := wantStep_mem fam h.db c r y hc hh ids [] (Or.inl hy)
  have hl := wantStep_len fam h.db c r ids []
  have hadm := admit_mem cfg.maxKnown c.asked _ y (List.mem_reverse.2 hm) ha
    (by rw [List.length_reverse]; simp only [List.length_nil] at hl; omega)
  obtain ⟨W, hxW, hl, hW⟩ := chunks_cover cfg _ Msg.want hmax hadm
  refine ⟨W, hxW, hl, ?_⟩
  show (Msg.want W).op ∈ ((c.onHold fam cfg r ids : HeldM F Step) h).1.send
  rw [onHold_apply, ite_eq_right (by simp [has_of_mem hr]), ite_eq_right (by omega)]
  simp only [Step.limit_send]
  exact hW

/-- What `onHold` asks it also wants, on the wire. -/
theorem onHold_asked (fam : Family F) (cfg : Config) (c : Conn) (r : Id) (ids : List Id) (h : Held F) (y : Id)
    (hmax : 0 < cfg.maxIds) (hy : y ∈ ((c.onHold fam cfg r ids : HeldM F Step).run h).1.conn.asked) :
    y ∈ c.asked ∨ ∃ W, y ∈ W ∧ W.length ≤ cfg.maxIds ∧ (Msg.want W).op ∈ ((c.onHold fam cfg r ids : HeldM F Step).run h).1.send := by
  change y ∈ ((c.onHold fam cfg r ids : HeldM F Step) h).1.conn.asked at hy
  show y ∈ c.asked ∨ ∃ W, y ∈ W ∧ W.length ≤ cfg.maxIds ∧ (Msg.want W).op ∈ ((c.onHold fam cfg r ids : HeldM F Step) h).1.send
  rw [onHold_apply] at hy ⊢
  by_cases h0 : (!has c.rooms r) = true
  · rw [ite_eq_left h0] at hy; exact Or.inl hy
  · rw [ite_eq_right h0] at hy ⊢
    by_cases h1 : ids.length > cfg.maxIds
    · rw [ite_eq_left h1] at hy; exact Or.inl hy
    · rw [ite_eq_right h1] at hy ⊢
      simp only [Step.limit_send]
      rcases mem_foldl_insert _ _ (Step.limit_asked cfg _ hy) with hy | hy
      · exact Or.inl hy
      · obtain ⟨W, hxW, hl, hW⟩ := chunks_cover cfg _ Msg.want hmax hy
        exact Or.inr ⟨W, hxW, hl, hW⟩

theorem finish_asked (st : Step) : (Conn.finish st).conn.asked = st.conn.asked := by
  unfold Conn.finish Conn.report
  by_cases h : st.conn.asked.isEmpty = true <;> simp [h]

theorem onRbsr_asked (cfg : Config) (ix : Index) (c : Conn) (r : Id) (k : Nat) (cs : List Claim) (now : Nat)
    (y : Id) (hmax : 0 < cfg.maxIds) (hy : y ∈ (c.onRbsr cfg ix r k cs now).conn.asked) :
    y ∈ c.asked ∨ ∃ W, y ∈ W ∧ W.length ≤ cfg.maxIds ∧ (Msg.want W).op ∈ (c.onRbsr cfg ix r k cs now).send := by
  unfold Conn.onRbsr at hy ⊢
  split at hy
  · exact Or.inl hy
  · rename_i h0
    simp only [h0, Bool.false_eq_true, ↓reduceIte] at hy ⊢
    split at hy
    · exact Or.inl hy
    · rename_i h1
      simp only [h1, Bool.false_eq_true, ↓reduceIte, Step.limit_send]
      rcases mem_foldl_insert _ _ (Step.limit_asked cfg _ hy) with hy | hy
      · left
        split at hy <;> exact hy
      · obtain ⟨W, hxW, hl, hW⟩ := chunks_cover cfg _ Msg.want hmax hy
        exact Or.inr ⟨W, hxW, hl, List.mem_cons_of_mem _ (List.mem_append_right _ hW)⟩

section
variable (fam : Family F) (cfg : Config) (hw : WalkLaws (F := F) fam cfg)
include hw

/-- **What a connection asks on what it receives, it wants on the wire.** -/
theorem recv_asked (ix : Index) (c : Conn) (b : ByteArray) (now : Nat) (h : Held F) (y : Id) (hmax : 0 < cfg.maxIds)
    (hy : y ∈ ((Conn.recv fam cfg ix c b now : HeldM F Step).run h).1.conn.asked) :
    y ∈ c.asked ∨ ∃ W, y ∈ W ∧ W.length ≤ cfg.maxIds ∧ (Msg.want W).op ∈ ((Conn.recv fam cfg ix c b now : HeldM F Step).run h).1.send := by
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
      · rename_i h1
        simp only [h1, Bool.false_eq_true, ↓reduceIte, HeldM.run_pure, Conn.finish_send] at hy ⊢
        rw [finish_asked] at hy
        have hy := Step.limit_asked _ _ hy
        rw [Std.HashSet.mem_erase] at hy
        exact Or.inl hy.2
    | some m =>
      simp only [hm] at hy ⊢
      cases m with
      | hello f =>
        simp only [HeldM.run_pure, Conn.finish_send] at hy ⊢
        rw [finish_asked] at hy
        left
        split at hy
        · unfold Conn.start at hy; split at hy <;> exact hy
        · exact hy
      | rbsr r k cs =>
        simp only [HeldM.run_pure, Conn.finish_send] at hy ⊢
        rw [finish_asked] at hy
        exact onRbsr_asked cfg ix _ r k cs now y hmax hy
      | hold r ids =>
        simp only [HeldM.run_bind, HeldM.run_pure, Conn.finish_send] at hy ⊢
        rw [finish_asked] at hy
        exact onHold_asked fam cfg _ r ids h y hmax hy
      | want ids =>
        simp only [HeldM.run_bind, HeldM.run_pure, Conn.finish_send] at hy ⊢
        rw [finish_asked] at hy
        left
        unfold Conn.onWant at hy
        split at hy
        · exact hy
        · simp only [HeldM.run_bind, Read.run_heldW, HeldM.run_pure] at hy
          exact Step.limit_asked _ _ hy

end

/-! ## How many ids a session asks -/

theorem foldl_insert_size : ∀ (l : List Id) (s : Std.HashSet Id), (l.foldl (·.insert ·) s).size ≤ s.size + l.length
  | [], s => by simp
  | a :: t, s => by
    have h1 := foldl_insert_size t (s.insert a)
    have h2 := @Std.HashSet.size_insert_le _ _ _ s _ _ a
    simp only [List.foldl_cons, List.length_cons]; omega

theorem Step.limit_asked_size (cfg : Config) (s : Step) : (s.limit cfg).conn.asked.size ≤ s.conn.asked.size := by
  unfold Step.limit; split
  · exact Nat.le_refl _
  · simp

theorem admitAsks_len (cap : Nat) (asked : Std.HashSet Id) (ids : List Id) :
    (admitAsks cap asked ids).length ≤ ids.length := by
  unfold admitAsks
  have h1 := length_eraseDups_le _ (ids.filter fun i => !asked.contains i) (Nat.le_refl _)
  have h2 := List.length_filter_le (fun i => !asked.contains i) ids
  rw [List.length_take]
  omega


@[simp] theorem asksOf_rbsr (r : Id) (k : Nat) (cs : List Claim) : asksOf (Msg.rbsr r k cs).op.bytes = claimIds cs := by
  simp [asksOf, Op.decode_bytes]

@[simp] theorem asksOf_hold (r : Id) (l : List Id) : asksOf (Msg.hold r l).op.bytes = l := by
  simp [asksOf, Op.decode_bytes, Msg.ofOp, Msg.op, kRbsr, kHave, Codec.decode_encode]

theorem onRbsr_asked_size (cfg : Config) (ix : Index) (c : Conn) (r : Id) (k : Nat) (cs : List Claim) (now : Nat) :
    (c.onRbsr cfg ix r k cs now).conn.asked.size ≤ c.asked.size + (claimIds cs).length := by
  unfold Conn.onRbsr
  split
  · exact Nat.le_add_right _ _
  · dsimp only
    split
    · exact Nat.le_add_right _ _
    · refine Nat.le_trans (Step.limit_asked_size cfg _) ?_
      refine Nat.le_trans (foldl_insert_size _ _) ?_
      refine Nat.le_trans (Nat.add_le_add_left (Nat.le_trans (admitAsks_len _ _ _)
        (answer_wants_len cfg.params _ cs)) _) ?_
      split <;> exact Nat.le_refl _

theorem onHold_asked_size (fam : Family F) (cfg : Config) (c : Conn) (r : Id) (ids : List Id) (h : Held F) :
    ((c.onHold fam cfg r ids : HeldM F Step).run h).1.conn.asked.size ≤ c.asked.size + ids.length := by
  show ((c.onHold fam cfg r ids : HeldM F Step) h).1.conn.asked.size ≤ _
  rw [onHold_apply]
  split
  · exact Nat.le_add_right _ _
  · split
    · exact Nat.le_add_right _ _
    · refine Nat.le_trans (Step.limit_asked_size cfg _) ?_
      refine Nat.le_trans (foldl_insert_size _ _) ?_
      have h1 := admitAsks_len cfg.maxKnown c.asked (ids.foldl (wantStep fam h.db c r) []).reverse
      have h2 := wantStep_len fam h.db c r ids []
      rw [List.length_reverse] at h1
      simp only [List.length_nil, Nat.zero_add] at h2
      omega

theorem recv_asked_size (fam : Family F) (cfg : Config) (ix : Index) (c : Conn) (b : ByteArray) (now : Nat)
    (h : Held F) :
    ((Conn.recv fam cfg ix c b now : HeldM F Step).run h).1.conn.asked.size ≤ c.asked.size + (asksOf b).length := by
  unfold Conn.recv asksOf
  cases hd : Op.decode b with
  | none => simp only [HeldM.run_pure]; exact Nat.le_add_right _ _
  | some o =>
    simp only
    cases hm : Msg.ofOp o with
    | none =>
      simp only
      split
      · exact Nat.le_add_right _ _
      · simp only [HeldM.run_pure]
        rw [finish_asked]
        refine Nat.le_trans (Step.limit_asked_size cfg _) ?_
        exact Nat.le_trans Std.HashSet.size_erase_le (Nat.le_add_right _ _)
    | some m =>
      cases m with
      | hello f =>
        simp only [HeldM.run_pure]
        rw [finish_asked]
        split
        · unfold Conn.start; split <;> exact Nat.le_add_right _ _
        · exact Nat.le_add_right _ _
      | rbsr r k cs =>
        simp only [HeldM.run_pure]
        rw [finish_asked]
        exact onRbsr_asked_size cfg ix _ r k cs now
      | hold r ids =>
        simp only [HeldM.run_bind, HeldM.run_pure]
        rw [finish_asked]
        exact onHold_asked_size fam cfg _ r ids h
      | want ids =>
        simp only [HeldM.run_bind, HeldM.run_pure]
        rw [finish_asked]
        unfold Conn.onWant
        split
        · exact Nat.le_add_right _ _
        · simp only [HeldM.run_bind, Read.run_heldW, HeldM.run_pure]
          exact Nat.le_trans (Step.limit_asked_size cfg _) (Nat.le_add_right _ _)

theorem filed_asked (fam : Family F) (cfg : Config) (c : Conn) (ids : List Id) (h : Held F) :
    ((c.filed fam cfg ids : HeldM F Step).run h).1.conn.asked = c.asked := by
  unfold Conn.filed
  simp only [HeldM.run_bind, HeldM.run_pure, finish_asked]
  apply forIn_inv _ _ (fun st : List (Id × Id) × Conn => st.2.asked = c.asked)
  · intro i st h' hs
    obtain ⟨off, c'⟩ := st
    dsimp only at hs ⊢
    split
    · simp only [HeldM.run_bind]
      split
      · split <;> exact hs
      · exact hs
    · exact hs
  · rfl

theorem conn_map (n : Node) (cid : Id) (g : Id × Conn → Conn) (c : Conn) (hc : n.conn? cid = some c) :
    ({ n with conns := n.conns.map fun p => (p.1, g p) } : Node).conn? cid = some (g (cid, c)) := by
  unfold Node.conn? at hc ⊢
  rw [find_map_fst (fun p => (p.1, g p)) (fun _ => rfl)]
  cases e : n.conns.find? (fun p => Decidable.decide (p.1 = cid)) with
  | none => rw [e] at hc; cases hc
  | some p =>
    rw [e] at hc
    have hp := List.find?_some e
    simp only [decide_eq_true_eq] at hp
    simp only [Option.map_some, Option.some.injEq] at hc
    have : p = (cid, c) := Prod.ext hp hc
    subst this; rfl

section
variable (fam : Family F) (cfg : Config) (rms : Held F → Id → List Id)

/-- After a step on session cid that does not drop it, the session's
connection asks exactly what the step's does. -/
theorem apply_asked (n : Node) (cid : Id) (s : Step) (now : Nat) (h : Held F) (hd : s.drop = false) (c₀ : Conn)
    (hc : n.conn? cid = some c₀) :
    ∃ c', ((n.apply (psync fam cfg rms) cid s now).run h).1.1.conn? cid = some c' ∧ c'.asked = s.conn.asked := by
  rw [apply_run fam cfg rms _ _ _ _ _ hd, store_run]
  have hset : (setConn n cid s.conn).conn? cid = some s.conn := by
    have := conn_map n cid (fun p => if p.1 = cid then s.conn else p.2) c₀ hc
    simp only [↓reduceIte] at this
    unfold setConn
    rw [← this]
    congr 2
    apply List.map_congr_left
    intro p _
    split <;> simp_all
  simp only [Node.put, psync_fam]
  have wn := write_node fam cfg rms (setConn n cid s.conn) (intake fam false s.take) h
  have hw : (((setConn n cid s.conn).write (psync fam cfg rms) (intake fam false s.take)).run h).1.1.conn? cid =
      some s.conn := by
    unfold Node.conn?; rw [wn.1]; exact hset
  by_cases he : (((setConn n cid s.conn).write (psync fam cfg rms) (intake fam false s.take)).run h).1.2.isEmpty = true
  · simp only [he, ↓reduceIte]; exact ⟨_, hw, rfl⟩
  · simp only [he, ↓reduceIte, Bool.false_eq_true]
    generalize ((setConn n cid s.conn).write (psync fam cfg rms) (intake fam false s.take)).run h = W at hw ⊢
    obtain ⟨-, -, -, -, e5⟩ := fanout_node fam cfg rms W.1.1 W.1.2 W.2
    have := conn_map W.1.1 cid
      (fun p => ((Conn.filed fam cfg (p.2.setRooms (rms W.2 p.1)) W.1.2 : HeldM F Step).run W.2).1.conn) s.conn hw
    refine ⟨_, by unfold Node.conn? at this ⊢; rw [e5]; exact this, ?_⟩
    rw [filed_asked]; rfl

variable (hw : WalkLaws (F := F) fam cfg)
include hw

/-- **One payload asks on session cid only what it wants on cid.** -/
theorem frameStep_asked (cid : Id) (now : Nat) (st : (Node × Acts) × Held F) (b : ByteArray) (y : Id)
    (hmax : 0 < cfg.maxIds) (c' : Conn) (hc' : (frameStep fam cfg rms cid now st b).1.1.conn? cid = some c')
    (hy : y ∈ c'.asked) :
    (∃ c, st.1.1.conn? cid = some c ∧ y ∈ c.asked) ∨
      ∃ W, y ∈ W ∧ W.length ≤ cfg.maxIds ∧ (Route.conn cid, (Msg.want W).op.bytes) ∈ (frameStep fam cfg rms cid now st b).1.2.send := by
  unfold frameStep at hc' ⊢
  cases hc : st.1.1.conn? cid with
  | none => simp only [hc] at hc'; cases hc'
  | some c =>
    simp only [hc] at hc' ⊢
    have hd := recv_drop fam cfg st.1.1.ix (c.setRooms (rms st.2 cid)) b now st.2
    obtain ⟨c'', hc'', e⟩ := apply_asked fam cfg rms st.1.1 cid _ now st.2 hd c hc
    rw [hc''] at hc'; cases hc'
    rw [e] at hy
    rcases recv_asked fam cfg hw st.1.1.ix (c.setRooms (rms st.2 cid)) b now st.2 y hmax hy with h1 | ⟨W, hxW, hl, hW⟩
    · exact Or.inl ⟨c, rfl, h1⟩
    · right
      refine ⟨W, hxW, hl, ?_⟩
      rw [apply_run fam cfg rms _ _ _ _ _ hd]
      apply List.mem_append_right
      apply List.mem_append_left
      exact List.mem_map.2 ⟨_, hW, rfl⟩

end

@[simp] theorem ofOp_have (r : Id) (l : List Id) : Msg.ofOp (Msg.hold r l).op = some (.hold r l) := by
  simp [Msg.ofOp, Msg.op, kRbsr, kHave, Codec.decode_encode]

theorem recv_have (fam : Family F) (cfg : Config) (ix : Index) (c : Conn) (r : Id) (l : List Id) (now : Nat)
    (h : Held F) :
    ((Conn.recv fam cfg ix c (Msg.hold r l).op.bytes now : HeldM F Step).run h).1 =
      Conn.finish (((({ c with heard := now } : Conn).onHold fam cfg r l : HeldM F Step).run h).1) := by
  simp [Conn.recv, Op.decode_bytes]

section
variable (fam : Family F) (cfg : Config) (rms : Held F → Id → List Id)

/-- **H4, one payload: a have of an op the store lacks, not yet asked on the
session, is answered with a want for it.** -/
theorem have_step (cid : Id) (now : Nat) (st : (Node × Acts) × Held F) (c : Conn)
    (hc : st.1.1.conn? cid = some c) (r : Id) (H : List Id) (y : Id) (hr : r ∈ rms st.2 cid) (hy : y ∈ H)
    (ha : y ∉ c.asked) (hn : st.2.db.ops y = none) (hmax : 0 < cfg.maxIds) (hH : H.length ≤ cfg.maxIds)
    (hroom : c.asked.size + H.length ≤ cfg.maxKnown) :
    ∃ W, y ∈ W ∧ W.length ≤ cfg.maxIds ∧
      (Route.conn cid, (Msg.want W).op.bytes) ∈ (frameStep fam cfg rms cid now st (Msg.hold r H).op.bytes).1.2.send := by
  obtain ⟨W, hxW, hl, hm⟩ := onHold_wants fam cfg ({ c.setRooms (rms st.2 cid) with heard := now } : Conn) r H st.2 y
    hr hy (fun e => ha (by simpa [Conn.setRooms] using e)) hn hmax hH (by simpa [Conn.setRooms] using hroom)
  refine ⟨W, hxW, hl, ?_⟩
  unfold frameStep
  rw [hc]; dsimp only
  have hd := recv_drop fam cfg st.1.1.ix (c.setRooms (rms st.2 cid)) (Msg.hold r H).op.bytes now st.2
  rw [apply_run fam cfg rms _ _ _ _ _ hd, recv_have]
  apply List.mem_append_right
  apply List.mem_append_left
  exact List.mem_map.2 ⟨_, hm, rfl⟩

variable (hw : WalkLaws (F := F) fam cfg)
include hw

/-- Through a frame's payloads: what session cid asks it asked before, or
wanted on the wire in this frame. -/
theorem frame_fold_asked (cid : Id) (now : Nat) (y : Id) (hmax : 0 < cfg.maxIds) :
    ∀ (l : List ByteArray) (st : (Node × Acts) × Held F), NodeOk fam st.1.1 st.2 → ∀ c',
      (l.foldl (frameStep fam cfg rms cid now) st).1.1.conn? cid = some c' → y ∈ c'.asked →
      (∃ c, st.1.1.conn? cid = some c ∧ y ∈ c.asked) ∨
        ∃ W, y ∈ W ∧ W.length ≤ cfg.maxIds ∧ (Route.conn cid, (Msg.want W).op.bytes) ∈ (l.foldl (frameStep fam cfg rms cid now) st).1.2.send := by
  intro l
  induction l with
  | nil => intro st _ c' hc' hy; exact Or.inl ⟨c', hc', hy⟩
  | cons b t ih =>
    intro st ok c' hc' hy
    obtain ⟨ok1, -, -, -, s1⟩ := frameStep_ok fam cfg rms hw cid now st b ok
    rcases ih _ ok1 c' hc' hy with ⟨c1, hc1, hy1⟩ | ⟨W, hxW, hl, hW⟩
    · rcases frameStep_asked fam cfg rms hw cid now st b y hmax c1 hc1 hy1 with h | ⟨W, hxW, hl, hW⟩
      · exact Or.inl h
      · right
        exact ⟨W, hxW, hl, (frame_fold fam cfg rms hw cid now t _ ok1).2.2.2.2 _ hW⟩
    · exact Or.inr ⟨W, hxW, hl, hW⟩

omit hw in
/-- One payload grows what session cid asks by at most the ids it offers. -/
theorem frameStep_asked_size (cid : Id) (now : Nat) (st : (Node × Acts) × Held F) (b : ByteArray) (c c' : Conn)
    (hc : st.1.1.conn? cid = some c) (hc' : (frameStep fam cfg rms cid now st b).1.1.conn? cid = some c') :
    c'.asked.size ≤ c.asked.size + (asksOf b).length := by
  unfold frameStep at hc'
  simp only [hc] at hc'
  have hd := recv_drop fam cfg st.1.1.ix (c.setRooms (rms st.2 cid)) b now st.2
  obtain ⟨c'', hc'', e⟩ := apply_asked fam cfg rms st.1.1 cid _ now st.2 hd c hc
  rw [hc''] at hc'; cases hc'
  rw [e]
  simpa [Conn.setRooms] using recv_asked_size fam cfg st.1.1.ix (c.setRooms (rms st.2 cid)) b now st.2

/-- Through a frame's payloads, session cid asks at most the ids they offer
beyond what it asked. -/
theorem frame_fold_asked_size (cid : Id) (now : Nat) : ∀ (l : List ByteArray) (st : (Node × Acts) × Held F),
    NodeOk fam st.1.1 st.2 → ∀ c, st.1.1.conn? cid = some c → ∀ c',
      (l.foldl (frameStep fam cfg rms cid now) st).1.1.conn? cid = some c' →
      c'.asked.size ≤ c.asked.size + (l.flatMap asksOf).length := by
  intro l
  induction l with
  | nil => intro st _ c hc c' hc'; simp only [List.foldl_nil] at hc'; rw [hc] at hc'; cases hc'; simp
  | cons b t ih =>
    intro st ok c hc c' hc'
    obtain ⟨ok1, -, c1, -, -⟩ := frameStep_ok fam cfg rms hw cid now st b ok
    obtain ⟨c1', hc1⟩ := (conn_iff _ _).2 (by rw [c1]; exact (conn_iff _ _).1 ⟨c, hc⟩)
    have h1 := frameStep_asked_size fam cfg rms cid now st b c c1' hc hc1
    have h2 := ih _ ok1 c1' hc1 c' hc'
    simp only [List.flatMap_cons, List.length_append]
    omega

/-- **H4: a have, delivered, of an op the node lacks and has not asked for
on the session, is answered with a want for it**, in a frame back to the
have's sender; or the node holds it by the frame's end. -/
theorem have_wants (n : Node) (h : Held F) (ok : NodeOk fam n h) (a bytes : ByteArray) (now : Nat) (cid : Id)
    (inner : List ByteArray) (hp : plainPeek bytes = some (cid, inner)) (c : Conn) (hc : n.conn? cid = some c)
    (r : Id) (hr : ∀ h', r ∈ rms h' cid) (H : List Id) (y : Id)
    (hb : (Msg.hold r H).op.bytes ∈ inner) (hy : y ∈ H) (ha : y ∉ c.asked) (hmax : 0 < cfg.maxIds)
    (hH : H.length ≤ cfg.maxIds) (hroom : c.asked.size + (inner.flatMap asksOf).length ≤ cfg.maxKnown) :
    Named ((n.onFrame (psync fam cfg rms) a bytes now).run h).2 y ∨
      ∃ W g, y ∈ W ∧ W.length ≤ cfg.maxIds ∧ (Msg.want W).op.bytes ∈ g ∧
        (a, plainFrame cid g) ∈ ((n.onFrame (psync fam cfg rms) a bytes now).run h).1.2.send := by
  obtain ⟨h0, bundle, hb', hi⟩ := plainFrame_of_peek hp
  rw [onFrame_fold fam cfg rms hw n a bytes now h cid bundle inner c h0 hb' hi hc]
  have ok0 := setAddr_ok fam n cid a h ok
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hb
  rw [List.foldl_append, List.foldl_cons]
  simp only [List.flatMap_append, List.flatMap_cons, List.length_append, asksOf_hold] at hroom
  obtain ⟨ok1, e1, c1, a1, -⟩ := frame_fold fam cfg rms hw cid now pre ((n.setAddr cid a, {}), h) ok0
  have hask := frame_fold_asked fam cfg rms hw cid now y hmax pre ((n.setAddr cid a, {}), h) ok0
  have hsize := frame_fold_asked_size fam cfg rms hw cid now pre ((n.setAddr cid a, {}), h) ok0 c hc
  generalize pre.foldl (frameStep fam cfg rms cid now) ((n.setAddr cid a, {}), h) = st1 at ok1 e1 c1 a1 hask hsize
  obtain ⟨c1', hc1⟩ := (conn_iff _ _).2 (by rw [c1]; exact (conn_iff _ _).1 ⟨c, hc⟩)
  obtain ⟨ok2, e2, -, a2, s2⟩ := frameStep_ok fam cfg rms hw cid now st1 (Msg.hold r H).op.bytes ok1
  obtain ⟨ok3, e3, -, a3, s3⟩ := frame_fold fam cfg rms hw cid now post _ ok2
  have ha3 : (post.foldl (frameStep fam cfg rms cid now) (frameStep fam cfg rms cid now st1
      (Msg.hold r H).op.bytes)).1.1.addr? cid = some a := by
    unfold Node.addr?; rw [a3, a2, a1]; exact setAddr_addr n cid a
  by_cases hn : Named st1.2 y
  · left
    rw [frame_end_store fam cfg rms now _ ok3]
    exact (hn.ext e2).ext e3
  · right
    have hwant : ∃ W, y ∈ W ∧ W.length ≤ cfg.maxIds ∧
        (Route.conn cid, (Msg.want W).op.bytes) ∈ (frameStep fam cfg rms cid now st1 (Msg.hold r H).op.bytes).1.2.send := by
      by_cases hy1 : y ∈ c1'.asked
      · rcases hask c1' hc1 hy1 with ⟨c0, hc0, hy0⟩ | ⟨W, hxW, hl, hW⟩
        · exfalso
          have h1 : (n.setAddr cid a).conn? cid = n.conn? cid := rfl
          simp only at hc0
          rw [h1, hc] at hc0; cases hc0
          exact ha hy0
        · exact ⟨W, hxW, hl, s2 _ hW⟩
      · have hn' : st1.2.db.ops y = none := by
          cases e : st1.2.db.ops y with
          | none => rfl
          | some _ => exact absurd (by unfold Named; rw [e]; rfl) hn
        have hs := hsize c1' hc1
        obtain ⟨W, hxW, hl, hm⟩ := have_step fam cfg rms cid now st1 c1' hc1 r H y (hr _) hy hy1 hn' hmax hH
          (by omega)
        exact ⟨W, hxW, hl, hm⟩
    obtain ⟨W, hxW, hl, hW⟩ := hwant
    obtain ⟨g, hg, hf⟩ := frame_end fam cfg rms cid now _ ok3 a _ ha3 (s3 _ hW)
    exact ⟨W, g, hxW, hl, hg, hf⟩

/-- **H1: a claim of ids, delivered, is answered with a want** for each
id it lists that the node lacks and has not asked for on the session, in
a frame back to the claim's sender, when the session's asks have room for
the ids the frame offers (finding 7); or the node holds it by the frame's
end. -/
theorem claim_wants (n : Node) (h : Held F) (ok : NodeOk fam n h) (a bytes : ByteArray) (now : Nat) (cid : Id)
    (inner : List ByteArray) (hp : plainPeek bytes = some (cid, inner)) (c : Conn) (hc : n.conn? cid = some c)
    (r : Id) (hr : ∀ h', r ∈ rms h' cid) (kr : Nat) (cs : List Claim) (rg : Range) (L : List Id) (x : Id)
    (hb : (Msg.rbsr r kr cs).op.bytes ∈ inner) (hcs : Claim.ids rg L ∈ cs) (hx : x ∈ L) (hmax : 0 < cfg.maxIds)
    (ha : x ∉ c.asked) (hroom : c.asked.size + (inner.flatMap asksOf).length ≤ cfg.maxKnown) :
    Named ((n.onFrame (psync fam cfg rms) a bytes now).run h).2 x ∨
      ∃ W g, x ∈ W ∧ W.length ≤ cfg.maxIds ∧ (Msg.want W).op.bytes ∈ g ∧
        (a, plainFrame cid g) ∈ ((n.onFrame (psync fam cfg rms) a bytes now).run h).1.2.send := by
  obtain ⟨h0, bundle, hb', hi⟩ := plainFrame_of_peek hp
  rw [onFrame_fold fam cfg rms hw n a bytes now h cid bundle inner c h0 hb' hi hc]
  have ok0 := setAddr_ok fam n cid a h ok
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hb
  rw [List.foldl_append, List.foldl_cons]
  simp only [List.flatMap_append, List.flatMap_cons, List.length_append, asksOf_rbsr] at hroom
  obtain ⟨ok1, e1, c1, a1, -⟩ := frame_fold fam cfg rms hw cid now pre ((n.setAddr cid a, {}), h) ok0
  have hask := frame_fold_asked fam cfg rms hw cid now x hmax pre ((n.setAddr cid a, {}), h) ok0
  have hsize := frame_fold_asked_size fam cfg rms hw cid now pre ((n.setAddr cid a, {}), h) ok0 c hc
  generalize pre.foldl (frameStep fam cfg rms cid now) ((n.setAddr cid a, {}), h) = st1 at ok1 e1 c1 a1 hask hsize
  obtain ⟨c1', hc1⟩ := (conn_iff _ _).2 (by rw [c1]; exact (conn_iff _ _).1 ⟨c, hc⟩)
  obtain ⟨ok2, e2, -, a2, s2⟩ := frameStep_ok fam cfg rms hw cid now st1 (Msg.rbsr r kr cs).op.bytes ok1
  obtain ⟨ok3, e3, -, a3, s3⟩ := frame_fold fam cfg rms hw cid now post _ ok2
  have ha3 : (post.foldl (frameStep fam cfg rms cid now) (frameStep fam cfg rms cid now st1
      (Msg.rbsr r kr cs).op.bytes)).1.1.addr? cid = some a := by
    unfold Node.addr?; rw [a3, a2, a1]; exact setAddr_addr n cid a
  by_cases hn : Named st1.2 x
  · left
    rw [frame_end_store fam cfg rms now _ ok3]
    exact (hn.ext e2).ext e3
  · right
    have hwant : ∃ W, x ∈ W ∧ W.length ≤ cfg.maxIds ∧
        (Route.conn cid, (Msg.want W).op.bytes) ∈ (frameStep fam cfg rms cid now st1 (Msg.rbsr r kr cs).op.bytes).1.2.send := by
      by_cases hx1 : x ∈ c1'.asked
      · rcases hask c1' hc1 hx1 with ⟨c0, hc0, hx0⟩ | ⟨W, hxW, hl, hW⟩
        · exfalso
          have h1 : (n.setAddr cid a).conn? cid = n.conn? cid := rfl
          simp only at hc0
          rw [h1, hc] at hc0; cases hc0
          exact ha hx0
        · exact ⟨W, hxW, hl, s2 _ hW⟩
      · have hs := hsize c1' hc1
        exact claim_step fam cfg rms cid now st1 ok1 c1' hc1 r kr cs rg L x (hr _) hcs hx hmax hn hx1 (by omega)
    obtain ⟨W, hxW, hl, hW⟩ := hwant
    obtain ⟨g, hg, hf⟩ := frame_end fam cfg rms cid now _ ok3 a _ ha3 (s3 _ hW)
    exact ⟨W, g, hxW, hl, hg, hf⟩

end

end Engine.World
