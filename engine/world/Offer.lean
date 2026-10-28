/-
An offer delivers, proven of the running code (`offer_delivers`): a have
of room r naming y, from j to i on a joined session, gets y to i within
3Δ, provided y is not already asked on i's side while the have is in
flight. The stream, a round's reverse leg and closure offers all end
with such a have, so each of them is this law plus the step that sends
the have.

- **H4** (`have_step`, `have_wants`): a have of an op the node lacks and
  has not asked for is answered with a want, over frames of any payloads.
  It reads `onHold` through holmes-a3's `onHold_apply` (OfferLaws).
- **Asks are wants on the wire** (`recv_asked`, `frameStep_asked`,
  `frame_fold_asked`): whatever a session asks during a frame, it asked
  before or wanted in that frame. So an ask that was not there when the
  frame came was answered by a want in it.
- Then H2 (`want_sends`) and H3 (`op_taken`) carry y back, as in the
  pilot.
-/
import engine.world.Pilot
import ops.sync.OfferLaws
namespace Engine.World
open Engine Engine.Sync
variable {F : Type}

attribute [local instance] byteArray_lawfulBEq

/-! ## Asks: what a connection has wanted -/

theorem mem_foldl_insert {y : Id} : ∀ (l : List Id) (s : Std.HashSet Id),
    y ∈ l.foldl (·.insert ·) s → y ∈ s ∨ y ∈ l := by
  intro l
  induction l with
  | nil => intro s h; exact Or.inl h
  | cons a t ih =>
    intro s h
    rcases ih _ h with h | h
    · rw [Std.HashSet.mem_insert] at h
      rcases h with e | h
      · exact Or.inr (by rw [show a = y from eq_of_beq e]; exact List.mem_cons_self ..)
      · exact Or.inl h
    · exact Or.inr (List.mem_cons_of_mem _ h)

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

/-- **H4, at a connection: a have of an op this side lacks, not yet asked,
is answered with a want for it.** -/
theorem onHold_wants (fam : Family F) (cfg : Config) (c : Conn) (r : Id) (ids : List Id) (h : Held F) (y : Id)
    (hr : r ∈ c.rooms) (hy : y ∈ ids) (ha : y ∉ c.asked) (hn : h.db.ops y = none) (hmax : 0 < cfg.maxIds) :
    ∃ W, y ∈ W ∧ W.length ≤ cfg.maxIds ∧ (Msg.want W).op ∈ ((c.onHold fam cfg r ids : HeldM F Step).run h).1.send := by
  have hc : c.asked.contains y = false := Bool.eq_false_iff.2 fun e => ha (Std.HashSet.mem_iff_contains.2 e)
  have hh : heldIn fam h.db r y = false := by simp [heldIn, hn]
  have hm := wantStep_mem fam h.db c r y hc hh ids [] (Or.inl hy)
  obtain ⟨W, hxW, hl, hW⟩ := chunks_cover cfg _ Msg.want hmax (List.mem_reverse.2 hm)
  refine ⟨W, hxW, hl, ?_⟩
  show (Msg.want W).op ∈ ((c.onHold fam cfg r ids : HeldM F Step) h).1.send
  rw [onHold_apply]
  simp only [has_of_mem hr, Bool.not_true, Bool.false_eq_true, ite_false]
  exact hW

/-- What `onHold` asks it also wants, on the wire. -/
theorem onHold_asked (fam : Family F) (cfg : Config) (c : Conn) (r : Id) (ids : List Id) (h : Held F) (y : Id)
    (hmax : 0 < cfg.maxIds) (hy : y ∈ ((c.onHold fam cfg r ids : HeldM F Step).run h).1.conn.asked) :
    y ∈ c.asked ∨ ∃ W, y ∈ W ∧ W.length ≤ cfg.maxIds ∧ (Msg.want W).op ∈ ((c.onHold fam cfg r ids : HeldM F Step).run h).1.send := by
  change y ∈ ((c.onHold fam cfg r ids : HeldM F Step) h).1.conn.asked at hy
  show y ∈ c.asked ∨ ∃ W, y ∈ W ∧ W.length ≤ cfg.maxIds ∧ (Msg.want W).op ∈ ((c.onHold fam cfg r ids : HeldM F Step) h).1.send
  rw [onHold_apply] at hy ⊢
  split at hy
  · exact Or.inl hy
  · rename_i h0
    simp only [h0, ↓reduceIte]
    rcases mem_foldl_insert _ _ hy with hy | hy
    · exact Or.inl hy
    · obtain ⟨W, hxW, hl, hW⟩ := chunks_cover cfg _ Msg.want hmax (List.mem_reverse.2 hy)
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
      simp only [h1, Bool.false_eq_true, ↓reduceIte]
      rcases mem_foldl_insert _ _ hy with hy | hy
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
        · simp only [HeldM.run_bind, HeldM.run_pure] at hy
          rw [(hw.same _ _).asked] at hy
          exact hy

end

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
    (ha : y ∉ c.asked) (hn : st.2.db.ops y = none) (hmax : 0 < cfg.maxIds) :
    ∃ W, y ∈ W ∧ W.length ≤ cfg.maxIds ∧
      (Route.conn cid, (Msg.want W).op.bytes) ∈ (frameStep fam cfg rms cid now st (Msg.hold r H).op.bytes).1.2.send := by
  obtain ⟨W, hxW, hl, hm⟩ := onHold_wants fam cfg ({ c.setRooms (rms st.2 cid) with heard := now } : Conn) r H st.2 y
    hr hy (fun e => ha (by simpa [Conn.setRooms] using e)) hn hmax
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

/-- **H4: a have, delivered, of an op the node lacks and has not asked for
on the session, is answered with a want for it**, in a frame back to the
have's sender; or the node holds it by the frame's end. -/
theorem have_wants (n : Node) (h : Held F) (ok : NodeOk fam n h) (a bytes : ByteArray) (now : Nat) (cid : Id)
    (inner : List ByteArray) (hp : plainPeek bytes = some (cid, inner)) (c : Conn) (hc : n.conn? cid = some c)
    (r : Id) (hr : ∀ h', r ∈ rms h' cid) (H : List Id) (y : Id)
    (hb : (Msg.hold r H).op.bytes ∈ inner) (hy : y ∈ H) (ha : y ∉ c.asked) (hmax : 0 < cfg.maxIds) :
    Named ((n.onFrame (psync fam cfg rms) a bytes now).run h).2 y ∨
      ∃ W g, y ∈ W ∧ W.length ≤ cfg.maxIds ∧ (Msg.want W).op.bytes ∈ g ∧
        (a, plainFrame cid g) ∈ ((n.onFrame (psync fam cfg rms) a bytes now).run h).1.2.send := by
  obtain ⟨h0, bundle, hb', hi⟩ := plainFrame_of_peek hp
  rw [onFrame_sealed fam cfg rms hw n a bytes now h cid bundle inner c h0 hb' hi hc]
  have ok0 := setAddr_ok fam n cid a h ok
  obtain ⟨pre, post, e⟩ := fold_at (frameStep fam cfg rms cid now) inner _ hb ((n.setAddr cid a, {}), h)
  rw [e]
  obtain ⟨ok1, e1, c1, a1, -⟩ := frame_fold fam cfg rms hw cid now pre ((n.setAddr cid a, {}), h) ok0
  have hask := frame_fold_asked fam cfg rms hw cid now y hmax pre ((n.setAddr cid a, {}), h) ok0
  generalize pre.foldl (frameStep fam cfg rms cid now) ((n.setAddr cid a, {}), h) = st1 at ok1 e1 c1 a1 hask
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
        obtain ⟨W, hxW, hl, hm⟩ := have_step fam cfg rms cid now st1 c1' hc1 r H y (hr _) hy hy1 hn' hmax
        exact ⟨W, hxW, hl, hm⟩
    obtain ⟨W, hxW, hl, hW⟩ := hwant
    obtain ⟨g, hg, hf⟩ := frame_end fam cfg rms cid now _ ok3 a _ ha3 (s3 _ hW)
    exact ⟨W, g, hxW, hl, hg, hf⟩

end

theorem joined_conns {F : Type} {Q : Plain F} {E : Q.Run} {i j : Fin Q.n} {cid : Id} {k : Nat}
    (hJ : Joined E i j cid k ∨ Joined E j i cid k) (k' : Nat) (hk : k ≤ k') :
    (∃ c, ((E.world k').node i).conn? cid = some c) ∧ (∃ c, ((E.world k').node j).conn? cid = some c) := by
  rcases hJ with hJ | hJ
  · obtain ⟨⟨c, hc, -⟩, ⟨c', hc', -⟩, -⟩ := hJ k' hk
    exact ⟨⟨c, hc⟩, ⟨c', hc'⟩⟩
  · obtain ⟨⟨c, hc, -⟩, ⟨c', hc', -⟩, -⟩ := hJ k' hk
    exact ⟨⟨c', hc'⟩, ⟨c, hc⟩⟩

/-- **An offer delivers, proven of the running code.** The have arrives
within Δ and i wants y unless it has it (`have_wants`); the want arrives
within Δ and j sends y (`want_sends`); y arrives within Δ and i stores it
(`op_taken`). -/
theorem offer_delivers : offer_delivers_stmt := by
  intro F Q N E W i j cid r k q qs H y hf hG hJ hgst hlive hrooms hq hsrc hdst hpeek hhave hyH hy hnask
  have wl := walk_proof F Q.fam Q.cfg
  have hok : ∀ m l, NodeOk Q.fam ((E.world m).node l) ((E.world m).box l) := fun m =>
    reach_ok Q wl noAdv _ (E.reachable m)
  have hfl : ∀ m, FlightOk Q (E.world m) := fun m => reach_flight Q noAdv _ (E.reachable m)
  have hmax := hf.ok.maxIds
  have atj : Q.setup.at? (Q.addr j) = some j := at_addr Q hf.ok j
  have ati : Q.setup.at? (Q.addr i) = some i := at_addr Q hf.ok i
  have grow : ∀ l m m', m ≤ m' → Q.Holds (E.world m) l r y → Q.Holds (E.world m') l r y := fun l m m' hle h =>
    held_on E (fun m hm => grows_all F Q noAdv _ _ l r y (E.reachable m) (E.legal m) hm) m m' hle h
  have hsentk : q.sent ≤ (E.world k).now := (hfl k q hq).1
  have horig : q.origin = Q.addr j := (hfl k q hq).2 j hsrc
  -- The have arrives at i.
  obtain ⟨k1, idx1, t1, hk1, hact1, hfl1, ht1⟩ := hf.net.timely k q j i hq hsrc (by rw [hdst]; exact ati) hG hgst
    (hlive.mono (Nat.le_refl _) (by omega))
  have hle1 : (E.world k1).now ≤ t1 := by have := E.legal k1; rw [hact1] at this; exact this.2
  have hk1now := Exec.now_mono E hk1
  have e1 : E.world (k1 + 1) = (E.world k1).step Q.setup (.deliver idx1 t1) := by rw [← hact1]; rfl
  obtain ⟨n1, b1, now1, sent1⟩ := deliver_at Q (E.world k1) idx1 t1 q i hfl1 (by rw [hdst]; exact ati)
  obtain ⟨⟨c1, hc1⟩, -⟩ := joined_conns hJ k1 hk1
  have hq1 : q ∈ (E.world k1).flight := List.mem_of_getElem? hfl1
  rcases have_wants Q.fam Q.cfg (Q.rooms i) wl _ _ (hok k1 i) q.origin q.bytes t1 cid qs hpeek c1 hc1 r
      (fun h' => (hrooms h').1) H y hhave hyH (hnask k1 c1 hk1 hq1 hc1) hmax with hn | ⟨Wn, g, hxW, hWl, hWg, hsend⟩
  · refine ⟨k1 + 1, by omega, by rw [e1, now1]; omega, ?_⟩
    apply holds_named Q _ (hf.unclashed (k1 + 1)) j i r y (grow j k (k1 + 1) (by omega) hy)
    rw [e1, b1]; exact hn
  · -- The want goes back to j.
    obtain ⟨s1, hq'⟩ := sent1 _ _ hsend
    rw [← e1, horig] at hq'
    obtain ⟨k2, idx2, t2, hk2, hact2, hfl2, ht2⟩ := hf.net.timely (k1 + 1) _ i j hq' rfl atj (hf.symm j i hG)
      (show N.gst ≤ t1 by omega)
      ((hlive.mono (show q.sent ≤ t1 by omega) (show t1 + N.Δ ≤ q.sent + 3 * N.Δ by omega)).symm)
    simp only at ht2
    have hnow1 : (E.world (k1 + 1)).now = t1 := by rw [e1, now1]
    have hk2now := Exec.now_mono E hk2
    have hle2 : (E.world k2).now ≤ t2 := by have := E.legal k2; rw [hact2] at this; exact this.2
    have e2 : E.world (k2 + 1) = (E.world k2).step Q.setup (.deliver idx2 t2) := by rw [← hact2]; rfl
    obtain ⟨n2, b2, now2, sent2⟩ := deliver_at Q (E.world k2) idx2 t2 _ j hfl2 atj
    obtain ⟨-, ⟨c2, hc2⟩⟩ := joined_conns hJ k2 (by omega)
    obtain ⟨o, ho, hor⟩ := grow j k k2 (by omega) hy
    obtain ⟨g', hog, hsend'⟩ := want_sends Q.fam Q.cfg (Q.rooms j) wl _ _ (hok k2 j) (Q.addr i) _ t2 cid g
      (peek_plainFrame cid g) c2 hc2 r (fun h' => (hrooms h').2) Wn y o hWg hWl hxW ho hor
    -- y goes to i.
    obtain ⟨s2, hq''⟩ := sent2 _ _ hsend'
    rw [← e2] at hq''
    obtain ⟨k3, idx3, t3, hk3, hact3, hfl3, ht3⟩ := hf.net.timely (k2 + 1) _ j i hq'' rfl ati hG
      (show N.gst ≤ t2 by omega)
      (hlive.mono (show q.sent ≤ t2 by omega) (show t2 + N.Δ ≤ q.sent + 3 * N.Δ by omega))
    simp only at ht3
    have hnow2 : (E.world (k2 + 1)).now = t2 := by rw [e2, now2]
    have hk3now := Exec.now_mono E hk3
    have e3 : E.world (k3 + 1) = (E.world k3).step Q.setup (.deliver idx3 t3) := by rw [← hact3]; rfl
    obtain ⟨-, b3, now3, -⟩ := deliver_at Q (E.world k3) idx3 t3 _ i hfl3 ati
    obtain ⟨⟨c3, hc3⟩, -⟩ := joined_conns hJ k3 (by omega)
    have hor' : Q.fam.room o = some r := hor
    have hshared : Q.fam.shared o = true := by simp [Family.shared, hor']
    have hstored := op_taken Q.fam Q.cfg (Q.rooms i) wl _ _ (hok k3 i) (Q.addr j) _ t3 cid g'
      (peek_plainFrame cid g') c3 hc3 r (fun h' => (hrooms h').1) o hog (hf.ok.wire o hshared) hor
    have hid : o.id = y := (hok k2 j).ids y o ho
    refine ⟨k3 + 1, by omega, by rw [e3, now3]; omega, ?_⟩
    apply holds_named Q _ (hf.unclashed (k3 + 1)) j i r y (grow j k (k3 + 1) (by omega) hy)
    rw [e3, b3, ← hid]; exact hstored

end Engine.World
