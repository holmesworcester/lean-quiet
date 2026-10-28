/-
The leaf regime, proven of the running code: with every room's index at
most `leaf` items at every step, every round message in flight lists ids
only (`leaf_flight`). So in that regime a responder answers every round
from its index and ends it (Round.lean), which the reverse leg and
`round_ends` rest on.

- At a connection: an opening of a window over at most `leaf` items
  lists ids only (`opening_ids`, `start_leaf`); a reply to round
  messages of ids only lists no claims (`onRbsr_leaf`); haves, wants and
  served ops are no round messages (`recv_leaf`, `tick_leaf`,
  `filed_leaf`).
- At a node: a frame's payloads only add to the index
  (`frame_fold_len`), so every opening a frame makes is over at most the
  step's final index; every entry point's session frames list ids only
  in their round messages (`onFrame_framesLeaf`, `onTick_framesLeaf`,
  `onWrite_framesLeaf`, `connect_framesLeaf`).
-/
import engine.world.Round
namespace Engine.World
open Engine Engine.Sync
variable {F : Type}

/-- An op that, read as a round message, lists ids only. -/
def LeafOp (o : Op) : Prop := ∀ r k cs, Msg.ofOp o = some (.rbsr r k cs) → IdsOnly cs

/-- A payload that, read as a round message, lists ids only. -/
def LeafOk (b : ByteArray) : Prop := ∀ o, Op.decode b = some o → LeafOp o

theorem leafOk_bytes {o : Op} (h : LeafOp o) : LeafOk o.bytes := fun o' hd => by
  rw [Op.decode_bytes] at hd; cases hd; exact h

theorem leafOp_hold (r : Id) (l : List Id) : LeafOp (Msg.hold r l).op := fun _ _ _ h => by
  rw [ofOp_have] at h; cases h

theorem leafOp_want (l : List Id) : LeafOp (Msg.want l).op := fun _ _ _ h => by
  rw [ofOp_want] at h; cases h

theorem leafOp_hello (f : Nat) : LeafOp (Msg.hello f).op := fun _ _ _ h => by
  simp [Msg.ofOp, Msg.op, Codec.decode_encode] at h

theorem leafOp_rbsr (r : Id) (k : Nat) (cs : List Claim) (hcs : IdsOnly cs) : LeafOp (Msg.rbsr r k cs).op :=
  fun _ _ _ h => by rw [ofOp_rbsr] at h; cases h; exact hcs

theorem leafOp_data {o : Op} (h : isWire o.kind = false) : LeafOp o := fun _ _ _ e => by
  rw [ofOp_data h] at e; cases e

theorem chunks_leaf (cfg : Config) (ids : List Id) (mk : List Id → Msg) (hmk : ∀ l, LeafOp (mk l).op) :
    ∀ o ∈ chunks cfg ids mk, LeafOp o := by
  intro o ho
  simp only [chunks, List.mem_map] at ho
  obtain ⟨l, -, rfl⟩ := ho
  exact hmk l

theorem holdsOf_leaf (cfg : Config) (offer : List (Id × Id)) : ∀ o ∈ holdsOf cfg offer, LeafOp o := by
  intro o ho
  simp only [holdsOf, List.mem_flatMap] at ho
  obtain ⟨r, -, ho⟩ := ho
  exact chunks_leaf cfg _ _ (fun l => leafOp_hold r l) o ho

/-- An opening of a window over at most `leaf` items lists ids only. -/
theorem opening_ids (P : Params) (X : List Item) (hX : X.length ≤ P.leaf) (ws : List Range) :
    IdsOnly (ws.map (opening Prod.fst Prod.snd sha256 P X)) := by
  intro cl hcl
  obtain ⟨rg, -, rfl⟩ := List.mem_map.1 hcl
  have : (within Prod.fst rg X).length ≤ P.leaf := Nat.le_trans (List.length_filter_le _ _) hX
  exact ⟨rg, (within Prod.fst rg X).map Prod.snd, by simp only [opening, this, ↓reduceIte]⟩

/-- The rooms of an index all have at most n items. -/
def IxSmall (ix : Index) (n : Nat) : Prop := ∀ r, (ix.items r).length ≤ n

theorem start_leaf (cfg : Config) (ix : Index) (hx : IxSmall ix cfg.params.leaf) (c : Conn) (now : Nat) :
    ∀ o ∈ (c.start cfg ix now).send, LeafOp o := by
  intro o ho
  unfold Conn.start at ho
  split at ho
  · cases ho
  · simp only [List.mem_map] at ho
    obtain ⟨⟨⟨r, k⟩, s⟩, hs, rfl⟩ := ho
    simp only [List.mem_map, Prod.mk.injEq] at hs
    obtain ⟨r', -, ⟨rfl, rfl⟩, rfl⟩ := hs
    exact leafOp_rbsr _ _ _ (opening_ids cfg.params _ (hx r') _)

/-- **A reply to round messages of ids only lists no claims.** -/
theorem onRbsr_leaf (cfg : Config) (ix : Index) (c : Conn) (r : Id) (k : Nat) (cs : List Claim) (now : Nat)
    (hcs : IdsOnly cs) : ∀ o ∈ (c.onRbsr cfg ix r k cs now).send, LeafOp o := by
  intro o ho
  unfold Conn.onRbsr at ho
  split at ho
  · cases ho
  · dsimp only at ho
    split at ho
    · cases ho
    · simp only [Step.limit_send] at ho
      rw [answer_ids_noclaims cfg.params _ cs hcs] at ho
      rotate_left
      · intro _; rfl
      · intro _; rfl
      rcases List.mem_cons.1 ho with rfl | ho
      · exact leafOp_rbsr _ _ _ (fun _ h => by cases h)
      · rcases List.mem_append.1 ho with ho | ho
        · exact chunks_leaf cfg _ _ (fun l => leafOp_hold r l) o ho
        · exact chunks_leaf cfg _ _ (fun l => leafOp_want l) o ho

section
variable (fam : Family F) (cfg : Config)

theorem tick_leaf (ix : Index) (hx : IxSmall ix cfg.params.leaf) (c : Conn) (now : Nat) (h : Held F) :
    ∀ o ∈ ((c.tick fam cfg ix now : HeldM F Step).run h).1.send, LeafOp o := by
  intro o ho
  unfold Conn.tick at ho
  split at ho
  · cases ho
  · simp only [HeldM.run_bind, HeldM.run_pure, Conn.finish_send] at ho
    rcases List.mem_append.1 ho with ho | ho
    · split at ho
      · exact start_leaf cfg ix hx _ now o ho
      · cases ho
    · rcases List.mem_append.1 ho with ho | ho
      · exact holdsOf_leaf cfg _ o ho
      · exact chunks_leaf cfg _ _ (fun l => leafOp_want l) o ho

theorem filed_leaf (c : Conn) (ids : List Id) (h : Held F) :
    ∀ o ∈ ((c.filed fam cfg ids : HeldM F Step).run h).1.send, LeafOp o := by
  intro o ho
  rw [filed_run, Conn.finish_send] at ho
  exact holdsOf_leaf cfg _ o ho

/-- **What a connection sends on a payload that lists ids only, if a
round message, lists ids only**, its index at most `leaf` items per
room, every op it serves a data op. -/
theorem recv_leaf (ix : Index) (hx : IxSmall ix cfg.params.leaf) (c : Conn) (b : ByteArray) (now : Nat) (h : Held F)
    (hb : LeafOk b) (hdata : ∀ o, c.shows fam o = true → isWire o.kind = false) :
    ∀ o ∈ ((Conn.recv fam cfg ix c b now : HeldM F Step).run h).1.send, LeafOp o := by
  intro o ho
  unfold Conn.recv at ho
  cases hd : Op.decode b with
  | none => simp only [hd, HeldM.run_pure] at ho; cases ho
  | some o0 =>
    simp only [hd] at ho
    cases hm : Msg.ofOp o0 with
    | none =>
      simp only [hm] at ho
      split at ho
      · cases ho
      · simp only [HeldM.run_pure, Conn.finish_send, Step.limit_send] at ho; cases ho
    | some m =>
      simp only [hm] at ho
      cases m with
      | hello f =>
        simp only [HeldM.run_pure, Conn.finish_send] at ho
        split at ho
        · exact start_leaf cfg ix hx _ now o ho
        · cases ho
      | rbsr r k cs =>
        simp only [HeldM.run_pure, Conn.finish_send] at ho
        exact onRbsr_leaf cfg ix _ r k cs now (hb o0 hd r k cs hm) o ho
      | hold r ids =>
        simp only [HeldM.run_bind, HeldM.run_pure, Conn.finish_send] at ho
        change o ∈ ((Conn.onHold fam cfg _ r ids : HeldM F Step) h).1.send at ho
        rw [onHold_apply] at ho
        split at ho
        · cases ho
        · split at ho
          · cases ho
          · simp only [Step.limit_send] at ho; exact chunks_leaf cfg _ _ (fun l => leafOp_want l) o ho
      | want ids =>
        simp only [HeldM.run_bind, HeldM.run_pure, Conn.finish_send] at ho
        unfold Conn.onWant at ho
        split at ho
        · cases ho
        · simp only [HeldM.run_bind, Read.run_heldW, HeldM.run_pure, Step.limit_send] at ho
          exact leafOp_data (hdata o (serve_shownW _ _ _ _ o ho).1)

end


/-! ## At a node: every round message it sends lists ids only -/

theorem ins_len (a : Item) : ∀ l : List Item, l.length ≤ (Engine.Sync.ins a l).length := by
  intro l
  induction l with
  | nil => simp [Engine.Sync.ins]
  | cons b t ih =>
    simp only [Engine.Sync.ins]
    split
    · simp
    · split
      · simp
      · simp only [List.length_cons]; omega

theorem addStep_len (fam : Family F) (db : DB F) (r : Id) : ∀ (l : List Op) (st : Index × List Id),
    (st.1.items r).length ≤ ((l.foldl (addStep fam db) st).1.items r).length := by
  intro l
  induction l with
  | nil => intro st; exact Nat.le_refl _
  | cons o t ih =>
    intro st
    refine Nat.le_trans ?_ (ih _)
    unfold addStep
    split
    · show (st.1.items r).length ≤ ((st.1.add fam o).items r).length
      rw [items_add_eq]
      split
      · exact ins_len _ _
      · exact Nat.le_refl _
    · exact Nat.le_refl _

section
variable (fam : Family F) (cfg : Config) (rms : Held F → Id → List Id)

theorem write_len (n : Node) (ops : List Op) (h : Held F) (r : Id) :
    (n.ix.items r).length ≤ (((n.write (psync fam cfg rms) ops).run h).1.1.ix.items r).length := by
  rw [write_run]; dsimp only
  split
  · exact Nat.le_refl _
  · dsimp only; exact addStep_len _ _ r _ (n.ix, [])

theorem store_len (n : Node) (ops : List Op) (mine : Bool) (h : Held F) (r : Id) :
    (n.ix.items r).length ≤ (((n.store (psync fam cfg rms) ops mine).run h).1.1.ix.items r).length := by
  rw [store_run]
  simp only [Node.put, psync_fam]
  have hw := write_len fam cfg rms n (intake fam mine ops) h r
  by_cases hc : ((n.write (psync fam cfg rms) (intake fam mine ops)).run h).1.2.isEmpty = true
  · simp only [hc, ↓reduceIte]; exact hw
  · simp only [hc, ↓reduceIte, Bool.false_eq_true]
    rw [(fanout_node fam cfg rms _ _ _).2.1]; exact hw

/-- A frame's payloads only add to the index. -/
theorem frameStep_len (cid : Id) (now : Nat) (st : (Node × Acts) × Held F) (b : ByteArray) (r : Id) :
    (st.1.1.ix.items r).length ≤ ((frameStep fam cfg rms cid now st b).1.1.ix.items r).length := by
  unfold frameStep
  split
  · rename_i c _
    dsimp only
    rw [apply_run fam cfg rms _ _ _ _ _ (recv_drop fam cfg st.1.1.ix (c.setRooms (rms st.2 cid)) b now st.2)]
    exact store_len fam cfg rms (setConn st.1.1 cid ((Conn.recv fam cfg st.1.1.ix (c.setRooms (rms st.2 cid)) b now :
      HeldM F Step).run st.2).1.conn) ((Conn.recv fam cfg st.1.1.ix (c.setRooms (rms st.2 cid)) b now :
      HeldM F Step).run st.2).1.take false st.2 r
  · exact Nat.le_refl _

theorem frame_fold_len (cid : Id) (now : Nat) (r : Id) : ∀ (l : List ByteArray) (st : (Node × Acts) × Held F),
    (st.1.1.ix.items r).length ≤ ((l.foldl (frameStep fam cfg rms cid now) st).1.1.ix.items r).length := by
  intro l
  induction l with
  | nil => intro st; exact Nat.le_refl _
  | cons b t ih => intro st; exact Nat.le_trans (frameStep_len fam cfg rms cid now st b r) (ih _)

/-- Every payload an entry point sends on a session, if a round message,
lists ids only. -/
def LeafSends (out : Acts) : Prop := ∀ d b, (Route.conn d, b) ∈ out.send → LeafOk b

theorem leafSends_append {a b : Acts} (ha : LeafSends a) (hb : LeafSends b) : LeafSends (a ++ b) := fun d x hx => by
  rcases List.mem_append.1 hx with hx | hx
  · exact ha d x hx
  · exact hb d x hx

theorem leafSends_sends (d : Id) (ops : List Op) (h : ∀ o ∈ ops, LeafOp o) : LeafSends (sends d ops) := by
  intro d' b hb
  simp only [sends, List.mem_map] at hb
  obtain ⟨o, ho, e⟩ := hb
  cases e
  exact leafOk_bytes (h o ho)

theorem store_leafSends (n : Node) (ops : List Op) (mine : Bool) (h : Held F) :
    LeafSends ((n.store (psync fam cfg rms) ops mine).run h).1.2 := by
  rw [store_run]
  dsimp only
  split
  · exact fun _ _ hb => by cases hb
  · rw [fanout_run]
    have : ∀ (l : List (Id × Conn)) st, LeafSends st.2.1 →
        LeafSends (l.foldl (fanStep fam cfg rms ((n.put (psync fam cfg rms) ops mine).run h).2
          ((n.put (psync fam cfg rms) ops mine).run h).1.2) st).2.1 := by
      intro l
      induction l with
      | nil => intro st hs; exact hs
      | cons p t ih =>
        intro st hs
        apply ih
        exact leafSends_append hs (leafSends_sends p.1 _ (filed_leaf fam cfg _ _ _))
    exact this _ _ (fun _ _ hb => by cases hb)

end


theorem shows_data {fam : Family F} (hwire : ∀ o, fam.shared o = true → isWire o.kind = false) (c : Conn) (o : Op)
    (h : c.shows fam o = true) : isWire o.kind = false := by
  apply hwire
  unfold Conn.shows at h
  split at h
  · rename_i r hr; simp [Family.shared, hr]
  · cases h

section
variable (fam : Family F) (cfg : Config) (rms : Held F → Id → List Id)
variable (hwire : ∀ o, fam.shared o = true → isWire o.kind = false)
include hwire

theorem frameStep_leafSends (cid : Id) (now : Nat) (st : (Node × Acts) × Held F) (b : ByteArray) (hb : LeafOk b)
    (hx : IxSmall st.1.1.ix cfg.params.leaf) (hs : LeafSends st.1.2) :
    LeafSends (frameStep fam cfg rms cid now st b).1.2 := by
  unfold frameStep
  split
  · rename_i c _
    dsimp only
    rw [apply_run fam cfg rms _ _ _ _ _ (recv_drop fam cfg st.1.1.ix (c.setRooms (rms st.2 cid)) b now st.2)]
    refine leafSends_append hs (leafSends_append (leafSends_sends cid _ ?_) (store_leafSends fam cfg rms _ _ _ _))
    exact recv_leaf fam cfg st.1.1.ix hx _ b now st.2 hb (shows_data hwire _)
  · exact hs

theorem frame_fold_leafSends (cid : Id) (now : Nat) : ∀ (l : List ByteArray) (st : (Node × Acts) × Held F),
    (∀ b ∈ l, LeafOk b) → IxSmall (l.foldl (frameStep fam cfg rms cid now) st).1.1.ix cfg.params.leaf →
    LeafSends st.1.2 → LeafSends (l.foldl (frameStep fam cfg rms cid now) st).1.2 := by
  intro l
  induction l with
  | nil => intro st _ _ hs; exact hs
  | cons b t ih =>
    intro st hb hx hs
    apply ih _ (fun b' h' => hb b' (List.mem_cons_of_mem _ h')) hx
    apply frameStep_leafSends fam cfg rms hwire cid now st b (hb b (List.mem_cons_self ..)) _ hs
    intro r
    exact Nat.le_trans (Nat.le_trans (frameStep_len fam cfg rms cid now st b r)
      (frame_fold_len fam cfg rms cid now r t _)) (hx r)

theorem tickStep_leafSends (now : Nat) (st : (Node × Acts) × Held F) (p : Id × Conn)
    (hx : IxSmall st.1.1.ix cfg.params.leaf) (hs : LeafSends st.1.2) :
    LeafSends (tickStep fam cfg rms now st p).1.2 ∧ (tickStep fam cfg rms now st p).1.1.ix = st.1.1.ix := by
  unfold tickStep
  split
  · rename_i c _
    dsimp only
    by_cases hd : ((Conn.tick fam cfg st.1.1.ix (c.setRooms (rms st.2 p.1)) now : HeldM F Step).run st.2).1.drop = true
    · simp only [Node.apply, hd, ↓reduceIte, HeldM.run_pure]
      exact ⟨leafSends_append hs (fun _ _ hb => by cases hb), rfl⟩
    · rw [apply_run fam cfg rms _ _ _ _ _ (by simpa using hd), tick_take, store_nil]
      exact ⟨leafSends_append hs (leafSends_append (leafSends_sends _ _ (tick_leaf fam cfg _ hx _ now st.2))
        (fun _ _ hb => by cases hb)), rfl⟩
  · exact ⟨hs, rfl⟩

theorem tick_fold_leafSends (now : Nat) : ∀ (l : List (Id × Conn)) (st : (Node × Acts) × Held F),
    IxSmall st.1.1.ix cfg.params.leaf → LeafSends st.1.2 →
    LeafSends (l.foldl (tickStep fam cfg rms now) st).1.2 := by
  intro l
  induction l with
  | nil => intro st _ hs; exact hs
  | cons p t ih =>
    intro st hx hs
    obtain ⟨h1, e1⟩ := tickStep_leafSends fam cfg rms hwire now st p hx hs
    exact ih _ (by rw [e1]; exact hx) h1

/-- Every session frame among these sends lists, in its round messages,
ids only. -/
def FramesLeaf (send : List (ByteArray × ByteArray)) : Prop :=
  ∀ a bytes, (a, bytes) ∈ send → ∀ cid ps, plainPeek bytes = some (cid, ps) → ∀ b ∈ ps, LeafOk b

theorem seal_framesLeaf (n : Node) (out : Acts) (h : Held F) (hs : LeafSends out) :
    FramesLeaf ((n.seal (psync fam cfg rms) out).run h).1 := by
  intro a bytes hab cid ps hp b hb
  exact hs cid b (seal_from fam cfg rms n out h a bytes hab cid ps hp b hb)

theorem onWrite_framesLeaf (n : Node) (ops : List Op) (now : Nat) (h : Held F) (ok : NodeOk fam n h) :
    FramesLeaf ((n.onWrite (psync fam cfg rms) ops now).run h).1.2.send := by
  unfold Node.onWrite
  simp only [HeldM.run_bind]
  rw [finish_run fam cfg rms _ _ _ _ (store_ok fam cfg rms n ops true h ok).managed]
  exact seal_framesLeaf fam cfg rms hwire _ _ _ (store_leafSends fam cfg rms n ops true h)

theorem connect_framesLeaf (n : Node) (cid : Id) (a : ByteArray) (dl : Bool) (now : Nat) (h : Held F)
    (ok : NodeOk fam n h) : FramesLeaf ((n.connect (psync fam cfg rms) cid a dl now).run h).1.2.send := by
  unfold Node.connect Node.open
  simp only [HeldM.run_bind, psync_rooms, readH_run, HeldM.run_pure]
  rw [finish_run fam cfg rms _ _ _ _ (by simp [Node.setAddr, Node.close, ok.managed])]
  exact seal_framesLeaf fam cfg rms hwire _ _ _ (leafSends_sends cid _ (fun o ho => by
    simp only [Conn.open, List.mem_singleton] at ho; rw [ho]; exact leafOp_hello _))

variable (hw : WalkLaws (F := F) fam cfg)
include hw

theorem onTick_framesLeaf (n : Node) (now : Nat) (h : Held F) (ok : NodeOk fam n h)
    (hx : IxSmall n.ix cfg.params.leaf) : FramesLeaf ((n.onTick (psync fam cfg rms) now).run h).1.2.send := by
  rw [onTick_run fam cfg rms hw]
  have okf := tick_fold_ok fam cfg rms hw now n.conns ((n, {}), h) ok
  rw [finish_run fam cfg rms _ _ _ _ okf.managed]
  exact seal_framesLeaf fam cfg rms hwire _ _ _ (tick_fold_leafSends fam cfg rms hwire now _ _ hx (fun _ _ hb => by cases hb))

theorem onFrame_framesLeaf (n : Node) (a b : ByteArray) (now : Nat) (h : Held F) (ok : NodeOk fam n h)
    (hb : ∀ cid ps, plainPeek b = some (cid, ps) → ∀ b' ∈ ps, LeafOk b')
    (hx : IxSmall ((n.onFrame (psync fam cfg rms) a b now).run h).1.1.ix cfg.params.leaf) :
    FramesLeaf ((n.onFrame (psync fam cfg rms) a b now).run h).1.2.send := by
  have none_ok : FramesLeaf [] := fun _ _ hm => by cases hm
  cases h0 : b[0]? with
  | none => simp only [Node.onFrame, h0, HeldM.run_pure]; exact none_ok
  | some t =>
    by_cases t1 : t = 1
    · subst t1
      cases hd : (Codec.decode (b.extract 1 b.size) : Option (Id × ByteArray)) with
      | none => simp only [Node.onFrame, h0, psync_openFrame, HeldM.pure_bind, hd, Node.onSealed, HeldM.run_pure]
                exact none_ok
      | some q =>
        obtain ⟨cid, bundle⟩ := q
        cases hc : n.conn? cid with
        | none => simp only [Node.onFrame, h0, psync_openFrame, HeldM.pure_bind, hd, Node.onSealed, hc, HeldM.run_pure]
                  exact none_ok
        | some c =>
          cases hi : (Codec.decode bundle : Option (List ByteArray)) with
          | none => simp only [Node.onFrame, h0, psync_openFrame, HeldM.pure_bind, hd, Node.onSealed, hc, hi,
                      HeldM.run_pure]
                    exact none_ok
          | some inner =>
            have hpk := peek_of_parts h0 hd hi
            rw [onFrame_fold fam cfg rms hw n a b now h cid bundle inner c h0 hd hi hc] at hx ⊢
            have ok0 := setAddr_ok fam n cid a h ok
            obtain ⟨okE, -, -, -, -⟩ := frame_fold fam cfg rms hw cid now inner ((n.setAddr cid a, {}), h) ok0
            rw [finish_run fam cfg rms _ _ _ _ okE.managed] at hx ⊢
            exact seal_framesLeaf fam cfg rms hwire _ _ _ (frame_fold_leafSends fam cfg rms hwire cid now inner _
              (hb cid inner hpk) hx (fun _ _ hb => by cases hb))
    · by_cases t0 : t = 0
      · subst t0
        cases hd : Op.decode (b.extract 1 b.size) with
        | none => simp only [Node.onFrame, h0, hd, HeldM.run_pure]; exact none_ok
        | some o =>
          by_cases he : (intakeConn fam [o]).isEmpty = true
          · simp only [Node.onFrame, h0, hd, psync_fam, he, ↓reduceIte, HeldM.run_pure]; exact none_ok
          · simp only [Node.onFrame, h0, hd, psync_fam, he, ↓reduceIte, Bool.false_eq_true, HeldM.run_bind,
              psync_recv, HeldM.pure_bind, store_nil]
            have wok := write_ok fam cfg rms n (intakeConn fam [o]) h ok
            rw [finish_run fam cfg rms ((n.write (psync fam cfg rms) (intakeConn fam [o])).run h).1.1 {} now
              ((n.write (psync fam cfg rms) (intakeConn fam [o])).run h).2 wok.managed]
            exact seal_framesLeaf fam cfg rms hwire ((n.write (psync fam cfg rms) (intakeConn fam [o])).run h).1.1 {}
              ((n.write (psync fam cfg rms) (intakeConn fam [o])).run h).2 (fun _ _ hb => by cases hb)
      · unfold Node.onFrame
        rw [h0]
        split
        · rename_i e; cases e; exact absurd rfl t0
        · rename_i e; cases e; exact absurd rfl t1
        · exact none_ok

end


/-! ## Over an execution: every round message in flight lists ids only -/

/-- Every session frame in flight lists, in its round messages, ids only. -/
def LeafFlight {n : Nat} (w : World (Held F) n) : Prop :=
  ∀ p ∈ w.flight, ∀ cid ps, plainPeek p.bytes = some (cid, ps) → ∀ b ∈ ps, LeafOk b

/-- What an entry point at node j sends is in flight as new packets, and
only those are new. -/
theorem enter_leaf (Q : Plain F) (w : World (Held F) Q.n) (j : Fin Q.n) (t : Nat)
    (f : Node → HeldM F (Node × Effects)) (hl : LeafFlight w)
    (hf : FramesLeaf ((f (w.node j)).run (w.box j)).1.2.send) : LeafFlight (w.enter Q.setup j t f) := by
  intro p hp cid ps hpk b hb
  simp only [World.enter] at hp
  rcases List.mem_append.1 hp with hp | hp
  · exact hl p hp cid ps hpk b hb
  · obtain ⟨-, d, hd⟩ := packets_from j _ t _ _ p hp
    exact hf d p.bytes hd cid ps hpk b hb

/-- **In the leaf regime every round message in flight lists ids only**:
with every room's index at most `leaf` items at every step, every
round message any node sends lists ids only. -/
theorem leaf_flight (Q : Plain F) (E : Q.Run) (hok : PlainOk Q) (hx : ∀ k i, IxSmall ((E.world k).node i).ix Q.cfg.params.leaf) :
    ∀ k, LeafFlight (E.world k) := by
  have wl := walk_proof F Q.fam Q.cfg
  have hwire := hok.wire
  intro k
  induction k with
  | zero => intro p hp; cases hp
  | succ k ih =>
    have okw := reach_ok Q wl noAdv _ (E.reachable k)
    have hl : Legal Q.setup noAdv (E.world k) (E.act k) := E.legal k
    have hxk := hx k
    have hx1 := hx (k + 1)
    rw [Exec.world_succ] at hx1 ⊢
    cases ha : E.act k with
    | deliver idx t =>
      rw [ha] at hx1
      cases hk : (E.world k).flight[idx]? with
      | none => simp only [World.step, hk]; exact ih
      | some p =>
        have ih' : LeafFlight ({ E.world k with flight := (E.world k).flight.eraseIdx idx } : World (Held F) Q.n) :=
          fun q hq => ih q (List.mem_of_mem_eraseIdx hq)
        cases hj : Q.setup.at? p.dst with
        | none => simp only [World.step, hk, hj]; exact ih'
        | some j =>
          simp only [World.step, hk, hj] at hx1 ⊢
          have hxj : IxSmall (((E.world k).node j).onFrame (psync Q.fam Q.cfg (Q.rooms j)) p.origin p.bytes t |>.run
              ((E.world k).box j)).1.1.ix Q.cfg.params.leaf := by
            have := hx1 j
            simpa only [World.enter, upd_same] using this
          have hf := onFrame_framesLeaf Q.fam Q.cfg (Q.rooms j) hwire wl _ _ _ _ _ (okw j)
            (ih p (List.mem_of_getElem? hk)) hxj
          exact fun q hq => enter_leaf Q { E.world k with flight := (E.world k).flight.eraseIdx idx } j t
            (fun nd => nd.onFrame (psync Q.fam Q.cfg (Q.rooms j)) p.origin p.bytes t) ih' hf q hq
    | dup idx =>
      simp only [World.step]
      split
      · exact ih
      · rename_i p hp
        intro q hq cid ps hpk b hb
        rcases List.mem_append.1 hq with hq | hq
        · exact ih q hq cid ps hpk b hb
        · rw [List.mem_singleton] at hq; subst hq
          exact ih p (List.mem_of_getElem? hp) cid ps hpk b hb
    | drop idx => exact fun q hq => ih q (List.mem_of_mem_eraseIdx hq)
    | tick j t =>
      exact enter_leaf Q _ j t _ ih (onTick_framesLeaf Q.fam Q.cfg (Q.rooms j) hwire wl _ _ _ (okw j) (hxk j))
    | write j ops t =>
      intro q hq
      exact enter_leaf Q _ j t (fun nd => nd.onWrite (psync Q.fam Q.cfg (Q.rooms j)) ops t) ih
        (onWrite_framesLeaf Q.fam Q.cfg (Q.rooms j) hwire _ _ _ _ (okw j)) q hq
    | restart j t => exact ih
    | connect j j' cid d t =>
      exact enter_leaf Q _ j t _ ih (connect_framesLeaf Q.fam Q.cfg (Q.rooms j) hwire _ _ _ _ _ _ (okw j))
    | inject j o b t => rw [ha] at hl; exact absurd hl.1 id

end Engine.World
