/-
A frame taken twice is taken once, proven of the running code
(`idem_proof`), when a node's rooms do not depend on its store (finding
6): delivering the same bytes to a node again, right after, leaves its
store as the first delivery left it.

- What a connection takes from a payload is the payload's op, a data op
  it shows (`recv_take_of`); with fixed rooms the first delivery stored
  every such op of the frame (`first_named`).
- A store, or a write, of ops already held changes nothing
  (`write_held`, `store_held`); so the second delivery's payloads, one at
  a time, leave the store as it was (`second_keeps`).
-/
import engine.world.Members
namespace Engine.World
open Engine Engine.Sync
variable {F : Type}

attribute [local instance] byteArray_lawfulBEq

theorem absentStep_held (db : DB F) : ∀ (l acc : List Op), (∀ o ∈ l, (db.ops o.id).isSome = true) →
    l.foldl (absentStep db) acc = acc := by
  intro l
  induction l with
  | nil => intro acc _; rfl
  | cons a t ih =>
    intro acc h
    simp only [List.foldl_cons]
    have : absentStep db acc a = acc := by
      unfold absentStep
      have ha := h a (List.mem_cons_self ..)
      simp [Option.isNone_iff_eq_none, Option.isSome_iff_ne_none.1 ha]
    rw [this]; exact ih acc (fun o ho => h o (List.mem_cons_of_mem _ ho))

/-- **A write of ops already held changes nothing.** -/
theorem write_held (x : Sync F (HeldM F)) (n : Node) (ops : List Op) (h : Held F)
    (hn : ∀ o ∈ ops, Named h o.id) : (n.write x ops).run h = ((n, []), h) := by
  rw [write_run]
  dsimp only
  rw [absentStep_held h.db ops [] hn]
  rfl

section
variable (fam : Family F) (cfg : Config) (rms : Held F → Id → List Id)

/-- **A store of ops already held changes nothing.** -/
theorem store_held (n : Node) (ops : List Op) (mine : Bool) (h : Held F) (hn : ∀ o ∈ ops, Named h o.id) :
    ((n.store (psync fam cfg rms) ops mine).run h).2 = h := by
  have hi : ∀ o ∈ intake fam mine ops, Named h o.id := fun o ho => by
    unfold intake at ho; split at ho
    · exact hn o ho
    · exact hn o (List.mem_filter.1 ho).1
  rw [store_run]
  simp only [Node.put, psync_fam, write_held (psync fam cfg rms) n _ h hi, List.isEmpty_nil, ↓reduceIte]

/-- What a connection takes from a payload is the payload's op, a data op
it shows. -/
theorem recv_take_of (ix : Index) (c : Conn) (b : ByteArray) (now : Nat) (h : Held F) (o : Op)
    (ho : o ∈ ((Conn.recv fam cfg ix c b now : HeldM F Step).run h).1.take) :
    Op.decode b = some o ∧ isWire o.kind = false ∧ c.shows fam o = true := by
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
      · rename_i hc
        simp only [HeldM.run_pure, Conn.finish_take, Step.limit_take, List.mem_singleton] at ho
        subst ho
        simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_true] at hc
        have h2 : Conn.shows fam ({ c with heard := now } : Conn) o = true := by simpa using hc.2
        exact ⟨rfl, hc.1, h2⟩
    | some m =>
      simp only [hm] at ho
      exfalso
      cases m with
      | hello f =>
        simp only [HeldM.run_pure, Conn.finish_take] at ho
        split at ho
        · rw [(start_send cfg ix _ now).2] at ho; cases ho
        · cases ho
      | rbsr r k cs =>
        simp only [HeldM.run_pure, Conn.finish_take] at ho
        rw [(onRbsr_send cfg ix _ _ _ _ now).2] at ho; cases ho
      | hold r ids =>
        simp only [HeldM.run_bind, HeldM.run_pure, Conn.finish_take] at ho
        change o ∈ ((Conn.onHold fam cfg _ r ids : HeldM F Step) h).1.take at ho
        rw [onHold_apply] at ho
        split at ho
        · cases ho
        · split at ho
          · cases ho
          · simp only [Step.limit_take] at ho; cases ho
      | want ids =>
        simp only [HeldM.run_bind, HeldM.run_pure, Conn.finish_take] at ho
        unfold Conn.onWant at ho
        split at ho
        · cases ho
        · simp only [HeldM.run_bind, Read.run_heldW, HeldM.run_pure, Step.limit_take] at ho; cases ho

/-- With the ops a frame's step would take already held, the step keeps
the store. -/
theorem frameStep_held (cid : Id) (now : Nat) (st : (Node × Acts) × Held F) (b : ByteArray)
    (hn : ∀ o, Op.decode b = some o → isWire o.kind = false → (∃ r, fam.room o = some r ∧ r ∈ rms st.2 cid) →
      Named st.2 o.id) :
    (frameStep fam cfg rms cid now st b).2 = st.2 := by
  unfold frameStep
  split
  · rename_i c _
    dsimp only
    have hdr := recv_drop fam cfg st.1.1.ix (c.setRooms (rms st.2 cid)) b now st.2
    rw [apply_run fam cfg rms _ _ _ _ _ hdr]
    apply store_held
    intro o ho
    obtain ⟨hd, hw, hsh⟩ := recv_take_of fam cfg _ _ b now st.2 o ho
    apply hn o hd hw
    unfold Conn.shows at hsh
    split at hsh
    · rename_i r hr
      exact ⟨r, hr, (has_iff _ _).1 (by simpa [Conn.setRooms] using hsh)⟩
    · cases hsh
  · rfl

/-- **The second delivery's payloads keep the store**, when it holds every
data op of a shown room among them. -/
theorem second_keeps (cid : Id) (now : Nat) (R : List Id) (hR : ∀ h, rms h cid = R) :
    ∀ (l : List ByteArray) (st : (Node × Acts) × Held F),
    (∀ b ∈ l, ∀ o, Op.decode b = some o → isWire o.kind = false → (∃ r, fam.room o = some r ∧ r ∈ R) →
      Named st.2 o.id) →
    (l.foldl (frameStep fam cfg rms cid now) st).2 = st.2 := by
  intro l
  induction l with
  | nil => intro st _; rfl
  | cons b t ih =>
    intro st hn
    have e := frameStep_held fam cfg rms cid now st b (fun o hd hw' hr => by
      rw [hR] at hr; exact hn b (List.mem_cons_self ..) o hd hw' hr)
    rw [List.foldl_cons, ih _ (fun b' hb' o hd hw' hr => by rw [e]; exact hn b' (List.mem_cons_of_mem _ hb') o hd hw' hr), e]

variable (hw : WalkLaws (F := F) fam cfg)
include hw

/-- **The first delivery takes every data op of a shown room** among its
payloads, on a session the node holds. -/
theorem first_named (cid : Id) (now : Nat) (R : List Id) (hR : ∀ h, rms h cid = R) :
    ∀ (l : List ByteArray) (st : (Node × Acts) × Held F), NodeOk fam st.1.1 st.2 → cid ∈ cids st.1.1 →
    ∀ b ∈ l, ∀ o, Op.decode b = some o → isWire o.kind = false → (∃ r, fam.room o = some r ∧ r ∈ R) →
      Named (l.foldl (frameStep fam cfg rms cid now) st).2 o.id := by
  intro l
  induction l with
  | nil => intro st _ _ b hb; cases hb
  | cons b t ih =>
    intro st ok hc b' hb' o hd hw' ⟨r, hor, hr⟩
    obtain ⟨ok1, -, c1, -, -⟩ := frameStep_ok fam cfg rms hw cid now st b ok
    rcases List.mem_cons.1 hb' with rfl | hb'
    · obtain ⟨c, hcc⟩ := (conn_iff _ _).2 hc
      obtain ⟨-, e2, -, -, -⟩ := frame_fold fam cfg rms hw cid now t _ ok1
      rw [List.foldl_cons]
      refine (?_ : Named _ o.id).ext e2
      unfold frameStep
      rw [hcc]; dsimp only
      have hdr := recv_drop fam cfg st.1.1.ix (c.setRooms (rms st.2 cid)) b' now st.2
      have hsh : Conn.shows fam ({ c.setRooms (rms st.2 cid) with heard := now } : Conn) o = true := by
        simp only [Conn.shows, Conn.setRooms, hor, hR]; exact (has_iff _ _).2 hr
      have hrd : ((Conn.recv fam cfg st.1.1.ix (c.setRooms (rms st.2 cid)) b' now : HeldM F Step).run st.2).1.take
          = [o] := by
        simp only [Conn.recv, hd, ofOp_data hw', hw', hsh, Bool.false_or, Bool.not_true, Bool.false_eq_true,
          ↓reduceIte, HeldM.run_pure, Conn.finish_take, Step.limit_take]
      rw [apply_run fam cfg rms _ _ _ _ _ hdr, hrd]
      exact store_named fam cfg rms _ o st.2 (by simp [Family.shared, hor])
    · rw [List.foldl_cons]
      exact ih _ ok1 (by rw [c1]; exact hc) b' hb' o hd hw' ⟨r, hor, hr⟩

end


section
variable (fam : Family F) (cfg : Config) (rms : Held F → Id → List Id) (hw : WalkLaws (F := F) fam cfg)
include hw

/-- **A frame taken twice is taken once, at a node** whose rooms do not
depend on its store. -/
theorem onFrame_idem (n : Node) (a b : ByteArray) (t t' : Nat) (h : Held F) (ok : NodeOk fam n h)
    (hfix : ∀ h h' cid, rms h cid = rms h' cid) :
    ((((n.onFrame (psync fam cfg rms) a b t).run h).1.1.onFrame (psync fam cfg rms) a b t').run
      ((n.onFrame (psync fam cfg rms) a b t).run h).2).2 = ((n.onFrame (psync fam cfg rms) a b t).run h).2 := by
  cases h0 : b[0]? with
  | none => simp only [Node.onFrame, h0, HeldM.run_pure]
  | some tg =>
    by_cases t1 : tg = 1
    · subst t1
      cases hd : (Codec.decode (b.extract 1 b.size) : Option (Id × ByteArray)) with
      | none => simp only [Node.onFrame, h0, psync_openFrame, HeldM.pure_bind, hd, Node.onSealed, HeldM.run_pure]
      | some q =>
        obtain ⟨cid, bundle⟩ := q
        cases hc : n.conn? cid with
        | none => simp only [Node.onFrame, h0, psync_openFrame, HeldM.pure_bind, hd, Node.onSealed, hc, HeldM.run_pure]
        | some c =>
          cases hi : (Codec.decode bundle : Option (List ByteArray)) with
          | none => simp only [Node.onFrame, h0, psync_openFrame, HeldM.pure_bind, hd, Node.onSealed, hc, hi,
              HeldM.run_pure]
          | some inner =>
            have ok0 := setAddr_ok fam n cid a h ok
            obtain ⟨okE, -, cE, -, -⟩ := frame_fold fam cfg rms hw cid t inner ((n.setAddr cid a, {}), h) ok0
            have hcE : cid ∈ cids (inner.foldl (frameStep fam cfg rms cid t) ((n.setAddr cid a, {}), h)).1.1 := by
              rw [cE]; exact (conn_iff _ _).1 ⟨c, hc⟩
            have hnamed := first_named fam cfg rms hw cid t (rms h cid) (fun h' => hfix h' h cid) inner
              ((n.setAddr cid a, {}), h) ok0 ((conn_iff _ _).1 ⟨c, hc⟩)
            rw [onFrame_fold fam cfg rms hw n a b t h cid bundle inner c h0 hd hi hc]
            rw [finish_run fam cfg rms _ _ _ _ okE.managed]
            generalize hE : inner.foldl (frameStep fam cfg rms cid t) ((n.setAddr cid a, {}), h) = E at okE hcE hnamed ⊢
            obtain ⟨c', hc'⟩ := (conn_iff _ _).2 hcE
            have hc'' : ({ E.1.1 with fresh := [] } : Node).conn? cid = some c' := hc'
            rw [onFrame_fold fam cfg rms hw _ a b t' E.2 cid bundle inner c' h0 hd hi hc'']
            have okF : NodeOk fam ({ E.1.1 with fresh := [] } : Node) E.2 :=
              ⟨okE.sub, okE.managed, okE.ids, okE.log, okE.wf, okE.exact, okE.logx, okE.stored, okE.offered⟩
            have ok1 := setAddr_ok fam _ cid a E.2 okF
            obtain ⟨okE2, -, -, -, -⟩ := frame_fold fam cfg rms hw cid t' inner
              ((({ E.1.1 with fresh := [] } : Node).setAddr cid a, {}), E.2) ok1
            rw [frame_end_store fam cfg rms t' _ okE2]
            exact second_keeps fam cfg rms cid t' (rms h cid) (fun h' => hfix h' h cid) inner _
              (fun b' hb' o hdo hwo hr => hnamed b' hb' o hdo hwo hr)
    · by_cases t0 : tg = 0
      · subst t0
        cases hd : Op.decode (b.extract 1 b.size) with
        | none => simp only [Node.onFrame, h0, hd, HeldM.run_pure]
        | some o =>
          by_cases he : (intakeConn fam [o]).isEmpty = true
          · simp only [Node.onFrame, h0, hd, psync_fam, he, ↓reduceIte, HeldM.run_pure]
          · have wok := write_ok fam cfg rms n (intakeConn fam [o]) h ok
            have hn := write_named fam cfg rms n (intakeConn fam [o]) h
            simp only [Node.onFrame, h0, hd, psync_fam, he, ↓reduceIte, Bool.false_eq_true, HeldM.run_bind,
              psync_recv, HeldM.pure_bind, store_nil]
            rw [finish_run fam cfg rms ((n.write (psync fam cfg rms) (intakeConn fam [o])).run h).1.1 {} t
              ((n.write (psync fam cfg rms) (intakeConn fam [o])).run h).2 wok.managed]
            dsimp only
            rw [write_held (psync fam cfg rms) _ _ _ hn]
            simp only [store_nil]
            rw [finish_run fam cfg rms _ _ _ _ (by rw [(write_node fam cfg rms _ _ _).2.2]; exact ok.managed)]
      · simp only [Node.onFrame, h0]
        split
        · rename_i e; cases e; exact absurd rfl t0
        · rename_i e; cases e; exact absurd rfl t1
        · simp only [HeldM.run_pure]

end

/-- **L-idem, proven of the running code:** delivering the same bytes to
a node again, right after, leaves its store as the first delivery left
it, when its rooms do not depend on its store (finding 6). -/
theorem idem_proof : idem_stmt := by
  intro F Q adv w i a b t t' hr hfix
  have wl := walk_proof F Q.fam Q.cfg
  have ok := reach_ok Q wl adv w hr i
  simp only [World.enter, upd_same]
  exact onFrame_idem Q.fam Q.cfg (Q.rooms i) wl (w.node i) a b t t' (w.box i) ok hfix

end Engine.World
