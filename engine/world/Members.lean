/-
Only members receive, proven of the running code (`members_only_proof`):
every session frame an honest node sends carries only sync messages and
ops of rooms the session showed during the step that sent it, whatever
the attacker does.

- At a connection: everything a step sends is a sync wire op or an op
  the connection shows (`recv_shown`, `tick_wire`, `filed_wire`; with
  holmes-a3's `start_send`, `onRbsr_send`, `chunks_wire`, `holdsOf_wire`
  from ConnLaws).
- At a node: every payload an entry point sends on session d is wire, or
  an op of a room d showed at a store between the entry point's start
  and its end (`SendsOk`), through frames, ticks, writes and connects;
  and a session's frame carries only that session's payloads
  (`seal_from`).
- At the world: a new packet on the wire is what an entry point sealed.
-/
import engine.world.Stream
import ops.sync.ConnLaws
namespace Engine.World
open Engine Engine.Sync
variable {F : Type}

attribute [local instance] byteArray_lawfulBEq

/-! ## At a connection: wire, or shown -/

section
variable (fam : Family F) (cfg : Config)

theorem recv_shown (ix : Index) (c : Conn) (b : ByteArray) (now : Nat) (h : Held F) (o : Op)
    (ho : o ∈ ((Conn.recv fam cfg ix c b now : HeldM F Step).run h).1.send) :
    isWire o.kind = true ∨ c.shows fam o = true := by
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
        · exact Or.inl ((start_send cfg ix _ now).1 o ho)
        · cases ho
      | rbsr r k cs =>
        simp only [HeldM.run_pure, Conn.finish_send] at ho
        exact Or.inl ((onRbsr_send cfg ix _ _ _ _ now).1 o ho)
      | hold r ids =>
        simp only [HeldM.run_bind, HeldM.run_pure, Conn.finish_send] at ho
        left
        change o ∈ ((Conn.onHold fam cfg _ r ids : HeldM F Step) h).1.send at ho
        rw [onHold_apply] at ho
        split at ho
        · cases ho
        · split at ho
          · cases ho
          · simp only [Step.limit_send] at ho; exact chunks_wire cfg _ _ o ho
      | want ids =>
        simp only [HeldM.run_bind, HeldM.run_pure, Conn.finish_send] at ho
        unfold Conn.onWant at ho
        split at ho
        · cases ho
        · simp only [HeldM.run_bind, Read.run_heldW, HeldM.run_pure, Step.limit_send] at ho
          exact Or.inr (serve_shownW _ _ _ _ o ho).1

theorem tick_wire (ix : Index) (c : Conn) (now : Nat) (h : Held F) (o : Op)
    (ho : o ∈ ((c.tick fam cfg ix now : HeldM F Step).run h).1.send) : isWire o.kind = true := by
  unfold Conn.tick at ho
  split at ho
  · cases ho
  · simp only [HeldM.run_bind, HeldM.run_pure, Conn.finish_send] at ho
    rcases List.mem_append.1 ho with ho | ho
    · split at ho
      · exact (start_send cfg ix _ now).1 o ho
      · cases ho
    · rcases List.mem_append.1 ho with ho | ho
      · exact holdsOf_wire cfg _ o ho
      · exact chunks_wire cfg _ _ o ho

theorem filed_wire (c : Conn) (ids : List Id) (h : Held F) (o : Op)
    (ho : o ∈ ((c.filed fam cfg ids : HeldM F Step).run h).1.send) : isWire o.kind = true := by
  rw [filed_run, Conn.finish_send] at ho
  exact holdsOf_wire cfg _ o ho

end


/-! ## A session's frame carries only that session's payloads -/

theorem peek_bare (b : ByteArray) : plainPeek (tagged bareTag b) = none := by
  unfold plainPeek
  rw [if_neg (by rw [tagged_head]; decide)]

theorem bundles_sub (max : Nat) : ∀ (l : List ByteArray), ∀ g ∈ bundles max l, ∀ x ∈ g, x ∈ l := by
  intro l
  induction l with
  | nil => intro g hg; cases hg
  | cons b rest ih =>
    intro g hg x hx
    unfold bundles at hg
    split at hg
    · rcases List.mem_singleton.1 hg with rfl
      rcases List.mem_singleton.1 hx with rfl
      exact List.mem_cons_self ..
    · rename_i g0 gs he
      split at hg
      · rcases List.mem_cons.1 hg with rfl | hg
        · rcases List.mem_cons.1 hx with rfl | hx
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (ih g0 (by rw [he]; exact List.mem_cons_self ..) x hx)
        · exact List.mem_cons_of_mem _ (ih g (by rw [he]; exact List.mem_cons_of_mem _ hg) x hx)
      · rcases List.mem_cons.1 hg with rfl | hg
        · rcases List.mem_singleton.1 hx with rfl
          exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (ih g (by rw [he]; exact hg) x hx)

/-- What a list of sealed sends may carry on a session: only that
session's payloads of `out`. -/
def SealOk (out : Acts) (L : List (ByteArray × ByteArray)) : Prop :=
  ∀ a bytes, (a, bytes) ∈ L → ∀ cid ps, plainPeek bytes = some (cid, ps) → ∀ b ∈ ps, (Route.conn cid, b) ∈ out.send

theorem cids_sealOk (out : Acts) : ∀ (L : List (Route × ByteArray)) st, SealOk out st.1 →
    SealOk out (L.foldl cidsStep st).1 := by
  intro L
  induction L with
  | nil => intro st h; exact h
  | cons x t ih =>
    intro st h
    apply ih
    obtain ⟨r, b⟩ := x
    cases r with
    | bare a =>
      intro a' bytes hm cid ps hp
      simp only [cidsStep, List.mem_cons] at hm
      rcases hm with e | hm
      · cases e; rw [peek_bare] at hp; cases hp
      · exact h a' bytes hm cid ps hp
    | conn c => simp only [cidsStep]; split <;> exact h

theorem seal_sealOk (cfg : Config) (n : Node) (out : Acts) : ∀ (L : List Id) acc, SealOk out acc →
    SealOk out (L.foldl (sealStep cfg n out) acc) := by
  intro L
  induction L with
  | nil => intro acc h; exact h
  | cons c t ih =>
    intro acc h
    apply ih
    simp only [sealStep]
    split
    · rename_i a _
      rw [foldl_cons_acc]
      intro a' bytes hm cid ps hp b hb
      rcases List.mem_append.1 hm with hm | hm
      · obtain ⟨g, hg, e⟩ := List.mem_map.1 (List.mem_reverse.1 hm)
        cases e
        simp only [peek_plainFrame, Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        have hbp := bundles_sub cfg.bundle _ g hg b hb
        simp only [payloadsOf, List.mem_filterMap] at hbp
        obtain ⟨⟨r, b'⟩, hm', e⟩ := hbp
        cases r with
        | bare _ => cases e
        | conn c' =>
          simp only at e
          split at e
          · rename_i hc; cases e; rw [hc] at hm'; exact hm'
          · cases e
      · exact h a' bytes hm cid ps hp b hb
    · exact h

section
variable (fam : Family F) (cfg : Config) (rms : Held F → Id → List Id)

/-- **A session's frame carries only that session's payloads.** -/
theorem seal_from (n : Node) (out : Acts) (h : Held F) :
    SealOk out ((n.seal (psync fam cfg rms) out).run h).1 := by
  simp only [Node.seal, HeldM.run_bind]
  rw [forIn_yield out.send _ cidsStep h (fun x st => by
    rcases x with ⟨r, b⟩; cases r <;> simp only [cidsStep] <;> (try split) <;> rfl)]
  rw [forIn_yield _ _ (sealStep cfg n out) h (fun c sent => by
    simp only [sealStep]
    cases hc : n.addr? c with
    | none => rfl
    | some a' =>
      simp only [HeldM.run_bind]
      rw [forIn_yield _ _ (fun acc g => (a', plainFrame c g) :: acc) h (fun g acc => by
        simp [plainFrame, psync_sealFor])]
      rfl)]
  simp only [HeldM.run_pure]
  intro a bytes hm
  exact seal_sealOk cfg n out _ _ (cids_sealOk out out.send ([], []) (fun _ _ h => by cases h)) a bytes
    (List.mem_reverse.1 hm)

end

/-! ## At a node: what an entry point sends on a session -/

theorem Kept.refl (h : Held F) : Kept h h := fun _ _ e => e
theorem Kept.trans {a b c : Held F} (h1 : Kept a b) (h2 : Kept b c) : Kept a c := fun x o e => h2 x o (h1 x o e)
theorem Kept.of_ext {a b : Held F} (e : Ext a b) : Kept a b := e.1

section
variable (fam : Family F) (rms : Held F → Id → List Id)

/-- Payload b on session d is a sync wire op, or an op of a room d showed
at a store between h₀ and h. -/
def Member (h₀ h : Held F) (d : Id) (b : ByteArray) : Prop :=
  ∀ o, Op.decode b = some o → isWire o.kind = true ∨
    ∃ h' r, Kept h₀ h' ∧ Kept h' h ∧ r ∈ rms h' d ∧ fam.room o = some r

/-- Every payload an entry point has sent on a session is a member's. -/
def SendsOk (h₀ h : Held F) (out : Acts) : Prop :=
  ∀ d b, (Route.conn d, b) ∈ out.send → Member fam rms h₀ h d b

theorem Member.mono {h₀ h h2 : Held F} {d : Id} {b : ByteArray} (hm : Member fam rms h₀ h d b) (k : Kept h h2) :
    Member fam rms h₀ h2 d b := fun o ho => by
  rcases hm o ho with hw | ⟨h', r, k1, k2, hr, hor⟩
  · exact Or.inl hw
  · exact Or.inr ⟨h', r, k1, k2.trans k, hr, hor⟩

theorem SendsOk.mono {h₀ h h2 : Held F} {out : Acts} (hs : SendsOk fam rms h₀ h out) (k : Kept h h2) :
    SendsOk fam rms h₀ h2 out := fun d b hb => (hs d b hb).mono fam rms k

theorem sendsOk_empty (h₀ h : Held F) : SendsOk fam rms h₀ h {} := fun _ _ hb => by cases hb

theorem sendsOk_append {h₀ h : Held F} {a b : Acts} (ha : SendsOk fam rms h₀ h a) (hb : SendsOk fam rms h₀ h b) :
    SendsOk fam rms h₀ h (a ++ b) := fun d x hx => by
  rcases List.mem_append.1 hx with hx | hx
  · exact ha d x hx
  · exact hb d x hx

/-- A step's sends on session d, each wire or shown by a connection of
the rooms d shows at h'. -/
theorem sendsOk_sends {h₀ h' h : Held F} (k1 : Kept h₀ h') (k2 : Kept h' h) (d : Id) (c : Conn)
    (hc : c.rooms = rms h' d) (ops : List Op) (hops : ∀ o ∈ ops, isWire o.kind = true ∨ c.shows fam o = true) :
    SendsOk fam rms h₀ h (sends d ops) := by
  intro d' b hb
  simp only [sends, List.mem_map] at hb
  obtain ⟨o, ho, e⟩ := hb
  cases e
  intro o' hd
  rw [Op.decode_bytes] at hd; cases hd
  rcases hops o ho with hw | hsh
  · exact Or.inl hw
  · right
    unfold Conn.shows at hsh
    split at hsh
    · rename_i r hr
      exact ⟨h', r, k1, k2, by rw [← hc]; exact (has_iff _ _).1 hsh, hr⟩
    · cases hsh

theorem sendsOk_wire {h₀ h : Held F} (d : Id) (ops : List Op) (hops : ∀ o ∈ ops, isWire o.kind = true) :
    SendsOk fam rms h₀ h (sends d ops) := by
  intro d' b hb
  simp only [sends, List.mem_map] at hb
  obtain ⟨o, ho, e⟩ := hb
  cases e
  intro o' hd
  rw [Op.decode_bytes] at hd; cases hd
  exact Or.inl (hops o ho)

end



section
variable (fam : Family F) (cfg : Config) (rms : Held F → Id → List Id)

theorem fanStep_sendsOk (h₀ h hs : Held F) (ids : List Id) : ∀ (l : List (Id × Conn)) st,
    SendsOk fam rms h₀ h st.2.1 → SendsOk fam rms h₀ h (l.foldl (fanStep fam cfg rms hs ids) st).2.1 := by
  intro l
  induction l with
  | nil => intro st hst; exact hst
  | cons p t ih =>
    intro st hst
    apply ih
    exact sendsOk_append fam rms hst (sendsOk_wire fam rms p.1 _ (fun o ho => filed_wire fam cfg _ ids hs o ho))

/-- A store sends only haves. -/
theorem store_sendsOk (n : Node) (ops : List Op) (mine : Bool) (h h₀ h' : Held F) :
    SendsOk fam rms h₀ h' ((n.store (psync fam cfg rms) ops mine).run h).1.2 := by
  rw [store_run]
  dsimp only
  split
  · exact sendsOk_empty fam rms h₀ h'
  · rw [fanout_run]
    exact fanStep_sendsOk fam cfg rms h₀ h' _ _ _ _ (sendsOk_empty fam rms h₀ h')

theorem tickStep_sendsOk (now : Nat) (h₀ : Held F) (st : (Node × Acts) × Held F)
    (hs : SendsOk fam rms h₀ st.2 st.1.2) :
    SendsOk fam rms h₀ (tickStep fam cfg rms now st p).2 (tickStep fam cfg rms now st p).1.2 := by
  rw [tickStep_store]
  unfold tickStep
  split
  · rename_i c _
    dsimp only
    by_cases hd : ((Conn.tick fam cfg st.1.1.ix (c.setRooms (rms st.2 p.1)) now : HeldM F Step).run st.2).1.drop = true
    · simp only [Node.apply, hd, ↓reduceIte, HeldM.run_pure]
      exact sendsOk_append fam rms hs (fun _ _ hb => by cases hb)
    · rw [apply_run fam cfg rms _ _ _ _ _ (by simpa using hd), tick_take, store_nil]
      refine sendsOk_append fam rms hs (sendsOk_append fam rms ?_ (sendsOk_empty fam rms _ _))
      exact sendsOk_wire fam rms _ _ (fun o ho => tick_wire fam cfg _ _ now st.2 o ho)
  · exact hs

theorem tick_fold_sendsOk (now : Nat) (h₀ : Held F) : ∀ (l : List (Id × Conn)) (st : (Node × Acts) × Held F),
    SendsOk fam rms h₀ st.2 st.1.2 →
    SendsOk fam rms h₀ (l.foldl (tickStep fam cfg rms now) st).2 (l.foldl (tickStep fam cfg rms now) st).1.2 := by
  intro l
  induction l with
  | nil => intro st h; exact h
  | cons p t ih => intro st h; exact ih _ (tickStep_sendsOk fam cfg rms now h₀ st h)

variable (hw : WalkLaws (F := F) fam cfg)
include hw

theorem frameStep_sendsOk (cid : Id) (now : Nat) (h₀ : Held F) (st : (Node × Acts) × Held F) (b : ByteArray)
    (ok : NodeOk fam st.1.1 st.2) (k0 : Kept h₀ st.2) (hs : SendsOk fam rms h₀ st.2 st.1.2) :
    SendsOk fam rms h₀ (frameStep fam cfg rms cid now st b).2 (frameStep fam cfg rms cid now st b).1.2 := by
  have e := (frameStep_ok fam cfg rms hw cid now st b ok).2.1
  have hs' := hs.mono fam rms (Kept.of_ext e)
  cases hc : st.1.1.conn? cid with
  | none =>
    have e0 : frameStep fam cfg rms cid now st b = st := by unfold frameStep; rw [hc]
    rw [e0]; exact hs
  | some c =>
    have hdr := recv_drop fam cfg st.1.1.ix (c.setRooms (rms st.2 cid)) b now st.2
    unfold frameStep at hs' e ⊢
    simp only [hc] at hs' e ⊢
    rw [apply_run fam cfg rms _ _ _ _ _ hdr] at hs' e ⊢
    refine sendsOk_append fam rms hs' (sendsOk_append fam rms ?_ (store_sendsOk fam cfg rms _ _ _ _ _ _))
    exact sendsOk_sends fam rms k0 (Kept.of_ext e) cid (c.setRooms (rms st.2 cid)) rfl _
      (fun o ho => recv_shown fam cfg _ _ b now st.2 o ho)

theorem frame_fold_sendsOk (cid : Id) (now : Nat) (h₀ : Held F) : ∀ (l : List ByteArray) (st : (Node × Acts) × Held F),
    NodeOk fam st.1.1 st.2 → Kept h₀ st.2 → SendsOk fam rms h₀ st.2 st.1.2 →
    SendsOk fam rms h₀ (l.foldl (frameStep fam cfg rms cid now) st).2 (l.foldl (frameStep fam cfg rms cid now) st).1.2 := by
  intro l
  induction l with
  | nil => intro st _ _ h; exact h
  | cons b t ih =>
    intro st ok k0 hs
    obtain ⟨ok1, e1, -, -, -⟩ := frameStep_ok fam cfg rms hw cid now st b ok
    exact ih _ ok1 (k0.trans (Kept.of_ext e1)) (frameStep_sendsOk fam cfg rms hw cid now h₀ st b ok k0 hs)

end


/-! ## At a node: every session frame an entry point sends -/

section
variable (fam : Family F) (cfg : Config) (rms : Held F → Id → List Id)

/-- Every session frame among these sends carries only member payloads. -/
def FramesOk (h₀ h : Held F) (send : List (ByteArray × ByteArray)) : Prop :=
  ∀ a bytes, (a, bytes) ∈ send → ∀ cid ps, plainPeek bytes = some (cid, ps) → ∀ b ∈ ps, Member fam rms h₀ h cid b

theorem seal_framesOk (n : Node) (out : Acts) (h₀ h h' : Held F) (hs : SendsOk fam rms h₀ h' out) :
    FramesOk fam rms h₀ h' ((n.seal (psync fam cfg rms) out).run h).1 := by
  intro a bytes hab cid ps hp b hb
  exact hs cid b (seal_from fam cfg rms n out h a bytes hab cid ps hp b hb)

theorem finish_framesOk (n : Node) (out : Acts) (now : Nat) (h₀ h : Held F) (hm : n.managed = [])
    (hs : SendsOk fam rms h₀ h out) : FramesOk fam rms h₀ h ((n.finish (psync fam cfg rms) out now).run h).1.2.send := by
  rw [finish_run fam cfg rms _ _ _ _ hm]
  intro a bytes hab cid ps hp b hb
  exact hs cid b (seal_from fam cfg rms n out h a bytes hab cid ps hp b hb)

theorem onWrite_framesOk (n : Node) (ops : List Op) (now : Nat) (h : Held F) (ok : NodeOk fam n h) :
    FramesOk fam rms h ((n.onWrite (psync fam cfg rms) ops now).run h).2
      ((n.onWrite (psync fam cfg rms) ops now).run h).1.2.send := by
  unfold Node.onWrite
  simp only [HeldM.run_bind]
  have okS := store_ok fam cfg rms n ops true h ok
  rw [finish_run fam cfg rms _ _ _ _ okS.managed]
  have := finish_framesOk fam cfg rms _ ((n.store (psync fam cfg rms) ops true).run h).1.2 now h
    ((n.store (psync fam cfg rms) ops true).run h).2 okS.managed (store_sendsOk fam cfg rms n ops true h h _)
  rw [finish_run fam cfg rms _ _ _ _ okS.managed] at this
  exact this

theorem connect_framesOk (n : Node) (cid : Id) (a : ByteArray) (dl : Bool) (now : Nat) (h : Held F)
    (ok : NodeOk fam n h) :
    FramesOk fam rms h ((n.connect (psync fam cfg rms) cid a dl now).run h).2
      ((n.connect (psync fam cfg rms) cid a dl now).run h).1.2.send := by
  unfold Node.connect Node.open
  simp only [HeldM.run_bind, psync_rooms, readH_run, HeldM.run_pure]
  rw [finish_run fam cfg rms _ _ _ _ (by simp [Node.setAddr, Node.close, ok.managed])]
  exact seal_framesOk fam cfg rms _ _ h h h (sendsOk_wire fam rms cid _ (fun o ho => by
    simp only [Conn.open, List.mem_singleton] at ho; rw [ho]; exact msg_wire _))

variable (hw : WalkLaws (F := F) fam cfg)
include hw

theorem onTick_framesOk (n : Node) (now : Nat) (h : Held F) (ok : NodeOk fam n h) :
    FramesOk fam rms h ((n.onTick (psync fam cfg rms) now).run h).2
      ((n.onTick (psync fam cfg rms) now).run h).1.2.send := by
  rw [onTick_run fam cfg rms hw]
  have okf := tick_fold_ok fam cfg rms hw now n.conns ((n, {}), h) ok
  have hs := tick_fold_sendsOk fam cfg rms now h n.conns ((n, {}), h) (sendsOk_empty fam rms h h)
  have := finish_framesOk fam cfg rms _ _ now h _ okf.managed hs
  rw [finish_run fam cfg rms _ _ _ _ okf.managed] at this ⊢
  exact this

theorem onFrame_framesOk (n : Node) (a b : ByteArray) (now : Nat) (h : Held F) (ok : NodeOk fam n h) :
    FramesOk fam rms h ((n.onFrame (psync fam cfg rms) a b now).run h).2
      ((n.onFrame (psync fam cfg rms) a b now).run h).1.2.send := by
  have none_ok : ∀ h', FramesOk fam rms h h' [] := fun _ _ _ hm => by cases hm
  cases h0 : b[0]? with
  | none => simp only [Node.onFrame, h0, HeldM.run_pure]; exact none_ok _
  | some t =>
    by_cases t1 : t = 1
    · subst t1
      cases hd : (Codec.decode (b.extract 1 b.size) : Option (Id × ByteArray)) with
      | none => simp only [Node.onFrame, h0, psync_openFrame, HeldM.pure_bind, hd, Node.onSealed, HeldM.run_pure]
                exact none_ok _
      | some q =>
        obtain ⟨cid, bundle⟩ := q
        cases hc : n.conn? cid with
        | none => simp only [Node.onFrame, h0, psync_openFrame, HeldM.pure_bind, hd, Node.onSealed, hc, HeldM.run_pure]
                  exact none_ok _
        | some c =>
          cases hi : (Codec.decode bundle : Option (List ByteArray)) with
          | none => simp only [Node.onFrame, h0, psync_openFrame, HeldM.pure_bind, hd, Node.onSealed, hc, hi,
                      HeldM.run_pure]
                    exact none_ok _
          | some inner =>
            rw [onFrame_fold fam cfg rms hw n a b now h cid bundle inner c h0 hd hi hc]
            have ok0 := setAddr_ok fam n cid a h ok
            obtain ⟨okE, -, -, -, -⟩ := frame_fold fam cfg rms hw cid now inner ((n.setAddr cid a, {}), h) ok0
            have hs := frame_fold_sendsOk fam cfg rms hw cid now h inner ((n.setAddr cid a, {}), h) ok0
              (Kept.refl h) (sendsOk_empty fam rms h h)
            have := finish_framesOk fam cfg rms _ _ now h _ okE.managed hs
            rw [finish_run fam cfg rms _ _ _ _ okE.managed] at this ⊢
            exact this
    · by_cases t0 : t = 0
      · subst t0
        cases hd : Op.decode (b.extract 1 b.size) with
        | none => simp only [Node.onFrame, h0, hd, HeldM.run_pure]; exact none_ok _
        | some o =>
          by_cases he : (intakeConn fam [o]).isEmpty = true
          · simp only [Node.onFrame, h0, hd, psync_fam, he, ↓reduceIte, HeldM.run_pure]; exact none_ok _
          · simp only [Node.onFrame, h0, hd, psync_fam, he, ↓reduceIte, Bool.false_eq_true, HeldM.run_bind,
              psync_recv, HeldM.pure_bind, store_nil]
            have wok := write_ok fam cfg rms n (intakeConn fam [o]) h ok
            rw [finish_run fam cfg rms ((n.write (psync fam cfg rms) (intakeConn fam [o])).run h).1.1 {} now
              ((n.write (psync fam cfg rms) (intakeConn fam [o])).run h).2 wok.managed]
            exact seal_framesOk fam cfg rms ((n.write (psync fam cfg rms) (intakeConn fam [o])).run h).1.1 {} h
              ((n.write (psync fam cfg rms) (intakeConn fam [o])).run h).2
              ((n.write (psync fam cfg rms) (intakeConn fam [o])).run h).2 (sendsOk_empty fam rms _ _)
      · unfold Node.onFrame
        rw [h0]
        split
        · rename_i e; cases e; exact absurd rfl t0
        · rename_i e; cases e; exact absurd rfl t1
        · exact none_ok _

end


/-! ## Over every reachable world -/

theorem packets_from {n : Nat} (i : Fin n) (o : ByteArray) (t : Nat) : ∀ (s : Nat) (l : List (ByteArray × ByteArray)) q,
    q ∈ packets i o t s l → q.src = some i ∧ ∃ d, (d, q.bytes) ∈ l := by
  intro s l
  induction l generalizing s with
  | nil => intro q h; cases h
  | cons x t' ih =>
    intro q h
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨rfl, x.1, List.mem_cons_self ..⟩
    · obtain ⟨e, d, hd⟩ := ih _ q h
      exact ⟨e, d, List.mem_cons_of_mem _ hd⟩

/-- A new packet on the wire from an entry point at node j whose session
frames carry only member payloads carries only member payloads. -/
theorem enter_member (Q : Plain F) (w : World (Held F) Q.n) (j : Fin Q.n) (t : Nat)
    (f : Node → HeldM F (Node × Effects))
    (hf : FramesOk Q.fam (Q.rooms j) (w.box j) ((f (w.node j)).run (w.box j)).2 ((f (w.node j)).run (w.box j)).1.2.send)
    (p : Packet Q.n) (hp : p ∈ (w.enter Q.setup j t f).wire) (hpn : p ∉ w.wire) (i : Fin Q.n)
    (hsrc : p.src = some i) (cid : Id) (ps : List ByteArray) (hpeek : plainPeek p.bytes = some (cid, ps))
    (b : ByteArray) (hb : b ∈ ps) (o : Op) (hdo : Op.decode b = some o) :
    isWire o.kind = true ∨ ∃ h r, Kept (w.box i) h ∧ Kept h ((w.enter Q.setup j t f).box i) ∧
      r ∈ Q.rooms i h cid ∧ Q.fam.room o = some r := by
  simp only [World.enter] at hp ⊢
  rcases List.mem_append.1 hp with hp | hp
  · exact absurd hp hpn
  · obtain ⟨e, d, hd⟩ := packets_from j _ t _ _ p hp
    rw [hsrc] at e
    cases e
    simp only [upd_same]
    exact hf d p.bytes hd cid ps hpeek b hb o hdo

/-- **Only members receive, proven of the running code.** Every session
frame an honest node puts on the wire carries sync messages, and ops of
rooms the session showed at a store the step passed through, whatever
the attacker does. -/
theorem members_only_proof : members_only_stmt := by
  intro F Q adv w a hr _ p hp hpn i hsrc cid ps hpeek b hb o hdo
  have wl := walk_proof F Q.fam Q.cfg
  have okw := reach_ok Q wl adv w hr
  cases a with
  | deliver k t =>
    cases hk : w.flight[k]? with
    | none => simp only [World.step, hk] at hp; exact absurd hp hpn
    | some p' =>
      cases hj : Q.setup.at? p'.dst with
      | none => simp only [World.step, hk, hj] at hp; exact absurd hp hpn
      | some j =>
        simp only [World.step, hk, hj] at hp ⊢
        exact enter_member Q { w with flight := w.flight.eraseIdx k } j t
          (fun nd => nd.onFrame (psync Q.fam Q.cfg (Q.rooms j)) p'.origin p'.bytes t)
          (onFrame_framesOk Q.fam Q.cfg (Q.rooms j) wl _ _ _ _ _ (okw j)) p hp hpn i hsrc cid ps hpeek b hb o hdo
  | dup k =>
    simp only [World.step] at hp
    split at hp <;> exact absurd hp hpn
  | drop k => exact absurd hp hpn
  | tick j t =>
    exact enter_member Q w j t (fun nd => nd.onTick (psync Q.fam Q.cfg (Q.rooms j)) t)
      (onTick_framesOk Q.fam Q.cfg (Q.rooms j) wl _ _ _ (okw j)) p hp hpn i hsrc cid ps hpeek b hb o hdo
  | write j ops t =>
    exact enter_member Q w j t (fun nd => nd.onWrite (psync Q.fam Q.cfg (Q.rooms j)) ops t)
      (onWrite_framesOk Q.fam Q.cfg (Q.rooms j) _ _ _ _ (okw j)) p hp hpn i hsrc cid ps hpeek b hb o hdo
  | restart j t => exact absurd hp hpn
  | connect j j' cid' d t =>
    exact enter_member Q w j t (fun nd => nd.connect (psync Q.fam Q.cfg (Q.rooms j)) cid' (Q.setup.addr j') d t)
      (connect_framesOk Q.fam Q.cfg (Q.rooms j) _ _ _ _ _ _ (okw j)) p hp hpn i hsrc cid ps hpeek b hb o hdo
  | inject j origin bytes t =>
    exact enter_member Q w j t (fun nd => nd.onFrame (psync Q.fam Q.cfg (Q.rooms j)) origin bytes t)
      (onFrame_framesOk Q.fam Q.cfg (Q.rooms j) wl _ _ _ _ _ (okw j)) p hp hpn i hsrc cid ps hpeek b hb o hdo

end Engine.World
