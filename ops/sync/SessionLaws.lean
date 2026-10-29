/-
Every handler follows Session.Allows. Closed is terminal even under a
replayed hello. The witness runs hello reception and a silence timeout.
-/
import ops.sync.RetryLaws

namespace Engine.Sync
variable {F : Type} (fam : Family F) (cfg : Config)

theorem start_session (ix : Index) (c : Conn) (now : Nat) :
    (c.start cfg ix now).conn.session = c.session := by
  unfold Conn.start; split <;> rfl

theorem round_session (ix : Index) (c : Conn) (r : Id) (k now : Nat) (cs : List Claim) :
    (c.onRbsr cfg ix r k cs now).conn.session = c.session := by
  unfold Conn.onRbsr
  split
  · rfl
  · dsimp only; split
    · rfl
    · split <;> rfl

theorem hold_session (c : Conn) (r : Id) (ids : List Id) (h : Held F) :
    ((c.onHold fam cfg r ids : HeldM F Step) h).1.conn.session = c.session := by
  rw [onHold_apply]; split
  · rfl
  · split <;> rfl

theorem want_session (ix : Index) (c : Conn) (ids : List Id) (h : Held F) :
    ((c.onWant fam cfg ix ids : HeldM F Step) h).1.conn.session = c.session := by
  unfold Conn.onWant; split
  · rfl
  · simp only [HeldM.bind_apply, HeldM.pure_apply]; rfl

theorem walk_session (h : Held F) : ∀ fuel (c : Conn) offers,
    ((c.walkN fam cfg offers fuel : HeldM F _) h).1.1.session = c.session := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
    intro c offers
    rw [Conn.walkN]
    cases c.frontier with
    | nil => rfl
    | cons x rest =>
      dsimp only
      split
      · exact ih _ _
      · rw [HeldM.bind_apply, HeldM.getOp_apply]
        cases h.db.ops x with
        | none => exact ih _ _
        | some o => dsimp only; split <;> exact ih _ _

theorem work_session (ix : Index) (c : Conn) (now : Nat) (h : Held F) :
    ((c.work fam cfg ix now : HeldM F Step) h).1.conn.session = c.session := by
  unfold Conn.work
  simp only [HeldM.bind_apply, HeldM.pure_apply]
  split
  · rw [start_session]; exact walk_session fam cfg h _ _ _
  · exact walk_session fam cfg h _ _ _

theorem filed_session (c : Conn) (ids : List Id) (h : Held F) :
    ((c.filed fam cfg ids : HeldM F Step) h).1.conn.session = c.session := by
  unfold Conn.filed
  simp only [HeldM.bind_apply]
  rw [HeldM.forIn_reads (g := fileOffer fam cfg h.db)]
  · exact foldl_inv (fun b : List (Id × Id) × Conn => b.2.session = c.session)
      (fileOffer fam cfg h.db)
      (by intro b i hb; unfold fileOffer; split <;> try exact hb
          split <;> try exact hb
          split <;> exact hb) ids ([], c) rfl
  · intro a b
    unfold fileOffer
    split
    · rw [HeldM.bind_apply, HeldM.getOp_apply]
      cases h.db.ops a with
      | none => rfl
      | some o => dsimp only; split <;> rfl
    · rfl

theorem recv_transition (ix : Index) (c : Conn) (bytes : ByteArray) (now : Nat) (h : Held F) :
    c.session.Allows ((c.recv fam cfg ix bytes now : HeldM F Step) h).1.conn.session := by
  unfold Conn.recv
  cases Op.decode bytes with
  | none => exact Or.inl rfl
  | some o =>
    dsimp only
    cases Msg.ofOp o with
    | none => dsimp only; split <;> exact Or.inl rfl
    | some msg =>
      cases msg with
      | hello f =>
        simp only [HeldM.pure_apply]
        split
        · rw [start_session]; exact Session.hello_allowed _
        · exact Session.hello_allowed _
      | rbsr r k cs =>
        simp only [HeldM.pure_apply]
        rw [round_session]; exact Or.inl rfl
      | hold r ids =>
        simp only [HeldM.bind_apply, HeldM.pure_apply, hold_session]
        exact Or.inl rfl
      | want ids =>
        simp only [HeldM.bind_apply, HeldM.pure_apply, want_session]
        exact Or.inl rfl

/-- The responder repeats its window after the dialer has session keys. -/
theorem hello_answered (ix : Index) (c : Conn) (floor now : Nat) (h : Held F)
    (hr : c.dialer = false) :
    ((c.recv fam cfg ix (Msg.hello floor).op.bytes now : HeldM F Step) h).1.send =
      [(Msg.hello c.floor).op] := by
  simp [Conn.recv, Op.decode_bytes, Msg.ofOp, Msg.op, kRbsr, Codec.decode_encode, hr]

/-- Every handler on an existing connection respects the same relation. -/
theorem handlers_transition (c : Conn) (now : Nat) (h : Held F) (s : Step)
    (call : c.Call fam cfg now h s) : c.session.Allows s.conn.session := by
  cases call with
  | carry rooms => exact Or.inl rfl
  | notify => unfold Conn.notify; rw [(give_shape fam cfg h _ c).1]; exact Or.inl rfl
  | filedGive ids =>
    simp only [Conn.filedGive, HeldM.bind_apply, HeldM.pure_apply, Step.then, filed_session]
    unfold Conn.notify; rw [(give_shape fam cfg h _ c).1]; exact Or.inl rfl
  | tickGive ix =>
    simp only [Conn.tickGive, HeldM.bind_apply, HeldM.pure_apply]
    split <;> try dsimp only [Step.then]
    all_goals
      unfold Conn.tick
      split
      · exact Or.inr (Or.inr (Or.inr rfl))
      · simp only [HeldM.bind_apply, HeldM.pure_apply, Step.pulse_conn, work_session]
        unfold Conn.notify; rw [(give_shape fam cfg h _ c).1]; exact Or.inl rfl
  | rooms rooms => exact Or.inl rfl
  | work ix => rw [work_session]; exact Or.inl rfl
  | start ix => rw [start_session]; exact Or.inl rfl
  | round ix r k cs => rw [round_session]; exact Or.inl rfl
  | hold r ids => rw [hold_session]; exact Or.inl rfl
  | want ix ids => rw [want_session]; exact Or.inl rfl
  | recv ix bytes => exact recv_transition fam cfg ix c bytes now h
  | filed ids => rw [filed_session]; exact Or.inl rfl
  | tick ix =>
    unfold Conn.tick
    split
    · exact Or.inr (Or.inr (Or.inr rfl))
    · simp only [HeldM.bind_apply, HeldM.pure_apply, Step.pulse_conn, work_session]
      exact Or.inl rfl

/-- A closed connection can never return to another phase. -/
theorem closed_terminal (c : Conn) (now : Nat) (h : Held F) (s : Step)
    (call : c.Call fam cfg now h s) (hc : c.session = .closed) : s.conn.session = .closed := by
  have ht := handlers_transition fam cfg c now h s call
  rw [hc] at ht
  exact Session.closed_terminal _ ht

/-- A fresh allocation takes exactly the first edge. -/
theorem open_session (dialer : Bool) (rooms : List Id) (floor now : Nat) :
    (Conn.open dialer rooms floor now).conn.session = .hello := rfl

/-- Both remaining edges run, on an empty store with no special premises. -/
theorem session_runs :
    let c := (Conn.open false [] 0 0).conn
    let d := ((c.recv fam cfg {} (Msg.hello 0).op.bytes 0 : HeldM F Step) {}).1.conn
    d.session = .live ∧
      ((d.tick fam cfg {} (cfg.live + 1) : HeldM F Step) {}).1.conn.session = .closed := by
  simp [Conn.open, Conn.recv, Op.decode_bytes, Msg.ofOp, Msg.op, kRbsr,
    Codec.decode_encode, Session.sayHello, Session.hearHello, Conn.tick, Session.close]
end Engine.Sync
