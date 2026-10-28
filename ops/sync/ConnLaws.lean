/-
What a connection may send and take, proven of `Conn`'s code run on
the model store:

- `recv_take`: an op `recv` hands the writer is a data op (never a
  sync wire op) in one of the connection's rooms, so shared: `intake`
  keeps it, and no local or conn op, nor an op of a room the peer may
  not see, is ever taken from a session.
- `recv_send`, `filed_send`, `tick_send`, `start_send`: everything a
  connection sends is a sync wire op, or an op the peer may see (in one
  of the connection's rooms). In particular a want for an op of another
  room, a local op or a conn op sends nothing of it.
-/
import ops.sync.Conn
import engine.core.Run

namespace Engine.Sync
open Std

theorem msg_wire (m : Msg) : isWire m.op.kind = true := by
  cases m <;> simp [Msg.op, isWire, kRbsr, kHave, kWant]

section
variable {F : Type} (fam : Family F) (cfg : Config)

theorem chunks_wire (ids : List Id) (mk : List Id → Msg) : ∀ o ∈ chunks cfg ids mk, isWire o.kind = true := by
  intro o ho
  simp only [chunks, List.mem_map] at ho
  obtain ⟨_, _, rfl⟩ := ho
  exact msg_wire _

/-- What a connection may send: a sync wire op, or an op the peer may see. -/
def Sendable (c : Conn) (o : Op) : Prop := isWire o.kind = true ∨ c.shows fam o = true

/-- What a connection may hand the writer: a data op the peer may see. -/
def Takeable (c : Conn) (o : Op) : Prop := isWire o.kind = false ∧ c.shows fam o = true

theorem shows_heard (c : Conn) (now : Nat) (o : Op) : ({ c with heard := now } : Conn).shows fam o = c.shows fam o := rfl

theorem finish_send (s : Step) : (Conn.finish s).send = s.send ∧ (Conn.finish s).take = s.take := by
  unfold Conn.finish; simp

theorem start_send (ix : Index) (c : Conn) (now : Nat) :
    (∀ o ∈ (c.start cfg ix now).send, isWire o.kind = true) ∧ (c.start cfg ix now).take = [] := by
  unfold Conn.start
  split
  · simp
  · refine ⟨?_, rfl⟩
    intro o ho
    simp only [List.mem_map] at ho
    obtain ⟨_, _, rfl⟩ := ho
    exact msg_wire _

theorem onRbsr_send (ix : Index) (c : Conn) (r : Id) (k : Nat) (cs : List Claim) (now : Nat) :
    (∀ o ∈ (c.onRbsr cfg ix r k cs now).send, isWire o.kind = true) ∧
      (c.onRbsr cfg ix r k cs now).take = [] := by
  unfold Conn.onRbsr
  by_cases h1 : (!has c.rooms r) = true
  · simp [h1]
  · rw [if_neg h1]
    dsimp only
    by_cases h2 : cs.isEmpty = true
    · simp [h2]
    · rw [if_neg h2]
      refine ⟨?_, rfl⟩
      intro o ho
      simp only [List.mem_cons, List.mem_append] at ho
      rcases ho with rfl | ho | ho
      · exact msg_wire _
      · exact chunks_wire cfg _ _ o ho
      · exact chunks_wire cfg _ _ o ho

variable [Store F (Model F)]

theorem onHold_send (c : Conn) (ids : List Id) (s : DB F) :
    (∀ o ∈ ((c.onHold cfg ids : Model F Step).run s).1.send, isWire o.kind = true) ∧
      ((c.onHold cfg ids : Model F Step).run s).1.take = [] := by
  unfold Conn.onHold
  simp only [Model.run_bind, Model.run_pure]
  exact ⟨chunks_wire cfg _ _, trivial⟩

theorem onWant_send (c : Conn) (ids : List Id) (s : DB F) :
    (∀ o ∈ ((c.onWant fam cfg ids : Model F Step).run s).1.send, Sendable fam c o) ∧
      ((c.onWant fam cfg ids : Model F Step).run s).1.take = [] := by
  unfold Conn.onWant
  split
  · simp [Model.run_pure]
  · simp only [Model.run_bind, Model.run_pure]
    refine ⟨?_, trivial⟩
    intro o ho
    simp only [List.mem_append, List.mem_filter] at ho
    rcases ho with ⟨_, h⟩ | ho
    · exact Or.inr h
    · exact Or.inl (chunks_wire cfg _ _ o ho)

/-- What `recv` does with bytes that decode to op o: by o's message. -/
theorem recv_cases (ix : Index) (c : Conn) (bytes : ByteArray) (now : Nat) (s : DB F) (o : Op)
    (hd : Op.decode bytes = some o) :
    let c' : Conn := { c with heard := now }
    ((Conn.recv fam cfg ix c bytes now : Model F Step).run s).1 =
      match Msg.ofOp o with
      | some (.hello f) => Conn.finish (if c'.dialer then
          ({ c' with peerFloor := some f } : Conn).start cfg ix now else { conn := { c' with peerFloor := some f } })
      | some (.rbsr r k cs) => Conn.finish (c'.onRbsr cfg ix r k cs now)
      | some (.hold ids) => Conn.finish ((c'.onHold cfg ids : Model F Step).run s).1
      | some (.want ids) => Conn.finish ((c'.onWant fam cfg ids : Model F Step).run s).1
      | none => if isWire o.kind || !c'.shows fam o then { conn := c' }
          else Conn.finish (Step.mk { c' with asked := c'.asked.erase o.id, known := c'.known.insert o.id }
            [] [o] [] false) := by
  intro c'
  unfold Conn.recv
  rw [hd]
  dsimp only
  cases Msg.ofOp o with
  | none => by_cases hw : (isWire o.kind || !c'.shows fam o) = true <;> simp [hw, c']
  | some m => cases m <;> simp [Model.run_bind, Model.run_pure, c']

/-- **A session hands the writer only data ops the peer may see.** -/
theorem recv_take (ix : Index) (c : Conn) (bytes : ByteArray) (now : Nat) (s : DB F) :
    ∀ o ∈ ((Conn.recv fam cfg ix c bytes now : Model F Step).run s).1.take, Takeable fam c o := by
  cases hd : Op.decode bytes with
  | none => unfold Conn.recv; rw [hd]; simp
  | some o =>
    rw [recv_cases fam cfg ix c bytes now s o hd]
    dsimp only
    cases Msg.ofOp o with
    | none =>
      by_cases hw : (isWire o.kind || !c.shows fam o) = true
      · rw [if_pos (show (isWire o.kind || !Conn.shows fam ({ c with heard := now } : Conn) o) = true by rw [shows_heard]; exact hw)]; simp
      · rw [if_neg (show ¬ (isWire o.kind || !Conn.shows fam ({ c with heard := now } : Conn) o) = true by rw [shows_heard]; exact hw), (finish_send _).2]
        intro p hp
        have hpo : p = o := by simpa using hp
        subst hpo
        simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false] at hw
        exact ⟨by simpa using hw.1, hw.2⟩
    | some m =>
      cases m with
      | hello f =>
        rw [(finish_send _).2]; split
        · rw [(start_send cfg ix _ now).2]; simp
        · simp
      | rbsr r k cs => rw [(finish_send _).2, (onRbsr_send cfg ix _ _ _ _ now).2]; simp
      | hold ids => rw [(finish_send _).2, (onHold_send cfg _ _ _).2]; simp
      | want ids => rw [(finish_send _).2, (onWant_send fam cfg _ _ _).2]; simp

/-- **A session sends only sync wire ops and ops the peer may see.** -/
theorem recv_send (ix : Index) (c : Conn) (bytes : ByteArray) (now : Nat) (s : DB F) :
    ∀ o ∈ ((Conn.recv fam cfg ix c bytes now : Model F Step).run s).1.send, Sendable fam c o := by
  cases hd : Op.decode bytes with
  | none => unfold Conn.recv; rw [hd]; simp
  | some o =>
    rw [recv_cases fam cfg ix c bytes now s o hd]
    dsimp only
    cases Msg.ofOp o with
    | none =>
      by_cases hw : (isWire o.kind || !c.shows fam o) = true
      · rw [if_pos (show (isWire o.kind || !Conn.shows fam ({ c with heard := now } : Conn) o) = true by rw [shows_heard]; exact hw)]; simp
      · rw [if_neg (show ¬ (isWire o.kind || !Conn.shows fam ({ c with heard := now } : Conn) o) = true by rw [shows_heard]; exact hw), (finish_send _).1]; simp
    | some m =>
      cases m with
      | hello f =>
        rw [(finish_send _).1]; split
        · intro p hp; exact Or.inl ((start_send cfg ix _ now).1 p hp)
        · simp
      | rbsr r k cs =>
        rw [(finish_send _).1]; intro p hp; exact Or.inl ((onRbsr_send cfg ix _ _ _ _ now).1 p hp)
      | hold ids =>
        rw [(finish_send _).1]; intro p hp; exact Or.inl ((onHold_send cfg _ _ _).1 p hp)
      | want ids =>
        rw [(finish_send _).1]; intro p hp
        rcases (onWant_send fam cfg _ _ _).1 p hp with h | h
        · exact Or.inl h
        · exact Or.inr (by rw [shows_heard] at h; exact h)

/-- **The stream offers ids only.** -/
theorem filed_send (c : Conn) (ids : List Id) (s : DB F) :
    (∀ o ∈ ((c.filed fam cfg ids : Model F Step).run s).1.send, isWire o.kind = true) ∧
      ((c.filed fam cfg ids : Model F Step).run s).1.take = [] := by
  unfold Conn.filed
  simp only [Model.run_bind, Model.run_pure]
  rw [(finish_send _).1, (finish_send _).2]
  exact ⟨chunks_wire cfg _ _, rfl⟩

/-- **The clock sends only round messages and offers.** -/
theorem tick_send (ix : Index) (c : Conn) (now : Nat) (s : DB F) :
    (∀ o ∈ ((c.tick fam cfg ix now : Model F Step).run s).1.send, isWire o.kind = true) ∧
      ((c.tick fam cfg ix now : Model F Step).run s).1.take = [] := by
  unfold Conn.tick
  split
  · simp
  · simp only [Model.run_bind, Model.run_pure]
    rw [(finish_send _).1, (finish_send _).2]
    split
    · refine ⟨?_, (start_send cfg ix _ now).2⟩
      intro o ho
      simp only [List.mem_append] at ho
      rcases ho with ho | ho
      · exact (start_send cfg ix _ now).1 o ho
      · exact chunks_wire cfg _ _ o ho
    · refine ⟨?_, rfl⟩
      intro o ho
      simp only [List.mem_append, List.not_mem_nil, false_or] at ho
      exact chunks_wire cfg _ _ o ho

end

end Engine.Sync
