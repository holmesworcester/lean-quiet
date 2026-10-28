/-
The Connection family's writers cite a constant number of requirements,
within the intake cap (engine/core/Sync.lean), and sync's wire messages
never reach intake (docs/PERF.md; holmes-a3's checks before landing the
cap).

- Per writer: a request cites nothing; an ephemeral, a connection (the
  answer), a courier and an arrival record one op; an opened two; an
  established four (`*_reqs`).
- Sync's have and want carry up to `maxIds` ids as requirements, so the
  cap would refuse them; they never meet it. A session's bytes go to
  `Conn.recv`, which parses them and takes for storing only ops of no
  wire kind (`recv_takes_no_wire`); a bare op goes through `intakeConn`, which
  keeps only conn ops, and a wire op is never one in the node's family
  (`wire_not_conn`, `intakeConn_wire`).
-/
import ops.connection.Intents
import ops.sync.Conn

namespace Connection
open Engine Engine.Sync

/-! ## Each writer, its requirements -/

@[simp] theorem eph_reqs (sk : B) (of : Id) : (Eph.op sk of).reqs = [of] := rfl
@[simp] theorem opened_reqs (req s : Id) : (Opened.op req s).reqs = [req, s] := rfl
@[simp] theorem established_reqs (cid req e s : Id) : (Established.op cid req e s).reqs = [cid, req, e, s] := rfl
@[simp] theorem send_reqs (addr : B) (x : Op) : (Send.op addr x).reqs = [x.id] := rfl
@[simp] theorem recv_reqs (x : Id) (via : Option Id) (addr : B) (t : Nat) : (Recv.op x via addr t).reqs = [x] := rfl

theorem request_reqs (K : Keys) (seed to e h : B) {o : Op} (ho : Request.op K seed to e h = some o) :
    o.reqs = [] := by
  unfold Request.op at ho
  cases hw : Noise.write1 K.suite prologue (K.xSec seed) e (K.xPub to) h with
  | none => rw [hw] at ho; cases ho
  | some p => rw [hw] at ho; cases ho; rfl

theorem reply_reqs (K : Keys) (req : Id) (seed frm m1 f : B) {o : Op} (ho : Reply.op K req seed frm m1 f = some o) :
    o.reqs = [req] := by
  unfold Reply.op at ho
  simp only [bind, Option.bind] at ho
  split at ho
  · cases ho
  · dsimp only at ho
    split at ho
    · cases ho
    · cases ho; rfl

/-- **Every op the Connection family writes cites at most four**, within
the cap. -/
theorem writers_le : (∀ sk of, (Eph.op sk of).reqs.length ≤ maxReqs) ∧
    (∀ req s, (Opened.op req s).reqs.length ≤ maxReqs) ∧
    (∀ cid req e s, (Established.op cid req e s).reqs.length ≤ maxReqs) ∧
    (∀ addr x, (Send.op addr x).reqs.length ≤ maxReqs) ∧
    (∀ x via addr t, (Recv.op x via addr t).reqs.length ≤ maxReqs) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> simp [maxReqs]

/-! ## Sync's wire messages never reach intake -/

/-- **A wire op is never a conn op** in the node's family: the
Connection family owns kinds 32 to 38, and Community's scope is shared
or local. -/
theorem wire_not_conn (C : Community.Crypto) (K : Keys) {o : Op} (h : isWire o.kind = true) :
    (node C K).scope o ≠ .conn := by
  have hk : owns o.kind = false := by
    simp only [isWire, kRbsr, kHave, kWant, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with (h | h) | h <;> rw [h] <;> decide
  show (if owns o.kind then scopeOf o else Community.scopeOf o) ≠ .conn
  rw [hk]
  simp only [Bool.false_eq_true, ite_false, Community.scopeOf]
  split
  · split <;> simp
  · simp

/-- **The bare path takes no wire op.** -/
theorem intakeConn_wire (C : Community.Crypto) (K : Keys) {ops : List Op} {o : Op} (h : isWire o.kind = true) :
    o ∉ intakeConn (node C K) ops := fun hm => wire_not_conn C K h (intakeConn_conn _ hm).1

end Connection

namespace Connection.WireIntake
open Engine Engine.Sync

section
variable {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type}

theorem sat_pure' {P : α → Prop} {a : α} (h : P a) : Sat P (pure a : m α) :=
  ⟨pure ⟨a, h⟩, by simp⟩

theorem sat_bind_all {P : β → Prop} (x : m α) {f : α → m β} (h : ∀ a, Sat P (f a)) : Sat P (x >>= f) := by
  have h' : ∀ a, ∃ z : m { b // P b }, Subtype.val <$> z = f a := h
  refine ⟨x >>= fun a => Classical.choose (h' a), ?_⟩
  rw [map_bind]
  exact congrArg (x >>= ·) (funext fun a => Classical.choose_spec (h' a))

theorem sat_bind_pure {Q : α → Prop} {P : β → Prop} {x : m α} {g : α → β} (hx : Sat Q x)
    (h : ∀ a, Q a → P (g a)) : Sat P (x >>= fun a => pure (g a)) := by
  obtain ⟨z, hz⟩ := hx
  refine ⟨(fun a => ⟨g a.1, h a.1 a.2⟩) <$> z, ?_⟩
  rw [← hz, Functor.map_map, bind_map_left, map_eq_pure_bind]

end

section
variable {F : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Store F m] (fam : Family F) (cfg : Config)

theorem finish_take (s : Step) : (Conn.finish s).take = s.take := by
  unfold Conn.finish; rfl

theorem start_take (ix : Index) (c : Conn) (now : Nat) : (Conn.start cfg ix c now).take = [] := by
  unfold Conn.start; split <;> rfl

theorem onRbsr_take (ix : Index) (c : Conn) (r : Id) (k : Nat) (cs : List Claim) (now : Nat) :
    (Conn.onRbsr cfg ix c r k cs now).take = [] := by
  unfold Conn.onRbsr
  dsimp only
  repeat' split
  all_goals first | rfl | simp

theorem onHold_take_sat (c : Conn) (r : Id) (ids : List Id) :
    Sat (fun s : Step => s.take = []) (Conn.onHold (F := F) (m := m) fam cfg c r ids) := by
  unfold Conn.onHold
  split
  · exact sat_pure' rfl
  · split
    · exact sat_pure' rfl
    · exact sat_bind_all _ fun _ => sat_pure' (by simp)

theorem onWant_take_sat (ix : Index) (c : Conn) (ids : List Id) :
    Sat (fun s : Step => s.take = []) (Conn.onWant (F := F) (m := m) fam cfg ix c ids) := by
  unfold Conn.onWant
  split
  · exact sat_pure' rfl
  · exact sat_bind_all _ fun _ => sat_pure' (by simp)

/-- **A session's bytes are stored only as ops of no wire kind**: of what
the peer sends, `Conn.recv` takes for storing at most the one op it
decoded, and only when it is not sync's (`isWire`): a have, a want or a
round message is parsed and answered, never stored. -/
theorem recv_takes_no_wire (ix : Index) (c : Conn) (bytes : ByteArray) (now : Nat) :
    Sat (fun s : Step => ∀ o ∈ s.take, isWire o.kind = false) (Conn.recv (F := F) (m := m) fam cfg ix c bytes now) := by
  unfold Conn.recv
  split
  · exact sat_pure' (by simp)
  · rename_i o _
    dsimp only
    split
    · exact sat_pure' (by rw [finish_take]; split <;> simp [start_take])
    · exact sat_pure' (by rw [finish_take, onRbsr_take]; simp)
    · exact sat_bind_pure (onHold_take_sat (F := F) (m := m) fam cfg _ _ _) fun s hs => by
        show ∀ o ∈ (Conn.finish s).take, _
        rw [finish_take, hs]; simp
    · exact sat_bind_pure (onWant_take_sat (F := F) (m := m) fam cfg _ _ _) fun s hs => by
        show ∀ o ∈ (Conn.finish s).take, _
        rw [finish_take, hs]; simp
    · split
      · exact sat_pure' (by simp)
      · rename_i hw
        exact sat_pure' (by
          rw [finish_take, Step.limit_take]
          intro p hp
          simp only [List.mem_singleton] at hp
          subst hp
          simp only [Bool.or_eq_true, not_or] at hw
          simpa using hw.1)

end

end Connection.WireIntake
