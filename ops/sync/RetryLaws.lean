/-
Bounds do not end sessions: honest_no_drop classifies every dropping
connection call as a timer expiry. retry_bounded counts actual decoded
want ids in tick's output. Ask timestamps expire independently of traffic.
-/
import ops.sync.TimeLaws
import ops.sync.BoundsLaws
import engine.wire.WorldLaws

namespace Engine.Sync
attribute [local instance] byteArray_lawfulBEq
variable {F : Type} (fam : Family F) (cfg : Config)

theorem known_forgets (cap : Nat) (known : Std.HashSet Id) (i : Id)
    (hp : 0 < cap) (hf : cap < (known.insert i).size) :
    remember cap known i = ({} : Std.HashSet Id).insert i := by
  simp [remember, show cap ≠ 0 by omega, show ¬ (known.insert i).size ≤ cap by omega]

theorem asked_full (cap : Nat) (asked : Std.HashSet Id) (ids : List Id)
    (hf : cap ≤ asked.size) : admitAsks cap asked ids = [] := by
  simp [admitAsks, Nat.sub_eq_zero_of_le hf]

theorem round_no_drop (ix : Index) (c : Conn) (r : Id) (k now : Nat) (cs : List Claim) :
    (c.onRbsr cfg ix r k cs now).drop = false := by
  unfold Conn.onRbsr
  split
  · rfl
  · dsimp only; split
    · rfl
    · exact Step.limit_drop _ _

theorem hold_no_drop (c : Conn) (r : Id) (ids : List Id) (h : Held F) :
    ((c.onHold fam cfg r ids : HeldM F Step) h).1.drop = false := by
  rw [onHold_apply]; split
  · rfl
  · split
    · rfl
    · exact Step.limit_drop _ _

theorem want_no_drop (ix : Index) (c : Conn) (ids : List Id) (h : Held F) :
    ((c.onWant fam cfg ix ids : HeldM F Step) h).1.drop = false := by
  unfold Conn.onWant; split
  · rfl
  · simp only [HeldM.bind_apply, HeldM.pure_apply, Step.limit_drop]

theorem recv_no_drop (ix : Index) (c : Conn) (bytes : ByteArray) (now : Nat) (h : Held F) :
    ((c.recv fam cfg ix bytes now : HeldM F Step) h).1.drop = false := by
  unfold Conn.recv
  cases hd : Op.decode bytes with
  | none => rfl
  | some o =>
    dsimp only
    cases hm : Msg.ofOp o with
    | none =>
      dsimp only
      split <;> simp [HeldM.pure_apply, Conn.finish, Step.limit_drop]
    | some msg =>
      cases msg with
      | hello f =>
        change (Conn.finish _).drop = false
        rw [Conn.finish_drop]
        split <;> rfl
      | rbsr r k cs => exact round_no_drop cfg _ _ _ _ _ _
      | hold r ids => simp only [HeldM.bind_apply, HeldM.pure_apply, Conn.finish_drop]; exact hold_no_drop fam cfg _ _ _ _
      | want ids => simp only [HeldM.bind_apply, HeldM.pure_apply, Conn.finish_drop]; exact want_no_drop fam cfg _ _ _ _

/-- An observed return from a public Conn entry point, using the running code. -/
inductive Conn.Call (fam : Family F) (cfg : Config) (c : Conn) (now : Nat) (h : Held F) : Step → Prop where
  | open (dialer rooms floor) : Call fam cfg c now h (Conn.open dialer rooms floor now)
  | start (ix) : Call fam cfg c now h (c.start cfg ix now)
  | round (ix r k cs) : Call fam cfg c now h (c.onRbsr cfg ix r k cs now)
  | hold (r ids) : Call fam cfg c now h ((c.onHold fam cfg r ids : HeldM F Step) h).1
  | want (ix ids) : Call fam cfg c now h ((c.onWant fam cfg ix ids : HeldM F Step) h).1
  | recv (ix bytes) : Call fam cfg c now h ((c.recv fam cfg ix bytes now : HeldM F Step) h).1
  | tick (ix) : Call fam cfg c now h ((c.tick fam cfg ix now : HeldM F Step) h).1
  | filed (ids) : Call fam cfg c now h ((c.filed fam cfg ids : HeldM F Step) h).1

/-- No set size or message handler drops a connection. Transport errors
and retirement enter Node's close path; within Conn only timers drop. -/
theorem honest_no_drop (c : Conn) (now : Nat) (h : Held F) (s : Step)
    (call : c.Call fam cfg now h s) (hd : s.drop = true) :
    (c.waiting = true ∧ c.waitStart + cfg.patience < now) ∨
      (c.dialer = false ∧ c.heard + cfg.lease < now) := by
  cases call with
  | «open» => cases hd
  | start ix => unfold Conn.start at hd; split at hd <;> cases hd
  | round ix r k cs => rw [round_no_drop] at hd; cases hd
  | hold r ids => rw [hold_no_drop] at hd; cases hd
  | want ix ids => rw [want_no_drop] at hd; cases hd
  | recv ix bytes => rw [recv_no_drop] at hd; cases hd
  | tick ix => exact (tick_drop_iff fam cfg ix c now h).1 hd
  | filed ids => simp [Conn.filed, HeldM.bind_apply, HeldM.pure_apply, Conn.finish] at hd

/-- The dropping premise is inhabited: a silent responder really expires. -/
theorem honest_no_drop_runs :
    ∃ (c : Conn) (s : Step), c.Call fam cfg (cfg.lease + 1) ({} : Held F) s ∧ s.drop = true := by
  let c : Conn := { dialer := false, rooms := [], floor := 0, peerFloor := some 0 }
  refine ⟨c, _, .tick {}, ?_⟩
  exact responder_expires fam cfg {} c (cfg.lease + 1) {} rfl (by simp [c])

theorem asks_expire (c : Conn) (now : Nat) (i : Id)
    (ht : (c.askTime[i]?.getD c.heard) + cfg.patience < now) :
    i ∉ (c.expireAsks cfg now).asked := by
  simp [Conn.expireAsks, Std.HashSet.mem_filter, show ¬ now ≤ (c.askTime[i]?.getD c.heard) + cfg.patience by omega]

/-- All decoded want ids, including every chunk, in an actual output. -/
def retried (ops : List Op) : List Id := ops.flatMap fun o =>
  match Msg.ofOp o with | some (.want ids) => ids | _ => []

@[simp] theorem retried_append (a b : List Op) : retried (a ++ b) = retried a ++ retried b := by
  simp [retried]

theorem retried_start (ix : Index) (c : Conn) (now : Nat) :
    retried (c.start cfg ix now).send = [] := by
  unfold Conn.start; split
  · rfl
  · simp [retried, Msg.ofOp, Msg.op, kRbsr, kHave, kWant, Codec.decode_encode]

theorem retried_holds (offers : List (Id × Id)) : retried (holdsOf cfg offers) = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro o ho
  obtain ⟨r, _, ho⟩ := List.mem_flatMap.mp ho
  obtain ⟨ids, _, rfl⟩ := List.mem_map.mp ho
  simp

theorem retried_chunks (ids : List Id) :
    retried (chunks cfg ids .want) = (pieceIds cfg.maxIds ids.length ids).flatten := by
  simp [retried, chunks, List.flatMap_map, Function.comp_def, List.flatten]

theorem pieces_short (n k : Nat) (ids : List Id) (hl : ids.length ≤ n) :
    (pieceIds n k ids).flatten.length ≤ ids.length := by
  cases k with
  | zero => simp [pieceIds]
  | succ k =>
    cases ids with
    | nil => simp [pieceIds]
    | cons i ids =>
      have he : pieceIds n k [] = [] := by cases k <;> rfl
      simp [pieceIds, List.take_of_length_le hl, List.drop_eq_nil_iff.mpr hl, he]

theorem retry_bounded (ix : Index) (c : Conn) (now : Nat) (h : Held F) :
    (retried ((c.tick fam cfg ix now : HeldM F Step) h).1.send).length ≤ cfg.maxIds := by
  unfold Conn.tick
  split
  · simp [HeldM.pure_apply, retried]
  · simp only [HeldM.bind_apply, HeldM.pure_apply, Conn.finish_send, retried_append, retried_holds, List.nil_append]
    have hr : ∀ d : Conn, (retried (chunks cfg (d.retryIds cfg now) .want)).length ≤ cfg.maxIds := by
      intro d
      rw [retried_chunks]
      have hl : (d.retryIds cfg now).length ≤ cfg.maxIds := by
        unfold Conn.retryIds; split
        · exact List.length_take_le _ _
        · simp
      exact Nat.le_trans (pieces_short _ _ _ hl) hl
    split
    · simpa only [retried_start, List.nil_append] using hr _
    · simpa only [retried, List.flatMap_nil, List.nil_append] using hr _

end Engine.Sync
