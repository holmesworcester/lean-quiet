/- Store progress for the actual Node.write deduplication path. -/
import engine.wire.NodeLaws
import engine.core.Locality
import engine.core.CarryLaws

namespace Engine.Sync
variable {F : Type}

local instance : LawfulBEq ByteArray where
  eq_of_beq {a b} h := ByteArray.ext (eq_of_beq (show a.data == b.data from h))
  rfl {a} := show a.data == a.data from beq_self_eq_true a.data

/-- The real session decoder hands a shown data operation's exact bytes
to the writer. Sync control messages and unshown data are excluded. -/
theorem recv_data_takes (fam : Family F) (cfg : Config) (ix : Index) (c : Conn)
    (o : Op) (now : Nat) (h : Held F)
    (hm : Msg.ofOp o = none) (hw : isWire o.kind = false) (hs : c.shows fam o = true) :
    ((c.recv fam cfg ix o.bytes now : HeldM F Step) h).1.take = [o] := by
  have hs' : ({ c with heard := now } : Conn).shows fam o = true := hs
  simp [Conn.recv, Op.decode_bytes, hm, hw, hs', HeldM.pure_apply]

/-- The index-update loop only reads; the only store change in `Node.write`
is the actual turn of previously absent operations. -/
theorem write_store (x : Sync F (HeldM F)) (n : Node) (h : Held F) (ops : List Op) :
    (n.write x ops h).2 =
      let absent := ops.foldl (absentStep h.db) []
      if absent.isEmpty then h else ((Turn.turn x.fam absent.reverse : HeldM F Unit) h).2 := by
  unfold Node.write
  simp only [HeldM.bind_apply]
  rw [HeldM.forIn_reads (g := absentStep h.db)]
  · dsimp only
    generalize ops.foldl (absentStep h.db) [] = absent
    split
    · rfl
    · simp only [HeldM.bind_apply]
      rw [HeldM.forIn_reads (g := fileStep x.fam ((Turn.turn x.fam absent.reverse : HeldM F Unit) h).2.db)]
      · rfl
      · intro a b
        rw [HeldM.bind_apply, HeldM.getOp_apply]
        unfold fileStep
        split <;> rfl
  · intro a b
    unfold absentStep
    split
    · rw [HeldM.bind_apply, HeldM.getOp_apply]
      split <;> rfl
    · rfl

theorem absentStep_keeps (s : DB F) (b : List Op) (p o : Op) (hp : p ∈ b) :
    p ∈ absentStep s b o := by
  unfold absentStep
  split
  · split
    · exact List.mem_cons_of_mem _ hp
    · exact hp
  · exact hp

theorem absentStep_source (s : DB F) (b : List Op) (p o : Op)
    (hp : p ∈ absentStep s b o) : p ∈ b ∨ p = o := by
  unfold absentStep at hp
  split at hp
  · split at hp
    · rcases List.mem_cons.mp hp with rfl | hp
      · exact Or.inr rfl
      · exact Or.inl hp
    · exact Or.inl hp
  · exact Or.inl hp

theorem absentFold_keeps (s : DB F) (ops b : List Op) {p : Op} (hp : p ∈ b) :
    p ∈ ops.foldl (absentStep s) b := by
  induction ops generalizing b with
  | nil => exact hp
  | cons o os ih => exact ih _ (absentStep_keeps s b p o hp)

theorem absentFold_source (s : DB F) (ops b : List Op) {p : Op}
    (hp : p ∈ ops.foldl (absentStep s) b) : p ∈ b ∨ p ∈ ops := by
  induction ops generalizing b with
  | nil => exact Or.inl hp
  | cons o os ih =>
    rcases ih _ hp with hp | hp
    · rcases absentStep_source s b p o hp with hp | rfl
      · exact Or.inl hp
      · exact Or.inr (List.mem_cons_self ..)
    · exact Or.inr (List.mem_cons_of_mem _ hp)

/-- Every absent input id survives deduplication through some input op.
The collision agreement below then identifies that op's full bytes. -/
theorem absentFold_covers (s : DB F) (ops b : List Op) {o : Op}
    (ho : o ∈ ops) (hn : s.ops o.id = none) :
    ∃ p ∈ ops.foldl (absentStep s) b, p.id = o.id := by
  induction ops generalizing b with
  | nil => cases ho
  | cons a os ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp ho with rfl | ho
    · by_cases hb : b.any (fun p => p.id == o.id) = true
      · obtain ⟨p, hp, hid⟩ := List.any_eq_true.mp hb
        exact ⟨p, absentFold_keeps s _ _ (absentStep_keeps s b p o hp), eq_of_beq hid⟩
      · refine ⟨o, absentFold_keeps s _ _ ?_, rfl⟩
        simp [absentStep, hb, hn]
    · exact ih _ ho

/-- Existing bytes are never overwritten by the running deduplicating write. -/
theorem write_preserves_op (x : Sync F (HeldM F)) (n : Node) (h : Held F) (ops : List Op)
    {i : Id} {o : Op} (ho : h.db.ops i = some o) :
    (n.write x ops h).2.db.ops i = some o := by
  rw [write_store]
  dsimp only
  split
  · exact ho
  · rw [turn_apply]
    show (turnCappedS _ _ _ _).ops i = some o
    rw [turnCappedS_ops]
    exact foldl_ingest_keep _ ho

/-- An incoming operation is stored, including when its id was already
present, provided all representations of that id agree on its bytes. -/
theorem write_takes (x : Sync F (HeldM F)) (n : Node) (h : Held F) (ops : List Op)
    (hi : Inv x.fam h.db) {o : Op} (ho : o ∈ ops)
    (sameInput : ∀ p ∈ ops, p.id = o.id → p = o)
    (sameStore : ∀ p, h.db.ops o.id = some p → p = o) :
    (n.write x ops h).2.db.ops o.id = some o := by
  cases hg : h.db.ops o.id with
  | some p =>
    have he := sameStore p hg
    subst p
    exact write_preserves_op x n h ops hg
  | none =>
    obtain ⟨p, hp, hid⟩ := absentFold_covers h.db ops [] ho hg
    have hsource : p ∈ ops := (absentFold_source h.db ops [] hp).resolve_left (by simp)
    have he := sameInput p hsource hid
    subst p
    have hn : (ops.foldl (absentStep h.db) []).isEmpty = false := by
      cases he : ops.foldl (absentStep h.db) [] with
      | nil => rw [he] at hp; cases hp
      | cons q qs => rfl
    rw [write_store]
    simp only [hn, Bool.false_eq_true, ite_false, turn_apply]
    show (turnCappedS _ _ _ _).ops o.id = some o
    rw [turnCappedS_ops]
    obtain ⟨hnew, hdistinct⟩ := absentOf_new h.db ops
    exact (foldl_ingest_new x.fam hi (ops.foldl (absentStep h.db) []).reverse
      (fun q hq => hnew q (List.mem_reverse.mp hq))
      (by rw [List.map_reverse]; exact (List.reverse_perm _).nodup_iff.mpr hdistinct)).2.2
      o (List.mem_reverse.mpr hp)

/-- The Held log records the same received operations as an actual engine
history. Its chronological order may differ from `Engine.Reach`'s list. -/
def Held.Reachable (fam : Family F) (h : Held F) : Prop :=
  ∃ history, Engine.Reach fam history h.db ∧ ∀ o, o ∈ history ↔ o ∈ h.log

theorem held_empty_reachable (fam : Family F) : ({} : Held F).Reachable fam :=
  ⟨[], .empty, fun _ => Iff.rfl⟩

theorem ingest_many_reachable (fam : Family F) (ops history : List Op) (s : DB F)
    (hr : Engine.Reach fam history s) :
    Engine.Reach fam (ops.reverse ++ history) (ops.foldl (fun s o => ingestS o s) s) := by
  induction ops generalizing history s with
  | nil => simpa using hr
  | cons o os ih =>
    simpa [List.reverse_cons, List.append_assoc] using ih (o :: history) (ingestS o s) (.ingest o hr)

theorem turn_reachable (fam : Family F) (ops : List Op) (h : Held F) (hr : h.Reachable fam) :
    (((Turn.turn fam ops : HeldM F Unit) h).2).Reachable fam := by
  obtain ⟨history, hr, same⟩ := hr
  refine ⟨ops.reverse ++ history, reach_turnCapped hr drainCap ops, ?_⟩
  intro o
  simpa only [turn_apply, List.mem_append, List.mem_reverse, same] using
    (or_comm : o ∈ ops ∨ o ∈ h.log ↔ o ∈ h.log ∨ o ∈ ops)

/-- **A write turn keeps urgent work settled** (`turn_waiting`), on the
store a node runs: whatever it leaves queued, every urgent op whose
closure is all urgent is decided or waits on an undecided requirement. -/
theorem turn_waiting_held (fam : Family F) (ops : List Op) (h : Held F)
    (hr : h.Reachable fam) (hw : UrgentWaiting fam h.db) :
    UrgentWaiting fam (((Turn.turn fam ops : HeldM F Unit) h).2).db :=
  let ⟨_, hr, _⟩ := hr; turn_waiting hr hw drainCap ops

/-- A write turn's tables are a capped turn's. -/
theorem turn_step (fam : Family F) (ops : List Op) (h : Held F) :
    TurnStep fam drainCap h.db (((Turn.turn fam ops : HeldM F Unit) h).2).db := Or.inr ⟨ops, rfl⟩

theorem write_reachable (x : Sync F (HeldM F)) (n : Node) (h : Held F) (ops : List Op)
    (hr : h.Reachable x.fam) : ((n.write x ops h).2).Reachable x.fam := by
  rw [write_store]
  dsimp only
  split
  · exact hr
  · exact turn_reachable x.fam _ h hr

theorem write_log_subset (x : Sync F (HeldM F)) (n : Node) (h : Held F) (ops : List Op) :
    (n.write x ops h).2.log ⊆ h.log ++ ops := by
  rw [write_store]
  dsimp only
  split
  · exact List.subset_append_left _ _
  · rw [turn_apply]
    intro o ho
    rcases List.mem_append.mp ho with ho | ho
    · exact List.mem_append_left _ ho
    · exact List.mem_append_right _
        ((absentFold_source h.db ops [] (List.mem_reverse.mp ho)).resolve_left (by simp))

theorem write_waiting (x : Sync F (HeldM F)) (n : Node) (h : Held F) (ops : List Op)
    (hr : h.Reachable x.fam) (hw : UrgentWaiting x.fam h.db) :
    UrgentWaiting x.fam (n.write x ops h).2.db := by
  rw [write_store]
  dsimp only
  split
  · exact hw
  · exact turn_waiting_held x.fam _ h hr hw

/-- A write's tables are its turn's, or unchanged. -/
theorem write_step (x : Sync F (HeldM F)) (n : Node) (h : Held F) (ops : List Op) :
    TurnStep x.fam drainCap h.db (n.write x ops h).2.db := by
  rw [write_store]
  dsimp only
  split
  · exact Or.inl rfl
  · exact turn_step x.fam _ h

/-- Receive turns of the actual `Node.put` path after wire decoding and
session authorization, and idle turns (a tick's `Turn.turn` of no ops,
`Node.onTick`) that carry what a capped turn left queued. The transport
contract supplies input operations, not a claim about the final
database. Each input can contain duplicates and arrive in arbitrary
dependency order. -/
structure ReceiverRun (x : Sync F (HeldM F)) where
  node : Nat → Node
  store : Nat → Held F
  input : Nat → List Op
  /-- Whether step n is an idle turn rather than a receive. -/
  idle : Nat → Bool
  next : ∀ n, store (n + 1) = if idle n then ((Turn.turn x.fam [] : HeldM F Unit) (store n)).2
    else ((node n).put x (input n) false (store n)).2
  initial : (store 0).Reachable x.fam
  initialWaiting : UrgentWaiting x.fam (store 0).db
  /-- Collision agreement on this finite prefix, including retransmissions. -/
  distinct : ∀ n, Distinct ((store n).log ++ input n)

/-- **Turns keep coming**: the receiver's process keeps getting scheduled,
so idle turns recur (the environment's assumption; the runner's timer
fires ticks: holmes-ce's selector/timer law). -/
def ReceiverRun.Ticks {x : Sync F (HeldM F)} (r : ReceiverRun x) : Prop := ∀ N, ∃ j ≥ N, r.idle j = true

namespace ReceiverRun
variable {x : Sync F (HeldM F)} (r : ReceiverRun x)

theorem store_reachable (n : Nat) : (r.store n).Reachable x.fam := by
  induction n with
  | zero => exact r.initial
  | succ n ih =>
    rw [r.next]
    split
    · exact turn_reachable x.fam _ _ ih
    · exact write_reachable x _ _ _ ih

theorem invariant (n : Nat) : Inv x.fam (r.store n).db :=
  let ⟨_, hr, _⟩ := r.store_reachable n; reach_inv hr

/-- **Urgent work is settled at every step** (`UrgentWaiting`, so
`UrgentSettled`). -/
theorem waiting (n : Nat) : UrgentWaiting x.fam (r.store n).db := by
  induction n with
  | zero => exact r.initialWaiting
  | succ n ih =>
    rw [r.next]
    split
    · exact turn_waiting_held x.fam _ _ (r.store_reachable n) ih
    · exact write_waiting x _ _ _ (r.store_reachable n) ih

/-- Each step's tables are a capped turn's, or unchanged. -/
theorem step (n : Nat) : TurnStep x.fam drainCap (r.store n).db (r.store (n + 1)).db := by
  rw [r.next]
  split
  · exact turn_step x.fam _ _
  · exact write_step x _ _ _

/-- With ticks, turns recur. -/
theorem turnsRecur (ht : r.Ticks) : TurnsRecur x.fam drainCap fun n => (r.store n).db := by
  intro N
  obtain ⟨j, hj, hi⟩ := ht N
  refine ⟨j, hj, [], ?_⟩
  show (r.store (j + 1)).db = _
  rw [r.next, if_pos hi]; rfl

theorem keeps {n : Nat} {i : Id} {o : Op} (ho : (r.store n).db.ops i = some o) :
    (r.store (n + 1)).db.ops i = some o := by
  rw [r.next]
  split
  · show (turnCappedS _ _ _ _).ops i = some o
    rw [turnCappedS_ops]; exact ho
  · exact write_preserves_op x _ _ _ ho

theorem retains {n k : Nat} {i : Id} {o : Op} (hnk : n ≤ k)
    (ho : (r.store n).db.ops i = some o) : (r.store k).db.ops i = some o := by
  induction hnk with
  | refl => exact ho
  | step _ ih => exact r.keeps ih

/-- Actual receive intake stores every shared input within the
requirement cap; duplicate and out-of-order receipt do not weaken this
guarantee. -/
theorem receives {n : Nat} {o : Op} (hn : r.idle n = false) (ho : o ∈ r.input n) (hs : x.fam.shared o = true)
    (hc : o.capped = true) :
    (r.store (n + 1)).db.ops o.id = some o := by
  rw [r.next, if_neg (by rw [hn]; exact Bool.false_ne_true)]
  apply write_takes x _ _ _ (r.invariant n)
  · exact mem_intake_shared x.fam ho hs hc
  · intro p hp he
    exact r.distinct n p (List.mem_append_right _ (intake_sub x.fam hp))
      o (List.mem_append_right _ ho) he
  · intro p hp
    obtain ⟨history, hr, same⟩ := r.store_reachable n
    obtain ⟨hmem, hid⟩ := reach_stored hr _ p hp
    exact r.distinct n p (List.mem_append_left _ ((same p).mp hmem))
      o (List.mem_append_right _ ho) hid

end ReceiverRun

end Engine.Sync
