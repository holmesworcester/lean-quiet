/- Store progress for the actual Node.write deduplication path. -/
import engine.wire.NodeLaws
import engine.core.Locality

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
    simp only [drainS_ops]
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
    simp only [hn, Bool.false_eq_true, ite_false, turn_apply, drainS_ops]
    obtain ⟨hnew, hdistinct⟩ := absentOf_new h.db ops
    exact (foldl_ingest_new x.fam hi (ops.foldl (absentStep h.db) []).reverse
      (fun q hq => hnew q (List.mem_reverse.mp hq))
      (by rw [List.map_reverse]; exact (List.reverse_perm _).nodup_iff.mpr hdistinct)).2.2
      o (List.mem_reverse.mpr hp)

theorem dedup_nodup (ops : List Op) : ops.eraseDups.Nodup := by
  match ops with
  | [] => simp
  | o :: os =>
    rw [List.eraseDups_cons, List.nodup_cons]
    exact ⟨by simp, dedup_nodup _⟩
termination_by ops.length
decreasing_by have := List.length_filter_le (fun p : Op => !p == o) os; simp; omega

/-- The engine's finite draining budget depends on the set of received
operations, not the order used to record their history. -/
theorem budget_same_ops (a b : List Op) (s : DB F)
    (same : ∀ o, o ∈ a ↔ o ∈ b) : budget a s = budget b s := by
  have hp : a.eraseDups.Perm b.eraseDups :=
    (List.perm_ext_iff_of_nodup (dedup_nodup a) (dedup_nodup b)).mpr
      (fun o => by simpa using same o)
  have hu := (hp.filter (fun o => (s.status o.id).isNone)).length_eq
  simp only [budget, undecided, hp.length_eq, hu]

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
  refine ⟨ops.reverse ++ history, reach_drain (ingest_many_reachable fam ops history h.db hr) _, ?_⟩
  intro o
  simpa only [turn_apply, List.mem_append, List.mem_reverse, same] using
    (or_comm : o ∈ ops ∨ o ∈ h.log ↔ o ∈ h.log ∨ o ∈ ops)

/-- The actual turn's computed budget settles validation; it is not a
fairness assumption about a separate judging process. -/
theorem turn_settles (fam : Family F) (ops : List Op) (h : Held F)
    (hr : h.Reachable fam) (hd : Distinct (h.log ++ ops)) :
    (((Turn.turn fam ops : HeldM F Unit) h).2).db.queue = [] := by
  obtain ⟨history, hr, same⟩ := hr
  have hsame : ∀ o, o ∈ ops.reverse ++ history ↔ o ∈ h.log ++ ops := by
    intro o
    simp only [List.mem_append, List.mem_reverse, same]
    exact or_comm
  have hdistinct : Distinct (ops.reverse ++ history) :=
    fun a ha b hb he => hd a ((hsame a).mp ha) b ((hsame b).mp hb) he
  have hreach := ingest_many_reachable fam ops history h.db hr
  rw [turn_apply]
  exact drain_bounded hdistinct _ _ hreach (Nat.le_of_eq (budget_same_ops _ _ _ hsame))

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

theorem write_settles (x : Sync F (HeldM F)) (n : Node) (h : Held F) (ops : List Op)
    (hr : h.Reachable x.fam) (hq : h.db.queue = []) (hd : Distinct (h.log ++ ops)) :
    (n.write x ops h).2.db.queue = [] := by
  rw [write_store]
  dsimp only
  split
  · exact hq
  · apply turn_settles x.fam _ h hr
    have sub : (ops.foldl (absentStep h.db) []).reverse ⊆ ops := by
      intro o ho
      exact (absentFold_source h.db ops [] (List.mem_reverse.mp ho)).resolve_left (by simp)
    intro a ha b hb he
    apply hd a (List.mem_append.mp ha |>.elim (List.mem_append_left _) (fun h => List.mem_append_right _ (sub h)))
      b (List.mem_append.mp hb |>.elim (List.mem_append_left _) (fun h => List.mem_append_right _ (sub h))) he

/-- Receive turns of the actual `Node.put` path after wire decoding and
session authorization. The transport contract supplies input operations,
not a claim about the final database. Each input can contain duplicates and
arrive in arbitrary dependency order. -/
structure ReceiverRun (x : Sync F (HeldM F)) where
  node : Nat → Node
  store : Nat → Held F
  input : Nat → List Op
  next : ∀ n, store (n + 1) = ((node n).put x (input n) false (store n)).2
  initial : (store 0).Reachable x.fam
  initialQueue : (store 0).db.queue = []
  /-- Collision agreement on this finite prefix, including retransmissions. -/
  distinct : ∀ n, Distinct ((store n).log ++ input n)

namespace ReceiverRun
variable {x : Sync F (HeldM F)} (r : ReceiverRun x)

theorem reachable (n : Nat) : (r.store n).Reachable x.fam := by
  induction n with
  | zero => exact r.initial
  | succ n ih => rw [r.next]; exact write_reachable x _ _ _ ih

theorem invariant (n : Nat) : Inv x.fam (r.store n).db :=
  let ⟨_, hr, _⟩ := r.reachable n; reach_inv hr

theorem settled (n : Nat) : (r.store n).db.queue = [] := by
  induction n with
  | zero => exact r.initialQueue
  | succ n ih =>
    rw [r.next]
    apply write_settles x _ _ _ (r.reachable n) ih
    intro a ha b hb he
    have sub : intake x.fam false (r.input n) ⊆ r.input n := by
      intro o ho
      exact (List.mem_filter.mp ho).1
    exact r.distinct n a (List.mem_append.mp ha |>.elim (List.mem_append_left _) (fun h => List.mem_append_right _ (sub h)))
      b (List.mem_append.mp hb |>.elim (List.mem_append_left _) (fun h => List.mem_append_right _ (sub h))) he

theorem keeps {n : Nat} {i : Id} {o : Op} (ho : (r.store n).db.ops i = some o) :
    (r.store (n + 1)).db.ops i = some o := by
  rw [r.next]
  exact write_preserves_op x _ _ _ ho

theorem retains {n k : Nat} {i : Id} {o : Op} (hnk : n ≤ k)
    (ho : (r.store n).db.ops i = some o) : (r.store k).db.ops i = some o := by
  induction hnk with
  | refl => exact ho
  | step _ ih => exact r.keeps ih

/-- Actual receive intake stores every shared input; duplicate and
out-of-order receipt do not weaken this guarantee. -/
theorem receives {n : Nat} {o : Op} (ho : o ∈ r.input n) (hs : x.fam.shared o = true) :
    (r.store (n + 1)).db.ops o.id = some o := by
  rw [r.next]
  apply write_takes x _ _ _ (r.invariant n)
  · exact List.mem_filter.mpr ⟨ho, hs⟩
  · intro p hp he
    exact r.distinct n p (List.mem_append_right _ (List.mem_filter.mp hp).1)
      o (List.mem_append_right _ ho) he
  · intro p hp
    obtain ⟨history, hr, same⟩ := r.reachable n
    obtain ⟨hmem, hid⟩ := reach_stored hr _ p hp
    exact r.distinct n p (List.mem_append_left _ ((same p).mp hmem))
      o (List.mem_append_right _ ho) hid

end ReceiverRun

end Engine.Sync
