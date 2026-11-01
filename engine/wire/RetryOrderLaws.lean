import engine.wire.RetryOrder

namespace Engine.Sync.RetryOrder
set_option linter.unusedSectionVars false
variable {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]

theorem claim_false (address : Option β) (candidate : Bool) (claimed : List β)
    (h : (claim address candidate claimed).1 = false) :
    (claim address candidate claimed).2 = claimed := by
  cases address <;> simp only [claim] at h ⊢
  split <;> simp_all

theorem claim_ready (a : β) (claimed : List β) (free : a ∉ claimed) :
    claim (some a) true claimed = (true, claimed ++ [a]) := by
  simp [claim, free]

theorem claim_busy (a : β) (candidate : Bool) (claimed : List β) (busy : a ∈ claimed) :
    claim (some a) candidate claimed = (false, claimed) := by
  simp [claim, busy]

/-- The actual singleton calls compose to the same streaming admission fold. -/
theorem scan_append (address : α → Option β) (candidate : α → Bool)
    (claimed : List β) (xs ys : List α) :
    scan address candidate claimed (xs ++ ys) =
      let first := scan address candidate claimed xs
      let second := scan address candidate first.2 ys
      (first.1 ++ second.1, second.2) := by
  induction xs generalizing claimed with
  | nil => simp [scan]
  | cons x xs ih =>
    simp only [List.cons_append, scan, ih]
    split <;> simp

theorem scan_members (address : α → Option β) (candidate : α → Bool)
    (claimed : List β) (queued : List α) :
    ∀ id ∈ (scan address candidate claimed queued).1, id ∈ queued := by
  induction queued generalizing claimed with
  | nil => simp [scan]
  | cons head tail ih =>
    simp only [scan]
    split
    · intro id mem
      rcases List.mem_cons.mp mem with rfl | mem
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih _ _ mem)
    · intro id mem
      exact List.mem_cons_of_mem _ (ih _ _ mem)

theorem offered_perm (sent queued : List α) : List.Perm (offered sent queued) queued := by
  have e : (fun id => !(!sent.contains id)) = sent.contains := by funext id; simp
  simpa only [offered, e] using List.filter_append_perm (fun id => !sent.contains id) queued

theorem offered_members (sent queued : List α) (id : α) :
    id ∈ offered sent queued ↔ id ∈ queued := (offered_perm sent queued).mem_iff

theorem offered_length (sent queued : List α) : (offered sent queued).length = queued.length :=
  (offered_perm sent queued).length_eq

theorem offered_nodup (sent queued : List α) (h : queued.Nodup) : (offered sent queued).Nodup :=
  (offered_perm sent queued).nodup_iff.mpr h

theorem offered_none (queued : List α) : offered [] queued = queued := by
  have yes : queued.filter (fun _ => true) = queued := List.filter_eq_self.mpr (by simp)
  have no : queued.filter ([] : List α).contains = [] := List.filter_eq_nil_iff.mpr (by simp)
  simpa only [offered, List.contains_nil, Bool.not_false, yes, no, List.append_nil]

theorem reconcile_members (live queued : List α) (id : α) :
    id ∈ reconcile live queued ↔ id ∈ live := by
  by_cases h : id ∈ queued <;> simp [reconcile, h]

theorem reconcile_prefix (live queued : List α) :
    (queued.filter live.contains).IsPrefix (reconcile live queued) := ⟨_, rfl⟩

theorem reconcile_nodup (live queued : List α) (hl : live.Nodup) (hq : queued.Nodup) :
    (reconcile live queued).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨hq.filter _, hl.filter _, ?_⟩
  intro a ha b hb eq
  subst b
  have hqa := (List.mem_filter.mp ha).1
  have hnb := (List.mem_filter.mp hb).2
  simpa [hqa] using hnb

/-- Filtering earlier entries never moves retained work backwards. -/
theorem filter_rank (keep : α → Bool) (queued : List α) (target : α)
    (present : target ∈ queued) (retained : keep target = true) :
    rank target (queued.filter keep) ≤ rank target queued := by
  unfold rank
  induction queued with
  | nil => cases present
  | cons head tail ih =>
    by_cases same : head = target
    · subst head; simp [retained]
    · have hit : target ∈ tail := (List.mem_cons.mp present).resolve_left (Ne.symm same)
      have h := ih hit
      by_cases kept : keep head = true
      · simpa [kept, List.idxOf_cons, same] using h
      · simp [kept, List.idxOf_cons, same]
        omega

theorem offered_rank (sent queued : List α) (target : α)
    (present : target ∈ queued) (waiting : target ∉ sent) :
    rank target (offered sent queued) ≤ rank target queued := by
  have retained : (!sent.contains target) = true := by simp [waiting]
  have mem : target ∈ queued.filter (fun id => !sent.contains id) :=
    List.mem_filter.mpr ⟨present, retained⟩
  unfold offered rank
  rw [List.idxOf_append, if_pos mem]
  exact filter_rank (fun id => !sent.contains id) queued target present retained

/-- In a vacant reservation opportunity, the executable admission scan either
selects a pending eligible target or rotates an earlier offerer behind it.
Other addresses may also be served; all predecessors count in the rank. -/
theorem scan_progress (address : α → Option β) (candidate : α → Bool)
    (claimed : List β) (queued : List α) (target : α) (a : β)
    (unique : queued.Nodup) (present : target ∈ queued)
    (route : address target = some a) (ready : candidate target = true)
    (free : a ∉ claimed) :
    let sent := (scan address candidate claimed queued).1
    target ∈ sent ∨ target ∈ offered sent queued ∧
      rank target (offered sent queued) < rank target queued := by
  induction queued generalizing claimed with
  | nil => cases present
  | cons head tail ih =>
    have hn := List.nodup_cons.mp unique
    by_cases same : head = target
    · subst head
      left
      simp [scan, route, ready, claim_ready a claimed free]
    · have hit : target ∈ tail := (List.mem_cons.mp present).resolve_left (Ne.symm same)
      cases decided : (claim (address head) (candidate head) claimed).1 with
      | true =>
        let sent := (scan address candidate claimed (head :: tail)).1
        by_cases selected : target ∈ sent
        · exact Or.inl selected
        · right
          have hs : head ∈ sent := by simp [sent, scan, decided]
          have retained : (!sent.contains target) = true := by simp [selected]
          have mem : target ∈ tail.filter (fun id => !sent.contains id) := List.mem_filter.mpr ⟨hit, retained⟩
          refine ⟨(offered_members sent _ _).mpr present, ?_⟩
          have less := filter_rank (fun id => !sent.contains id) tail target hit retained
          change rank target (offered sent (head :: tail)) < rank target (head :: tail)
          have hhead : sent.contains head = true := by simpa using hs
          have e : offered sent (head :: tail) =
              tail.filter (fun id => !sent.contains id) ++ head :: tail.filter sent.contains := by
            simp only [offered, List.filter_cons, hhead, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, List.cons_append]
          rw [e]
          unfold rank
          rw [List.idxOf_append, if_pos mem]
          have hne : (head == target) = false := by simp [same]
          simpa only [rank, List.idxOf_cons, hne, Bool.false_eq_true, ↓reduceIte, Nat.succ_eq_add_one] using Nat.lt_succ_of_le less
      | false =>
        have unchanged := claim_false (address head) (candidate head) claimed decided
        have eq : (scan address candidate claimed (head :: tail)).1 =
            (scan address candidate claimed tail).1 := by simp [scan, decided, unchanged]
        rw [eq]
        rcases ih claimed hn.2 hit free with selected | smaller
        · exact Or.inl selected
        · right
          let sent := (scan address candidate claimed tail).1
          have absent : head ∉ sent := fun mem => hn.1 (scan_members address candidate claimed tail head mem)
          refine ⟨(offered_members sent _ _).mpr present, ?_⟩
          change rank target (offered sent (head :: tail)) < rank target (head :: tail)
          have hhead : sent.contains head = false := by simp [absent]
          have e : offered sent (head :: tail) = head :: offered sent tail := by
            simp only [offered, List.filter_cons, hhead, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, List.cons_append]
          rw [e]
          have hne : (head == target) = false := by simp [same]
          simpa only [rank, List.idxOf_cons, hne, Bool.false_eq_true, ↓reduceIte, Nat.succ_eq_add_one] using Nat.succ_lt_succ smaller.2

theorem reconcile_rank (live queued : List α) (target : α)
    (present : target ∈ queued) (retained : target ∈ live) :
    rank target (reconcile live queued) ≤ rank target queued := by
  have kept : live.contains target = true := by simpa using retained
  have mem : target ∈ queued.filter live.contains := List.mem_filter.mpr ⟨present, kept⟩
  unfold reconcile rank
  rw [List.idxOf_append, if_pos mem]
  exact filter_rank live.contains queued target present kept

/-- A candidate is pending/eligible and its socket reservation is initially
vacant. This is a property of the actual scan inputs, not selector fairness. -/
def eligible (address : α → Option β) (candidate : α → Bool)
    (claimed : List β) (target : α) : Bool :=
  candidate target && (address target).any (fun a => !claimed.contains a)

theorem eligible_spec (address : α → Option β) (candidate : α → Bool)
    (claimed : List β) (target : α) (h : eligible address candidate claimed target = true) :
    candidate target = true ∧ ∃ a, address target = some a ∧ a ∉ claimed := by
  simp only [eligible, Bool.and_eq_true] at h
  refine ⟨h.1, ?_⟩
  cases route : address target with
  | none => simp [route] at h
  | some a => exact ⟨a, rfl, by simpa [route] using h.2⟩

/-- The running admission core's successive scans. Removals and new sessions
are reconciled after each scan; other socket routes and eligibility may vary. -/
structure Run (α β : Type) [BEq α] [BEq β] where
  queue : Nat → List α
  address : Nat → α → Option β
  candidate : Nat → α → Bool
  claimed : Nat → List β
  live : Nat → List α
  next : ∀ i, queue (i+1) = reconcile (live i)
    (offered (scan (address i) (candidate i) (claimed i) (queue i)).1 (queue i))

def Run.sent (r : Run α β) (i : Nat) : List α :=
  (scan (r.address i) (r.candidate i) (r.claimed i) (r.queue i)).1

def Run.opportunities (r : Run α β) (target : α) (start : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => r.opportunities target start n +
      if eligible (r.address (start+n)) (r.candidate (start+n)) (r.claimed (start+n)) target then 1 else 0

theorem Run.nodup (r : Run α β) (first : (r.queue 0).Nodup)
    (live : ∀ i, (r.live i).Nodup) (i : Nat) : (r.queue i).Nodup := by
  induction i with
  | zero => exact first
  | succ i ih => rw [r.next]; exact reconcile_nodup _ _ (live i) (offered_nodup _ _ ih)

/-- While the target waits, each eligible vacancy spends one predecessor.
Busy-socket ticks may be arbitrarily frequent; later arrivals never add rank. -/
theorem waiting_rank (r : Run α β) (unique : ∀ i, (r.queue i).Nodup)
    (start : Nat) (target : α) (present : target ∈ r.queue start) (n : Nat)
    (waiting : ∀ j, start ≤ j → j < start+n → target ∉ r.sent j ∧ target ∈ r.live j) :
    target ∈ r.queue (start+n) ∧
      rank target (r.queue (start+n)) + r.opportunities target start n ≤ rank target (r.queue start) := by
  induction n with
  | zero => simpa [Run.opportunities] using (And.intro present (Nat.le_refl (rank target (r.queue start))))
  | succ n ih =>
    have prev := ih (fun j lo hi => waiting j lo (by omega))
    have now := waiting (start+n) (by omega) (by omega)
    have mem : target ∈ offered (r.sent (start+n)) (r.queue (start+n)) :=
      (offered_members _ _ _).mpr prev.1
    have keepRank := reconcile_rank (r.live (start+n)) _ target mem now.2
    have nextMem : target ∈ r.queue (start+(n+1)) := by
      rw [show start+(n+1) = (start+n)+1 by omega, r.next]
      exact (reconcile_members _ _ _).mpr now.2
    refine ⟨nextMem, ?_⟩
    rw [show start+(n+1) = (start+n)+1 by omega, r.next]
    by_cases good : eligible (r.address (start+n)) (r.candidate (start+n)) (r.claimed (start+n)) target = true
    · obtain ⟨ready, a, route, free⟩ := eligible_spec _ _ _ _ good
      rcases scan_progress (r.address (start+n)) (r.candidate (start+n)) (r.claimed (start+n))
        (r.queue (start+n)) target a (unique _) prev.1 route ready free with selected | progress
      · exact False.elim (now.1 selected)
      · have less := Nat.lt_of_le_of_lt keepRank progress.2
        simp only [Run.opportunities, good, ↓reduceIte]
        change rank target (reconcile _ (offered (r.sent (start+n)) _)) + _ ≤ _
        omega
    · have weak := offered_rank (r.sent (start+n)) (r.queue (start+n)) target prev.1 now.1
      have le := Nat.le_trans keepRank weak
      have bad : eligible (r.address (start+n)) (r.candidate (start+n)) (r.claimed (start+n)) target = false := by simpa using good
      simp only [Run.opportunities, bad, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      change rank target (reconcile _ (offered (r.sent (start+n)) _)) + _ ≤ _
      omega

/-- Within p+1 pending-eligible vacant-reservation opportunities, a queued
session is offered service or explicitly retired. This bounds completed core
scans, not native sends, OS time, or the time between such opportunities. -/
theorem offered_or_retired (r : Run α β) (unique : ∀ i, (r.queue i).Nodup)
    (start : Nat) (target : α) (present : target ∈ r.queue start) (n : Nat)
    (enough : rank target (r.queue start) + 1 ≤ r.opportunities target start n) :
    ∃ j, start ≤ j ∧ j < start+n ∧ (target ∈ r.sent j ∨ target ∉ r.live j) := by
  classical
  apply Classical.byContradiction
  intro absent
  have waiting : ∀ j, start ≤ j → j < start+n → target ∉ r.sent j ∧ target ∈ r.live j := by
    intro j lo hi
    constructor
    · intro selected; exact absent ⟨j, lo, hi, Or.inl selected⟩
    · apply Classical.byContradiction
      intro retired
      exact absent ⟨j, lo, hi, Or.inr retired⟩
  have bound := (waiting_rank r unique start target present n waiting).2
  omega

end Engine.Sync.RetryOrder
