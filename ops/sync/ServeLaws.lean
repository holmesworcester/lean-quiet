/-
Read traces and byte bounds for the want reader used by Conn.onWant.
The trace is the running read program with a pure store lookup; its
interpreters below agree on both held stores and the engine's DB.
-/
import engine.wire.NodeLaws

namespace Engine.Sync

variable {F : Type}

theorem Read.run_held (p : Read α) (h : Held F) :
    (p.run (Store.getOp (F := F)) : HeldM F α) h = ((p.trace h.db.ops).1, h) := by
  induction p with
  | done a => rfl
  | get i next ih => simp [Read.run, Read.trace, ih]

theorem Read.run_model (p : Read α) (s : DB F) :
    (p.run (Store.getOp (F := F)) : Model F α).run s = ((p.trace s.ops).1, s) := by
  induction p with
  | done a => rfl
  | get i next ih => simp [Read.run, Read.trace, ih]

/-! ## Serving a queue, as a read program -/

section
variable (shows : Op → Bool)

theorem serve_nil (get : Id → Option Op) (budget : Nat) :
    (serve shows budget []).trace get = (([], []), []) := rfl

theorem serve_zero (get : Id → Option Op) (ids : List Id) :
    (serve shows 0 ids).trace get = (([], ids), []) := by
  cases ids <;> rfl

theorem serve_cons (get : Id → Option Op) (i : Id) (ids : List Id) (budget : Nat) (hb : 0 < budget) :
    (serve shows budget (i :: ids)).trace get =
      match get i with
      | none => let t := (serve shows budget ids).trace get; (t.1, i :: t.2)
      | some o =>
        if shows o then
          if budget ≤ o.bytes.size then (([o], ids), [i])
          else let t := (serve shows (budget - o.bytes.size) ids).trace get; ((o :: t.1.1, t.1.2), i :: t.2)
        else let t := (serve shows budget ids).trace get; (t.1, i :: t.2) := by
  simp only [serve, Nat.ne_of_gt hb, ite_false, Read.trace]
  cases get i with
  | none => rfl
  | some o =>
    dsimp only
    split
    · split
      · rfl
      · simp [Read.trace_map]
    · rfl

/-- **A queue is served only from its own ids.** -/
theorem serve_reads (get : Id → Option Op) (ids : List Id) (budget : Nat) :
    ∀ i ∈ ((serve shows budget ids).trace get).2, i ∈ ids := by
  induction ids generalizing budget with
  | nil => simp [serve_nil]
  | cons x xs ih =>
    rcases Nat.eq_zero_or_pos budget with rfl | hb
    · simp [serve_zero]
    rw [serve_cons shows get x xs budget hb]
    intro i hi
    cases hg : get x with
    | none =>
      simp only [hg] at hi
      rcases List.mem_cons.1 hi with rfl | hi
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih _ i hi)
    | some o =>
      simp only [hg] at hi
      split at hi
      · split at hi
        · simp at hi; subst hi; exact List.mem_cons_self ..
        · rcases List.mem_cons.1 hi with rfl | hi
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (ih _ i hi)
      · rcases List.mem_cons.1 hi with rfl | hi
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (ih _ i hi)

/-- **What a queue's service sends is shown, and stored under one of its
ids.** -/
theorem serve_shown (get : Id → Option Op) (ids : List Id) (budget : Nat) :
    ∀ o ∈ ((serve shows budget ids).trace get).1.1, shows o = true ∧ ∃ i ∈ ids, get i = some o := by
  induction ids generalizing budget with
  | nil => simp [serve_nil]
  | cons x xs ih =>
    rcases Nat.eq_zero_or_pos budget with rfl | hb
    · simp [serve_zero]
    rw [serve_cons shows get x xs budget hb]
    intro o ho
    cases hg : get x with
    | none =>
      simp only [hg] at ho
      obtain ⟨hs, i, hi, e⟩ := ih budget o ho
      exact ⟨hs, i, List.mem_cons_of_mem _ hi, e⟩
    | some y =>
      simp only [hg] at ho
      split at ho
      · rename_i hy
        split at ho
        · simp at ho; subst ho; exact ⟨hy, x, List.mem_cons_self .., hg⟩
        · rcases List.mem_cons.1 ho with rfl | ho
          · exact ⟨hy, x, List.mem_cons_self .., hg⟩
          · obtain ⟨hs, i, hi, e⟩ := ih _ o ho
            exact ⟨hs, i, List.mem_cons_of_mem _ hi, e⟩
      · obtain ⟨hs, i, hi, e⟩ := ih budget o ho
        exact ⟨hs, i, List.mem_cons_of_mem _ hi, e⟩

/-- **Blind outside the queue:** stores agreeing on the queue's ids have
exactly the same reads, ops and rest. -/
theorem serve_blind (a b : Id → Option Op) (ids : List Id) (budget : Nat)
    (agree : ∀ i ∈ ids, a i = b i) :
    (serve shows budget ids).trace a = (serve shows budget ids).trace b := by
  induction ids generalizing budget with
  | nil => rfl
  | cons x xs ih =>
    rcases Nat.eq_zero_or_pos budget with rfl | hb
    · simp [serve_zero]
    have ht := fun i hi => agree i (List.mem_cons_of_mem x hi)
    rw [serve_cons shows a x xs budget hb, serve_cons shows b x xs budget hb, agree x (List.mem_cons_self ..)]
    cases b x with
    | none => simp [ih _ ht]
    | some o =>
      dsimp only
      split
      · split
        · rfl
        · simp [ih _ ht]
      · simp [ih _ ht]

/-- **A step serves at most `budget` bytes, and one op more.** -/
theorem serve_budget (get : Id → Option Op) (ids : List Id) (budget : Nat) :
    let ops := ((serve shows budget ids).trace get).1.1
    replyBytes ops ≤ budget + largestOp ops := by
  induction ids generalizing budget with
  | nil => simp [serve_nil, replyBytes, largestOp]
  | cons x xs ih =>
    rcases Nat.eq_zero_or_pos budget with rfl | hb
    · simp [serve_zero, replyBytes, largestOp]
    rw [serve_cons shows get x xs budget hb]
    cases get x with
    | none => exact ih budget
    | some o =>
      dsimp only; split
      · split
        · simp [replyBytes, largestOp]
        · have := ih (budget - o.bytes.size)
          simp only [replyBytes, largestOp, List.map_cons, List.sum_cons, List.foldr_cons] at this ⊢
          omega
      · exact ih budget

/-- **First in, first out:** what is left is the queue's tail. -/
theorem serve_rest (get : Id → Option Op) (ids : List Id) (budget : Nat) :
    ∃ pre, ids = pre ++ ((serve shows budget ids).trace get).1.2 := by
  induction ids generalizing budget with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
    rcases Nat.eq_zero_or_pos budget with rfl | hb
    · exact ⟨[], by simp [serve_zero]⟩
    rw [serve_cons shows get x xs budget hb]
    cases get x with
    | none => obtain ⟨pre, e⟩ := ih budget; exact ⟨x :: pre, by simp [← e]⟩
    | some o =>
      dsimp only; split
      · split
        · exact ⟨[x], rfl⟩
        · obtain ⟨pre, e⟩ := ih (budget - o.bytes.size); exact ⟨x :: pre, by simp [← e]⟩
      · obtain ⟨pre, e⟩ := ih budget; exact ⟨x :: pre, by simp [← e]⟩

/-- **A step with a budget serves the queue's head** when its op is
stored and shown, and always moves past it. -/
theorem serve_head (get : Id → Option Op) (i : Id) (ids : List Id) (budget : Nat) (hb : 0 < budget)
    (o : Op) (hg : get i = some o) (hs : shows o = true) :
    o ∈ ((serve shows budget (i :: ids)).trace get).1.1 := by
  rw [serve_cons shows get i ids budget hb, hg]
  simp only [hs, ite_true]
  split <;> simp

theorem serve_shrinks (get : Id → Option Op) (i : Id) (ids : List Id) (budget : Nat) (hb : 0 < budget) :
    ((serve shows budget (i :: ids)).trace get).1.2.length ≤ ids.length := by
  rw [serve_cons shows get i ids budget hb]
  cases get i with
  | none =>
    obtain ⟨pre, e⟩ := serve_rest shows get ids budget
    exact (congrArg List.length e).symm ▸ (by simp)
  | some o =>
    dsimp only; split
    · split
      · simp
      · obtain ⟨pre, e⟩ := serve_rest shows get ids (budget - o.bytes.size)
        exact (congrArg List.length e).symm ▸ (by simp)
    · obtain ⟨pre, e⟩ := serve_rest shows get ids budget
      exact (congrArg List.length e).symm ▸ (by simp)

/-! ## Fetching a list -/

theorem fetch_cons (get : Id → Option Op) (i : Id) (ids : List Id) :
    (fetch shows (i :: ids)).trace get =
      let t := (fetch shows ids).trace get
      ((match get i with | some o => if shows o then o :: t.1 else t.1 | none => t.1), i :: t.2) := by
  simp only [fetch, Read.trace]
  cases get i with
  | none => rfl
  | some o => dsimp only; split <;> simp [Read.trace_map]

theorem fetch_reads (get : Id → Option Op) (ids : List Id) :
    ((fetch shows ids).trace get).2 = ids := by
  induction ids with
  | nil => rfl
  | cons x xs ih => rw [fetch_cons]; simp [ih]

theorem fetch_shown (get : Id → Option Op) (ids : List Id) :
    ∀ o ∈ ((fetch shows ids).trace get).1, shows o = true ∧ ∃ i ∈ ids, get i = some o := by
  induction ids with
  | nil => simp [fetch, Read.trace]
  | cons x xs ih =>
    rw [fetch_cons]
    intro o ho
    cases hg : get x with
    | none =>
      simp only [hg] at ho
      obtain ⟨hs, i, hi, e⟩ := ih o ho; exact ⟨hs, i, List.mem_cons_of_mem _ hi, e⟩
    | some y =>
      simp only [hg] at ho
      split at ho
      · rcases List.mem_cons.1 ho with rfl | ho
        · exact ⟨by assumption, x, List.mem_cons_self .., hg⟩
        · obtain ⟨hs, i, hi, e⟩ := ih o ho; exact ⟨hs, i, List.mem_cons_of_mem _ hi, e⟩
      · obtain ⟨hs, i, hi, e⟩ := ih o ho; exact ⟨hs, i, List.mem_cons_of_mem _ hi, e⟩

/-- **Every id fetched whose op is stored and shown is sent.** -/
theorem fetch_all (get : Id → Option Op) (ids : List Id) (i : Id) (o : Op) (hi : i ∈ ids)
    (hg : get i = some o) (hs : shows o = true) : o ∈ ((fetch shows ids).trace get).1 := by
  induction ids with
  | nil => cases hi
  | cons x xs ih =>
    rw [fetch_cons]
    rcases List.mem_cons.1 hi with rfl | hi
    · simp [hg, hs]
    · have := ih hi
      dsimp only
      cases get x with
      | none => exact this
      | some y => dsimp only; split <;> simp [this]

theorem fetch_blind (a b : Id → Option Op) (ids : List Id) (agree : ∀ i ∈ ids, a i = b i) :
    (fetch shows ids).trace a = (fetch shows ids).trace b := by
  induction ids with
  | nil => rfl
  | cons x xs ih =>
    rw [fetch_cons, fetch_cons, agree x (List.mem_cons_self ..), ih fun i hi => agree i (List.mem_cons_of_mem _ hi)]

end

local instance : LawfulBEq ByteArray where
  eq_of_beq {a b} h := ByteArray.ext (eq_of_beq (show a.data == b.data from h))
  rfl {a} := show a.data == a.data from beq_self_eq_true a.data

theorem eraseDups_loop_length {α} (r : α → α → Bool) :
    ∀ (l acc : List α), (List.eraseDupsBy.loop r l acc).length ≤ l.length + acc.length
  | [], acc => by simp [List.eraseDupsBy.loop]
  | a :: l, acc => by
    unfold List.eraseDupsBy.loop
    split
    · have := eraseDups_loop_length r l acc; simp only [List.length_cons]; omega
    · have := eraseDups_loop_length r l (a :: acc); simp only [List.length_cons] at this ⊢; omega

theorem eraseDups_length_le {α} [BEq α] (l : List α) : l.eraseDups.length ≤ l.length := by
  have := eraseDups_loop_length (· == ·) l []
  simpa [List.eraseDups, List.eraseDupsBy] using this

theorem authorize_mem (ix : Index) (c : Conn) (ids : List Id) (i : Id) :
    i ∈ authorize ix c ids ↔ i ∈ ids ∧ ∃ r ∈ c.rooms, ∃ a ∈ ix.items r, a.2 = i := by
  simp only [authorize, List.mem_filter, List.any_eq_true, decide_eq_true_eq]

/-! ## The want queue -/

/-- **Only authorized ids join the queue:** each id a want adds is one
of the want's, indexed in a room the session shows. No blob is read. -/
theorem onWant_authorized (cfg : Config) (ix : Index) (c : Conn) (ids : List Id) :
    ∀ i ∈ (c.onWant cfg ix ids).conn.owed, i ∈ c.owed ∨ (i ∈ ids ∧ ∃ r ∈ c.rooms, ∃ a ∈ ix.items r, a.2 = i) := by
  intro i hi
  unfold Conn.onWant at hi
  split at hi
  · exact Or.inl hi
  · rcases List.mem_append.1 hi with hi | hi
    · exact Or.inl hi
    · right
      have := List.mem_of_mem_take hi
      have := (List.mem_eraseDups.1 this)
      exact (authorize_mem ix c ids i).1 (List.mem_filter.1 this).1

/-- **Every authorized want is queued in full**, when the queue has room
for it: no truncation by bytes. -/
theorem onWant_all (cfg : Config) (ix : Index) (c : Conn) (ids : List Id) (hm : ids.length ≤ cfg.maxIds)
    (hroom : c.owed.length + ids.length ≤ cfg.maxKnown) (i : Id) (hi : i ∈ authorize ix c ids) :
    i ∈ c.owing ∨ i ∈ (c.onWant cfg ix ids).conn.owed := by
  by_cases ho : c.owing.contains i = true
  · exact Or.inl (Std.HashSet.mem_iff_contains.2 ho)
  right
  unfold Conn.onWant
  rw [if_neg (by omega)]
  apply List.mem_append_right
  have hf : i ∈ ((authorize ix c ids).filter fun i => !c.owing.contains i).eraseDups :=
    List.mem_eraseDups.2 (List.mem_filter.2 ⟨hi, by simpa using ho⟩)
  rw [List.take_of_length_le]
  · exact hf
  · have h1 : ((authorize ix c ids).filter fun i => !c.owing.contains i).eraseDups.length ≤ ids.length :=
      Nat.le_trans (eraseDups_length_le _) (Nat.le_trans (List.length_filter_le _ _) (List.length_filter_le _ _))
    omega

/-- A want sends nothing at once: everything goes through the queue. -/
@[simp] theorem onWant_silent (cfg : Config) (ix : Index) (c : Conn) (ids : List Id) :
    (c.onWant cfg ix ids).send = [] := by
  unfold Conn.onWant; split <;> rfl

@[simp] theorem onWant_drop (cfg : Config) (ix : Index) (c : Conn) (ids : List Id) :
    (c.onWant cfg ix ids).drop = false := by
  unfold Conn.onWant; split <;> rfl

@[simp] theorem onWant_take (cfg : Config) (ix : Index) (c : Conn) (ids : List Id) :
    (c.onWant cfg ix ids).take = [] := by
  unfold Conn.onWant; split <;> rfl

/-- **The queue never passes `maxKnown` ids.** -/
theorem onWant_bounded_owed (cfg : Config) (ix : Index) (c : Conn) (ids : List Id)
    (hb : c.owed.length ≤ cfg.maxKnown) : (c.onWant cfg ix ids).conn.owed.length ≤ cfg.maxKnown := by
  unfold Conn.onWant
  split
  · exact hb
  · simp only [List.length_append]
    have := List.length_take_le (cfg.maxKnown - c.owed.length)
      ((authorize ix c ids).filter fun i => !c.owing.contains i).eraseDups
    omega

/-! ## Serving the queue -/

section
variable (fam : Family F) (cfg : Config)

/-- **Serving the queue, on held data**: the urgent ops are the fresh
ones fetched, the serve lane's the queue served in order within the
budget, and the store is only read. -/
theorem serveOwed_eq (c : Conn) (budget : Nat) (first : List Id) (h : Held F) :
    (c.serveOwed fam cfg budget first : HeldM F _) h =
      let urgent := ((fetch (c.shows fam) (c.hotOf first)).trace h.db.ops).1
      let t := ((serve (c.shows fam) budget (c.owedAfter first)).trace h.db.ops).1
      ((c.served cfg (c.hotOf first ++ (c.owedAfter first).take ((c.owedAfter first).length - t.2.length)) t.2
        (urgent ++ t.1), urgent, t.1), h) := by
  simp only [Conn.serveOwed, HeldM.bind_apply, Read.run_held, HeldM.pure_apply]

theorem serveOwed_run (c : Conn) (budget : Nat) (first : List Id) (h : Held F) :
    let urgent := ((fetch (c.shows fam) (c.hotOf first)).trace h.db.ops).1
    let t := ((serve (c.shows fam) budget (c.owedAfter first)).trace h.db.ops).1
    ((c.serveOwed fam cfg budget first : HeldM F _) h).1.2 = (urgent, t.1) ∧
      ((c.serveOwed fam cfg budget first : HeldM F _) h).1.1.owed = t.2 ∧
      ((c.serveOwed fam cfg budget first : HeldM F _) h).2 = h := by
  rw [serveOwed_eq]
  exact ⟨rfl, rfl, rfl⟩

/-- **A fresh write the peer wants is served urgent,** whatever the
budget: every id of `first` in the queue whose op is stored and shown. -/
theorem serveOwed_hot (c : Conn) (budget : Nat) (first : List Id) (h : Held F) (i : Id) (o : Op)
    (hi : i ∈ first) (hq : c.owing.contains i = true) (hg : h.db.ops i = some o) (hs : c.shows fam o = true) :
    o ∈ ((c.serveOwed fam cfg budget first : HeldM F _) h).1.2.1 := by
  rw [(serveOwed_run fam cfg c budget first h).1]
  exact fetch_all _ _ _ i o (List.mem_eraseDups.2 (List.mem_filter.2 ⟨hi, hq⟩)) hg hs

/-- **The queue is served in order, and in full:** with a budget, the
head of the queue (when no fresh write is served first) is sent if its
op is stored and shown, and what is left is the queue's tail, shorter. -/
theorem serveOwed_head (c : Conn) (budget : Nat) (h : Held F) (i : Id) (rest : List Id) (o : Op)
    (hb : 0 < budget) (hq : c.owed = i :: rest) (hg : h.db.ops i = some o) (hs : c.shows fam o = true) :
    o ∈ ((c.serveOwed fam cfg budget [] : HeldM F _) h).1.2.2 := by
  rw [(serveOwed_run fam cfg c budget [] h).1]
  simp only [Conn.owedAfter, Conn.hotOf, List.filter_nil, List.eraseDups_nil, List.isEmpty_nil, ite_true, hq]
  exact serve_head _ _ _ _ _ hb o hg hs

theorem serveOwed_fifo (c : Conn) (budget : Nat) (h : Held F) :
    ∃ pre, c.owed = pre ++ ((c.serveOwed fam cfg budget [] : HeldM F _) h).1.1.owed := by
  rw [(serveOwed_run fam cfg c budget [] h).2.1]
  simp only [Conn.owedAfter, Conn.hotOf, List.filter_nil, List.eraseDups_nil, List.isEmpty_nil, ite_true]
  exact serve_rest _ _ _ _

theorem serveOwed_shrinks (c : Conn) (budget : Nat) (h : Held F) (hb : 0 < budget) (hne : c.owed ≠ []) :
    ((c.serveOwed fam cfg budget [] : HeldM F _) h).1.1.owed.length < c.owed.length := by
  rw [(serveOwed_run fam cfg c budget [] h).2.1]
  simp only [Conn.owedAfter, Conn.hotOf, List.filter_nil, List.eraseDups_nil, List.isEmpty_nil, ite_true]
  obtain ⟨i, rest, hq⟩ : ∃ i rest, c.owed = i :: rest := by
    cases e : c.owed with
    | nil => exact absurd e hne
    | cons i rest => exact ⟨i, rest, rfl⟩
  rw [hq]
  have := serve_shrinks (c.shows fam) h.db.ops i rest budget hb
  simp only [List.length_cons]
  omega

theorem owed_drains (budget : Nat) (h : Held F) (hb : 0 < budget) :
    ∀ (k : Nat) (c : Conn),
      (Nat.repeat (fun c => ((c.serveOwed fam cfg budget [] : HeldM F _) h).1.1) k c).owed.length ≤ c.owed.length - k := by
  intro k
  induction k with
  | zero => intro c; simp [Nat.repeat]
  | succ k ih =>
    intro c
    simp only [Nat.repeat]
    generalize hd : Nat.repeat (fun c => ((c.serveOwed fam cfg budget [] : HeldM F _) h).1.1) k c = d
    have hk := ih c
    rw [hd] at hk
    by_cases hne : d.owed = []
    · obtain ⟨pre, e⟩ := serveOwed_fifo fam cfg d budget h
      rw [hne] at e
      rw [(List.append_eq_nil_iff.1 e.symm).2]; simp
    · have := serveOwed_shrinks fam cfg d budget h hb hne
      omega

/-- **Every authorized want is served within its queue position.** Steps
with a budget (none serving a fresh write first) empty a queue of p ids
in at most p steps, each sending the head's op if it is stored and
shown at its turn (`serveOwed_head`), the queue served in order
(`serveOwed_fifo`): so the id at position p is served by step p + 1. A
want on an empty queue is answered in the same step, so the pilot's 3Δ
holds. -/
theorem owed_within (budget : Nat) (h : Held F) (hb : 0 < budget) (c : Conn) :
    (Nat.repeat (fun c => ((c.serveOwed fam cfg budget [] : HeldM F _) h).1.1) c.owed.length c).owed = [] :=
  List.eq_nil_of_length_eq_zero (by have := owed_drains fam cfg budget h hb c.owed.length c; omega)

/-- **The serve lane gets at most the budget, and one op more.** -/
theorem serveOwed_budget (c : Conn) (budget : Nat) (first : List Id) (h : Held F) :
    let bulk := ((c.serveOwed fam cfg budget first : HeldM F _) h).1.2.2
    replyBytes bulk ≤ budget + largestOp bulk := by
  intro bulk
  have e : bulk = ((serve (c.shows fam) budget (c.owedAfter first)).trace h.db.ops).1.1 := by
    simp only [bulk, (serveOwed_run fam cfg c budget first h).1]
  rw [e]
  exact serve_budget _ _ _ _

/-- **Only what the session shows goes, and only what was wanted:**
every op served is in a room the session shows now, stored under an id
of the queue or of `first` that the peer wanted. -/
theorem serveOwed_shown (c : Conn) (budget : Nat) (first : List Id) (h : Held F) (o : Op)
    (ho : o ∈ ((c.serveOwed fam cfg budget first : HeldM F _) h).1.2.1 ∨
      o ∈ ((c.serveOwed fam cfg budget first : HeldM F _) h).1.2.2) :
    c.shows fam o = true ∧ ∃ i, (i ∈ c.owed ∨ (i ∈ first ∧ c.owing.contains i = true)) ∧ h.db.ops i = some o := by
  rw [(serveOwed_run fam cfg c budget first h).1] at ho
  rcases ho with ho | ho
  · obtain ⟨hs, i, hi, e⟩ := fetch_shown _ _ _ o ho
    exact ⟨hs, i, Or.inr (List.mem_filter.1 (List.mem_eraseDups.1 hi)), e⟩
  · obtain ⟨hs, i, hi, e⟩ := serve_shown _ _ _ _ o ho
    refine ⟨hs, i, Or.inl ?_, e⟩
    unfold Conn.owedAfter at hi
    split at hi
    · exact hi
    · exact (List.mem_filter.1 hi).1

/-- **Blind outside the wants:** stores agreeing on the queue's ids and
`first`'s give the same service. -/
theorem serveOwed_blind (c : Conn) (budget : Nat) (first : List Id) (a b : Held F)
    (agree : ∀ i, (i ∈ c.owed ∨ i ∈ first) → a.db.ops i = b.db.ops i) :
    ((c.serveOwed fam cfg budget first : HeldM F _) a).1 = ((c.serveOwed fam cfg budget first : HeldM F _) b).1 := by
  rw [serveOwed_eq, serveOwed_eq]
  have hf : (fetch (c.shows fam) (c.hotOf first)).trace a.db.ops = (fetch (c.shows fam) (c.hotOf first)).trace b.db.ops :=
    fetch_blind _ _ _ _ fun i hi => agree i (Or.inr (List.mem_filter.1 (List.mem_eraseDups.1 hi)).1)
  have hs : (serve (c.shows fam) budget (c.owedAfter first)).trace a.db.ops =
      (serve (c.shows fam) budget (c.owedAfter first)).trace b.db.ops :=
    serve_blind _ _ _ _ _ fun i hi => by
      apply agree i; left
      unfold Conn.owedAfter at hi; split at hi
      · exact hi
      · exact (List.mem_filter.1 hi).1
  simp only [hf, hs]

end

end Engine.Sync
