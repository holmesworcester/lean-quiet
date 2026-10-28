/-
Judging terminates: from any reachable state, some number of steps
empties the queue (`drain_terminates`), and then every verdict is the
spec's (`drain_settles`).

The measure is lexicographic: the received ops still undecided, then
the queue's length. A step that decides an op lowers the first (it may
queue that op's waiters); every other step leaves the first alone and
takes one id off the queue.
-/
import Engine.Proofs

namespace Engine
variable {F : Type} {fam : Family F}

/-- How many received ops are undecided. -/
def undecided (L : List Op) (s : DB F) : Nat := (L.filter fun o => (s.status o.id).isNone).length

theorem filter_le {α} (L : List α) (p q : α → Bool) (hsub : ∀ a ∈ L, q a = true → p a = true) :
    (L.filter q).length ≤ (L.filter p).length := by
  induction L with
  | nil => simp
  | cons b t ih =>
    have := ih fun a ha => hsub a (List.mem_cons_of_mem _ ha)
    by_cases hq : q b = true
    · simp [hq, hsub b (List.mem_cons_self ..) hq]; omega
    · simp only [List.filter_cons, hq, Bool.false_eq_true, ite_false]
      split <;> simp <;> omega

theorem filter_lt {α} (L : List α) (p q : α → Bool) (hsub : ∀ a ∈ L, q a = true → p a = true)
    (hx : ∃ a ∈ L, p a = true ∧ q a = false) : (L.filter q).length < (L.filter p).length := by
  induction L with
  | nil => obtain ⟨a, ha, _⟩ := hx; cases ha
  | cons b t ih =>
    have hsub' : ∀ a ∈ t, q a = true → p a = true := fun a ha => hsub a (List.mem_cons_of_mem _ ha)
    have hle := filter_le t p q hsub'
    obtain ⟨a, ha, hpa, hqa⟩ := hx
    rcases List.mem_cons.1 ha with rfl | ha
    · simp only [List.filter_cons, hpa, hqa, ite_true, Bool.false_eq_true, ite_false, List.length_cons]
      omega
    · have := ih hsub' ⟨a, ha, hpa, hqa⟩
      by_cases hq : q b = true
      · simp [hq, hsub b (List.mem_cons_self ..) hq]; omega
      · simp only [List.filter_cons, hq, Bool.false_eq_true, ite_false]
        by_cases hp : p b = true
        · simp [hp]; omega
        · simp [hp]; omega

/-- A step on a non-empty queue lowers the measure. -/
theorem step_decreases {L : List Op} {s : DB F} (h : Reach fam L s) (hd : Distinct L)
    {x : Id} {q : List Id} (hq : s.queue = x :: q) :
    undecided L (stepS fam s) < undecided L s ∨
    (undecided L (stepS fam s) = undecided L s ∧ (stepS fam s).queue.length < s.queue.length) := by
  have same : ∀ t : DB F, t.status = s.status → t.queue = q →
      undecided L t < undecided L s ∨
      (undecided L t = undecided L s ∧ t.queue.length < (x :: q).length) := by
    intro t h1 h2
    right; refine ⟨by unfold undecided; rw [h1], ?_⟩
    rw [h2]; simp
  unfold stepS; rw [hq]; simp only
  cases hs : s.status x with
  | some _ => simp only; exact same { s with queue := q } rfl rfl
  | none =>
    simp only
    cases ho : s.ops x with
    | none => exact same { s with queue := q } rfl rfl
    | some o =>
      simp only
      cases hj : judge fam o (o.reqs.map s.status) with
      | none => exact same (waitOnS x o.reqs { s with queue := q }) (waitOnS_status _ _ _) (waitOnS_queue _ _ _)
      | some v =>
        simp only
        left
        obtain ⟨_, d2, _⟩ := decideS_fields (fam := fam) x v { s with queue := q }
        unfold undecided; rw [d2]
        have hx := (reach_ops h hd x o).1 ho
        apply filter_lt
        · intro a _ ha
          by_cases hax : a.id = x
          · simp [hax] at ha
          · simpa [hax] using ha
        · exact ⟨o, hx.1, by simp [hx.2, hs], by simp [hx.2]⟩

/-- **Judging terminates.** From any state reachable by receiving ops
and stepping, finitely many steps empty the queue. -/
theorem drain_terminates {L : List Op} (hd : Distinct L) :
    ∀ s : DB F, Reach fam L s → ∃ n, (drainS fam n s).queue = [] := by
  suffices key : ∀ k j (s : DB F), undecided L s = k → s.queue.length = j → Reach fam L s →
      ∃ n, (drainS fam n s).queue = [] from
    fun s h => key _ _ s rfl rfl h
  intro k
  induction k using Nat.strongRecOn with
  | _ k ihk =>
    intro j
    induction j using Nat.strongRecOn with
    | _ j ihj =>
      intro s hk hj h
      cases hq : s.queue with
      | nil => exact ⟨0, hq⟩
      | cons x q =>
        have hr := Reach.step (fam := fam) h
        have more : ∀ n, (drainS fam (n + 1) s) = drainS fam n (stepS fam s) := by
          intro n; simp [drainS, hq]
        rcases step_decreases h hd hq with hlt | ⟨heq, hlen⟩
        · obtain ⟨n, hn⟩ := ihk _ (hk ▸ hlt) _ (stepS fam s) rfl rfl hr
          exact ⟨n + 1, by rw [more]; exact hn⟩
        · obtain ⟨n, hn⟩ := ihj _ (hj ▸ hlen) (stepS fam s) (heq.trans hk) rfl hr
          exact ⟨n + 1, by rw [more]; exact hn⟩

/-- **And then it is settled.** After those steps every verdict is the
spec's, over exactly the ops received. -/
theorem drain_settles {L : List Op} (hd : Distinct L) {s : DB F} (h : Reach fam L s) :
    ∃ n, (drainS fam n s).queue = [] ∧
      ∀ x v, (drainS fam n s).status x = some v ↔ Spec fam (drainS fam n s).ops x v := by
  obtain ⟨n, hn⟩ := drain_terminates hd s h
  exact ⟨n, hn, status_iff_spec (reach_inv (reach_drain h n)) hn⟩

/-- **Same ops, any order, same verdicts.** Two nodes that received the
same ops — in any orders, in any batches, with processing interleaved
anywhere — both finish processing, and then hold exactly the same
verdict, fact included, for every op. -/
theorem same_ops_same_verdicts {L M : List Op} {s t : DB F}
    (hs : Reach fam L s) (ht : Reach fam M t)
    (hd : Distinct (L ++ M)) (hsame : ∀ o, o ∈ L ↔ o ∈ M) :
    ∃ n m, (drainS fam n s).queue = [] ∧ (drainS fam m t).queue = [] ∧
      (drainS fam n s).status = (drainS fam m t).status := by
  have dL : Distinct L := fun a ha b hb => hd a (List.mem_append_left _ ha) b (List.mem_append_left _ hb)
  have dM : Distinct M := fun a ha b hb => hd a (List.mem_append_right _ ha) b (List.mem_append_right _ hb)
  obtain ⟨n, hn⟩ := drain_terminates dL s hs
  obtain ⟨m, hm⟩ := drain_terminates dM t ht
  exact ⟨n, m, hn, hm, order_free (reach_drain hs n) (reach_drain ht m) hd hsame hn hm⟩

end Engine
