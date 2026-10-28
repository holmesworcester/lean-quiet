/-
How many judging steps a write turn needs, as a number the writer can
read off its tables: the queue's length, plus the undecided stored ops
times the stored ops. Every step pops one queue entry; a step that
decides an op x pushes x's waiters back, at most one per stored op, and
x is decided for good. So the budget drops by at least one per step
(`step_budget`), and draining with it empties the queue
(`drain_bounded`). The writer drains with exactly this budget, so the
loop that runs is the proven `drain`, with no `partial` in the write
path.
-/
import Engine.Termination

namespace Engine
variable {F : Type} {fam : Family F}

/-- The steps a state needs at most: its queue, plus its undecided
stored ops times its stored ops. -/
def budget (L : List Op) (s : DB F) : Nat :=
  s.queue.length + undecided L.eraseDups s * L.eraseDups.length

/-! ## Waiters are distinct stored ops -/

/-- What the waits table always satisfies: each blocker's waiters are
distinct, and each is a stored op. -/
def WaitsOk (s : DB F) : Prop := ∀ r, (s.waits r).Nodup ∧ ∀ y ∈ s.waits r, (s.ops y).isSome

theorem ins_nodup {l : List Id} {x : Id} (h : l.Nodup) : (ins l x).Nodup := by
  unfold ins
  split
  · exact h
  · rename_i hx
    rw [List.nodup_append]
    refine ⟨h, List.nodup_cons.2 ⟨by simp, List.nodup_nil⟩, fun a ha b hb => ?_⟩
    rw [List.mem_singleton] at hb; subst hb
    intro e; subst e
    exact hx ((has_iff _ _).2 ha)

theorem waitsOk_waitOnS {s : DB F} (h : WaitsOk s) {x : Id} (hx : (s.ops x).isSome) (l : List Id) :
    WaitsOk (waitOnS x l s) := by
  induction l generalizing s with
  | nil => exact h
  | cons r t ih =>
    simp only [waitOnS]
    split
    · refine ih ?_ hx
      intro i
      show (if i = r then ins (s.waits r) x else s.waits i).Nodup ∧
        ∀ y ∈ (if i = r then ins (s.waits r) x else s.waits i), (s.ops y).isSome
      split
      · rename_i hi; subst hi
        refine ⟨ins_nodup (h i).1, fun y hy => ?_⟩
        rcases (mem_ins _ _ _).1 hy with hy | rfl
        · exact (h i).2 y hy
        · exact hx
      · exact h i
    · exact ih h hx

theorem waitsOk_reach {L : List Op} {s : DB F} (hr : Reach fam L s) : WaitsOk s := by
  induction hr with
  | empty => intro r; simp [DB.empty]
  | @ingest L s o _ ih =>
    unfold ingestS
    split
    · exact ih
    · intro r
      refine ⟨(ih r).1, fun y hy => ?_⟩
      show (if y = o.id then some o else s.ops y).isSome
      split
      · rfl
      · exact (ih r).2 y hy
  | @step L s _ ih =>
    unfold stepS
    cases hq : s.queue with
    | nil => exact ih
    | cons x q =>
      have ih' : WaitsOk ({ s with queue := q } : DB F) := ih
      simp only
      cases hs : s.status x with
      | some _ => exact ih'
      | none =>
        simp only
        cases ho : s.ops x with
        | none => exact ih'
        | some o =>
          simp only
          cases hj : judge fam o (o.reqs.map s.status) with
          | some v =>
            simp only
            obtain ⟨h1, _, _, h4, _⟩ := decideS_fields (fam := fam) x v { s with queue := q }
            intro r
            rw [h4 r, h1]
            split
            · exact ⟨List.nodup_nil, by simp⟩
            · exact ih' r
          | none => exact waitsOk_waitOnS ih' (by simp [ho]) _
  | @purge L s ids _ ih =>
    intro r
    refine ⟨?_, fun y hy => ?_⟩
    · show (if has _ r then [] else (s.waits r).filter _).Nodup
      split
      · exact List.nodup_nil
      · exact List.Nodup.sublist List.filter_sublist (ih r).1
    · obtain ⟨_, hy, hp⟩ := (mem_purgeS_waits s ids r y).1 hy
      rw [purgeS_ops_not s ids hp]; exact (ih r).2 y hy

/-- A list of distinct elements of M is no longer than M. -/
theorem nodup_length_le {l M : List Id} (hn : l.Nodup) (hs : ∀ y ∈ l, y ∈ M) : l.length ≤ M.length := by
  induction l generalizing M with
  | nil => simp
  | cons a t ih =>
    rw [List.nodup_cons] at hn
    have ha := hs a (List.mem_cons_self ..)
    let M' := M.filter fun y => !Decidable.decide (y = a)
    have h1 := ih hn.2 (M := M') fun y hy => by
      refine List.mem_filter.2 ⟨hs y (List.mem_cons_of_mem _ hy), ?_⟩
      have : y ≠ a := by intro e; subst e; exact hn.1 hy
      simpa using this
    have h2 : M'.length < (M.filter fun _ => true).length :=
      filter_lt M (fun _ => true) (fun y => !Decidable.decide (y = a)) (fun _ _ _ => rfl) ⟨a, ha, rfl, by simp⟩
    rw [List.filter_eq_self.2 (fun _ _ => rfl)] at h2
    simp only [List.length_cons]; omega

theorem waits_le {L : List Op} {s : DB F} (hr : Reach fam L s) (hd : Distinct L) (x : Id) :
    (s.waits x).length ≤ L.eraseDups.length := by
  have hw := waitsOk_reach hr x
  have := nodup_length_le (M := L.eraseDups.map (·.id)) hw.1 fun y hy => by
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 (hw.2 y hy)
    have := (reach_ops hr hd y o).1 ho
    exact List.mem_map.2 ⟨o, List.mem_eraseDups.2 this.1, this.2⟩
  simpa using this

/-! ## The budget drops with every step -/

theorem step_budget {L : List Op} {s : DB F} (h : Reach fam L s) (hd : Distinct L)
    {x : Id} {q : List Id} (hq : s.queue = x :: q) :
    budget L (stepS fam s) + 1 ≤ budget L s := by
  have same : ∀ t : DB F, t.status = s.status → t.queue = q → budget L t + 1 ≤ budget L s := by
    intro t h1 h2
    unfold budget undecided; rw [h1, h2, hq]; simp; omega
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
        obtain ⟨_, d2, d3, _, _⟩ := decideS_fields (fam := fam) x v { s with queue := q }
        have hx := (reach_ops h hd x o).1 ho
        have hlt : undecided L.eraseDups (decideS fam x v { s with queue := q }) < undecided L.eraseDups s := by
          unfold undecided; rw [d2]
          apply filter_lt
          · intro a _ ha
            by_cases hax : a.id = x
            · simp [hax] at ha
            · simpa [hax] using ha
          · exact ⟨o, List.mem_eraseDups.2 hx.1, by simp [hx.2, hs], by simp [hx.2]⟩
        have hw : (s.waits x).length ≤ L.eraseDups.length := waits_le h hd x
        have hU : undecided L.eraseDups (decideS fam x v { s with queue := q }) + 1 ≤
            undecided L.eraseDups s := hlt
        have hm := Nat.mul_le_mul_right L.eraseDups.length hU
        rw [Nat.add_mul, Nat.one_mul] at hm
        unfold budget
        rw [d3, hq]
        simp only [List.length_append, List.length_cons]
        omega

/-- **Draining with the budget empties the queue.** From any state
reachable by receiving ops and stepping, `budget` steps (or more) leave
the queue empty; so the writer, draining with the budget it reads off
its tables, runs the proven `drain` to rest. -/
theorem drain_bounded {L : List Op} (hd : Distinct L) :
    ∀ (n : Nat) (s : DB F), Reach fam L s → budget L s ≤ n → (drainS fam n s).queue = [] := by
  intro n
  induction n with
  | zero =>
    intro s _ hb
    show s.queue = []
    unfold budget at hb
    exact List.eq_nil_of_length_eq_zero (by omega)
  | succ n ih =>
    intro s h hb
    cases hq : s.queue with
    | nil =>
      have e : stepS fam s = s := by unfold stepS; rw [hq]
      simp only [drainS, hq, List.isEmpty_nil, ite_true, e]
    | cons x q =>
      simp only [drainS, hq, List.isEmpty_cons, Bool.false_eq_true, ite_false]
      have := step_budget h hd hq
      exact ih _ (Reach.step h) (by omega)

theorem drainS_ops (n : Nat) (s : DB F) : (drainS fam n s).ops = s.ops := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => unfold drainS; split <;> simp only [ih, stepS_ops]

/-- **After a purge, the engine settles on what remains.** From any
reachable state, purging and then draining with the budget read off the
purged tables empties the queue, and every verdict is then the spec's
over the remaining ops. -/
theorem purge_settles {L : List Op} {s : DB F} (h : Reach fam L s) (hd : Distinct L)
    (ids : List Id) :
    let L' := L.filter fun o => !has (purgeSet fam s ids) o.id
    let t := purgeS fam ids s
    (drainS fam (budget L' t) t).queue = [] ∧
      ∀ x v, (drainS fam (budget L' t) t).status x = some v ↔ Spec fam t.ops x v := by
  intro L' t
  have hr : Reach fam L' t := Reach.purge ids h
  have hd' : Distinct L' := fun a ha b hb => hd a (List.mem_filter.1 ha).1 b (List.mem_filter.1 hb).1
  have hq := drain_bounded hd' _ t hr (Nat.le_refl _)
  refine ⟨hq, fun x v => ?_⟩
  rw [status_iff_spec (reach_inv (reach_drain hr _)) hq, drainS_ops]

end Engine
