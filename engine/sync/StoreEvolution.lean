/- The actual write/purge effects of a complete node event. -/
import engine.sync.ClosureStore
import engine.wire.EgressLaws

namespace Engine
variable {F : Type} {fam : Family F}

/-- The stored operations occur in the received history even when that
history contains different inputs with the same id. Queue bounds therefore
do not require a collision-free history. -/
theorem waits_history_bound {L : List Op} {s : DB F} (hr : Reach fam L s) (x : Id) :
    (s.waits x).length ≤ L.eraseDups.length := by
  have hw := waitsOk_reach hr x
  have h := nodup_length_le (M := L.eraseDups.map (·.id)) hw.1 fun y hy => by
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 (hw.2 y hy)
    obtain ⟨hm, hi⟩ := reach_stored hr y o ho
    exact List.mem_map.2 ⟨o, List.mem_eraseDups.2 hm, hi⟩
  simpa using h

theorem step_history_budget {L : List Op} {s : DB F} (h : Reach fam L s)
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
        have hx := reach_stored h x o ho
        have hlt : undecided L.eraseDups (decideS fam x v { s with queue := q }) < undecided L.eraseDups s := by
          unfold undecided; rw [d2]
          apply filter_lt
          · intro a _ ha
            by_cases hax : a.id = x
            · simp [hax] at ha
            · simpa [hax] using ha
          · exact ⟨o, List.mem_eraseDups.2 hx.1, by simp [hx.2, hs], by simp [hx.2]⟩
        have hw := waits_history_bound h x
        have hU : undecided L.eraseDups (decideS fam x v { s with queue := q }) + 1 ≤
            undecided L.eraseDups s := hlt
        have hm := Nat.mul_le_mul_right L.eraseDups.length hU
        rw [Nat.add_mul, Nat.one_mul] at hm
        unfold budget
        rw [d3, hq]
        simp only [List.length_append, List.length_cons]
        omega

/-- The runtime's finite budget settles every reachable state. Collisions
can affect which input is kept, but cannot prevent this queue from draining. -/
theorem drain_history_budget {L : List Op} :
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
      have := step_history_budget h hq
      exact ih _ (Reach.step h) (by omega)

end Engine

namespace Engine.Sync
variable {F : Type} {fam : Family F}

theorem purge_reachable (fam : Family F) (ids : List Id) (scrub : Bool) (h : Held F)
    (hr : h.Reachable fam) :
    (((Turn.purge fam ids scrub : HeldM F Unit) h).2).Reachable fam := by
  obtain ⟨history, hr, same⟩ := hr
  refine ⟨history.filter fun o => !has (purgeSet fam h.db ids) o.id,
    reach_purgeCapped hr drainCap ids, ?_⟩
  intro o
  simp only [purge_apply, List.mem_filter, same]

/-- **A purge keeps urgent work settled** (`purge_waiting`): it judges the
urgent ops it requeued ahead, as a turn does. -/
theorem purge_waiting_held (fam : Family F) (ids : List Id) (scrub : Bool) (h : Held F)
    (hr : h.Reachable fam) (hw : UrgentWaiting fam h.db) :
    UrgentWaiting fam (((Turn.purge fam ids scrub : HeldM F Unit) h).2).db :=
  let ⟨_, hr, _⟩ := hr; purge_waiting hr hw drainCap ids

/- Reuse the exact primitive transition relation already derived from Node
in EgressLaws; these results add its storage consequences. -/
namespace Moves

theorem shared_retained {a b : Held F} (step : Moves fam a b)
    {i : Id} {o : Op} (ho : a.db.ops i = some o) (hs : (fam.room o).isSome) :
    b.db.ops i = some o := by
  induction step with
  | refl => exact ho
  | tail _ hm ih =>
    cases hm with
    | turn ops h =>
      simp only [HeldM.run, turn_apply]
      rw [turnCappedS_ops]
      exact foldl_ingest_keep _ ih
    | purge ids scrub h =>
      simp only [HeldM.run, purge_apply]
      rw [purgeCappedS_ops]
      exact purge_shared _ ids ih hs

theorem store_reachable {a b : Held F} (step : Moves fam a b)
    (hr : a.Reachable fam) : b.Reachable fam := by
  induction step with
  | refl => exact hr
  | tail _ hm ih =>
    cases hm with
    | turn ops h => exact turn_reachable fam ops _ ih
    | purge ids scrub h => exact purge_reachable fam ids scrub _ ih

/-- **Every store step keeps urgent work settled** (`UrgentWaiting`, so
`UrgentSettled`: an urgent op whose closure is all urgent has its spec
verdict), whatever is left queued. -/
theorem store_waiting {a b : Held F} (step : Moves fam a b)
    (hr : a.Reachable fam) (hw : UrgentWaiting fam a.db) : UrgentWaiting fam b.db := by
  induction step with
  | refl => exact hw
  | tail h1 hm ih =>
    cases hm with
    | turn ops h => exact turn_waiting_held fam ops _ (h1.store_reachable hr) ih
    | purge ids scrub h => exact purge_waiting_held fam ids scrub _ (h1.store_reachable hr) ih

end Moves
end Engine.Sync
