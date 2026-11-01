/- Observation of the exact store interpreter used by Node.sweep. These
equalities expose inputs to Sweep.retried_fair, not a separate scheduler. -/
import ops.sync.SweepLaws

namespace Engine.Sync.Sweep

private theorem bind_run {F α β} (x : HeldM F α) (f : α → HeldM F β) (h : Held F) :
    (x >>= f).run h = (f (x.run h).1).run (x.run h).2 := rfl
private theorem pure_run {F α} (x : α) (h : Held F) :
    (pure x : HeldM F α).run h = (x, h) := rfl
private theorem get_run {F} (id : Id) (h : Held F) :
    (Store.getOp (F := F) id : HeldM F _).run h = (h.db.ops id, h) := rfl

/-- The literal value read by run: an active sweep does not query the current
ceiling and supplies zero, which begin ignores. -/
def observedCeiling {F} (catalog : Catalog (HeldM F)) (s : Sweep) (h : Held F) : Nat :=
  if s.active then 0 else (catalog.ceiling.run h).1

def observedInput {F} (catalog : Catalog (HeldM F)) (s : Sweep) (h : Held F) : Option Op :=
  let prepared := s.begin (observedCeiling catalog s h)
  if prepared.high ≤ prepared.after then none
  else ((catalog.read (prepared.after + 1)).run h).1.bind h.db.ops

/-- One actual store call equals the pure transition proved fair above, and
leaves the held store unchanged. The only assumptions are that the catalog
reads do not write the store; no progress or delivery is assumed. -/
theorem run_observed {F} (catalog : Catalog (HeldM F)) (s : Sweep)
    (shows : Op → Bool) (room : Nat) (h : Held F)
    (ceilingRead : (catalog.ceiling.run h).2 = h)
    (rowRead : ∀ seq, ((catalog.read seq).run h).2 = h) :
    (s.run catalog shows room).run h =
      (s.step (observedCeiling catalog s h) (observedInput catalog s h) shows room, h) := by
  cases active : s.active with
  | false =>
    simp only [run, observedInput, observedCeiling, active, Bool.false_eq_true, ↓reduceIte,
      bind_run, ceilingRead]
    by_cases done : (s.begin (catalog.ceiling.run h).1).high ≤ (s.begin (catalog.ceiling.run h).1).after
    · simp only [done, ↓reduceIte, pure_run]
    · simp only [done, ↓reduceIte, bind_run, rowRead]
      cases hr : ((catalog.read ((s.begin (catalog.ceiling.run h).1).after + 1)).run h).1 <;>
        simp [bind_run, pure_run, get_run, Option.bind]
  | true =>
    simp only [run, observedInput, observedCeiling, active, ↓reduceIte,
      bind_run, pure_run]
    by_cases done : (s.begin 0).high ≤ (s.begin 0).after
    · simp only [done, ↓reduceIte, pure_run]
    · simp only [done, ↓reduceIte, bind_run, rowRead]
      cases hr : ((catalog.read ((s.begin 0).after + 1)).run h).1 <;>
        simp [bind_run, pure_run, get_run, Option.bind]

theorem held_run_observed {F} (fam : Family F) (s : Sweep)
    (shows : Op → Bool) (room : Nat) (h : Held F) :
    (s.run (Catalog.held fam) shows room).run h =
      (s.step (observedCeiling (Catalog.held fam) s h)
        (observedInput (Catalog.held fam) s h) shows room, h) :=
  run_observed _ _ _ _ _ rfl (fun _ => rfl)

end Engine.Sync.Sweep
