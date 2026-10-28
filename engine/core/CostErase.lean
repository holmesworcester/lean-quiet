/-
The meter erased: a counted run, its costs dropped, is the plain run.

Code whose cost matters is written once over its monad, and a budget law
runs it in `CostT m` (engine/core/Cost.lean). These laws say the meter
adds counts and nothing else: `erase` takes a counted action to the plain
one, and it commutes with `pure` and `bind` and sends every door to the
action it charges for (`charged`, `chargedBy`, `lift`) or to nothing
(`tick`). So code built from these erases, step by step, to the code that
runs with the meter free; each pilot's `val_*` law is that, for its code.
tests/Wiring.lean takes the meter as an instrument on these laws: a cost
law over running code is about running code.
-/
import engine.core.Cost

namespace Engine.CostT
variable {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type}

/-- A counted action with its costs erased. -/
def erase (x : CostT m α) : m α := Prod.fst <$> x.run

/-- A counted run, erased, is its value. -/
theorem erase_run (x : CostT m α) : Prod.fst <$> CostT.run x = erase x := rfl

theorem erase_pure (a : α) : erase (CostT.pure a : CostT m α) = pure a := by
  simp [erase, CostT.pure, run]

theorem erase_bind (x : CostT m α) (f : α → CostT m β) :
    erase (CostT.bind x f) = erase x >>= fun a => erase (f a) := by
  show Prod.fst <$> (x.run >>= fun p => (f p.1).run >>= fun q => pure (q.1, p.2 + q.2)) =
    (Prod.fst <$> x.run) >>= fun a => Prod.fst <$> (f a).run
  rw [map_bind, bind_map_left]
  congr 1; funext p
  rw [map_bind]
  simp only [map_pure]
  exact (map_eq_pure_bind _ _).symm

theorem erase_charged (c : Meter) (x : m α) : erase (CostT.charged c x) = x := by
  simp [erase, CostT.charged, run]

theorem erase_chargedBy (f : α → Meter) (x : m α) : erase (CostT.chargedBy f x) = x := by
  simp [erase, CostT.chargedBy, run]

theorem erase_lift (x : m α) : erase (CostT.lift x) = x := by
  simp [erase, CostT.lift, CostT.charged, run]

theorem erase_tick (c : Meter) : erase (tick c : CostT m Unit) = pure () := by
  simp [erase, tick, run]

end Engine.CostT

namespace Engine.Counted
variable {α : Type}

/-- Pure code, counted: its value is the erased run. -/
theorem val_erase (x : Counted α) : Counted.val x = Id.run (CostT.erase x) := rfl

/-- What a counted run charged is the meter's second half: it reads no
value of the run's. -/
theorem cost_run (x : Counted α) : Counted.cost x = (Id.run (CostT.run x)).2 := rfl

end Engine.Counted
