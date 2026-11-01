import engine.wire.ExpiryGraceLaws

namespace Vacuity.ExpiryGrace
open Engine.Sync

def owed : ExpiryGrace.State := ⟨100, ExpiryGrace.budget 2⟩

theorem sameGeneration :
    ExpiryGrace.check 999 100 true true (some owed) = (true, some owed) :=
  ExpiryGrace.same_generation 999 owed true

theorem junkDoesNotRearm :
    (ExpiryGrace.check 999 100 true true (some ⟨100, 0⟩)).2 = some ⟨100, 0⟩ :=
  ExpiryGrace.no_rearm 999 ⟨100, 0⟩ true

theorem junkCannotDelay :
    (ExpiryGrace.check 999 100 true true (some ⟨100, 0⟩)).1 = false :=
  ExpiryGrace.exhausted 999 100 true

theorem emptyCannotDelay :
    (ExpiryGrace.check 12 100 true false (some owed)).1 = false :=
  ExpiryGrace.empty_no_delay 12 100 true (some owed)

theorem freshClears : ExpiryGrace.check 12 200 false true (some owed) = (false, none) :=
  ExpiryGrace.fresh_clears 12 200 true (some owed)

theorem generationRetained : (ExpiryGrace.consume owed).heard = 100 :=
  ExpiryGrace.consume_keeps_generation owed

theorem selectionDecreases : (ExpiryGrace.consume owed).left < 12 :=
  ExpiryGrace.consume_decreases owed (by decide)

theorem zeroSaturates : ExpiryGrace.consume ⟨100, 0⟩ = ⟨100, 0⟩ :=
  ExpiryGrace.consume_saturates 100

theorem afterSeven : (ExpiryGrace.consumed 7 owed).left = 5 :=
  ExpiryGrace.consumed_left 7 owed

theorem afterTwelve : (ExpiryGrace.consumed 12 owed).left = 0 :=
  ExpiryGrace.budget_exhausted 2 100

theorem sourceOpportunity :
    ∃ j, 0 ≤ j ∧ j < 12 ∧ 0 < (ExpiryGrace.consumed (j-0) owed).left ∧
      (Ingress.Prioritized.churnFlood.selected j = some (.inr (⟨1, by decide⟩, 11)) ∨
        (⟨1, by decide⟩ : Fin 3) ∈ Ingress.Prioritized.churnFlood.closed j) :=
  ExpiryGrace.source_before_exhaustion Ingress.Prioritized.churnFlood 0 ⟨1, by decide⟩ 11 100 rfl

-- Nonempty local/peer sources keep arriving forever; a different slot is
-- canceled and reused every turn. The owed source is actually selected.
example : Ingress.Prioritized.churnFlood.selected 7 = some (.inr (⟨1, by decide⟩, 11)) :=
  Ingress.Prioritized.churnFlood_exact.2

end Vacuity.ExpiryGrace
