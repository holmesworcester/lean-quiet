module
import all Init.System.IO
import all Init.System.ST
public import Init.Control.Lawful

public section

/-- The pinned SDK's actual IO bind/pure definitions satisfy the monad laws.
This is not an assertion about any foreign primitive's implementation. -/
theorem Engine.Sync.io_lawful : LawfulMonad IO := .mk'
  (id_map := fun action => funext fun world => by
    simp only [Functor.map, instMonadEIO._aux_1, EST.bind, EST.pure, Function.comp_def]
    cases action world <;> rfl)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun action _ _ => funext fun world => by
    simp only [bind, instMonadEIO._aux_13, EST.bind]
    cases action world <;> rfl)
  (map_const := fun _ _ => rfl)
