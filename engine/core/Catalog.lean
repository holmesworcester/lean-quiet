/- Bounded reads for durable anti-entropy. Native positions never get reused,
even when local secrets are purged. A scan freezes its ceiling, so writes
which arrive during that scan cannot extend it. -/
import engine.core.Held

namespace Engine.Sync

structure Catalog (m : Type → Type) where
  ceiling : m Nat
  /-- Positions start at one. A deleted position is a hole, not a renumbering. -/
  read : Nat → m (Option Id)

def Catalog.sql {F : Type} : Catalog (SqlM F) where
  ceiling := countSql "SELECT CAST(seq AS TEXT) FROM sqlite_sequence WHERE name = 'catalog'"
  read seq := do
    return (col0 (← sqlQ s!"SELECT id FROM catalog WHERE seq = {seq}" #[])).head?

/-- The held interpreter enumerates shared log entries. Local-secret purge
does not remove these entries. Its list traversal is a proof/test interpreter,
not the native indexed-query implementation or its performance guarantee. -/
def Catalog.shared {F : Type} (fam : Family F) (h : Held F) : List Op :=
  h.log.filter fun o => (fam.room o).isSome

def Catalog.held {F : Type} (fam : Family F) : Catalog (HeldM F) where
  ceiling := fun h => ((shared fam h).length, h)
  read seq := fun h =>
    ((if seq = 0 then none else (shared fam h)[seq - 1]?.map Op.id), h)

end Engine.Sync
