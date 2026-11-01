/- The application's input policy: three local-preferred turns followed by
one guaranteed network-preferred turn. Empty preferred queues fall back in
the same turn. The finite phase is owned by Loop.State, not a producer. -/
import engine.wire.Lanes

namespace Engine.Sync.Inbox.Priority

abbrev Slot := Fin 4

def first : Slot := ⟨3, by decide⟩

def advance (slot : Slot) : Slot :=
  if h : slot.val = 0 then first else ⟨slot.val - 1, by omega⟩

def localFirst (slot : Slot) : Bool := slot.val != 0

/-- One actual poll. Only the finite runner-owned phase determines when
network service is compulsory. Producers cannot reset it by keeping a local
queue nonempty, and an empty preferred queue never wastes a service slot. -/
def next {m : Type → Type} [Monad m] {W E : Type} (slot : Slot)
    (writes : m (Option W)) (events : m (Option E)) : m (Option (W ⊕ E) × Slot) := do
  let (selected, _) ← Inbox.next (localFirst slot) writes events
  return (selected, advance slot)

structure State (W E : Type) where
  writes : List W
  events : List E
  slot : Slot := first

/-- Interpret the production selector with FIFO queue operations. -/
def step {W E : Type} (s : State W E) : Option (W ⊕ E) × State W E :=
  let r := (next s.slot popW popE).run (s.writes, s.events)
  (r.1.1, ⟨r.2.1, r.2.2, r.1.2⟩)

def State.append {W E : Type} (s : State W E) (ws : List W) (es : List E) : State W E :=
  { s with writes := s.writes ++ ws, events := s.events ++ es }

end Engine.Sync.Inbox.Priority
