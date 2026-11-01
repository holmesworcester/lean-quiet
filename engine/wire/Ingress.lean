/- Fixed source positions keep a peer's turn independent of connection churn.
The runner owns the cursor; each producer owns at most one bounded mailbox.
This is the executable selection core for the native ingress registry. -/
import Std

namespace Engine.Sync.Ingress

def advance {n : Nat} (cursor : Fin (n + 1)) : Fin (n + 1) :=
  if h : cursor.val + 1 < n + 1 then ⟨cursor.val + 1, h⟩ else ⟨0, by omega⟩

def distance {n : Nat} (cursor target : Fin (n + 1)) : Nat :=
  if cursor.val ≤ target.val then target.val - cursor.val
  else n + 1 - cursor.val + target.val

/-- A bounded scan. Empty positions are skipped in this same poll. Advancing
after success prevents a producer from retaining the next network slot. -/
def scan {α : Type} {n : Nat} (slots : Vector (Option α) (n + 1)) :
    Nat → Fin (n + 1) → Option (Fin (n + 1) × α) × Fin (n + 1)
  | 0, cursor => (none, cursor)
  | fuel + 1, cursor =>
    match slots[cursor.val] with
    | some value => (some (cursor, value), advance cursor)
    | none => scan slots fuel (advance cursor)

structure State (α : Type) (n : Nat) where
  slots : Vector (Option α) (n + 1) := Vector.replicate (n + 1) none
  cursor : Fin (n + 1) := ⟨0, by omega⟩

/-- A full source refuses another value rather than overwriting owed work. -/
def State.offer {α : Type} {n : Nat} (s : State α n) (source : Fin (n + 1))
    (value : α) : Bool × State α n :=
  match s.slots[source.val] with
  | some _ => (false, s)
  | none => (true, { s with slots := s.slots.set source.val (some value) })

/-- Retirement drops this incarnation's owed input and preserves every
other source's slot and the consumer-owned position. -/
def State.cancel {α : Type} {n : Nat} (s : State α n) (source : Fin (n + 1)) : State α n :=
  { s with slots := s.slots.set source.val none }

/-- Exactly the value chosen by the bounded scan is consumed. -/
def State.poll {α : Type} {n : Nat} (s : State α n) :
    Option (Fin (n + 1) × α) × State α n :=
  let (found, cursor) := scan s.slots (n + 1) s.cursor
  let slots := match found with
    | none => s.slots
    | some (source, _) => s.slots.set source.val none
  (found, { slots, cursor })

end Engine.Sync.Ingress
