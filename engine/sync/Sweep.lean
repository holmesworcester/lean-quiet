/- The retry cursor used by Node.onTick. One tick examines one durable
catalog position. A completed sweep starts again from zero, capturing a new
ceiling only then. New catalog entries cannot extend an in-flight sweep. -/
import engine.core.Catalog
import engine.wire.Frame

namespace Engine.Sync

structure Sweep where
  after : Nat := 0
  high : Nat := 0
  active : Bool := false
  deriving DecidableEq, Repr

/-- Durable progress belongs to an authenticated peer, not one disposable
session. Only one cursor is loaded at a time; the table is persistent history. -/
structure RetryStore (m : Type → Type) where
  load : Id → m Sweep
  save : Id → Sweep → m Unit

def RetryStore.sql {F : Type} : RetryStore (SqlM F) where
  load peer := do
    let row : Option (Nat × Nat × Bool) ← sqlOne "retry cursor"
      (← sqlQ "SELECT bytes FROM retry_cursor WHERE peer = ?" #[peer])
    return match row with
      | none => {}
      | some (a, h, active) => ⟨a, h, active⟩
  save peer s := sqlDo "INSERT OR REPLACE INTO retry_cursor (peer, bytes) VALUES (?, ?)"
    #[peer, Codec.encode (s.after, s.high, s.active)]

def Sweep.begin (s : Sweep) (ceiling : Nat) : Sweep :=
  if s.active then s else ⟨0, ceiling, true⟩

def Sweep.finish (s : Sweep) : Sweep := { s with active := false }

/-- Move by exactly one position, including catalog holes. -/
def Sweep.advance (s : Sweep) : Sweep := { s with after := s.after + 1 }

/-- Production Connection's single-op envelope: 32-byte session id,
24-byte nonce, AEAD tag, codec prefixes and the sealed discriminator. -/
def Sweep.cost (o : Op) : Nat := (Codec.encode [o.bytes]).size + 74

/-- A full output window preserves the cursor. Oversize historical imports
cannot block every later position; app admission excludes them for new writes. -/
def Sweep.offer (s : Sweep) (op : Option Op) (shows : Op → Bool) (room : Nat) : Sweep × Option Op :=
  match op with
  | none => (s.advance, none)
  | some o =>
    if !shows o || maxFrame < cost o then (s.advance, none)
    else if cost o ≤ room then (s.advance, some o)
    else (s, none)

def Sweep.next (s : Sweep) (op : Option Op) (shows : Op → Bool) (room : Nat) : Sweep × Option Op :=
  if s.high ≤ s.after then (s.finish, none) else s.offer op shows room

/-- The pure cursor transition called by the store interpreter below. -/
def Sweep.step (s : Sweep) (ceiling : Nat) (input : Option Op) (shows : Op → Bool) (room : Nat) :=
  (s.begin ceiling).next input shows room

/-- At most one catalog row and one op read. The ceiling query runs only
at a sweep boundary. Cursor/output are returned together to the caller. -/
def Sweep.run {F : Type} {m : Type → Type} [Monad m] [Store F m]
    (catalog : Catalog m) (s : Sweep) (shows : Op → Bool) (room : Nat) : m (Sweep × Option Op) := do
  let ceiling ← if s.active then pure 0 else catalog.ceiling
  let prepared := s.begin ceiling
  if prepared.high ≤ prepared.after then return s.step ceiling none shows room
  let op ← match ← catalog.read (prepared.after + 1) with
    | none => pure none
    | some id => Store.getOp (F := F) id
  return s.step ceiling op shows room

end Engine.Sync
