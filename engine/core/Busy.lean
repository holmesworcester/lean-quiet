/-
A store call that SQLite refused because another connection held a lock
past the busy timeout (SQLITE_BUSY, SQLITE_LOCKED: `IO.Error.resourceBusy`,
from engine/native/glue.c) changed nothing, and may run again. The runner
runs every store call through `retrying`, so a busy store slows the node
down and never stops it (engine/core/BusyLaws.lean).
-/
namespace Engine.Store

/-- Whether SQLite refused the call as busy or locked. -/
def busy : IO.Error → Bool
  | .resourceBusy .. => true
  | _ => false

/-- One try of a store call: its value, or `none` if SQLite was busy.
Any other failure is thrown, as before. -/
def attempt {α : Type} (act : IO α) : IO (Option α) :=
  tryCatch (do let a ← act; pure (some a)) fun e => if busy e then pure none else throw e

/-- The runner as it shipped: a store call ran as it was, so a busy
error reached `Tcp.runLoop`'s catch and ended the node's networking for
good ("network runner stopped: database is locked"). Kept as the
control (tests/wiring.txt); `shipped_busy_escapes` proves it fails. -/
def attemptShipped {α : Type} (act : IO α) : IO (Option α) := do
  let a ← act
  pure (some a)

/-- The pause before the next try, in ms: 10 doubling, at most 500. -/
def backoff (k : Nat) : Nat := min 500 (10 * 2 ^ min k 6)

/-- A store call, tried again after a pause for as long as SQLite is busy.
Its only failures are `attempt`'s, which are never busy. -/
partial def retrying {α : Type} (act : IO α) (k : Nat := 0) : IO α := do
  match ← attempt act with
  | some a => pure a
  | none =>
    if k % 20 == 19 then IO.eprintln s!"store busy: {k + 1} tries, still trying"
    IO.sleep (backoff k).toUInt32
    retrying act (k + 1)

end Engine.Store
