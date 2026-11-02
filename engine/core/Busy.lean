/-
A busy store slows the runner down and never stops it.

The glue (engine/native/glue.c) retries a statement SQLite refuses as
busy where the refusal changed nothing: a `BEGIN`, and a single statement
run outside a transaction. Whatever busy failure still escapes comes back
as `IO.Error.resourceBusy`, and the runner runs every store call through
`retrying`, which runs the call again from the same node state
(engine/core/BusyLaws.lean: `attempt` never fails busy). That second
retry is the backstop: a busy statement inside a held write transaction
is not expected in WAL mode, but if one came, the whole node step would
run again, repeating any fresh write committed earlier in it.
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
