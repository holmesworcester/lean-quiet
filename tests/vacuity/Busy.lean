import engine.core.BusyLaws

/-! The runner's store calls under a busy store (engine/core/BusyLaws.lean),
in the kernel: a call that returns gives its value, one SQLite refuses as
busy comes back to be tried again, and any other failure is thrown as it
was. On a real SQLite file, with a second connection holding the write
lock past the busy timeout: tests/vacuity/StoreTrust.lean. -/
namespace Vacuity.Busy
open Engine.Store

/-- SQLite's "database is locked", as the glue reports it. -/
def locked : IO.Error := .resourceBusy 5 "database is locked"
def ioFailed : IO.Error := .userError "disk I/O error"

theorem returns (w : Void IO.RealWorld) : attempt (pure 3 : IO Nat) w = .ok (some 3) w :=
  attempt_ok rfl

theorem busyRetried (w : Void IO.RealWorld) : attempt (throw locked : IO Nat) w = .ok none w :=
  attempt_busy rfl rfl

theorem otherThrown (w : Void IO.RealWorld) : attempt (throw ioFailed : IO Nat) w = .error ioFailed w :=
  attempt_other rfl rfl

/-- The failure an attempt does throw is not busy. -/
theorem thrownNotBusy (w : Void IO.RealWorld) : busy ioFailed = false :=
  attempt_never_busy (otherThrown w)

-- The content: a busy error is busy, so a check that let it through
-- would fail; and the old runner's catch-all would have ended on it.
example : busy locked = true := rfl
example : busy ioFailed = false := rfl

/-- The shipped runner, on the same locked call, fails busy. -/
theorem shippedEscapes (w : Void IO.RealWorld) :
    ∃ e', attemptShipped (throw locked : IO Nat) w = .error e' w ∧ busy e' = true :=
  shipped_busy_escapes rfl rfl

end Vacuity.Busy
