/- Small dependency surface for executing bookkeeping mutations. -/
import tests.engine.BigSync
import tests.engine.StatelessBook

open Tests

def main (args : List String) : IO UInt32 := do
  let t ← Checks.new
  Harden.bookChecks t
  Harden.bigSyncChecks t ((args[0]?.bind String.toNat?).getD 5000) 256
  t.finish "fullsync"
