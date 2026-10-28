import tests.engine.BigSync

open Tests

def main : IO UInt32 := do
  let t ← Checks.new
  Harden.clockChecks t
  Harden.wantChecks t
  Harden.memoryChecks t
  Harden.hostileChecks t
  Harden.bigSyncChecks t
  Harden.queueChecks t
  Harden.sharedSocketChecks t
  Harden.closeEffectsChecks t
  t.finish "harden"
