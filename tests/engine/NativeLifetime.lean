import tests.engine.ConnectTcp
import tests.engine.ReaderLease
import engine.core.Exit

def mainBody (args : List String) : IO UInt32 := do
  let t ← Tests.Checks.new
  if args.isEmpty || args.contains "--connect-only" then ConnectTcp.run t
  if args.isEmpty || args.contains "--reader-only" then ReaderLease.run t
  t.finish "native-lifetime"

/-- Leaves by `IO.Process.exit` (Engine.exitAfter): returning from
`main` with a runner's threads alive would wait for them for good. -/
def main (args : List String) : IO UInt32 := Engine.exitAfter (mainBody args)
