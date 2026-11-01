import tests.engine.ConnectTcp
import tests.engine.ReaderLease

def main (args : List String) : IO UInt32 := do
  let t ← Tests.Checks.new
  if args.isEmpty || args.contains "--connect-only" then ConnectTcp.run t
  if args.isEmpty || args.contains "--reader-only" then ReaderLease.run t
  t.finish "native-lifetime"
