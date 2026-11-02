/-!
# A program's end

When `main` returns, the Lean runtime waits for every task the program
started, dedicated ones too. A runner's socket reader and writer, and a
store's writer and pruner, never end on their own. So a program that may
hold one, and returns from `main` (after an uncaught exception, say), waits
for them for good: it hangs, its failure unreported (the cjk_scroll hang,
close_ingress's). `exitAfter` runs the program and leaves by
`IO.Process.exit` whatever happened, after saying what threw.
-/

namespace Engine

/-- Run `body`; then flush and exit with its code (an exception: report
it, exit 2). It never returns, so no task can keep the program alive. -/
def exitAfter (body : IO UInt32) : IO UInt32 := do
  let code ← try body catch e => do
    IO.eprintln s!"uncaught: {e}"
    pure 2
  (← IO.getStdout).flush
  (← IO.getStderr).flush
  IO.Process.exit (if code > 255 then 1 else code.toUInt8)

end Engine
