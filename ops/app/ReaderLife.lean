/- A revocable reader owned by a mounted page. Queries and publication
check its stop flag. The app detaches the board and polls completion;
Worker.stop is a joining API for callers outside the frame. -/
import ops.app.Reader

namespace Reader

structure Worker where
  stopped : IO.Ref Bool
  done : Task (Except IO.Error St)

def work (sh : Shared) (stopped : IO.Ref Bool) (initial : St) : IO St := do
  let mut s := initial
  while !(← stopped.get) do
    try
      let (busy, next) ← (pass sh (budgetMs := 4)).run s
      s := next
      if !busy then IO.sleep 2
    catch e =>
      IO.eprintln s!"reader: {e}"
      IO.sleep 50
  return s

def Worker.start (sh : Shared) (s : St) : IO Worker := do
  let stopped ← IO.mkRef false
  let done ← IO.asTask (prio := .dedicated) (work sh stopped { s with enabled := return !(← stopped.get) })
  return ⟨stopped, done⟩

/-- Publish cancellation through Ref.take/restore, so an overlapping native
Ref.get cannot restore an old false value over a completed stop request. -/
def Worker.requestStop (w : Worker) : IO Unit :=
  w.stopped.modify (fun _ => true)

def Worker.stop (w : Worker) : IO (Option St) := do
  w.requestStop
  match ← IO.wait w.done with
  | .ok s => return some s
  | .error e => throw e

end Reader
