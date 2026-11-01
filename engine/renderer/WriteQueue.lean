/- The actual app writer queue. Local and background submissions append to
separate FIFOs; one atomic state owns both lists and the finite 3:1 selector
phase. Admission remains unbounded: no accepted job is evicted by this queue. -/
import engine.core.Engine
import engine.wire.Priority

namespace Data
open Engine

/-- A write: ops (a file's bytes are ops too: its chunks). -/
structure Job where
  ops : List Op
  mine : Bool := false
  deriving Inhabited

abbrev WriterQueue := Engine.Sync.Inbox.Priority.State Job Job
namespace WriterQueue
open Engine.Sync.Inbox

def empty : WriterQueue := ⟨[], [], Priority.first⟩

def isEmpty (q : WriterQueue) : Bool := q.writes.isEmpty && q.events.isEmpty

/-- A producer only appends; it never resets service phase or overtakes
an already accepted job in the same class. -/
def push (q : WriterQueue) (job : Job) : WriterQueue :=
  if job.mine then { q with writes := q.writes ++ [job] }
  else { q with events := q.events ++ [job] }

/-- The same executable FIFO interpretation used by the selector's rank
proofs. The writer discards the source tag after selecting the actual job. -/
def take (q : WriterQueue) : Option Job × WriterQueue :=
  let (selected, next) := Priority.step q
  (selected.map (Sum.elim id id), next)

end WriterQueue
end Data
