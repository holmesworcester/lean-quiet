import engine.renderer.WriteQueueLaws
import ops.community.Compose

namespace Vacuity.WriterFairness
open Engine Data Engine.Sync.Inbox

-- The same signed-root constructor used by the native SQLite regression.
-- Kernel witnesses establish the queue premises, not the cryptographic
-- validity of these roots; the native regression checks their valid status.
def job (name : String) (mine : Bool) : Job :=
  ⟨[Community.root (Community.Device.named name) (sha256 name.toUTF8)], mine⟩

def oldLocal := job "old local" true
def nextLocal := job "next local" true
def oldBackground := job "old background" false
def nextBackground := job "next background" false
def arrivingLocal := job "continuing local" true
def arrivingBackground := job "continuing background" false

def initial : WriterQueue :=
  ⟨[oldLocal, nextLocal], [oldBackground, nextBackground], Priority.first⟩

-- Both nonempty producers continue forever; neither is drained first.
def busy : Priority.Run Job Job :=
  Priority.run initial (fun _ => [arrivingLocal]) (fun _ => [arrivingBackground])

theorem payloadsNonempty :
    oldLocal.ops.length = 1 ∧ oldBackground.ops.length = 1 ∧
    arrivingLocal.ops.length = 1 ∧ arrivingBackground.ops.length = 1 := by decide

theorem pushLocal : initial.push arrivingLocal = initial.append [arrivingLocal] [] :=
  WriterQueue.push_local initial arrivingLocal rfl

theorem pushBackground : initial.push arrivingBackground = initial.append [] [arrivingBackground] :=
  WriterQueue.push_background initial arrivingBackground rfl

theorem pushKeepsPhase : (initial.push arrivingLocal).slot = initial.slot :=
  WriterQueue.push_keeps_phase initial arrivingLocal

theorem localFIFO :
    (initial.push arrivingLocal).writes = [oldLocal, nextLocal, arrivingLocal] :=
  WriterQueue.local_fifo initial arrivingLocal rfl

theorem backgroundFIFO :
    (initial.push arrivingBackground).events = [oldBackground, nextBackground, arrivingBackground] :=
  WriterQueue.background_fifo initial arrivingBackground rfl

theorem localFirst : (WriterQueue.take initial).1 = some oldLocal :=
  WriterQueue.local_first oldLocal [nextLocal] [oldBackground, nextBackground]
    Priority.first (by decide)

theorem backgroundSlot :
    (WriterQueue.take ⟨[oldLocal, nextLocal], [oldBackground, nextBackground], ⟨0, by decide⟩⟩).1 =
      some oldBackground :=
  WriterQueue.background_slot [oldLocal, nextLocal] oldBackground [nextBackground] ⟨0, by decide⟩ rfl

theorem takeState : (WriterQueue.take initial).2 = (Priority.step initial).2 :=
  WriterQueue.take_state initial

theorem localDeadline :
    ∃ j, 0 ≤ j ∧ j < 4 ∧ (WriterQueue.take (busy.state j)).1 = some nextLocal :=
  WriterQueue.local_within busy 0 [oldLocal] [] nextLocal rfl

theorem backgroundDeadline :
    ∃ j, 0 ≤ j ∧ j < 8 ∧ (WriterQueue.take (busy.state j)).1 = some nextBackground :=
  WriterQueue.background_within busy 0 [oldBackground] [] nextBackground rfl

theorem localShare :
    ((List.range 4).filter fun i => Priority.localFirst
      (Priority.phaseAfter initial.slot i)).length = 3 :=
  WriterQueue.local_share initial.slot

-- This exact prefix independently identifies both initially waiting jobs.
theorem exactPrefix :
    (List.range 8).map (fun i => (WriterQueue.take (busy.state i)).1) =
      [some oldLocal, some nextLocal, some arrivingLocal, some oldBackground,
       some arrivingLocal, some arrivingLocal, some arrivingLocal, some nextBackground] := rfl

end Vacuity.WriterFairness
