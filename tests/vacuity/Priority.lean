import engine.wire.PriorityLaws
import engine.wire.LoopLaws
import tests.engine.LoopChecks

namespace Vacuity.Priority
open Engine.Sync

-- Both accepted-input producers append on EVERY turn, forever. The proof
-- does not replace a perpetually busy producer with a finite initial queue.
def busy : Inbox.Priority.Run String String :=
  Inbox.Priority.run ⟨["send Alice", "send Bob"], ["frame Alice", "frame Bob"], Inbox.Priority.first⟩
    (fun _ => ["continuing local write"]) (fun _ => ["continuing network frame"])

theorem writeDeadline : ∃ j, 0 ≤ j ∧ j < 4 ∧ busy.selected j = some (.inl "send Bob") :=
  Inbox.Priority.write_within busy 0 ["send Alice"] [] "send Bob" rfl

theorem eventDeadline : ∃ j, 0 ≤ j ∧ j < 8 ∧ busy.selected j = some (.inr "frame Bob") :=
  Inbox.Priority.event_within busy 0 ["frame Alice"] [] "frame Bob" rfl

theorem localShare :
    ((List.range 4).filter fun i => Inbox.Priority.localFirst
      (Inbox.Priority.phaseAfter Inbox.Priority.first i)).length = 3 :=
  Inbox.Priority.local_share Inbox.Priority.first

theorem phaseCycle : Inbox.Priority.phaseAfter Inbox.Priority.first 4 = Inbox.Priority.first :=
  Inbox.Priority.phase_cycle Inbox.Priority.first

theorem waiting : Inbox.Priority.Waiting (busy.state 0) (.inr "frame Bob") 8 :=
  Inbox.Priority.Waiting.event _ ["frame Alice"] [] "frame Bob" rfl

theorem waitingProgress :
    (Inbox.Priority.step (busy.state 0)).1 = some (.inr "frame Bob") ∨
      ∃ k < 8, Inbox.Priority.Waiting
        ((Inbox.Priority.step (busy.state 0)).2.append ["new local"] ["new frame"])
        (.inr "frame Bob") k :=
  Inbox.Priority.waiting_step waiting ["new local"] ["new frame"]

theorem servedFromRank : ∃ j, 0 ≤ j ∧ j < 0 + 8 ∧ busy.selected j = some (.inr "frame Bob") :=
  Inbox.Priority.served busy 0 (.inr "frame Bob") waiting

example : (List.range 8).map busy.selected =
    [some (.inl "send Alice"), some (.inl "send Bob"), some (.inl "continuing local write"),
     some (.inr "frame Alice"), some (.inl "continuing local write"),
     some (.inl "continuing local write"), some (.inl "continuing local write"),
     some (.inr "frame Bob")] := by decide

example : busy.selected 3 ≠ some (.inl "continuing local write") := by decide
example : busy.selected 0 ≠ some (.inr "frame Alice") := by decide

def state : Loop.State Nat := { value := 2, lastTick := 10 }
def memory : LoopChecks.Memory := { now := 20, writes := [7], events := [9] }

theorem turnRecords :
    let result := ((Loop.turn LoopChecks.backend 10 state).run memory).1
    result.state.slot = Inbox.Priority.advance state.slot ∧ result.observed.now = memory.now :=
  Loop.turn_records LoopChecks.backend 10 state memory

theorem turnTimer :
    let result := ((Loop.turn LoopChecks.backend 10 state).run memory).1
    (result.ticked, result.state.lastTick) = Tick.next 10 state.lastTick result.observed.now :=
  Loop.turn_timer LoopChecks.backend 10 state memory (by decide)

example : ((Loop.turn LoopChecks.backend 10 state).run memory).2.calls =
    ["clock", "poll-write", "write", "tick", "expire"] := by decide

end Vacuity.Priority
