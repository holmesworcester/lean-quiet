/- Service bounds for the exact FIFO queue called by Writer.turn/loop.
The existing rank theorem admits arbitrary finite tail arrivals between
completed polls; it needs no separate fairness assumption on this selector. -/
import engine.renderer.WriteQueue
import engine.wire.PriorityLaws

namespace Data.WriterQueue
open Engine.Sync.Inbox

theorem push_local (q : WriterQueue) (job : Job) (h : job.mine = true) :
    q.push job = q.append [job] [] := by simp [push, h, Priority.State.append]

theorem push_background (q : WriterQueue) (job : Job) (h : job.mine = false) :
    q.push job = q.append [] [job] := by simp [push, h, Priority.State.append]

theorem push_keeps_phase (q : WriterQueue) (job : Job) :
    (q.push job).slot = q.slot := by simp [push, Priority.State.append]; split <;> rfl

/-- No already queued local job moves behind a newer local submission. -/
theorem local_fifo (q : WriterQueue) (job : Job) (h : job.mine = true) :
    (q.push job).writes = q.writes ++ [job] := by simp [push_local q job h, Priority.State.append]

theorem background_fifo (q : WriterQueue) (job : Job) (h : job.mine = false) :
    (q.push job).events = q.events ++ [job] := by simp [push_background q job h, Priority.State.append]

/-- A local head wins each local-preferred poll, regardless of background depth. -/
theorem local_first (job : Job) (locals background : List Job) (slot : Priority.Slot)
    (h : slot.val ≠ 0) :
    (take ⟨job :: locals, background, slot⟩).1 = some job := by
  simp [take, Priority.step_write job locals background slot h]

/-- The reserved fourth phase serves a background head despite local demand. -/
theorem background_slot (locals : List Job) (job : Job) (background : List Job) (slot : Priority.Slot)
    (h : slot.val = 0) :
    (take ⟨locals, job :: background, slot⟩).1 = some job := by
  simp [take, Priority.step_event locals job background slot h]

/-- These runs have the actual queue state and the exact next state of take. -/
theorem take_state (q : WriterQueue) : (take q).2 = (Priority.step q).2 := rfl

/-- With p earlier local jobs, service occurs within 2(p+1) completed polls,
even if both producers keep appending. A local head waits at most one poll. -/
theorem local_within (r : Priority.Run Job Job) (i : Nat) (pre post : List Job) (job : Job)
    (h : (r.state i).writes = pre ++ job :: post) :
    ∃ j, i ≤ j ∧ j < i + 2 * (pre.length + 1) ∧ (take (r.state j)).1 = some job := by
  obtain ⟨j, hj, hb, hs⟩ := Priority.write_within r i pre post job h
  refine ⟨j, hj, hb, ?_⟩
  change ((Priority.step (r.state j)).1.map (Sum.elim id id)) = some job
  rw [show (Priority.step (r.state j)).1 = some (.inl job) from hs]
  rfl

/-- With p earlier background jobs, service occurs within 4(p+1) completed
polls under continuing local arrivals. No quiescence premise is used. -/
theorem background_within (r : Priority.Run Job Job) (i : Nat) (pre post : List Job) (job : Job)
    (h : (r.state i).events = pre ++ job :: post) :
    ∃ j, i ≤ j ∧ j < i + 4 * (pre.length + 1) ∧ (take (r.state j)).1 = some job := by
  obtain ⟨j, hj, hb, hs⟩ := Priority.event_within r i pre post job h
  refine ⟨j, hj, hb, ?_⟩
  change ((Priority.step (r.state j)).1.map (Sum.elim id id)) = some job
  rw [show (Priority.step (r.state j)).1 = some (.inr job) from hs]
  rfl

/-- The writer uses the proved 3:1 phase policy, including after any prefix. -/
theorem local_share (slot : Priority.Slot) :
    ((List.range 4).filter fun i => Priority.localFirst (Priority.phaseAfter slot i)).length = 3 :=
  Priority.local_share slot

end Data.WriterQueue
