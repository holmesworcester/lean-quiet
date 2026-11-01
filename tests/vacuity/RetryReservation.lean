/- Component execution counterexample and the current reservation core. This runs the
actual current Lanes/roomOf/Sweep.step functions and the production Reserved
core. It is not a native runner test, does not send on a socket, and does
not identify an emitted effect with a wire attempt. -/
import engine.wire.OutboxLaws
import engine.sync.SweepLaws

namespace Engine.Sync.ReservationCounterexample

def noise : ByteArray := "ordinary".toUTF8
def addr : ByteArray := "peer".toUTF8
def normal : Lanes := { serve := [noise] }
def waiting : Sweep := ⟨0, 1, true⟩

/-- Every cycle completes an ordinary writer take and then refills the
ordinary window before a retry service tick sees it. -/
def refill : Lanes :=
  let drained := (normal.take noise.size).2
  (drained.admit noise.size [(.serve, noise)]).getD drained

theorem ordinary_writer_steps : (normal.take noise.size).1 = [noise] := rfl
theorem refill_full : refill = normal := rfl
theorem no_retry_room : roomOf noise.size [(addr, refill)] addr = some 0 := by decide +kernel

def oldCycle (o : Op) (cursor : Sweep) : Sweep × Option Op :=
  cursor.step 1 (some o) (fun _ => true)
    ((roomOf noise.size [(addr, refill)] addr).getD 0)

theorem oldCycle_stalls (o : Op) (fits : Sweep.cost o ≤ maxFrame) :
    oldCycle o waiting = (waiting, none) := by
  have positive : ¬ Sweep.cost o ≤ 0 := by unfold Sweep.cost; omega
  simp [oldCycle, no_retry_room, Sweep.step, Sweep.begin, Sweep.next,
    Sweep.offer, waiting, Nat.not_lt.mpr fits, positive]

def oldRun (o : Op) : Nat → Sweep
  | 0 => waiting
  | n + 1 => (oldCycle o (oldRun o n)).1

/-- Infinitely many completed ordinary writer cycles are insufficient:
the target cursor remains at its first row for every cycle. -/
theorem oldRun_never_retries (o : Op) (fits : Sweep.cost o ≤ maxFrame) :
    ∀ n, oldRun o n = waiting ∧ (oldCycle o (oldRun o n)).2 = none := by
  intro n
  induction n with
  | zero => exact ⟨rfl, congrArg Prod.snd (oldCycle_stalls o fits)⟩
  | succ n ih =>
    have next : oldRun o (n + 1) = waiting := by
      simp only [oldRun, ih.1, oldCycle_stalls o fits]
    exact ⟨next, by rw [next, oldCycle_stalls o fits]⟩

/-- Reservation permits cursor *preparation* while the ordinary window
remains full. The returned advanced cursor is a ticket, not yet durable. -/
theorem prepared_despite_full_window (o : Op) (fits : Sweep.cost o ≤ maxFrame) :
    Sweep.step waiting 1 (some o) (fun _ => true) maxFrame =
      (waiting.advance, some o) := by
  simp [Sweep.step, Sweep.begin, Sweep.next, Sweep.offer, waiting,
    Nat.not_lt.mpr fits, fits]

/-- With a fitting sealed payload, normal queue saturation cannot prevent
its reserved admission. Native completion and durable acknowledgment are
separate stages; this only proves admission and the next writer batch. -/
theorem reserved_despite_full_window (t : Ticket) (payload : ByteArray)
    (fits : payload.size ≤ maxFrame) :
    let q : Reserved Ticket := { ordinary := refill }
    (q.offer maxFrame t payload).1 = true ∧
    payload ∈ ((q.offer maxFrame t payload).2.take noise.size).1 ∧
    ((q.offer maxFrame t payload).2.take noise.size).2.2.retry = .writing t := by
  simp [Reserved.offer, RetrySlot.offer, fits, Reserved.take, RetrySlot.take]

/-- Any number of intervening normal pushes, even overflows, preserve
the admitted retry, so an endlessly replenished normal producer cannot
erase or postpone it past the next writer take. -/
theorem arbitrary_flood_preserves (bytes frames : Nat) (t : Ticket) (payload : ByteArray)
    (batches : List (List (Lane × ByteArray))) (ordinary : Lanes) :
    (batches.foldl (fun q ps => (q.push bytes frames ps).2)
      ({ ordinary, retry := .queued t payload } : Reserved Ticket)).retry = .queued t payload := by
  suffices ∀ q : Reserved Ticket,
      (batches.foldl (fun q ps => (q.push bytes frames ps).2) q).retry = q.retry by
    exact this _
  induction batches with
  | nil => intro q; rfl
  | cons ps rest ih =>
    intro q
    rw [List.foldl_cons, ih, Reserved.push_preserves_retry]

end Engine.Sync.ReservationCounterexample

namespace Vacuity.RetryReservation
open Engine Engine.Sync

def ticket : RetryTicket := ⟨"authenticated-peer".toUTF8, ⟨1, 2, true⟩, ⟨2, 2, true⟩⟩
def localWrite : ByteArray := "Alice local write".toUTF8
def backlog : ByteArray := "ordinary sync".toUTF8
def retryPayload : ByteArray := "retained Bob post".toUTF8

def cfg : RunConfig := { sockCap := 128, sockFrames := 8 }
def box : Outbox := {
  lanes := { urgent := [localWrite], serve := [backlog] }
  control := { urgent := ["handshake".toUTF8] }
  retry := .queued ticket retryPayload }

theorem fits : Outbox.Bounded cfg box := by unfold Outbox.Bounded; decide +kernel

theorem nativeBatch : bytesOf ((box.take 32).1.map frame) ≤
    2 * cfg.sockCap + maxFrame + 4 * (2 * cfg.sockFrames + 1) :=
  Outbox.native_batch_bounded 32 fits

theorem retryNext : retryPayload ∈ (box.take 32).1 :=
  Outbox.retry_next_batch 32 box ticket retryPayload rfl

theorem localFirst : (box.take 32).1.head? = some localWrite := rfl

theorem normalOverflowKept :
    (box.push { cfg with sockCap := 0 } false [(.serve, backlog)]).2.control = box.control ∧
    (box.push { cfg with sockCap := 0 } false [(.serve, backlog)]).2.retry = box.retry ∧
    (box.push { cfg with sockCap := 0 } false [(.serve, backlog)]).1 = true :=
  Outbox.push_preserves_reserved _ box _

example : ¬Outbox.Bounded { cfg with sockCap := 1 } box := by unfold Outbox.Bounded; decide +kernel

def admitted : Lanes := { urgent := [localWrite], serve := [backlog] }

theorem admittedReach : Lanes.Reach 128 32 admitted :=
  .push [(.urgent, localWrite), (.serve, backlog)] .empty (by rfl)

theorem laneAppend : (admitted.take 32).1 ++ (admitted.take 32).2.serve =
    admitted.urgent ++ admitted.serve ∧ (admitted.take 32).2.urgent = [] :=
  take_append 32 admitted

theorem laneBytes : bytesOf (admitted.take 32).1 + (admitted.take 32).2.bytes =
    admitted.bytes := take_bytes 32 admitted

theorem laneBound : admitted.bytes ≤ 128 := lanes_bounded admittedReach

def reserved : Reserved RetryTicket := { ordinary := admitted }

theorem reservedFits : reserved.Bounded 128 8 maxFrame := by
  unfold Reserved.Bounded; decide +kernel

theorem offerBound : (reserved.offer maxFrame ticket retryPayload).2.Bounded 128 8 maxFrame :=
  Reserved.offer_bounded ticket retryPayload reservedFits

theorem pushBound : (reserved.push 128 8 [(.serve, backlog)]).2.Bounded 128 8 maxFrame :=
  Reserved.push_bounded _ reservedFits

theorem takeBound : (reserved.take 32).2.2.Bounded 128 8 maxFrame :=
  Reserved.take_bounded 32 reservedFits

theorem outboxPush : Outbox.Bounded cfg (box.push cfg false [(.serve, backlog)]).2 :=
  Outbox.push_bounded false _ fits

theorem outboxTake : Outbox.Bounded cfg (box.take 32).2.2 :=
  Outbox.take_bounded 32 fits

end Vacuity.RetryReservation
