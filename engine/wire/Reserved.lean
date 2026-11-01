/- The production Outbox writer calls this reservation core around the
existing Lanes operations and their proved semantics.
Each socket has one retry reservation independent of its ordinary queue.
The reservation stays occupied until the event loop records native-write
completion in durable retry metadata. -/
import engine.wire.LaneLaws

namespace Engine.Sync

/-- Metadata needed to commit progress after a transport attempt. The
concrete runtime ticket is (peer, cursor-before, cursor-after). -/
inductive RetrySlot (Ticket : Type) where
  | vacant
  | queued (ticket : Ticket) (payload : ByteArray)
  | writing (ticket : Ticket)
  | completed (ticket : Ticket)
  deriving Inhabited

namespace RetrySlot

def ready : RetrySlot Ticket → Bool
  | .queued _ _ => true
  | _ => false

def bytes : RetrySlot Ticket → Nat
  | .queued _ b => b.size
  | _ => 0

/-- A second retry cannot overwrite a queued, in-flight or completed one. -/
def offer (limit : Nat) (s : RetrySlot Ticket) (t : Ticket) (b : ByteArray) :
    Bool × RetrySlot Ticket :=
  match s with
  | .vacant => if b.size ≤ limit then (true, .queued t b) else (false, s)
  | _ => (false, s)

/-- Taking the frame does not release its reservation. -/
def take : RetrySlot Ticket → Option ByteArray × RetrySlot Ticket
  | .queued t b => (some b, .writing t)
  | s => (none, s)

/-- Called only for a native batch whose take included this retry. A
failed write leaves durable progress unchanged and ends the connection. -/
def sent (ok : Bool) : RetrySlot Ticket → RetrySlot Ticket
  | .writing t => if ok then .completed t else .vacant
  | s => s

def completed? : RetrySlot Ticket → Option Ticket
  | .completed t => some t
  | _ => none

/-- The loop first compare-and-swaps the durable cursor, then releases
the completed slot. Failure before the save leaves the row retryable. -/
def acknowledged : RetrySlot Ticket → RetrySlot Ticket
  | .completed _ => .vacant
  | s => s

theorem offer_busy {s : RetrySlot Ticket} (limit : Nat) (t : Ticket) (b : ByteArray)
    (busy : s ≠ .vacant) : s.offer limit t b = (false, s) := by
  cases s <;> simp_all [offer]

theorem offer_bound (limit : Nat) (s : RetrySlot Ticket) (t : Ticket) (b : ByteArray)
    (bounded : s.bytes ≤ limit) : (s.offer limit t b).2.bytes ≤ limit := by
  cases s <;> simp only [offer]
  · split <;> simp_all [bytes]
  · exact bounded
  · exact bounded
  · exact bounded

theorem take_queued (t : Ticket) (b : ByteArray) :
    take (.queued t b) = (some b, .writing t) := rfl

theorem cannot_refill_during_write (limit : Nat) (t u : Ticket) (b : ByteArray) :
    offer limit (.writing t) u b = (false, .writing t) := rfl

theorem successful_write_waits_for_ack (t : Ticket) :
    sent true (.writing t) = .completed t := rfl

end RetrySlot

structure Reserved (Ticket : Type) where
  ordinary : Lanes := {}
  retry : RetrySlot Ticket := .vacant
  deriving Inhabited

namespace Reserved

def Bounded (bytes frames retryBytes : Nat) (q : Reserved Ticket) : Prop :=
  q.ordinary.bytes ≤ bytes ∧
  q.ordinary.urgent.length + q.ordinary.serve.length ≤ frames ∧
  q.retry.bytes ≤ retryBytes

/-- Byte cap and frame count cap for the ordinary lanes. Overflow drops
this optimization batch, preserving the socket and its independent retry.
The catalogue retry path repairs loss of normal have/want/data frames. -/
def push (bytes frames : Nat) (q : Reserved Ticket) (ps : List (Lane × ByteArray)) :
    Bool × Reserved Ticket :=
  match q.ordinary.admit bytes ps with
  | none => (false, q)
  | some ordinary =>
    if ordinary.urgent.length + ordinary.serve.length ≤ frames then
      (true, { q with ordinary })
    else (false, q)

def offer (limit : Nat) (q : Reserved Ticket) (t : Ticket) (b : ByteArray) :
    Bool × Reserved Ticket :=
  let (ok, retry) := q.retry.offer limit t b
  (ok, { q with retry })

def ready (q : Reserved Ticket) : Bool := !q.ordinary.isEmpty || q.retry.ready

/-- UI/local urgent frames stay first. One reserved retry is in the very
next native batch, before the bounded ordinary serve burst. -/
def take (burst : Nat) (q : Reserved Ticket) : List ByteArray × Bool × Reserved Ticket :=
  let (bulk, rest) := cut burst q.ordinary.serve
  let (retryFrame, retry) := q.retry.take
  (q.ordinary.urgent ++ retryFrame.toList ++ bulk, retryFrame.isSome,
    { ordinary := { urgent := [], serve := rest }, retry })

theorem push_preserves_retry (bytes frames : Nat) (q : Reserved Ticket)
    (ps : List (Lane × ByteArray)) : (q.push bytes frames ps).2.retry = q.retry := by
  unfold push
  split
  · rfl
  · split <;> rfl

theorem rejected_push_preserves (bytes frames : Nat) (q : Reserved Ticket)
    (ps : List (Lane × ByteArray)) (rejected : (q.push bytes frames ps).1 = false) :
    (q.push bytes frames ps).2 = q := by
  cases ha : q.ordinary.admit bytes ps with
  | none => simp [push, ha]
  | some ordinary =>
    by_cases hc : ordinary.urgent.length + ordinary.serve.length ≤ frames
    · simp [push, ha, hc] at rejected
    · simp [push, ha, hc]

theorem push_bounded {bytes frames retryBytes : Nat} {q : Reserved Ticket}
    (ps : List (Lane × ByteArray)) (bounded : q.Bounded bytes frames retryBytes) :
    (q.push bytes frames ps).2.Bounded bytes frames retryBytes := by
  cases ha : q.ordinary.admit bytes ps with
  | none => simpa [push, ha] using bounded
  | some ordinary =>
    by_cases hc : ordinary.urgent.length + ordinary.serve.length ≤ frames
    · simp only [push, ha, hc, ↓reduceIte]
      exact ⟨(push_capped bytes q.ordinary ordinary ps ha).2, hc, bounded.2.2⟩
    · simpa [push, ha, hc] using bounded

theorem offer_bounded {bytes frames retryBytes : Nat} {q : Reserved Ticket}
    (t : Ticket) (b : ByteArray) (bounded : q.Bounded bytes frames retryBytes) :
    (q.offer retryBytes t b).2.Bounded bytes frames retryBytes := by
  exact ⟨bounded.1, bounded.2.1, RetrySlot.offer_bound _ _ _ _ bounded.2.2⟩

theorem take_retry_bytes (burst : Nat) (q : Reserved Ticket) :
    (q.take burst).2.2.retry.bytes ≤ q.retry.bytes := by
  cases q with
  | mk ordinary retry => cases retry <;> simp [take, RetrySlot.take, RetrySlot.bytes]

theorem take_bounded {bytes frames retryBytes : Nat} {q : Reserved Ticket}
    (burst : Nat) (bounded : q.Bounded bytes frames retryBytes) :
    (q.take burst).2.2.Bounded bytes frames retryBytes := by
  have rest := cut_append burst q.ordinary.serve
  have lengths := congrArg List.length rest
  have ordinary := take_bytes burst q.ordinary
  have budget : (q.take burst).2.2.ordinary.bytes ≤ q.ordinary.bytes := by
    change (q.ordinary.take burst).2.bytes ≤ q.ordinary.bytes
    omega
  refine ⟨Nat.le_trans budget bounded.1, ?_,
    Nat.le_trans (take_retry_bytes burst q) bounded.2.2⟩
  simp only [take, List.length_nil, Nat.zero_add]
  simp only [List.length_append] at lengths
  have := bounded.2.1
  omega

/-- Queue payload allocation, excluding native I/O's current batch. -/
theorem queued_bytes_bounded {bytes frames retryBytes : Nat} {q : Reserved Ticket}
    (bounded : q.Bounded bytes frames retryBytes) :
    q.ordinary.bytes + q.retry.bytes ≤ bytes + retryBytes := by
  have := bounded.1
  have := bounded.2.2
  omega

theorem take_batch_bytes {bytes frames retryBytes : Nat} {q : Reserved Ticket}
    (burst : Nat) (bounded : q.Bounded bytes frames retryBytes) :
    bytesOf (q.take burst).1 ≤ bytes + retryBytes := by
  have ordinary := take_bytes burst q.ordinary
  have base := bounded.1
  have retry := bounded.2.2
  cases q with
  | mk ordinaryQ retryQ =>
    cases retryQ <;>
      simp only [take, RetrySlot.take, Option.toList,
        bytesOf, List.map_nil, List.sum_nil, List.map_cons, List.sum_cons,
        List.map_append, List.sum_append,
        Nat.add_zero, Bounded, RetrySlot.bytes, Lanes.take] at * <;>
      omega

theorem take_batch_count {bytes frames retryBytes : Nat} {q : Reserved Ticket}
    (burst : Nat) (bounded : q.Bounded bytes frames retryBytes) :
    (q.take burst).1.length ≤ frames + 1 := by
  have rest := congrArg List.length (cut_append burst q.ordinary.serve)
  have base := bounded.2.1
  cases q with
  | mk ordinaryQ retryQ =>
    cases retryQ <;>
      simp only [take, RetrySlot.take, Option.toList, List.length_append,
        List.length_nil, List.length_cons] at * <;>
      omega

theorem framed_bytes (payloads : List ByteArray) :
    bytesOf (payloads.map frame) = bytesOf payloads + 4 * payloads.length := by
  induction payloads with
  | nil => simp [bytesOf]
  | cons b bs ih =>
    simp only [List.map_cons, bytesOf, List.map_cons, List.sum_cons,
      frame, ByteArray.size_append, size_be32, List.length_cons] at *
    omega

/-- The actual native writer receives ordinary frames plus at most one
retry, all including their four-byte transport length prefixes. -/
theorem native_batch_bytes {bytes frames retryBytes : Nat} {q : Reserved Ticket}
    (burst : Nat) (bounded : q.Bounded bytes frames retryBytes) :
    bytesOf ((q.take burst).1.map frame) ≤ bytes + retryBytes + 4 * (frames + 1) := by
  rw [framed_bytes]
  have := take_batch_bytes burst bounded
  have := take_batch_count burst bounded
  omega

theorem queued_next_batch (burst : Nat) (ordinary : Lanes) (t : Ticket) (b : ByteArray) :
    (take burst { ordinary, retry := .queued t b }).1 =
      ordinary.urgent ++ [b] ++ (cut burst ordinary.serve).1 := rfl

theorem queued_marked_inflight (burst : Nat) (ordinary : Lanes) (t : Ticket) (b : ByteArray) :
    (take burst { ordinary, retry := .queued t b }).2.2.retry = .writing t := rfl

/-- Any normal batch, including one rejected for overflow, cannot delay
the already-reserved retry beyond the next writer take. -/
theorem normal_flood_does_not_starve_retry (bytes frames burst : Nat)
    (ordinary : Lanes) (t : Ticket) (b : ByteArray) (ps : List (Lane × ByteArray)) :
    b ∈ ((push bytes frames { ordinary, retry := .queued t b } ps).2.take burst).1 := by
  have kept := push_preserves_retry bytes frames { ordinary, retry := .queued t b } ps
  generalize push bytes frames { ordinary, retry := .queued t b } ps = next at kept ⊢
  rcases next with ⟨ok, q⟩
  simp only at kept ⊢
  unfold take
  rw [kept]
  simp [RetrySlot.take]

end Reserved
end Engine.Sync
