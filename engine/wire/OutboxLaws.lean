/- Bounds of the actual socket writer's Outbox functions. These count the
admitted queues and one native batch; they do not bound prior Node computation
or imply termination of SQLite/native calls. -/
import engine.wire.Tcp

namespace Engine.Sync.Outbox

def Bounded (cfg : RunConfig) (o : Outbox) : Prop :=
  o.lanes.bytes ≤ cfg.sockCap ∧ o.control.bytes ≤ cfg.sockCap ∧
  o.lanes.urgent.length + o.lanes.serve.length ≤ cfg.sockFrames ∧
  o.control.urgent.length + o.control.serve.length ≤ cfg.sockFrames ∧
  o.retry.bytes ≤ maxFrame

theorem empty_bounded (cfg : RunConfig) : Bounded cfg {} := by
  simp [Bounded, Lanes.bytes, bytesOf, RetrySlot.bytes]

theorem queued_bounded {cfg : RunConfig} {o : Outbox} (h : Bounded cfg o) :
    o.queued.Bounded (2 * cfg.sockCap) (2 * cfg.sockFrames) maxFrame := by
  rcases h with ⟨hn, hc, hnf, hcf, hr⟩
  refine ⟨?_, ?_, hr⟩
  · simp only [queued, Lanes.bytes, bytesOf_append]
    simp only [Lanes.bytes] at hn hc
    omega
  · simp only [queued, List.length_append]
    omega

theorem push_bounded {cfg : RunConfig} {o : Outbox} (critical : Bool)
    (ps : List (Lane × ByteArray)) (h : Bounded cfg o) :
    Bounded cfg (o.push cfg critical ps).2 := by
  rcases h with ⟨hn, hc, hnf, hcf, hr⟩
  cases critical with
  | false =>
    have hq : Reserved.Bounded cfg.sockCap cfg.sockFrames maxFrame
        ({ ordinary := o.lanes, retry := o.retry } : Reserved RetryTicket) := ⟨hn, hnf, hr⟩
    have hp := Reserved.push_bounded ps hq
    simp only [push, Bool.false_eq_true, ↓reduceIte]
    exact ⟨hp.1, hc, hp.2.1, hcf, hr⟩
  | true =>
    have hq : Reserved.Bounded cfg.sockCap cfg.sockFrames maxFrame
        ({ ordinary := o.control, retry := o.retry } : Reserved RetryTicket) := ⟨hc, hcf, hr⟩
    have hp := Reserved.push_bounded ps hq
    simp only [push, ↓reduceIte]
    exact ⟨hn, hp.1, hnf, hp.2.1, hr⟩

/-- Ordinary overflow never consumes the protected control or retry slots. -/
theorem push_preserves_reserved (cfg : RunConfig) (o : Outbox) (ps : List (Lane × ByteArray)) :
    (o.push cfg false ps).2.control = o.control ∧
    (o.push cfg false ps).2.retry = o.retry ∧
    (o.push cfg false ps).1 = true := by
  simp [push]

theorem take_bounded {cfg : RunConfig} {o : Outbox} (burst : Nat) (h : Bounded cfg o) :
    Bounded cfg (o.take burst).2.2 := by
  rcases h with ⟨hn, hc, hnf, hcf, hr⟩
  have ordinary := take_bytes burst o.lanes
  have frames := congrArg List.length (cut_append burst o.lanes.serve)
  have retries := Reserved.take_retry_bytes burst o.queued
  simp only [Bounded, take, Reserved.take, queued, Lanes.bytes, bytesOf, List.map_nil,
    List.sum_nil, Nat.zero_add, List.length_nil] at *
  simp only [Lanes.take, Lanes.bytes, bytesOf_append, bytesOf, List.map_nil,
    List.sum_nil, Nat.zero_add, List.length_append] at *
  exact ⟨by omega, by omega, by omega, by omega, Nat.le_trans retries hr⟩

/-- Both queue byte caps and the single retry payload, including every
frame's four-byte wire length, bound the exact batch sent by writer. -/
theorem native_batch_bounded {cfg : RunConfig} {o : Outbox} (burst : Nat) (h : Bounded cfg o) :
    bytesOf ((o.take burst).1.map frame) ≤
      2 * cfg.sockCap + maxFrame + 4 * (2 * cfg.sockFrames + 1) :=
  Reserved.native_batch_bytes burst (queued_bounded h)

/-- Local urgent frames remain first even when control, retry and ordinary
sync work are all queued. The reserved frame follows in this same batch. -/
theorem urgent_then_retry (burst : Nat) (o : Outbox) :
    (o.take burst).1 = o.lanes.urgent ++ o.control.urgent ++ o.control.serve ++
      o.retry.take.1.toList ++ (cut burst o.lanes.serve).1 := rfl

theorem retry_next_batch (burst : Nat) (o : Outbox) (t : RetryTicket) (b : ByteArray)
    (queued : o.retry = .queued t b) : b ∈ (o.take burst).1 := by
  rw [urgent_then_retry, queued]
  simp [RetrySlot.take]

end Engine.Sync.Outbox
