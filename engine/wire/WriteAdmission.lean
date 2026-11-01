import engine.core.Core
import engine.wire.Frame

/-
Admission for new app writes, before optimistic display or durable queueing.
These are limits on admitted writes, not a claim about every app allocation.
The frame allowance is the production Connection envelope with a 32-byte
session id and 24-byte nonce. Low-level imports and historical stores still
need their own domain checks.
-/

namespace App.WriteAdmission
open Engine

structure Limits where
  ops : Nat := 8192
  bytes : Nat := 128 * 1024 * 1024

def bytes (xs : List ByteArray) : Nat := (xs.map ByteArray.size).sum

/-- Even when sent alone, an op must fit the encrypted transport frame. -/
def fits (o : Op) : Bool :=
  decide ((Codec.encode [o.bytes]).size + 74 ≤ Sync.maxFrame)

/-- Refusal leaves the existing queue and draft intact. -/
def refusal (lim : Limits) (pending : List ByteArray) (incoming : List Op) : Option String :=
  if !incoming.all fits then some "This message is too large to send. Shorten it and try again."
  else if lim.ops < pending.length + incoming.length ||
      lim.bytes < bytes pending + bytes (incoming.map Op.bytes) then
    some "Too many changes are waiting to be saved. Try again after they finish."
  else none

theorem admitted_frames {lim : Limits} {pending : List ByteArray} {incoming : List Op}
    (h : refusal lim pending incoming = none) :
    ∀ o ∈ incoming, (Codec.encode [o.bytes]).size + 74 ≤ Sync.maxFrame := by
  unfold refusal at h
  split at h
  · cases h
  · rename_i hf
    have ha : incoming.all fits = true := by simpa using hf
    intro o ho
    have := List.all_eq_true.mp ha o ho
    simpa [fits] using this

theorem admitted_count {lim : Limits} {pending : List ByteArray} {incoming : List Op}
    (h : refusal lim pending incoming = none) :
    pending.length + incoming.length ≤ lim.ops := by
  unfold refusal at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i hc
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hc
      omega

theorem admitted_bytes {lim : Limits} {pending : List ByteArray} {incoming : List Op}
    (h : refusal lim pending incoming = none) :
    bytes pending + bytes (incoming.map Op.bytes) ≤ lim.bytes := by
  unfold refusal at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i hc
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hc
      omega

end App.WriteAdmission
