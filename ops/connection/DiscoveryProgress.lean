/- Progress through the actual bounded address planner, interpreted by the
same Held/advancing-entropy interpreter as the connection progress laws.
These are step laws, not a claim that the whole native runner is fair. -/
import ops.connection.DiscoveryLaws
import ops.connection.ProgressTape

namespace Connection.DiscoveryProgress
open Engine Engine.Sync Codec Execution

/-- Ready advertised data produces the chosen destination and a persisted
retry op. Reading the plan neither consumes entropy nor changes the store. -/
theorem plan_ready (s : Memory) (c peer : B) (invite pub found : List B)
    (now : Nat) (old : Option (Nat × Nat)) (addr : B)
    (hr : (Discovery.retryState peer).eval s.held.db = old)
    (hdue : Discovery.canTry now old = true)
    (hp : (Discovery.advertised c peer now).eval s.held.db = pub)
    (hf : (Discovery.discovered peer now).eval s.held.db = found)
    (ha : Endpoint.pick (Discovery.candidates invite pub found) (Discovery.nextAttempt old) = some addr) :
    (Discovery.plan c peer invite now : M (Option (B × Op))) s =
      (some (addr, Community.mkOp [] (.retry peer now (Discovery.nextAttempt old))), s) := by
  simp only [Discovery.plan, ProgressTape.run_bind, ProgressTape.run_view, hr,
    hdue, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hp, hf, ha]
  rfl

/-- Address replacements cannot make this peer dial before its retry clock.
No assumption about the size, order or authors of new publications is needed. -/
theorem plan_backoff (s : Memory) (c peer : B) (invite : List B) (now : Nat)
    (old : Option (Nat × Nat))
    (hr : (Discovery.retryState peer).eval s.held.db = old)
    (hdue : Discovery.canTry now old = false) :
    (Discovery.plan c peer invite now : M (Option (B × Op))) s = (none, s) := by
  simp only [Discovery.plan, ProgressTape.run_bind, ProgressTape.run_view, hr,
    hdue, Bool.not_false, ↓reduceIte]
  rfl

/-- Waiting for the maximum backoff suffices for this next retained address.
Source is immaterial: invite, shared publication and DNS-SD are read by the
same planner. Fair service, fresh advertisements and delivery are separate. -/
theorem plan_after_backoff (s : Memory) (c peer : B) (invite pub found : List B)
    (last attempts now : Nat) (addr : B)
    (hr : (Discovery.retryState peer).eval s.held.db = some (last, attempts))
    (ht : last + 60000 ≤ now)
    (hp : (Discovery.advertised c peer now).eval s.held.db = pub)
    (hf : (Discovery.discovered peer now).eval s.held.db = found)
    (ha : Endpoint.pick (Discovery.candidates invite pub found)
      (Discovery.nextAttempt (some (last, attempts))) = some addr) :
    (Discovery.plan c peer invite now : M (Option (B × Op))) s =
      (some (addr, Community.mkOp [] (.retry peer now
        (Discovery.nextAttempt (some (last, attempts))))), s) :=
  plan_ready s c peer invite pub found now _ addr hr
    (DiscoveryLaws.retry_eventually_due last attempts now ht) hp hf ha

end Connection.DiscoveryProgress
