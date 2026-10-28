/-
The model's `Allowed` is what the engine's own `allowPeer` view answers:
for a node whose engine has received the ops L (in any order, with any
interleaving of processing) and finished processing them, the view, read
as lists over its persisted tables, accepts exactly the devices `Allowed`
names.
So the trust rule in `Net.Node` reads the running query, not a model of
it.
-/
import ops.connection.bootstrap.Scene

namespace Net
open Engine Community

theorem table_eq_ops {C : Crypto} {L : List Op} {s : DB Fact} (hr : Reach (family C) L s)
    (hd : Distinct L) : s.ops = table L := by
  funext i
  cases h : s.ops i with
  | none =>
    cases h' : table L i with
    | none => rfl
    | some o =>
      have := (reach_ops hr hd i o).2 (table_some h')
      rw [h] at this; cases this
  | some o =>
    have ⟨hm, hi⟩ := (reach_ops hr hd i o).1 h
    rw [← hi]; exact (table_of hd hm).symm

/-- **`Allowed` is `allowPeer` at rest.** -/
theorem allowPeer_iff {C : Crypto} {L : List Op} {s : DB Fact} (hr : Reach (family C) L s)
    (hd : Distinct L) (hq : s.queue = []) (c : Id) (p : Key) :
    (allowPeer c p).eval s = true ↔ Allowed C L c p := by
  rw [connect_iff (reach_inv hr) hq c p, table_eq_ops hr hd]; rfl

/-- And a node's engine always gets there: after enough processing
steps its queue is empty, so `allowPeer` answers `Allowed`. -/
theorem allowPeer_settles {C : Crypto} {L : List Op} {s : DB Fact} (hr : Reach (family C) L s)
    (hd : Distinct L) : ∃ n, ∀ c p,
      (allowPeer c p).eval (drainS (family C) n s) = true ↔ Allowed C L c p := by
  obtain ⟨n, hn⟩ := drain_terminates hd s hr
  exact ⟨n, fun c p => allowPeer_iff (reach_drain hr n) hd hn c p⟩

end Net
