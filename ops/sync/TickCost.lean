/-
What a connection's tick costs the store (docs/PERF.md), over every
store: the laws are `Within` budgets of the code that runs, counted in
`CostT m` for any lawful store monad m (SQLite's included).

- `walkN_reads`: the closure walk reads at most two rows a step (the op,
  and its status when the peer may see it), so `walk_reads`: at most
  2·`cfg.walk` reads, and `walk_idle`: none when the frontier is empty.
  It writes nothing (`walk_writes`).
- `tick_reads`: so a connection's tick reads at most 2·`cfg.walk` rows,
  and none when its frontier is empty (`tick_idle`): the clock's work on
  a connection is bounded by the configuration, whatever the store holds.

A node's tick runs this once per connection, after reading its rooms
(the Connection family's `rooms`); summing the two over the sessions is
the next step (docs/PERF.md). The negative control is the walk with no
budget, run in tests/engine/CostCheck.lean on a chain longer than it:
its reads grow with the chain.
-/
import ops.sync.Conn
import engine.core.CostStore

namespace Engine.Sync
open Engine

section
variable {F : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Store F m] (fam : Family F)
  (cfg : Config) {g : Meter → Nat} [Field g]

/-- **The closure walk charges at most two point reads a step.** -/
theorem walkN_within : ∀ (n : Nat) (c : Conn) (offer : List Id),
    Within g (n * (g { reads := 1 } + g { reads := 1 })) (Conn.walkN (m := CostT m) fam n c offer)
  | 0, c, offer => by rw [Nat.zero_mul]; exact within_pure _
  | n + 1, c, offer => by
    unfold Conn.walkN
    split
    · exact (within_pure _).mono (Nat.zero_le _)
    · simp only
      split
      · exact (walkN_within n _ _).mono (Nat.mul_le_mul_right _ (Nat.le_succ n))
      · refine within_bind_le (B := g { reads := 1 } + n * (g { reads := 1 } + g { reads := 1 }))
          (within_getOp _) (fun r => ?_) (by rw [Nat.succ_mul]; omega)
        cases r with
        | none =>
          exact (walkN_within n _ _).mono (by omega)
        | some o =>
          simp only
          split
          · exact within_bind (within_getStatus _) (fun _ => walkN_within n _ _)
          · exact (walkN_within n _ _).mono (by omega)

/-- With an empty frontier the walk charges nothing. -/
theorem walkN_idle (n : Nat) (c : Conn) (offer : List Id) (h : c.frontier = []) :
    Within g 0 (Conn.walkN (m := CostT m) fam n c offer) := by
  cases n with
  | zero => exact within_pure _
  | succ n => unfold Conn.walkN; rw [h]; exact within_pure _

theorem walk_within (c : Conn) :
    Within g (cfg.walk * (g { reads := 1 } + g { reads := 1 })) (c.walk (m := CostT m) fam cfg) :=
  within_bind_le (walkN_within fam _ _ _) (fun _ => within_pure _) (by omega)

/-- **The walk reads at most 2·`cfg.walk` rows.** -/
theorem walk_reads (c : Conn) : Within Meter.reads (2 * cfg.walk) (c.walk (m := CostT m) fam cfg) :=
  (walk_within fam cfg c).mono (by simp; omega)

/-- **The walk writes nothing.** -/
theorem walk_writes (c : Conn) : Within Meter.writes 0 (c.walk (m := CostT m) fam cfg) :=
  (walk_within fam cfg c).mono (by simp)

/-- **An empty frontier reads nothing.** -/
theorem walk_idle (c : Conn) (h : c.frontier = []) : Within g 0 (c.walk (m := CostT m) fam cfg) :=
  within_bind_le (walkN_idle fam _ _ _ h) (fun _ => within_pure _) (by omega)

/-- **A connection's tick reads at most 2·`cfg.walk` rows**, whatever
the store holds, and writes nothing. -/
theorem tick_reads (ix : Index) (c : Conn) (now : Nat) :
    Within Meter.reads (2 * cfg.walk) (c.tick (m := CostT m) fam cfg ix now) ∧
      Within Meter.writes 0 (c.tick (m := CostT m) fam cfg ix now) := by
  unfold Conn.tick
  constructor
  · refine within_ite (fun _ => (within_pure _).mono (Nat.zero_le _)) (fun _ => ?_)
    exact within_bind_le (walk_reads fam cfg c) (fun _ => within_pure _) (by omega)
  · refine within_ite (fun _ => within_pure _) (fun _ => ?_)
    exact within_bind_le (walk_writes fam cfg c) (fun _ => within_pure _) (by omega)

/-- **A connection with nothing to walk ticks without reading.** -/
theorem tick_idle (ix : Index) (c : Conn) (now : Nat) (h : c.frontier = []) :
    Within g 0 (c.tick (m := CostT m) fam cfg ix now) := by
  unfold Conn.tick
  refine within_ite (fun _ => within_pure _) (fun _ => ?_)
  exact within_bind_le (walk_idle fam cfg c h) (fun _ => within_pure _) (by omega)

end

end Engine.Sync
