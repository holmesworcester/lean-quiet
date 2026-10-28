/-
What stating the many-node laws found in the running code, each proven
of it (docs/PROOFS.md, "Findings"). Each is why a statement of
engine/world/Statements.lean is false today, and names the fix.

1. **Patience counted from the last receipt** (fixed on main by
   sync-harden, cad36f2). A dialer's idle session opened a round at its
   cadence tick and dropped it at the next tick when the peer was last
   heard patience or more before. Patience now starts at
   `max heard lastRound`, and holmes-a3's `round_not_dropped`
   (TimeLaws) proves a round opened at t survives through t + patience.
2. **A room only one end shows stops every round on the session**
   (`unshown_unanswered`, `no_round_while_open`). The answerer of a
   round in a room it does not show sends nothing; the dialer keeps that
   round's snapshot, so it waits (patience drops the session), and it
   opens no round in any room while one is open. Rooms differ at the two
   ends whenever one end has stored an admission the other has not, so
   this is every join. It falsifies `rooms_stmt` and `join_stmt`, and is
   why `Carries` assumes the rooms agree at both ends.
3. **`while` is `partial`, so opaque.** `Conn.walk` loops with `while`,
   which Lean compiles through a `partial` definition: no theorem can
   say anything about its result, and every tick and every answered want
   runs it. The laws here take what they need of it as the premise
   `WalkLaws` (`walk_stmt`), which a3/hostile's structural `walkN`
   discharges.
-/
import engine.world.Run

namespace Engine.World
open Engine Engine.Sync

variable {F : Type} (fam : Family F) (cfg : Config)

/-- **Finding 2, the answerer.** A round's message in a room this side
does not show is answered with nothing, and changes nothing. -/
theorem unshown_unanswered (ix : Index) (c : Conn) (r : Id) (k : Nat) (cs : List Claim) (now : Nat)
    (hr : r ∉ c.rooms) : (c.onRbsr cfg ix r k cs now).send = [] ∧ (c.onRbsr cfg ix r k cs now).conn = c := by
  have : has c.rooms r = false := (has_false _ _).2 hr
  simp [Conn.onRbsr, this]

/-- **Finding 2, the dialer.** While a round is open on a connection (its
snapshot kept), the clock opens no other: the round number stays. -/
theorem no_round_while_open (hw : WalkLaws (F := F) fam cfg) (ix : Index) (c : Conn) (now : Nat) (h : Held F)
    (hs : c.snaps ≠ []) :
    ((c.tick fam cfg ix now : HeldM F Step).run h).1.conn.round = c.round := by
  have e := hw.same c h
  unfold Conn.tick
  split
  · rfl
  · simp only [HeldM.run_bind, HeldM.run_pure, Conn.finish_conn_round]
    have hs' : (((c.walk fam cfg : HeldM F (Conn × List (Id × Id))).run h).1.1.snaps.isEmpty) = false := by
      rw [e.snaps]; cases e2 : c.snaps with
      | nil => exact absurd e2 hs
      | cons _ _ => rfl
    simp only [Conn.expireAsks_snaps, Conn.expireAsks_dialer, hs', Bool.and_false, Bool.false_and,
      Bool.false_eq_true, ite_false, Conn.expireAsks_round]
    exact e.round

end Engine.World
