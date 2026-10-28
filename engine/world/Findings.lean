/-
What stating the many-node laws found in the running code, each proven
of it (docs/PROOFS.md, "Findings"). Each is why a statement of
engine/world/Statements.lean is false today, and names the fix.

1. **Patience counts from the last receipt, not from the wait's start**
   (`patience_drops_idle`). A dialer's idle session (not waiting, last
   heard at h) opens a round at its cadence tick t; if h + patience ≤ t,
   its very next tick drops the session, before any answer could have
   arrived. With the defaults (a round every 30 s, patience 20 s) every
   session idle between rounds is dropped at its next round. This
   falsifies `session_stable_stmt` for any Δ > 0. Fix: `Conn.start` sets
   `heard := now` (the wait's start), so patience is silence while
   waiting, as SYNC.md says.
2. **A room only one end shows stops every round on the session**
   (`unshown_unanswered`, `no_round_while_open`). The answerer of a
   round in a room it does not show sends nothing; the dialer keeps that
   round's snapshot, so it waits (patience drops the session), and it
   opens no round in any room while one is open. Rooms differ at the two
   ends whenever one end has stored an admission the other has not, so
   this is the bootstrap's case. It is why `Healthy` must assume the
   rooms agree at both ends of a session, not only that both show r.
   Fix: answer a round in an unshown room with an empty claim list (it
   ends the round; the dialer's settle for that room is then vacuous, a
   choice for the user) or have the hello say which rooms it shows.
3. **`while` is `partial`, so opaque** (fixed on this branch).
   `Conn.walk` looped with `while`, which Lean compiles through a
   `partial` definition: no theorem can say anything about its result.
   Every tick and every answered want runs it, so after either, a node's
   store and connection were unknown to every proof. It is now a loop
   over `[0:cfg.walk]` with `break`, the same steps (`walk_keeps`,
   `walk_same`, `walk_idle` in engine/world/Run.lean).
-/
import engine.world.Run

namespace Engine.World
open Engine Engine.Sync

variable {F : Type} (fam : Family F) (cfg : Config)

/-- **Finding 1.** A dialing connection that is not waiting (its peer's
hello heard, nothing asked, no round open), its closure walk done, whose
cadence is due at t, and whose peer was last heard patience or more
before t: its tick at t opens a round, and its tick at t + 1 drops the
connection, though nothing could have been answered in between. -/
theorem patience_drops_idle (wl : WalkLaws (F := F) fam cfg) (ix : Index) (c : Conn) (pf t : Nat) (h : Held F)
    (hd : c.dialer = true) (hp : c.peerFloor = some pf) (hs : c.snaps = []) (ha : c.asked.isEmpty = true)
    (hf : c.frontier = []) (hr : c.rooms ≠ []) (hl : c.lastRound + cfg.every ≤ t)
    (hpat : c.heard + cfg.patience ≤ t) :
    let s₁ := ((c.tick fam cfg ix t : HeldM F Step).run h).1
    s₁.drop = false ∧ s₁.conn.round = c.round + 1 ∧
      ((s₁.conn.tick fam cfg ix (t + 1) : HeldM F Step).run h).1.drop = true := by
  have hw : c.waiting = false := by simp [Conn.waiting, hp, ha, hs]
  have hsn : (c.rooms.map fun r => ((r, c.round + 1), ix.items r)).isEmpty = false := by
    cases e : c.rooms with
    | nil => exact absurd e hr
    | cons _ _ => rfl
  simp only [Conn.tick, hw, Bool.false_and, Bool.false_eq_true, ite_false, HeldM.run_bind,
    wl.idle c h hf, hd, hs, List.isEmpty_nil, Bool.and_true,
    decide_eq_true hl, ite_true, HeldM.run_pure, Conn.start, hp, Conn.finish, Conn.report]
  refine ⟨trivial, by simp [ha], ?_⟩
  have hlt : c.heard + cfg.patience < t + 1 := by omega
  simp [ha, Conn.waiting, hsn, hlt]

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
  · simp only [HeldM.run_bind, HeldM.run_pure, Conn.finish, Conn.report]
    have hs' : (((c.walk fam cfg : HeldM F (Conn × List Id)).run h).1.1.snaps.isEmpty) = false := by
      rw [e.snaps]; cases e2 : c.snaps with
      | nil => exact absurd e2 hs
      | cons _ _ => rfl
    simp only [hs', Bool.and_false, Bool.false_and, Bool.false_eq_true, ite_false]
    split <;> exact e.round

end Engine.World
