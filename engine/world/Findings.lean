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
10. **An expired ask lets a room report settled without its op**
   (`expiry_settles`). Since sync-harden an ask expires `patience` after
   it was first made, even while other traffic keeps the session up. A
   room whose first round has ended is reported settled as soon as
   `asked` is empty, so when the last ask expires (its wants lost, or
   the peer never serving it), the next tick reports the room settled
   though the op never came. The Connection family writes that report
   as a local op. This falsifies `no_false_settle_stmt`. Fix: settle
   only when every id asked in the room's first round has arrived (a
   set only arrivals clear), or open a fresh round after an expiry.
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


attribute [local instance] byteArray_lawfulBEq

/-- **Finding 10.** A responding connection whose room r's first round
has ended, not yet reported settled, whose only outstanding ask x was
made at t0, heard from recently enough to stay up: its tick at a time
past t0 + patience expires x, keeps the session, and reports r settled,
though x never arrived. -/
theorem expiry_settles (wl : WalkLaws (F := F) fam cfg) (ix : Index) (c : Conn) (x r : Id) (t0 now : Nat)
    (h : Held F) (hd : c.dialer = false) (hf : c.frontier = []) (hr : c.rounded = [r]) (hs : c.settled = [])
    (_hx : x ∈ c.asked) (ha : ∀ y ∈ c.asked, y = x) (ht : c.askTime[x]? = some t0) (hexp : t0 + cfg.patience < now)
    (hlive : now ≤ c.heard + cfg.patience) (hlease : now ≤ c.heard + cfg.lease) :
    let s := ((c.tick fam cfg ix now : HeldM F Step).run h).1
    s.drop = false ∧ r ∈ s.conn.settled ∧ Status.settled r ∈ s.status ∧ x ∉ s.conn.asked := by
  have hno : ((c.waiting && Decidable.decide (c.waitStart + cfg.patience < now)) || c.expired cfg now) = false := by
    have h1 : ¬ c.waitStart + cfg.patience < now := by
      unfold Conn.waitStart; have := Nat.le_max_left c.heard c.lastRound; omega
    have h2 : c.expired cfg now = false := by
      simp [Conn.expired, hd, show ¬ c.heard + cfg.lease < now by omega]
    rw [h2, Bool.or_false, Bool.and_eq_false_iff]
    exact Or.inr (decide_eq_false h1)
  have hempty : (c.expireAsks cfg now).asked.isEmpty = true := by
    rw [Std.HashSet.isEmpty_iff_forall_not_mem]
    intro y hy
    simp only [Conn.expireAsks, Std.HashSet.mem_filter] at hy
    obtain ⟨hy, hl⟩ := hy
    rw [Std.HashSet.get_eq] at hl
    rw [ha y hy, ht] at hl
    simp at hl; omega
  unfold Conn.tick
  simp only [hno, Bool.false_eq_true, ↓reduceIte, HeldM.run_bind]
  rw [wl.idle c h hf]
  simp only [HeldM.run_pure, Conn.expireAsks_dialer, hd, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  simp only [Conn.finish, Conn.report]
  have he2 : ({ c.expireAsks cfg now with lastAsk := if c.lastAsk + cfg.retry ≤ now then now else c.lastAsk } :
      Conn).asked.isEmpty = true := hempty
  have er : (c.expireAsks cfg now).rounded = [r] := hr
  have es : (c.expireAsks cfg now).settled = [] := hs
  simp only [he2, ite_true]
  refine ⟨trivial, ?_, ?_, fun hx => ?_⟩
  · simp [er, es, has]
  · simp [er, es, has]
  have : (c.expireAsks cfg now).asked.isEmpty = true := hempty
  rw [Std.HashSet.isEmpty_iff_forall_not_mem] at this
  exact this x hx

end Engine.World
