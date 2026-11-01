import engine.renderer.ActsLaws
import app.Screen

/-! Concrete nonempty instances of the README's explicitly labelled models.
The board/reader worlds use two wants sharing one read. Their premises are
proved by the production constructors, not asserted as hypotheses. -/
set_option linter.defProp false
namespace Vacuity.RendererModels
open Engine Live

-- A loaded board, followed by a real commit and refill.
def base : Live.World Nat Nat Unit Nat String := { store := 0, wants := [()], comp := some "Draft" }
def loaded := (base.pass Gated.touch Gated.eval [()]).frame
private def baseInv := World.inv_start (C := Nat) (K := String) Gated.touch Gated.eval 0 [()]
private def loadedInv := World.inv_frame Gated.touch Gated.eval
  (World.inv_pass Gated.touch Gated.eval baseInv [()])

def worldCommit := World.inv_commit Gated.apply Gated.touch Gated.eval loadedInv 1 (Gated.stable 1 0)
def worldPass := World.inv_pass Gated.touch Gated.eval loadedInv [()]
def worldFrame := World.inv_frame Gated.touch Gated.eval
  (World.inv_pass Gated.touch Gated.eval loadedInv [()])
def worldSettles := World.settle Gated.touch Gated.eval loadedInv (pick := [()])
  (by intro x hx; cases x; simp) (x := ()) (by simp [loaded, base, World.frame, World.pass])
def boardSeen := Board.seen_take loadedInv.2

-- Reader has two loaded answers, then a commit changes their shared read.
def readerCommit := RWorld.inv_commit Eager.apply Eager.hits Eager.eval Eager.reads
  Eager.w1_inv 2 (Eager.stable 2 1)
def readerFrame := RWorld.inv_frame Eager.hits Eager.eval Eager.reads Eager.w1_inv
def readerSettles := RWorld.settle Eager.hits Eager.eval Eager.reads Eager.w1_inv (cap := 2)
  (by exact Nat.le_trans (List.length_filter_le _ _) (by decide))
  (x := true) (by simp [Eager.w1])

-- The source's nonempty indexed model; a user's own act wins over backlog.
private def actsStable : RWorld.ActsStable Eager.apply Eager.hits Eager.eval Eager.reads Eager.w0.store [1] :=
  ⟨Eager.stable 1 0, trivial⟩
def actsShown := RWorld.acts_shown Eager.apply Eager.hits Eager.eval Eager.reads Eager.hitQs
  Eager.exact Eager.w0_inv Eager.w0_idx actsStable 0
  (x := true) (by simp [Eager.w0]) (q := ()) (by simp [Eager.hitQs]) (qs := [()]) rfl (by simp)


def actionPicks := RWorld.passActs_picks Eager.apply Eager.hitQs [1] 0 Eager.w0


-- The running reader's index and board: want 1 reads 7, then a notice hits 7.
def wanted : Std.HashSet Nat := (∅ : Std.HashSet Nat).insert 1
def idx0 : Index Nat Nat := ⟨{}, {}, {}⟩
def idx1 : Index Nat Nat := idx0.record 1 #[7]
private theorem idx0Ok : Indexed idx0 := by intro w qs q h; simp [idx0] at h
theorem idx1Ok : Indexed idx1 := record_indexed idx0 1 #[7] idx0Ok
private theorem idx1Deps : idx1.deps[1]? = some #[7] := by simp [idx1, idx0, Index.record]
private theorem wanted1 : wanted.contains 1 = true := by simp [wanted]
theorem noticed : 1 ∈ (markHit (fun q => (idx1.rev.getD q #[]).toList) idx1.dirty [7]).filter wanted.contains :=
  marked_complete idx1 idx1Ok [7] wanted (q := 7) idx1Deps (by simp) (by simp) wanted1
theorem stillDirty : 1 ∈ (markHit (fun q => (idx1.rev.getD q #[]).toList) ((∅ : Std.HashSet Nat).insert 1) []).filter wanted.contains :=
  dirty_marked { idx1 with dirty := (∅ : Std.HashSet Nat).insert 1 } [] wanted (by simp) wanted1
theorem cleaned : 1 ∉ idx1.dirty := fun h => ((record_dirty idx0 1 1 #[7]).1 h).2 rfl

def evalR (w : Nat) : Nat × Array Nat := (w + 10, #[7])
private theorem fresh0 : Fresh evalR idx0 ({} : Board Nat Nat) wanted := by
  intro x _ v n hb; simp [Board.get?] at hb
theorem freshRead : Fresh evalR (idx0.record 1 (evalR 1).2) (({} : Board Nat Nat).put 1 (evalR 1).1) wanted :=
  fresh_record evalR idx0 {} wanted fresh0 1
theorem freshKept : Fresh evalR (idx0.record 1 (evalR 1).2) ((({} : Board Nat Nat).put 1 (evalR 1).1).keep (· == 1)) wanted :=
  fresh_keep evalR _ _ wanted (· == 1) freshRead
theorem freshNoticed : Fresh evalR ((idx0.record 1 (evalR 1).2).notice wanted [8]) (({} : Board Nat Nat).put 1 (evalR 1).1) wanted :=
  fresh_notice evalR evalR _ _ wanted [8] (record_indexed idx0 1 _ idx0Ok) freshRead (fun _ _ _ _ => rfl)
theorem settled : ∀ w, wanted.contains w = true → ∀ v n,
    (({} : Board Nat Nat).put 1 (evalR 1).1).get? w = some (v, n) → v = (evalR w).1 :=
  settle_fresh evalR (idx0.record 1 (evalR 1).2) _ wanted freshRead (fun w _ h => by
    have := (record_dirty idx0 1 w (evalR 1).2).1 h; simp [idx0] at this)

end Vacuity.RendererModels
