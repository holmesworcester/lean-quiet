import engine.renderer.Screen
import engine.renderer.ActsLaws
import ops.app.Reader

/-! Concrete nonempty instances of the README's explicitly labelled models.
The board/reader worlds use two wants sharing one read. Their premises are
proved by the production constructors, not asserted as hypotheses. -/
set_option linter.defProp false
namespace Vacuity.RendererModels
open Engine Live

-- The existing two-row screen fixture has one near and one far message.
def screenSubscriptions := Screen.screen_subs Screen.frame2_good

def listWin : Win := { key := ByteArray.mk #[7], lo := some (Screen.onScreen.pos, true), hi := none }
private theorem listWinOnly : Screen.frame2.listWins = [listWin] := by rfl
private theorem containsOnScreen : listWin.inside Screen.onScreen.pos = true := by
  simp [Win.inside, above, below, listWin, Pos.cmp_self]
def nearHull := Screen.hull_near Screen.frame2_good
  (w := listWin) (by rw [listWinOnly]; simp)
  (r := Screen.onScreen) (by simp [Screen.frame2]) containsOnScreen

def hullBound := Screen.past_hull_le (fr := Screen.frame2) (a := Screen.onScreen)
  (by simp [Screen.frame2]) (by decide) 2
  (Nat.le_trans (List.length_filter_le _ _) (by decide))
  (Nat.le_trans (List.length_filter_le _ _) (by decide))

def frameIndex := Screen.screen_index Screen.frame2 (fun _ => (7 : Nat)) 7 listWin

def scrolledOff := Screen.keep_scrolled_off

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

-- Leave a deliberately dirty want unrefilled; it must stay marked.
def dirty : Live.World Nat Nat Unit Nat String := { store := 1, wants := [()], dirty := [()] }
def stillMarked := World.marked_pass Gated.touch Gated.eval (w := dirty) (pick := []) (x := ())
  (by simp [World.marked, World.pass, dirty])

-- Reader has two loaded answers, then a commit changes their shared read.
def readerCommit := RWorld.inv_commit Eager.apply Eager.hits Eager.eval Eager.reads
  Eager.w1_inv 2 (Eager.stable 2 1)
def readerPass := RWorld.inv_pass Eager.hits Eager.eval Eager.reads Eager.w1_inv 2
def readerFrame := RWorld.inv_frame Eager.hits Eager.eval Eager.reads readerPass
def readerEvict := RWorld.inv_evict Eager.hits Eager.eval Eager.reads Eager.w1_inv (fun _ => false)
def readerSettles := RWorld.settle Eager.hits Eager.eval Eager.reads Eager.w1_inv (cap := 2)
  (by exact Nat.le_trans (List.length_filter_le _ _) (by decide))
  (x := true) (by simp [Eager.w1])

-- The source's nonempty indexed model; a user's own act wins over backlog.
private def actsStable : RWorld.ActsStable Eager.apply Eager.hits Eager.eval Eager.reads Eager.w0.store [1] :=
  ⟨Eager.stable 1 0, trivial⟩
def actsShown := RWorld.acts_shown Eager.apply Eager.hits Eager.eval Eager.reads Eager.hitQs
  Eager.exact Eager.w0_inv Eager.w0_idx actsStable 0
  (x := true) (by simp [Eager.w0]) (q := ()) (by simp [Eager.hitQs]) (qs := [()]) rfl (by simp)
def actionsInvariant := RWorld.inv_passActs Eager.apply Eager.hits Eager.eval Eager.reads Eager.hitQs
  Eager.exact Eager.w0_inv Eager.w0_idx actsStable 0

def actionIndex := RWorld.idxok_passActs Eager.apply Eager.hits Eager.eval Eager.reads Eager.hitQs
  Eager.exact (by intro s x; simp [Eager.reads]) Eager.w0_idx [1] 0

def actionPicks := RWorld.passActs_picks Eager.apply Eager.hitQs [1] 0 Eager.w0

def noActions := RWorld.passActs_nil Eager.apply Eager.hits Eager.eval Eager.reads Eager.hitQs 2 Eager.w0

def app : Live.AWorld Nat Nat Bool Nat Unit String := ⟨Eager.w0, [1, 2], some "Keep my draft"⟩
def composerKept := AWorld.passActs_comp Eager.apply Eager.hits Eager.eval Eager.reads Eager.hitQs 1 app
def composerIndependent := AWorld.passActs_indep Eager.apply Eager.hits Eager.eval Eager.reads Eager.hitQs 1 app (some "Edited")
def actionsTaken := AWorld.passActs_acts Eager.apply Eager.hits Eager.eval Eager.reads Eager.hitQs 1 app
def typing := AWorld.type_only (fun _ => some "Typed") app

-- A steady frame includes both its viewport reads and additional lists.
def ids : Reader.Want := .window (ByteArray.mk #[1]) none 100 100
def count : Reader.Want := .count (ByteArray.mk #[1]) none
def other : Reader.Want := .comms
def viewSteady := Reader.Want.withView_ofFrame ids count #[] #[] #[other]
def viewMutant := Reader.Want.withViewLast_moves ids count #[] #[] #[other] (by decide) (by simp [count, other])

end Vacuity.RendererModels
