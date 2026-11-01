import engine.renderer.Screen
import engine.renderer.ActsLaws
import app.Screen

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

def boardSeen := Board.seen_take loadedInv.2

end Vacuity.RendererModels
