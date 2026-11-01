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

def boardSeen := Board.seen_take loadedInv.2

end Vacuity.RendererModels
