/-
The desktop's laws (engine/renderer/desktop/Laws.lean), audited apart
from tests/Axioms.lean: the desktop is not in the README yet, whose
count is of the code that runs on the phones. tests/app/desktop.sh
requires each to rest on Lean's standard axioms only.
-/
import engine.renderer.desktop.Laws
import platforms.desktop.Laws
#print axioms Desktop.widths
#print axioms Desktop.adjacent
#print axioms Desktop.drawer_preserves_main
#print axioms Desktop.overlay_contained
#print axioms Desktop.minimum
#print axioms Desktop.monotone
#print axioms Desktop.controls_fit
#print axioms Desktop.controls_screen
#print axioms Desktop.hit_drawn
#print axioms Desktop.witness
#print axioms Desktop.settled_no_hold
