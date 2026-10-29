/-
The desktop's laws (engine/renderer/desktop/Laws.lean), audited apart
from tests/Axioms.lean: the desktop is not in the README yet, whose
count is of the code that runs on the phones. tests/app/desktop.sh
requires each to rest on Lean's standard axioms only.
-/
import engine.renderer.desktop.Laws
import platforms.desktop.Laws
import platforms.desktop.HoverLaws
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
#print axioms Hover.disabled
#print axioms Hover.absent
#print axioms Hover.leave_clears
#print axioms Hover.blur_clears
#print axioms Hover.touch_clears
#print axioms Hover.active_iff
#print axioms Hover.active_inside
#print axioms Hover.front_drawn
#print axioms Hover.overlay_blocks
#print axioms Hover.local_inside
#print axioms Hover.disabled_rest
#print axioms Hover.absent_rest
#print axioms Desktop.pointer_preserves_app
#print axioms Desktop.pointer_preserves_tracks
#print axioms Desktop.pointer_leave_clears
#print axioms Desktop.pointer_blur_clears
#print axioms Desktop.hover_preserves_row_layout
#print axioms Desktop.hover_preserves_composer_layout
#print axioms Desktop.hover_preserves_sheet_layout
#print axioms Hover.routed_head_blocks
#print axioms Desktop.popup_blocks_main
#print axioms Hover.grace_expires
#print axioms Hover.menu_reachable
