/- The iOS shell now copies Surface's rectangles like the other shells.
There is no flipped-scroll-view placement model. Audit the running
placement, crop and input mapping at the iOS build boundary as well. -/
import engine.renderer.SlideLaws
import engine.renderer.InputLaws
#print axioms Surface.row_place
#print axioms Surface.row_pinned
#print axioms Surface.crop_row
#print axioms Surface.visible_in_viewport
#print axioms Surface.pinned_visible
#print axioms Surface.newest_drawn
#print axioms Input.tap_page
#print axioms Input.tap_content

#print axioms Translate.equivariance
#print axioms Translate.pinned
#print axioms Translate.fill_covers
#print axioms Translate.fill_pixel

#print axioms Slide.edge_eq
#print axioms Slide.delta_eq
#print axioms Slide.pick_eq
#print axioms Slide.fillRow_eq
