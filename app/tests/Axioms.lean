import Quiet.Geometry
import Quiet.SheetGeom
import Quiet.Link
import Quiet.Camera
import Quiet.Switch
import Quiet.TextLaws
import Quiet.WrapLaws
import Quiet.RowLaws
import Quiet.ViewLaws
import Quiet.PeopleLaws
import Quiet.Remove
import Quiet.RemovedLaws
import Quiet.App
#print axioms Geometry.placed_row
#print axioms Geometry.visible_in_viewport
#print axioms Geometry.newest_visible
#print axioms Geometry.newest_drawn
#print axioms SheetGeom.hit_iff
#print axioms SheetGeom.hit_cell
#print axioms SheetGeom.keys_disjoint
#print axioms SheetGeom.reachable
#print axioms SheetGeom.clamp_le
#print axioms SheetGeom.compose_row
#print axioms SheetGeom.compose_top
#print axioms Geometry.pinned_row
#print axioms Geometry.pinned_visible
#print axioms Geometry.pinned_tap
#print axioms Link.hints_fit
#print axioms Link.qr_fits
#print axioms Camera.src_in
#print axioms Switch.dedupe_nodup
#print axioms Switch.select_tapped
#print axioms Switch.select_tapped_dedupe
#print axioms App.drawPage_key
#print axioms App.pageIn_acc
#print axioms Pages.switcherOrder_sound
#print axioms Pages.switcherOrder_complete
#print axioms Switch.dedupe_one_per_community
#print axioms Text.visual_perm
#print axioms Text.place_shows
#print axioms Text.oneLine_prefix
#print axioms Text.digits_keep_order
#print axioms Text.wrap_keeps
#print axioms Text.wrap_fits
#print axioms Text.place_starts
#print axioms RowLaws.picBox_aspect
#print axioms RowLaws.tally_nodup
#print axioms RowLaws.tally_mem
#print axioms RowLaws.time_shown
#print axioms RowLaws.name_placed
#print axioms ViewLaws.profile_read
#print axioms ViewLaws.message_read
#print axioms PeopleLaws.present_iff
#print axioms PeopleLaws.present_nodup
#print axioms Remove.writes_only_after_two
#print axioms Remove.cancel_writes_nothing
#print axioms Remove.open_fresh
#print axioms Remove.no_replace
#print axioms Remove.offered_only
#print axioms RemovedLaws.listed_iff
#print axioms RemovedLaws.told_once
#print axioms RemovedLaws.not_replayed
#print axioms RemovedLaws.landing_listed
#print axioms RemovedLaws.forget_clears
