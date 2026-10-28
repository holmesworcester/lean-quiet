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
import Quiet.ArrivalLaws
import Quiet.Ttf.Laws
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
#print axioms Data.overlay_total
#print axioms Text.controls_neutral
#print axioms Text.marks_invisible
#print axioms ArrivalLaws.percent_lt
#print axioms ArrivalLaws.percent_eq
#print axioms ArrivalLaws.done_iff
#print axioms ArrivalLaws.caption_none_iff
#print axioms ArrivalLaws.caption_some
#print axioms ArrivalLaws.lit_zero
#print axioms ArrivalLaws.lit_mono
#print axioms ArrivalLaws.lit_full
#print axioms ArrivalLaws.lit_clockwise
#print axioms ArrivalLaws.onRing_square
#print axioms ArrivalLaws.layout_done
#print axioms ArrivalLaws.layout_shown
#print axioms ArrivalLaws.layout_arriving
#print axioms ArrivalLaws.layout_percent_lt
#print axioms ArrivalLaws.layout_words
#print axioms ArrivalLaws.layout_inside
#print axioms ArrivalLaws.ring_inside
#print axioms ArrivalLaws.words_inside
#print axioms ArrivalLaws.ring_counts
#print axioms ArrivalLaws.arrival_none
#print axioms ArrivalLaws.arrival_some
#print axioms ArrivalLaws.picBox_progress
#print axioms ArrivalLaws.layout_progress
#print axioms ArrivalLaws.shown_file
#print axioms ArrivalLaws.shown_pre
#print axioms ArrivalLaws.readView_model
#print axioms ArrivalLaws.pic_progress
#print axioms ArrivalLaws.pic_len
#print axioms ArrivalLaws.arrival_progress
#print axioms ArrivalLaws.arrival_counts
#print axioms ArrivalLaws.complete_iff_held
#print axioms ArrivalLaws.file_whole
#print axioms ArrivalLaws.pic_complete_iff_held

#print axioms Ttf.byte_in_bounds
#print axioms Ttf.cmap_entry
#print axioms Ttf.cmap12_glyph
#print axioms Ttf.cmap4_delta
#print axioms Ttf.cmap4_array
#print axioms Ttf.coverage_value
#print axioms Ttf.coverage_bound
#print axioms Ttf.checked_valid
#print axioms Ttf.raster_valid
#print axioms Ttf.ink_witness
#print axioms Ttf.raster_pixel
