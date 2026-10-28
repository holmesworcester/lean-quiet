import engine.core.Engine
import ops.community.Community
import ops.connection.All
import engine.renderer.Geometry
import engine.renderer.SheetGeom
import ops.community.link.View
import engine.renderer.Camera
import ops.app.Switch
import engine.renderer.TextLaws
import engine.renderer.WrapLaws
import ops.community.reaction.RowLaws
import ops.community.message.ViewLaws
import ops.app.PeopleLaws
import ops.app.Remove
import ops.community.membership.RemovedLaws
import App
import ops.community.attachment.ArrivalLaws
import engine.renderer.qr.Qr
import engine.renderer.pic.Pic
import engine.wire.mdns.Mdns
import ops.connection.bootstrap.Net

/-! Every law of the repository, each of which must rest on Lean's
standard axioms only (tests/check.sh). One section per former package's
audit, with its `open`s. -/

section engine
open Engine Community
#print axioms Engine.inv_ingest
#print axioms Engine.inv_step
#print axioms Engine.status_iff_spec
#print axioms Engine.order_free
#print axioms Engine.reach_drain
#print axioms Engine.spec_extends
#print axioms Engine.Codec.decode_encode
#print axioms Engine.Codec.encode_decode
#print axioms Engine.Op.id_decode
#print axioms Engine.Op.decode_bytes
#print axioms Engine.distinct_of_collisionFree
#print axioms Engine.Sync.num_inj
#print axioms Engine.Sync.lbl_inj
#print axioms Engine.Sync.exchange_complete
#print axioms Engine.Sync.opening_honest
#print axioms Engine.intakeConn_conn
#print axioms Engine.Sync.recv_take
#print axioms Engine.Sync.recv_send
#print axioms Engine.Sync.filed_send
#print axioms Engine.Sync.tick_send
#print axioms Engine.Sync.spec_local
#print axioms Engine.run_step
#print axioms Engine.run_drain
#print axioms Community.message_authorized
#print axioms Community.no_impersonation
#print axioms Community.profile_authorized
#print axioms Community.no_renaming
#print axioms Community.admission_consented
#print axioms Community.admission_approved
#print axioms Community.request_invited
#print axioms Community.approval_signed
#print axioms Community.invitation_issued
#print axioms Community.request_valid
#print axioms Community.approve_valid
#print axioms Community.admit_admits
#print axioms Community.admission_needs_approval
#print axioms Community.removed_approver_admits
#print axioms Community.removal_authorized
#print axioms Community.admin_removal_stands
#print axioms Community.mutual_removal
#print axioms Community.admin_granted
#print axioms Community.removed_stays
#print axioms Community.valid_stays
#print axioms Community.connect_iff
#print axioms Community.refuse_nonmember
#print axioms Community.connect_admitted
#print axioms Community.connect_approved
#print axioms Community.recipients_iff
#print axioms Community.connect_agree
#print axioms Community.removal_cuts_off
#print axioms Engine.drain_terminates
#print axioms Engine.drain_settles
#print axioms Engine.same_ops_same_verdicts
#print axioms Engine.eval_stable
#print axioms Engine.view_stable
#print axioms Engine.View.run_model
#print axioms Community.members_iff
#print axioms Community.removals_iff
#print axioms Engine.Rel.key_ne_opKey
#print axioms Engine.mem_keysOf
#print axioms Engine.filed_rel
#print axioms Community.rels_distinct
#print axioms Engine.intake_local
#print axioms Engine.offer_shared
#print axioms Engine.offer_stored
#print axioms Engine.stored_local
#print axioms Community.parse_text
#print axioms Community.parse_valid
#print axioms Community.Base62.decode_encode
#print axioms Community.secret_derives
#print axioms Community.named_by_admin
#print axioms Community.local_fact_mine
#print axioms Community.joinOps_travels
#print axioms Community.found_travels
#print axioms Engine.drain_bounded
#print axioms Engine.step_budget
#print axioms Community.stopWaiting_local
#print axioms Connection.Noise.handshake_agrees
#print axioms Connection.Noise.sent1_write1
#print axioms Connection.wire_kinds
#print axioms Connection.local_kinds
#print axioms Engine.sum_left
#print axioms Engine.sum_scope_left
#print axioms Connection.open_seal
#print axioms Connection.cid_seal
#print axioms Connection.established_agrees
#print axioms Connection.Noise.sent1_read1
#print axioms Connection.Noise.read2_write2'
#print axioms Engine.purge_gone
#print axioms Engine.purge_named
#print axioms Engine.purge_shared
#print axioms Engine.purge_undecides
#print axioms Engine.mem_purgeSet
#print axioms Engine.purge_inv
#print axioms Engine.perm_sortPos
#print axioms Engine.matching_nodup
#print axioms Engine.purge_settles
#print axioms Engine.reach_ops
#print axioms Community.unbox_box
#print axioms Community.openBody_sealBody
#print axioms Community.check_reads_shared
#print axioms Community.openSealed_seal
#print axioms Community.member_opens
#print axioms Community.check_attach
#print axioms Community.check_chunk
#print axioms Community.chunk_is_slice
#print axioms Engine.eval_union
#print axioms Engine.mem_union
#print axioms Engine.mem_union_all
#print axioms Community.readable_held
#print axioms Community.readable_complete
#print axioms Community.Merkle.encode_verify
#print axioms Community.Merkle.verify_sound
#print axioms Community.Merkle.index_bound
#print axioms Community.Merkle.complete_assembles
#print axioms Community.Merkle.assemble_slices
#print axioms Community.Merkle.climb_path
#print axioms Community.Merkle.climb_sub
#print axioms Community.Merkle.no_injective_hash
#print axioms Community.Merkle.assumptions_hold
#print axioms Community.op_of_valid
#print axioms Community.chunk_id
#print axioms Community.chunk_unique
#print axioms Community.nodup_full
#print axioms Community.progress_exact
#print axioms Community.progress_le
#print axioms Community.progress_full
#print axioms Community.progress_done
#print axioms Connection.trusts_live
#print axioms Connection.rooms_trusted
#print axioms Connection.rooms_cut
#print axioms Connection.rooms_model
#print axioms Connection.Noise.Symbolic.good
#print axioms Connection.Noise.Symbolic.kk_runs
#print axioms Connection.Noise.Symbolic.derivable_clean
#print axioms Connection.Noise.Symbolic.derivable_sealed
#print axioms Connection.Noise.Symbolic.kk_secret_init
#print axioms Connection.Noise.Symbolic.kk_secret_resp
#print axioms Connection.Noise.Symbolic.kk_secret
#print axioms Connection.Noise.Symbolic.kk_forward_secret_init
#print axioms Connection.Noise.Symbolic.kk_forward_secret_resp
#print axioms Connection.Noise.Symbolic.kk_forward_secret
#print axioms Connection.Noise.Symbolic.kk_authentic
#print axioms Connection.Noise.Symbolic.kk_authentic_resp
#print axioms Connection.Noise.Symbolic.exposed_parts
#print axioms Connection.Noise.Symbolic.kk_secret_init_tight
#print axioms Community.root_of_admission
#print axioms Community.removeMember_valid
#print axioms Community.chunk_of_attachment
#print axioms Community.chunk_hangs_off
#print axioms Community.chunk_own
#print axioms Connection.openAt_seal
#print axioms Connection.openAt_sealed
#print axioms Connection.Frame.ctrOf_nonce
end engine

section app
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
end app

section qr
#print axioms Qr.parse_dataStream
#print axioms Qr.parse_segsBits
#print axioms Qr.parse_valid
#print axioms Qr.decodeFormat_correct
#print axioms Qr.decodeVersion_correct
#print axioms Qr.RS.correct_sound
#print axioms Qr.RS.correct_clean
#print axioms Qr.decodeImage_malformed
#print axioms Qr.readBits_bitsOf
#print axioms Qr.bytesBits_packBytes
#print axioms Pic.fit_small
#print axioms Pic.fit_le
#print axioms Pic.fit_pos
#print axioms Pic.fit_long
#print axioms Pic.fit_round
#print axioms Pic.layout_sizes
#print axioms Pic.layout_inside
#print axioms Pic.layout_apart
#print axioms Pic.add_stored
#print axioms Pic.scale_wellFormed
#print axioms Pic.render_wellFormed
#print axioms Pic.render_opaque
#print axioms Pic.decode_sized
end qr

section mdns
#print axioms Mdns.decode_encode
#print axioms Mdns.decode_valid
#print axioms Mdns.decode_roundtrip
end mdns

section net
open Net
#print axioms Net.Scene.no_connection_before_approval
#print axioms Net.Scene.sessions_trusted
#print axioms Net.Scene.bootstrap_possible
#print axioms Net.Scene.bootstrap
#print axioms Net.Scene.bootstrap_ideal
#print axioms Net.Scene.reachable_inv
#print axioms Net.Scene.admitted_inv
#print axioms Net.Scene.allowedA
#print axioms Net.Scene.allowedB
#print axioms Net.allowPeer_iff
#print axioms Net.allowPeer_settles
end net
