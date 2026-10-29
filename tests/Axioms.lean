import engine.renderer.SafeLaws
import engine.renderer.ThemeLaws
import engine.renderer.SlideLaws
import engine.renderer.InputLaws
import engine.renderer.TranslateLaws
import ops.sync.TreeLaws
import ops.app.LifecycleLaws
import ops.sync.StateLaws
import ops.sync.ClosureComplete
import ops.sync.TimeLaws
import ops.sync.SessionLaws
import ops.sync.SecrecyLaws
import ops.sync.Witnesses
import ops.sync.RetryLaws
import ops.sync.BoundsLaws
import ops.sync.ServeLaws
import engine.wire.CloseLaws
import engine.wire.LaneLaws
import engine.wire.Slots
import engine.core.Engine
import engine.core.IdemLaws
import ops.community.Community
import ops.connection.All
import engine.renderer.Geometry
import engine.renderer.Cover
import engine.renderer.ImageLaws
import engine.renderer.LiveLaws
import engine.renderer.SheetGeom
import ops.community.link.View
import engine.renderer.Camera
import ops.app.Switch
import engine.renderer.Nav
import ops.app.NavLaws
import engine.renderer.TextLaws
import engine.renderer.WrapLaws
import engine.renderer.Label
import ops.community.reaction.RowLaws
import ops.community.message.ViewLaws
import ops.community.profile.NamesakeLaws
import ops.community.message.Order
import ops.app.PeopleLaws
import ops.app.Remove
import ops.community.membership.RemovedLaws
import App
import engine.renderer.Ttf.Laws
import engine.renderer.Ttf.Cache
import ops.community.attachment.ArrivalLaws
import engine.renderer.qr.Qr
import engine.renderer.pic.Pic
import engine.wire.mdns.Mdns
import ops.connection.bootstrap.Net
import engine.core.WindowRead
import engine.core.WindowCost
import engine.core.WindowMutants
import engine.renderer.Screen
import engine.core.CodecCost
import ops.community.MerkleCost
import ops.app.Pics
import engine.core.IngestCost
import engine.core.ListCost
import engine.renderer.BoardLaws
import engine.renderer.Heights
import ops.community.WrapLaws
import engine.renderer.ReaderLaws
import engine.core.CostErase
import engine.renderer.ActsLaws
import engine.core.Project
import ops.connection.NodeLaws

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
#print axioms Engine.Codec.encode_eq_fast
#print axioms Engine.Codec.decode_eq_fast
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
#print axioms Engine.run_ingest
#print axioms Engine.CostT.erase_run
#print axioms Engine.CostT.erase_pure
#print axioms Engine.CostT.erase_bind
#print axioms Engine.CostT.erase_charged
#print axioms Engine.CostT.erase_chargedBy
#print axioms Engine.CostT.erase_lift
#print axioms Engine.CostT.erase_tick
#print axioms Engine.Counted.val_erase
#print axioms Engine.Counted.cost_run
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
#print axioms Engine.Sync.offer_shared
#print axioms Engine.Sync.offer_stored
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
#print axioms Engine.sortPos_eq_fast
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
#print axioms Engine.mem_union
#print axioms Engine.mem_union_all
#print axioms Community.readable_held
#print axioms Community.readable_complete
#print axioms Engine.Pos.cmp_eq_iff
#print axioms Engine.Pos.cmp_swap
#print axioms Engine.Pos.cmp_lt_trans
#print axioms Engine.sortPos_sorted
#print axioms Engine.top_max
#print axioms Community.received_of_message
#print axioms Community.lexCmp_be64
#print axioms Community.msg_cmp
#print axioms Community.time_is_display
#print axioms Community.order_total
#print axioms Community.topCount_ge
#print axioms Community.receipt_once
#print axioms Community.arrival_order
#print axioms Community.send_after
#print axioms Community.order_local
#print axioms Community.display_agrees
#print axioms Community.Merkle.encode_verify
#print axioms Community.Merkle.verify_sound
#print axioms Community.Merkle.index_bound
#print axioms Community.Merkle.complete_assembles
#print axioms Community.Merkle.assemble_slices
#print axioms Community.Merkle.climb_path
#print axioms Community.Merkle.climb_sub
#print axioms Community.Merkle.no_injective_hash
#print axioms Community.Merkle.assumptions_hold
#print axioms Community.Merkle.fileRoot_eq_fast
#print axioms Community.Merkle.proof_eq_fast
#print axioms Community.Merkle.rootAndProofs_eq_fast
#print axioms Community.op_of_valid
#print axioms Community.chunk_id
#print axioms Community.chunk_unique
#print axioms Community.nodup_full
#print axioms Community.progress_exact
#print axioms Community.progress_le
#print axioms Community.progress_full
#print axioms Community.progress_done
#print axioms Community.attach_chunks
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
#print axioms Engine.Op.decode_exact
#print axioms Engine.Op.decode_parts
#print axioms Engine.Codec.decode_sum
#print axioms Engine.Sync.frames_kept
#print axioms Engine.Sync.frames_tooBig
#print axioms Engine.Sync.frames_size
#print axioms Engine.Sync.frames_frame
#print axioms Engine.Sync.buffer_bounded
#print axioms Engine.Sync.onFrame_sealed
#print axioms Engine.Sync.onSealed_none
#print axioms Engine.Sync.sealed_unopened
#print axioms Connection.openFrame_reads
#print axioms Connection.openFrame_auth
#print axioms Connection.sealed_auth
#print axioms Engine.Sync.boot_cached
#print axioms Engine.Sync.write_cached
#print axioms Engine.Sync.purge_cached
#print axioms Engine.Sync.cached_items
#print axioms Engine.Sync.cached_shown
#print axioms Engine.Sync.start_keeps
#print axioms Engine.Sync.onRbsr_keeps
#print axioms Engine.Sync.walk_keeps
#print axioms Engine.Sync.onHold_keeps
#print axioms Engine.Sync.onWant_keeps
#print axioms Engine.Sync.filed_keeps
#print axioms Engine.Sync.recv_keeps
#print axioms Engine.Sync.tick_keeps
#print axioms Engine.Sync.open_keeps
#print axioms Engine.Sync.setRooms_snaps
#print axioms Engine.Sync.write_snaps
#print axioms Engine.Sync.have_shown
#print axioms Engine.Sync.holdsOf_hold
#print axioms Engine.Sync.holdsIn_apply
#print axioms Engine.Sync.heldIn_local
#print axioms Engine.Sync.onHold_local
#print axioms Engine.Sync.hold_reply_local
#print axioms Engine.Sync.heldIn_index
#print axioms Engine.Sync.have_shown_premises
#print axioms Engine.Sync.hold_reply_local_premises
#print axioms Engine.Sync.stream_delivers
#print axioms Engine.Sync.stream_delivers_steps
#print axioms Engine.Sync.stream_delivers_runs
#print axioms Engine.Sync.write_offers
#print axioms Engine.Sync.hold_wants
#print axioms Engine.Sync.want_sends
#print axioms Engine.Sync.op_taken
#print axioms Engine.Sync.stream_offered
#print axioms Engine.Sync.stream_offered_runs
#print axioms Engine.Sync.write_offers_all
#print axioms Engine.Sync.filed_offers
#print axioms Engine.Sync.fanout_offers
#print axioms Engine.Sync.seal_mem
#print axioms Engine.Sync.conn_answers_ids
#print axioms Engine.Sync.uncarried_room_answered
#print axioms Engine.Sync.start_bounded
#print axioms Engine.Sync.round_bounded
#print axioms Engine.Sync.hold_bounded
#print axioms Engine.Sync.onWant_bounded
#print axioms Engine.Sync.walkN_bounded
#print axioms Engine.Sync.tick_bounded
#print axioms Engine.Sync.recv_bounded
#print axioms Engine.Sync.filed_bounded
#print axioms Engine.Sync.conn_bounded
#print axioms Engine.Sync.Read.run_held
#print axioms Engine.Sync.Read.run_model
#print axioms Engine.Sync.serve_reads
#print axioms Engine.Sync.serve_shown
#print axioms Engine.Sync.serve_blind
#print axioms Engine.Sync.serve_budget
#print axioms Engine.Sync.authorize_mem
#print axioms Engine.Sync.endSession_purges
#print axioms Engine.Sync.close_gone
#print axioms Engine.Sync.close_purges
#print axioms Engine.Sync.admit_bounded
#print axioms Engine.Sync.Read.trace_map
#print axioms Engine.Sync.expire_bounded
#print axioms Engine.Sync.remember_bounded
#print axioms Engine.Sync.remember_fits
#print axioms Engine.Sync.known_forgets
#print axioms Engine.Sync.round_no_drop
#print axioms Engine.Sync.hold_no_drop
#print axioms Engine.Sync.want_no_drop
#print axioms Engine.Sync.recv_no_drop
#print axioms Engine.Sync.honest_no_drop
#print axioms Engine.Sync.honest_no_drop_runs
#print axioms Engine.Sync.asks_expire
#print axioms Engine.Sync.write_first
#print axioms Engine.Sync.write_within
#print axioms Engine.Sync.frame_next
#print axioms Engine.Sync.urgent_ahead
#print axioms Engine.Sync.ahead_bytes
#print axioms Engine.Sync.take_append
#print axioms Engine.Sync.cut_bytes
#print axioms Engine.Sync.cut_progress
#print axioms Engine.Sync.push_capped
#print axioms Engine.Sync.push_over
#print axioms Engine.Sync.take_bytes
#print axioms Engine.Sync.lanes_bounded
#print axioms Engine.Sync.room_window
#print axioms Engine.Sync.stall_closes
#print axioms Engine.Sync.shut_live
#print axioms Engine.Sync.framesFor_mem
#print axioms Engine.Sync.framesFor_only
#print axioms Engine.Sync.lane_control
#print axioms Engine.Sync.heat_hot
#print axioms Engine.Sync.write_hot
#print axioms Engine.Sync.serve_rest
#print axioms Engine.Sync.serve_head
#print axioms Engine.Sync.serve_shrinks
#print axioms Engine.Sync.fetch_all
#print axioms Engine.Sync.fetch_shown
#print axioms Engine.Sync.fetch_blind
#print axioms Engine.Sync.onWant_authorized
#print axioms Engine.Sync.onWant_all
#print axioms Engine.Sync.onWant_order
#print axioms Engine.Sync.onWant_bounded_owed
#print axioms Engine.Sync.serveOwed_hot
#print axioms Engine.Sync.serveOwed_head
#print axioms Engine.Sync.serveOwed_fifo
#print axioms Engine.Sync.serveOwed_shrinks
#print axioms Engine.Sync.owed_drains
#print axioms Engine.Sync.owed_within
#print axioms Engine.Sync.serveOwed_budget
#print axioms Engine.Sync.serveOwed_shown
#print axioms Engine.Sync.serveOwed_blind
#print axioms Engine.Sync.serveOwed_bounded
#print axioms Engine.Sync.serveOwed_send
#print axioms Engine.Sync.hot_ids
#print axioms Engine.Sync.fresh_served
#print axioms Engine.Sync.serveOwed_world
#print axioms Engine.Sync.split_urgent
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
#print axioms Cover.covered
#print axioms Composer.chips_apart
#print axioms Composer.x_clear
#print axioms Composer.chips_fit
#print axioms SheetGeom.itemAt_place
#print axioms SheetGeom.lineOf_ctop
#print axioms NodeOffer.offer_split
#print axioms NodeOffer.offer_runs
#print axioms Engine.ingestS_known
#print axioms Engine.ingestS_twice
#print axioms Engine.ingest_twice
#print axioms Engine.run_ingestEach
#print axioms Engine.ingestAll_again
#print axioms Image.decode_sized
#print axioms LiveLaws.agrees_empty
#print axioms LiveLaws.answer_agrees
#print axioms LiveLaws.agrees_store
#print axioms LiveLaws.agrees_notice
#print axioms LiveLaws.agrees_keep
#print axioms LiveLaws.read_one_moment
#print axioms LiveLaws.watched_held
#print axioms LiveLaws.agrees_unmount
#print axioms Cover.line_painted
#print axioms Cover.painted_no_hold
#print axioms Geometry.pinned_visible
#print axioms Geometry.pinned_tap
#print axioms Link.hints_fit
#print axioms Link.qr_fits
#print axioms Camera.src_in
#print axioms Switch.dedupe_nodup
#print axioms Switch.select_tapped
#print axioms Switch.select_tapped_dedupe
#print axioms Nav.back_go
#print axioms Nav.back_root
#print axioms Nav.back_reset
#print axioms Nav.go_page
#print axioms Nav.go_inv
#print axioms Nav.back_inv
#print axioms Nav.reset_inv
#print axioms Nav.swap_inv
#print axioms Nav.depth
#print axioms NavLaws.back_open
#print axioms NavLaws.back_root
#print axioms NavLaws.back_switch
#print axioms NavLaws.draft_open
#print axioms NavLaws.draft_back
#print axioms NavLaws.inv_open
#print axioms NavLaws.inv_back
#print axioms NavLaws.inv_switch
#print axioms NavLaws.depth
#print axioms App.drawPage_key
#print axioms App.pageIn_acc
#print axioms App.into_target
#print axioms App.into_native
#print axioms Pages.switcherOrder_sound
#print axioms Pages.switcherOrder_complete
#print axioms Switch.dedupe_one_per_community
#print axioms Kinds.Accepted.read_known
#print axioms Text.visual_perm
#print axioms Text.place_shows
#print axioms Text.oneLine_prefix
#print axioms Text.numbers_keep_order
#print axioms Text.arabic_numbers_keep_order
#print axioms Text.numbers_witness
#print axioms Text.arabic_numbers_witness
#print axioms Text.wrap_keeps
#print axioms Text.wrap_fits
#print axioms Text.place_starts
#print axioms RowLaws.picBox_aspect
#print axioms RowLaws.tally_nodup
#print axioms RowLaws.tally_mem
#print axioms RowLaws.time_shown
#print axioms RowLaws.name_placed
#print axioms RowLaws.flush_shows
#print axioms RowLaws.flush_start
#print axioms RowLaws.name_starts
#print axioms Composer.caret_clear
#print axioms ViewLaws.profile_read
#print axioms ViewLaws.others_iff
#print axioms ViewLaws.namesake_iff
#print axioms ViewLaws.row_marked
#print axioms RowLaws.twin_shown
#print axioms RowLaws.twin_before_time
#print axioms RowLaws.hit_twin
#print axioms ViewLaws.message_read
#print axioms PeopleLaws.present_iff
#print axioms PeopleLaws.present_nodup
#print axioms Reader.Want.withView_ofFrame
#print axioms Reader.Want.withViewLast_moves
#print axioms Live.acts_force
#print axioms Live.rest_ignores_acts
#print axioms Live.mem_pickActs
#print axioms Live.RWorld.passActs_picks
#print axioms Live.RWorld.passActs_nil
#print axioms Live.RWorld.inv_passActs
#print axioms Live.RWorld.idxok_passActs
#print axioms Live.RWorld.acts_shown
#print axioms Live.AWorld.passActs_comp
#print axioms Live.AWorld.passActs_indep
#print axioms Live.AWorld.passActs_acts
#print axioms Live.AWorld.type_only
#print axioms Live.Eager.acts_fresh
#print axioms Live.Eager.late_stale
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
#print axioms Community.deviceLive_iff
#print axioms Community.unremoved_iff
#print axioms Community.cut_not_live
#print axioms Community.nodeKeyOr_local
#print axioms Community.endpoint_signed
#print axioms Community.cut_stays
#print axioms Community.cut_consented
#print axioms Community.endpoint_derives
#print axioms Community.new_device_trusted
#print axioms Community.removals_at
#print axioms Community.mine_not_removed
#print axioms Community.rejoin_fresh
#print axioms Community.join_new_device
#print axioms Community.removed_stays_removed
#print axioms Connection.opened_endpoint
#print axioms Connection.established_endpoint
#print axioms Connection.meV_node
#print axioms Connection.room_connOp
#print axioms Connection.bare_takes_only_join
#print axioms Connection.answer_trusted
#print axioms Connection.resend_trusted
#print axioms PeopleLaws.present_not_removed

#print axioms Connection.eval_roomFor
#print axioms Connection.mem_roomsV
#print axioms Connection.rooms_removed
#print axioms Connection.rooms_complete
#print axioms Connection.roomsV_nil
#print axioms Connection.notice_then_cut
#print axioms Connection.requestOf_state
#print axioms Connection.dialOne_sends
#print axioms Connection.dialOne_state
#print axioms Connection.rejoin_dials
#print axioms Connection.reconnect_dials

#print axioms Engine.Sync.closureOps_sound
#print axioms Engine.Sync.closureOps_complete
#print axioms Engine.Sync.closure
#print axioms Engine.Sync.give_send
#print axioms Engine.Sync.give_gives
#print axioms Engine.Sync.give_quiet
#print axioms Engine.Sync.filed_given
#print axioms Engine.Sync.tick_given
#print axioms Engine.Sync.tick_drop
#print axioms Engine.Sync.notice_no_holds
#print axioms Engine.Sync.notice_sent
#print axioms Engine.Sync.notice_send
#print axioms Engine.Sync.notice_once
#print axioms Engine.Sync.filedGive_reads
#print axioms Engine.Sync.filedGive_quiet
#print axioms Connection.removed_gets_only_notice
#print axioms Engine.Sync.notify_bounded

section windows
open Engine
#print axioms Engine.run_exact
#print axioms Engine.fact_stable
#print axioms Engine.window_ne_iff
#print axioms Engine.window_ne_iff_flips
#print axioms Engine.oneOpPerId_of
#print axioms Engine.notice_iff
#print axioms Engine.rank_spec
#print axioms Engine.find_build
#print axioms Engine.Subs.find_iff
#print axioms Engine.Subs.mem_notifyM
#print axioms Engine.Subs.has_ofList
#print axioms Engine.Subs.has_add
#print axioms Engine.Subs.has_keep
#print axioms Engine.Subs.add_wf
#print axioms Engine.Subs.keep_wf
#print axioms Engine.Subs.ofList_wf
#print axioms Engine.mem_net
#print axioms Engine.read_rows_iff
#print axioms Engine.read_notice_iff
#print axioms Engine.watch_stable
#print axioms Engine.window_rows
#print axioms Engine.rank_costs
#print axioms Engine.find_costs
#print axioms Engine.notify_cost
#print axioms Engine.Mutants.key_notice_imprecise
#print axioms Engine.Mutants.exact_silent
#print axioms Engine.Mutants.unnetted_imprecise
#print axioms Screen.screen_subs
#print axioms Screen.hull_near
#print axioms Screen.past_hull_le
#print axioms Screen.screen_index
#print axioms Screen.keep_scrolled_off
end windows

#print axioms Engine.Sync.conn_state_bounded
#print axioms Engine.Sync.full_round_stateless
#print axioms Engine.Sync.closure_capped
#print axioms Engine.Sync.closure_complete_under_cap
#print axioms Engine.Sync.full_round_runs
#print axioms Engine.Sync.closure_under_cap_runs

section cost
-- Budgets over the code that runs (docs/PERF.md), and the negative
-- controls they catch.
#print axioms Community.Merkle.val_rootAndProofsM
#print axioms Community.Merkle.rootAndProofs_hashes
#print axioms Community.Merkle.rootAndProofs_hashes_lt
#print axioms Community.Merkle.rootAndProofs_hashed
#print axioms Community.Merkle.rootAndProofs_hashed_lt
#print axioms Community.Merkle.val_rootAndProofsSlowM
#print axioms Community.Merkle.slow_hashes
#print axioms Community.Merkle.slow_over_budget
#print axioms Engine.Codec.val_decNatFromM
#print axioms Engine.Codec.work_digitsM
#print axioms Engine.Codec.work_decNatFromM
#print axioms Engine.Codec.val_decBytesFromM
#print axioms Engine.Codec.work_decBytesFromM
#print axioms Engine.Codec.cost_decBytesFromM_at
#print axioms Engine.Codec.val_digitsSlowM
#print axioms Engine.Codec.work_digitsSlowM
#print axioms Engine.Codec.slow_digits_over_budget
#print axioms Engine.Codec.readAllM_eq
#print axioms Engine.Codec.slow_bytes_over_budget
#print axioms Pics.decoded_started
#print axioms Pics.image_steady
#print axioms Pics.image_settles
#print axioms Pics.image_twice
#print axioms Pics.steady_later
#print axioms Pics.imageV_over_budget
#print axioms Engine.within_bind
#print axioms Engine.within_bindP
#print axioms Engine.Costs.time
#print axioms Engine.Costs.mono
#print axioms Engine.costs_bind
#print axioms Engine.costs_bindP
#print axioms Engine.ingest_costs
#print axioms Engine.statuses_costs
#print axioms Engine.waitOn_costs
#print axioms Engine.decide_costs
#print axioms Engine.step_costs
#print axioms Engine.list_costs
#print axioms Engine.model_fits
#print axioms Engine.View.view_lists
#print axioms Live.Board.put_same
#print axioms Live.Board.put_moves
#print axioms Live.Board.ver_ident
#print axioms Live.Board.Step.fresh
#print axioms Live.Board.seen_put
#print axioms Live.Board.seen_take
#print axioms Live.Board.seen_keep
#print axioms Live.World.inv_commit
#print axioms Live.RWorld.inv_commit
#print axioms Live.RWorld.inv_pass
#print axioms Live.RWorld.inv_frame
#print axioms Live.RWorld.inv_evict
#print axioms Live.RWorld.settle
#print axioms Live.Eager.w1_inv
#print axioms Live.Eager.eager_stale
#print axioms Live.Eager.marked_fresh
#print axioms Live.World.inv_pass
#print axioms Live.World.inv_frame
#print axioms Live.World.settle
#print axioms Live.World.marked_pass
#print axioms Live.World.settle_passes
#print axioms Live.Gated.gated_stale
#print axioms Live.Gated.ungated_fresh
#print axioms Live.World.fold_commits
#print axioms Live.World.acts_shown
#print axioms Live.World.passActs_acts
#print axioms Live.World.passActs_comp
#print axioms Live.World.passActs_indep
#print axioms Live.World.type_only
#print axioms Heights.T.start_eq
#print axioms Heights.T.find_spec
#print axioms Heights.T.set_toList
#print axioms Heights.Rows.push_ok
#print axioms Heights.T.findM_cost
#print axioms Heights.T.startM_cost
#print axioms Heights.T.setM_cost
#print axioms Heights.rows_cost
#print axioms Heights.T.start_mono
#print axioms Heights.T.start_size
#print axioms Heights.T.below_window
#print axioms Heights.T.above_window
#print axioms Heights.Both.rowAt_spec
#print axioms Heights.le_pow_clog
#print axioms Heights.clog_least
#print axioms Heights.T.build_ok
#print axioms Heights.T.buildM_cost
#print axioms Heights.rebuild_ok
#print axioms Heights.rebuild_cost
#print axioms Heights.window_rows
#print axioms Heights.anchor_stable
#print axioms Engine.View.always_eval
#print axioms Engine.View.always_run
#print axioms Community.approveReq_ops
#print axioms Community.wrapAll_over
end cost

-- Paragraph bidi: the running passes and block reordering.
#print axioms Text.Bidi.w1_keeps
#print axioms Text.Bidi.w23_keeps
#print axioms Text.Bidi.w4_keeps
#print axioms Text.Bidi.et_keeps
#print axioms Text.Bidi.weak_keeps
#print axioms Text.Bidi.runs_keeps
#print axioms Text.Bidi.attach_keeps
#print axioms Text.Bidi.reset_keeps
#print axioms Text.Bidi.leveled_keeps
#print axioms Text.Bidi.reverseRuns_perm
#print axioms Text.Bidi.reorder_perm
#print axioms Text.Bidi.display_perm
#print axioms Text.Bidi.run_contiguous

-- The Community laws in the running node (sum_project).
#print axioms Engine.leftOps_eq_some
#print axioms Engine.leftOps_isSome
#print axioms Engine.specVerdict_eq_some
#print axioms Engine.specAt_valid_inv
#print axioms Engine.All2.of_map
#print axioms Engine.All2.to_map
#print axioms Engine.lefts_some
#print axioms Engine.specAt_inl
#print axioms Engine.specAt_left
#print axioms Engine.spec_sum_left
#print axioms Engine.proj_ops
#print axioms Engine.proj_status
#print axioms Engine.mem_proj_idx
#print axioms Engine.proj_inv
#print axioms Engine.proj_unique
#print axioms Engine.View.Reads.bind
#print axioms Engine.View.Reads.read
#print axioms Engine.View.Reads.mono
#print axioms Engine.leftKey_of
#print axioms Engine.Rel.key_names
#print axioms Engine.leftKey_rel
#print axioms Engine.leftKey_rels
#print axioms Engine.insertBy_map
#print axioms Engine.sortPos_map
#print axioms Engine.matching_proj
#print axioms Engine.eval_proj
#print axioms Engine.filterMap_inlRow
#print axioms Engine.view_proj
#print axioms Engine.sum_project
#print axioms Community.reads_unremoved
#print axioms Community.reads_deviceLive
#print axioms Community.reads_live
#print axioms Community.reads_allowPeer
#print axioms Community.reads_members
#print axioms Community.reads_recipients
#print axioms Connection.rels_apart
#print axioms Connection.sum_project_node
#print axioms Connection.community_inv
#print axioms Connection.view_node
#print axioms Connection.admitted_node
#print axioms Connection.removed_node
#print axioms Connection.connect_iff_node
#print axioms Connection.refuse_nonmember_node
#print axioms Connection.removal_cuts_off_node
#print axioms Connection.members_iff_node
#print axioms Connection.recipients_iff_node
#print axioms Connection.rooms_cut_node
#print axioms Connection.node_settles

-- Lifecycle: leases, unmount, restore and resize.
#print axioms Lifecycle.unmounted_quiet
#print axioms Lifecycle.old_quiet
#print axioms Lifecycle.subscriptions_exact
#print axioms Lifecycle.resize_anchor
#print axioms Lifecycle.follow_away
#print axioms Lifecycle.restore_checkpoint
#print axioms Lifecycle.mounted_runs
#print axioms App.page_round
#print axioms LifecycleLaws.unmount_read
#print axioms LifecycleLaws.unmount_write
#print axioms LifecycleLaws.old_callback
#print axioms LifecycleLaws.restore_page_anchor
#print axioms LifecycleLaws.viewport_geometry
#print axioms LifecycleLaws.viewport_possible
#print axioms LifecycleLaws.apply_page_anchor
#print axioms Lifecycle.live_exact

-- Noto reader, raster and bounded cache.
#print axioms Ttf.byte_in_bounds
#print axioms Ttf.cmap_entry
#print axioms Ttf.lookup_singleton
#print axioms Ttf.cmap12_glyph
#print axioms Ttf.cmap4_delta
#print axioms Ttf.cmap4_array
#print axioms Ttf.coverage_value
#print axioms Ttf.coverage_bound
#print axioms Ttf.checked_valid
#print axioms Ttf.raster_valid
#print axioms Ttf.ink_witness
#print axioms Ttf.raster_pixel
#print axioms Ttf.Cache.empty_valid
#print axioms Ttf.Cache.checked_valid
#print axioms Ttf.Cache.put_bound
#print axioms Ttf.Cache.payload_le_bytes
#print axioms Ttf.Cache.put_payload_bound

#print axioms Surface.row_place
#print axioms Surface.row_pinned
#print axioms Surface.placed_row
#print axioms Surface.pinned_row
#print axioms Surface.pinned_visible
#print axioms Surface.newest_drawn
#print axioms Surface.offset_bounds
#print axioms Input.moved_not_tap
#print axioms Input.release_tap
#print axioms Input.sample_remembers
#print axioms Input.release_moved
#print axioms Input.first_pointer
#print axioms Input.extra_down
#print axioms Input.deterministic
#print axioms Input.step_offset
#print axioms Input.sequence_offset
#print axioms Input.tap_content
#print axioms Input.tap_page
#print axioms Input.tap_key
#print axioms Input.classified_at_down
#print axioms Input.witnesses
#print axioms Surface.crop_row
#print axioms Surface.composer_top
#print axioms Surface.visible_in_viewport
#print axioms Input.other_pointer
#print axioms Input.release_event
#print axioms Input.classified_page
#print axioms Input.classified_key
#print axioms Surface.published_row
#print axioms Surface.published_composer
#print axioms Input.delivered_page
#print axioms Translate.equivariance
#print axioms Translate.pinned
#print axioms Translate.source_iff
#print axioms Translate.copied_row
#print axioms Translate.fill_covers
#print axioms Translate.fill_index
#print axioms Translate.tile_phase
#print axioms Translate.source_content
#print axioms Translate.outside
#print axioms Translate.covered
#print axioms Translate.line_painted
#print axioms Translate.edge_list
#print axioms Translate.edge_fill
#print axioms Translate.pick_source
#print axioms Translate.hold_row
#print axioms Translate.fill_pixel
#print axioms Translate.delta_value
#print axioms Translate.tap_content
#print axioms Translate.witnesses
#print axioms Slide.edge_eq
#print axioms Slide.delta_eq
#print axioms Slide.pick_eq
#print axioms Slide.fillRow_eq

#print axioms Input.revoked_release

#print axioms Theme.follows
#print axioms Theme.forced
#print axioms Theme.roundtrip
#print axioms Appearance.selected_label
#print axioms Contrast.channel_bounds
#print axioms Contrast.ink_meets
#print axioms Contrast.ink_control
#print axioms Contrast.ink_kept
#print axioms Contrast.possible
#print axioms Scrim.legible
#print axioms Overlay.edge_contrast
#print axioms Cue.nonempty
#print axioms Cue.same
#print axioms ThemeLaws.cleared
#print axioms ThemeLaws.palette
#print axioms ThemeLaws.content
#print axioms ThemeLaws.text
#print axioms Label.copy_exact
#print axioms Label.line_reachable
#print axioms Safe.content_inside
#print axioms Safe.inside_disjoint
#print axioms Safe.target_safe
#print axioms Safe.target_witness
#print axioms SafeFrame.band_colour
#print axioms Occlusion.placed_table
#print axioms Occlusion.placed_safe
#print axioms Occlusion.modal_inert
#print axioms Toast.placed_safe
#print axioms Toast.placed_view
#print axioms Toast.placed_size
#print axioms Toast.expired
#print axioms Toast.dismissed
#print axioms Toast.raised_visible
#print axioms Toast.placed_witness
#print axioms App.screenChanged_size
#print axioms App.screenChanged_insets
#print axioms SafeFrame.target_minimum

#print axioms Engine.Sync.drop_iff_silent
#print axioms Engine.Sync.keepalive_sent
#print axioms Engine.Sync.live_stays
#print axioms Engine.Sync.keepalive_runs
#print axioms Engine.Sync.unshown_room_answered
#print axioms Engine.Sync.room_independent
#print axioms Engine.Sync.handlers_transition
#print axioms Engine.Sync.closed_terminal
#print axioms Engine.Sync.open_session
#print axioms Engine.Sync.session_runs

#print axioms Engine.Sync.purges_notified
#print axioms Engine.Sync.flush_notifies
#print axioms Engine.Sync.Step.pulse_conn
#print axioms Engine.Sync.Step.pulse_take
#print axioms Engine.Sync.Step.pulse_drop
#print axioms Engine.Sync.work_no_drop
#print axioms Engine.Sync.tick_sends_or_recent
#print axioms Engine.Sync.peer_keeps_live
#print axioms Engine.Sync.start_session
#print axioms Engine.Sync.round_session
#print axioms Engine.Sync.hold_session
#print axioms Engine.Sync.want_session
#print axioms Engine.Sync.walk_session
#print axioms Engine.Sync.work_session
#print axioms Engine.Sync.filed_session
#print axioms Engine.Sync.recv_transition
#print axioms Engine.Sync.work_send
#print axioms Engine.Sync.secrecy_runs
#print axioms Engine.Sync.live_runs
#print axioms Engine.Sync.Session.hello_allowed
#print axioms Engine.Sync.Session.closed_terminal
#print axioms Engine.Sync.filed_origin
#print axioms Engine.Sync.holdsOf_shown
#print axioms Engine.Sync.work_retry_bounded
#print axioms Engine.Sync.work_keeps
#print axioms Engine.Sync.inserts_size
#print axioms Engine.Sync.remembers_bounded
#print axioms Engine.Sync.seal_single

#print axioms Engine.Sync.admitAsks_bounded
#print axioms Engine.Sync.hello_answered

#print axioms Engine.Sync.give_shape
#print axioms Engine.Sync.filedGive_no_drop
#print axioms Engine.Sync.tickGive_drop
#print axioms Engine.Sync.extra_give

#print axioms Engine.Sync.filedGive_reachable
#print axioms Engine.Sync.tickGive_reachable

/-! Compatible read-plan, membership-window and claim-tree ports. -/
#print axioms Engine.Pos.cmp_eq
#print axioms Engine.Pos.cmp_gt_of_le
#print axioms Engine.Pos.cmp_lt_le_trans
#print axioms Engine.Stmt.walks_le
#print axioms Engine.countWith_split
#print axioms Engine.id_bind
#print axioms Engine.inRange_unbounded
#print axioms Engine.listPlan_split
#print axioms Engine.pickMin_le
#print axioms Engine.plan_stmt_cost
#print axioms Engine.readPlan_cost
#print axioms Engine.readPlan_cost_le
#print axioms Engine.readPlan_cost_range
#print axioms Engine.sideCount_run
#print axioms Engine.splitWalk_cost
#print axioms Engine.splitWalk_exact
#print axioms Engine.splitWalk_steps
#print axioms Engine.eval_oriented
#print axioms Engine.eval_pairwise
#print axioms Engine.eval_strict
#print axioms Engine.foldr_insertBy
#print axioms Engine.insertBy_merge
#print axioms Engine.mem_mergeRuns_orient
#print axioms Engine.mem_orient
#print axioms Engine.mergeRuns_eq_sortPos
#print axioms Engine.pairwise_orient_cut
#print axioms Engine.perm_mergeRuns
#print axioms Engine.union_rows
#print axioms Engine.union_sorted
#print axioms Engine.Pos.cmp_succ
#print axioms Engine.bcmp_push_zero
#print axioms Engine.eval_partition
#print axioms Engine.lexCmp_append_zero
#print axioms Community.anchor_read
#print axioms Community.asMsg_sorted
#print axioms Community.count_partition
#print axioms Community.mem_eval_unlimited
#print axioms Community.orient_map
#print axioms Community.orient_orient
#print axioms Community.recKey_inj
#print axioms Community.recMsg_recKey
#print axioms Community.rec_succ
#print axioms Community.sum_map_add
#print axioms PeopleLaws.all_take
#print axioms PeopleLaws.byUser_users
#print axioms PeopleLaws.deviceLive_lists
#print axioms PeopleLaws.live_append
#print axioms PeopleLaws.live_lists_ge
#print axioms PeopleLaws.live_lists_le
#print axioms PeopleLaws.presentCount_complete
#print axioms PeopleLaws.presentW_complete
#print axioms PeopleLaws.presentW_lists
#print axioms PeopleLaws.presentW_lists_eq
#print axioms PeopleLaws.presentW_prefix
#print axioms PeopleLaws.present_lists_eq
#print axioms PeopleLaws.present_scans
#print axioms PeopleLaws.uniq_cons
#print axioms PeopleLaws.uniq_prefix
#print axioms PeopleLaws.unremoved_lists
#print axioms Engine.Sync.Tree.answer_step
#print axioms Engine.Sync.Tree.exchange_ids_stable
#print axioms Engine.Sync.Tree.exchange_log
#print axioms Engine.Sync.Tree.exchange_stable
#print axioms Engine.Sync.Tree.fold_congr
#print axioms Engine.Sync.Tree.pick_keys_gt
#print axioms Engine.Sync.Tree.pieces_le
#print axioms Engine.Sync.Tree.pieces_le_aux
#print axioms Engine.Sync.Tree.runLen_le
