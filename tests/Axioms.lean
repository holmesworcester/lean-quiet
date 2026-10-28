import ops.sync.TimeLaws
import ops.sync.RetryLaws
import ops.sync.BoundsLaws
import ops.sync.ServeLaws
import engine.wire.CloseLaws
import engine.wire.Slots
import engine.core.Engine
import ops.community.Community
import ops.connection.All
import engine.renderer.Geometry
import engine.renderer.Cover
import engine.renderer.LiveLaws
import engine.renderer.SheetGeom
import ops.community.link.View
import engine.renderer.Camera
import ops.app.Switch
import engine.renderer.TextLaws
import engine.renderer.WrapLaws
import ops.community.reaction.RowLaws
import ops.community.message.ViewLaws
import ops.community.profile.NamesakeLaws
import ops.community.message.Order
import ops.app.PeopleLaws
import ops.app.Remove
import ops.community.membership.RemovedLaws
import App
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
#print axioms Engine.Sync.tick_drop_iff
#print axioms Engine.Sync.patience_drop_iff
#print axioms Engine.Sync.round_not_dropped
#print axioms Engine.Sync.responder_expires
#print axioms Engine.Sync.live_not_expired
#print axioms Engine.Sync.uncarried_room_answered
#print axioms Engine.Sync.limit_bounded
#print axioms Engine.Sync.finish_bounded
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
#print axioms Engine.Sync.want_reads_authorized
#print axioms Engine.Sync.want_blind
#print axioms Engine.Sync.want_blind_step
#print axioms Engine.Sync.onWant_one
#print axioms Engine.Sync.want_budget
#print axioms Engine.Sync.endSession_purges
#print axioms Engine.Sync.close_gone
#print axioms Engine.Sync.close_purges
#print axioms Engine.Sync.admit_bounded
#print axioms Engine.Sync.Read.trace_map
#print axioms Engine.Sync.Step.limit_send
#print axioms Engine.Sync.Step.limit_take
#print axioms Engine.Sync.Step.limit_rooms
#print axioms Engine.Sync.Step.limit_snaps
#print axioms Engine.Sync.Conn.finish_known
#print axioms Engine.Sync.Conn.finish_asked
#print axioms Engine.Sync.limit_snaps
#print axioms Engine.Sync.keeps_limit
#print axioms Engine.Sync.Step.limit_drop
#print axioms Engine.Sync.expire_bounded
#print axioms Engine.Sync.remember_bounded
#print axioms Engine.Sync.remember_fits
#print axioms Engine.Sync.admit_one
#print axioms Engine.Sync.known_forgets
#print axioms Engine.Sync.asked_full
#print axioms Engine.Sync.round_no_drop
#print axioms Engine.Sync.hold_no_drop
#print axioms Engine.Sync.want_no_drop
#print axioms Engine.Sync.recv_no_drop
#print axioms Engine.Sync.honest_no_drop
#print axioms Engine.Sync.honest_no_drop_runs
#print axioms Engine.Sync.asks_expire
#print axioms Engine.Sync.retried_append
#print axioms Engine.Sync.retried_start
#print axioms Engine.Sync.retried_holds
#print axioms Engine.Sync.retried_chunks
#print axioms Engine.Sync.pieces_short
#print axioms Engine.Sync.retry_bounded
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
#print axioms LiveLaws.agrees_empty
#print axioms LiveLaws.answer_agrees
#print axioms LiveLaws.agrees_store
#print axioms LiveLaws.agrees_notice
#print axioms LiveLaws.agrees_keep
#print axioms LiveLaws.read_one_moment
#print axioms Cover.line_painted
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
#print axioms Kinds.Accepted.read_known
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
#print axioms ViewLaws.others_iff
#print axioms ViewLaws.namesake_iff
#print axioms ViewLaws.row_marked
#print axioms RowLaws.twin_shown
#print axioms RowLaws.twin_before_time
#print axioms RowLaws.hit_twin
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
