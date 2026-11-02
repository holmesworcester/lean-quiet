/-
The headline laws (docs/HEADLINE.md): for each, its place, its axioms
and its spec surface (tests/SpecSurface.lean's `#headline`). The file
fails if a law uses an axiom other than Lean's standard three (a `sorry`
among them), or no longer exists.

  lake build && lake build +Main && lake build SpecTools
  lake env lean tests/Headline.lean

The proposal, ranked; the user decides which laws are headline laws.
-/
import tests.SpecSurface
import Main
import app.Commands
import app.Proofs
import app.Screen
import app.community.Family
import app.community.Proofs
import app.community.Screen
import app.community.member.Proofs
import app.community.member.invite.Proofs
import app.community.member.remove.Proofs
import app.community.member.remove.View
import app.community.channel.message.Proofs
import app.community.channel.message.attachment.chunk.Proofs
import app.connection.Proofs
import engine.core.Budget
import engine.core.Codec
import engine.core.Core
import engine.core.IdemLaws
import engine.core.IngestCost
import engine.core.ListCost
import engine.core.Proofs
import engine.core.Purge
import engine.core.Termination
import engine.core.View
import engine.core.WindowLaws
import engine.core.WindowRead
import engine.renderer.BoardLaws
import engine.renderer.Cover
import engine.renderer.Demand
import engine.renderer.DemandRank
import engine.renderer.Geometry
import engine.renderer.ImageLaws
import engine.renderer.SheetGeom
import engine.renderer.Surface
import engine.renderer.TextLaws
import engine.renderer.TranslateLaws
import engine.renderer.WrapLaws
import engine.sync.ConnLaws
import engine.sync.SecrecyLaws
import engine.sync.ServeLaws
import engine.wire.EgressLaws
import engine.wire.IngressPriorityLaws
import engine.wire.NodeLaws
import engine.wire.NoiseSymbolic
import engine.wire.PriorityLaws
import engine.world.Plain

/-! ## The recommended headline laws, ranked -/

#headline
  Community.no_impersonation
  Community.admission_needs_approval
  Community.removal_authorized
  Community.removed_stays
  Community.connect_iff
  Connection.removal_reaches_session
  Engine.Sync.recv_send
  Connection.sealed_auth
  Connection.Noise.Symbolic.kk_secret
  Connection.Noise.Symbolic.kk_authentic
  Engine.same_ops_same_verdicts
  Community.display_agrees
  Cover.covered
  NavLaws.back_open
  Switch.select_tapped_dedupe
  Community.approveReq_ops
  Engine.ingest_costs
  PeopleLaws.deviceCut_removal

/-! ## Also considered: about running code, but left out of the top list -/

#headline
  Engine.Op.id_decode
  Remove.writes_only_after_two
  Text.wrap_keeps
  Community.message_authorized
  Community.removal_cuts_off
  Community.valid_stays
  Connection.removed_gets_only_notice
  Engine.Sync.entry_fresh
  Engine.Sync.offer_shared
  Engine.Sync.recv_take
  Engine.Sync.sealed_unopened
  Engine.Codec.encode_decode
  Engine.drain_bounded
  Engine.ingest_twice
  Engine.purge_shared
  Engine.status_iff_spec
  Community.chunk_is_slice
  Connection.bare_takes_only_join
  Community.order_total
  PeopleLaws.present_iff
  ViewLaws.namesake_iff
  Translate.covered
  Cover.line_painted
  Geometry.newest_visible
  Surface.pinned_visible
  Geometry.pinned_tap
  SheetGeom.hit_iff
  Pages.switcherOrder_complete
  Pages.switcherOrder_sound
  Text.visual_perm
  Image.decode_sized
  Engine.notice_iff
  Engine.read_notice_iff
  Engine.view_stable
  Engine.eval_stable
  LiveLaws.read_one_moment
  NodeOffer.offer_split
  Demand.next_visible
  Demand.selected_within
  Engine.window_rows
  Engine.step_costs
  Engine.Sync.owed_within

/-! ## Not about running code yet: for contrast

tests/Wiring.lean counts these apart from the wired laws. `converge`
runs the node's code in a World (a modelled network, plain frames,
sessions the harness opens). `list_costs` is a model: its subject is a
specification of the store's answers (`Fits`). The others this group
once held are about running code since the no-models rule (`row_marked`,
`offer_runs`, the schedulers' `write_within`), or were deleted with the
models they were over (the rows' heights tree, the board's World
passes). -/

#headline
  Engine.World.Plain.converge
  Engine.list_costs
