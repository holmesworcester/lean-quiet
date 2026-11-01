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
import app.Proofs
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
import engine.core.Proofs
import engine.core.Purge
import engine.core.Termination
import engine.renderer.ImageLaws
import engine.renderer.TextLaws
import engine.renderer.WrapLaws
import engine.sync.ConnLaws
import engine.sync.SecrecyLaws
import engine.wire.EgressLaws
import engine.wire.NodeLaws
import engine.wire.NoiseSymbolic
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
  Engine.Op.id_decode
  Connection.Noise.Symbolic.kk_secret
  Connection.Noise.Symbolic.kk_authentic
  Engine.same_ops_same_verdicts
  Remove.writes_only_after_two
  NavLaws.back_open
  Text.wrap_keeps

/-! ## Also considered: strong, but left out of the top fifteen -/

#headline
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
  Community.display_agrees
  PeopleLaws.present_iff
  Text.visual_perm
  Image.decode_sized
  Community.chunk_is_slice
  Connection.bare_takes_only_join

/-! ## Not about running code yet: for contrast

`converge` runs the node's code in a World (n nodes, a modelled network,
plain frames, sessions opened by the harness), so tests/Wiring.lean
counts it apart from the wired laws. -/

#headline Engine.World.Plain.converge
