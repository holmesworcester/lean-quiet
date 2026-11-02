/-
Which headline laws Comparator can judge under their own names
(docs/HEADLINE.md, "Comparator"): `#challenge_imports` (tests/SpecSurface.lean)
lists, for each, the modules a challenge must import, or the definitions
that block it (they live in the law's module, or in one that imports
it), and the fewest groups whose imports reach none of their own laws:
tests/comparator/solution.py's `OWN` follows them.

  lake env lean tests/comparator/Feasible.lean
-/
import tests.SpecSurface
import app.Proofs
import app.community.Proofs
import app.community.Screen
import app.community.member.Proofs
import app.community.member.invite.Proofs
import app.community.member.remove.Proofs
import app.community.channel.message.Proofs
import app.connection.Proofs
import engine.core.IngestCost
import engine.core.Termination
import engine.renderer.Cover
import engine.sync.ConnLaws
import engine.wire.NoiseSymbolic

/-! ## Each of the eighteen, and the fewest groups of them -/

#challenge_imports
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
