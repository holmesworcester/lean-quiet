import engine.core.Left
import engine.wire.HooksLeft
import app.connection.Family
import app.settings.Family

/-
The node's registry: every family of the app in one store (LAYOUT02).
Community's and Connection's ops (`Connection.node`, app/connection),
and on top the app's own: its settings (app/settings). The app's ops cite
only the app's facts and are all local, so Community's and Connection's
verdicts are unchanged in the composed store (`Engine.sum_left`), their
views answer as on their part (`Engine.sum_project`), and their hooks
read it as their own (`Engine.left_list`, `Engine.Sync.Hooks.left`).

Each stored fact's bytes carry one tag more than before the app's family
joined: the user's call (2026-11-01), no backward compatibility in the
prototype. Ops, their ids and the wire are unchanged.
-/

namespace Quiet
open Engine

/-- The app's own facts. -/
abbrev AppFact := Settings.Fact

/-- The node's facts: Community's and Connection's, then the app's. -/
abbrev F := Connection.F ⊕ AppFact

/-- The app's families, on top of the node's: each op cites only the
app's facts, and is judged by its own family. -/
def app : Family₂ Connection.F AppFact where
  validate o fs := (rights fs).bind (Settings.validate o)
  keys := Settings.keys
  scope := Settings.scopeOf
  owns := Settings.owns

/-- **The node's one family**: every op of the app, in one store. -/
def node (C : Community.Crypto) (K : Connection.Keys) : Family F := Family.sum (Connection.node C K) app

/-- An app op's verdict in the node is its family's, given app facts. -/
theorem node_app {C : Community.Crypto} {K : Connection.Keys} {o : Op} (h : Settings.owns o.kind = true)
    (fs : List AppFact) :
    (node C K).validate o (fs.map .inr) = (Settings.validate o fs).map .inr := by
  have hr : rights (fs.map (.inr : AppFact → Connection.F ⊕ AppFact)) = some fs := by
    induction fs with
    | nil => rfl
    | cons a t ih => simp only [rights, List.map_cons, List.mapM_cons] at *; simp [ih]
  simp [node, Family.sum, app, h, hr]

/-- **The node's ops keep their verdicts**: an op the app's families do
not own is judged as in `Connection.node` alone (`Engine.sum_left`). -/
theorem node_left {C : Community.Crypto} {K : Connection.Keys} {o : Op} (h : Settings.owns o.kind = false)
    (fs : List Connection.F) :
    (node C K).validate o (fs.map .inl) = ((Connection.node C K).validate o fs).map .inl :=
  sum_left _ app o fs h

end Quiet
