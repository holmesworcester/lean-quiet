import engine.core.Left
import engine.wire.HooksLeft
import app.connection.Family
import app.settings.Family
import app.nav.Family

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

/-- The app's own facts: its settings' and its window's place. -/
abbrev AppFact := Settings.Fact ⊕ Nav.Fact

/-- The node's facts: Community's and Connection's, then the app's. -/
abbrev F := Connection.F ⊕ AppFact

/-- Whether the app's families own a kind. -/
def appOwns (k : UInt8) : Bool := Settings.owns k || Nav.owns k

/-- The app's families, on top of the node's: each op cites only its own
family's facts, and is judged by its own family. -/
def app : Family₂ Connection.F AppFact where
  validate o fs := (rights fs).bind fun xs =>
    if Settings.owns o.kind then ((lefts xs).bind (Settings.validate o)).map .inl
    else ((rights xs).bind (Nav.validate o)).map .inr
  keys
    | .inl f => Settings.keys f
    | .inr f => Nav.keys f
  scope o := if Settings.owns o.kind then Settings.scopeOf o else Nav.scopeOf o
  owns := appOwns

/-- **The node's one family**: every op of the app, in one store. -/
def node (C : Community.Crypto) (K : Connection.Keys) : Family F := Family.sum (Connection.node C K) app

theorem rights_map {A B : Type} (fs : List B) : rights (fs.map (.inr : B → A ⊕ B)) = some fs := by
  induction fs with
  | nil => rfl
  | cons a t ih => simp only [rights, List.map_cons, List.mapM_cons] at *; simp [ih]

/-- A settings op's verdict in the node is its family's, given settings facts. -/
theorem node_settings {C : Community.Crypto} {K : Connection.Keys} {o : Op} (h : Settings.owns o.kind = true)
    (fs : List Settings.Fact) :
    (node C K).validate o (fs.map (.inr ∘ .inl)) = (Settings.validate o fs).map (.inr ∘ .inl) := by
  have hr : rights (fs.map (.inr ∘ .inl : Settings.Fact → F)) = some (fs.map .inl) := by
    rw [← List.map_map]; exact rights_map _
  have hl : lefts (fs.map (.inl : Settings.Fact → AppFact)) = some fs := lefts_map fs
  simp only [node, Family.sum, app, appOwns, h, Bool.true_or, ite_true, hr, Option.bind_some, hl]
  cases Settings.validate o fs <;> rfl

/-- A nav op's verdict in the node is its family's, given nav facts. -/
theorem node_nav {C : Community.Crypto} {K : Connection.Keys} {o : Op} (hs : Settings.owns o.kind = false)
    (h : Nav.owns o.kind = true) (fs : List Nav.Fact) :
    (node C K).validate o (fs.map (.inr ∘ .inr)) = (Nav.validate o fs).map (.inr ∘ .inr) := by
  have hr : rights (fs.map (.inr ∘ .inr : Nav.Fact → F)) = some (fs.map .inr) := by
    rw [← List.map_map]; exact rights_map _
  have hn : rights (fs.map (.inr : Nav.Fact → AppFact)) = some fs := rights_map fs
  simp only [node, Family.sum, app, appOwns, h, hs, Bool.or_true, ite_true, Bool.false_eq_true, ite_false, hr,
    Option.bind_some, hn]
  cases Nav.validate o fs <;> rfl

/-- **A nav op is ephemeral** in the node: it lives in the app's
in-memory log only. -/
theorem node_nav_ephemeral {C : Community.Crypto} {K : Connection.Keys} {o : Op}
    (hs : Settings.owns o.kind = false) (h : Nav.owns o.kind = true) :
    (node C K).scope o = .ephemeral := by
  simp [node, Family.sum, app, appOwns, h, hs, Nav.scopeOf]

/-- A nav fact comes only from a nav op: in the node, an op whose
verdict is one of Nav's facts has a kind Nav owns. -/
theorem node_nav_kind {C : Community.Crypto} {K : Connection.Keys} {o : Op} {fs : List F} {nf : Nav.Fact}
    (h : (node C K).validate o fs = some (.inr (.inr nf))) : Nav.owns o.kind = true := by
  unfold node Family.sum at h
  by_cases ha : app.owns o.kind = true
  · simp only [ha, ite_true] at h
    obtain ⟨g, hg, hgeq⟩ := Option.map_eq_some_iff.1 h
    cases hgeq
    obtain ⟨xs, -, hx⟩ := Option.bind_eq_some_iff.1 hg
    by_cases hs : Settings.owns o.kind = true
    · simp only [hs, ite_true] at hx
      obtain ⟨_, _, e⟩ := Option.map_eq_some_iff.1 hx
      cases e
    · have : appOwns o.kind = true := ha
      simp only [appOwns, Bool.or_eq_true] at this
      exact this.resolve_left hs
  · simp only [ha, Bool.false_eq_true, ite_false] at h
    obtain ⟨_, _, hx⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨_, _, e⟩ := Option.map_eq_some_iff.1 hx
    cases e

/-- **The node's ops keep their verdicts**: an op the app's families do
not own is judged as in `Connection.node` alone (`Engine.sum_left`). -/
theorem node_left {C : Community.Crypto} {K : Connection.Keys} {o : Op} (h : appOwns o.kind = false)
    (fs : List Connection.F) :
    (node C K).validate o (fs.map .inl) = ((Connection.node C K).validate o fs).map .inl :=
  sum_left _ app o fs h

end Quiet
