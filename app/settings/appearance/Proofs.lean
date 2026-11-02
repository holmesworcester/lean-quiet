import app.Family
import app.settings.appearance.View
import app.settings.appearance.Commands
import engine.core.Left

/-
Appearance's laws over the node's running store (`Quiet.node`, the family
`Data.fam` runs): the preference the app reads (`current`, through
`Data.appearance`) is the newest appearance stored.
-/

namespace Settings
open Engine Codec

namespace Appearance

/-- **A choice stays on this device**: the node never offers it to a
peer, nor takes one from a peer (`Engine.Sync.intake_local`). -/
theorem choose_local {C : Community.Crypto} {K : Connection.Keys} (rev : Nat) (s : Theme.Setting) :
    (Quiet.node C K).scope (Appearance.choose rev s) = .local := by
  simp [Quiet.node, Family.sum, Quiet.app, Quiet.appOwns, Settings.scopeOf, Appearance.choose, Settings.mkOp,
    Settings.Body.kind, Settings.owns]

/-- No relation of Community's, Connection's or Nav's is named `settings.appearance`. -/
theorem apart_community : ∀ r ∈ Community.rels, r.kind ≠ "settings.appearance" := by decide
theorem apart_connection : ∀ r ∈ Connection.rels, r.kind ≠ "settings.appearance" := by decide
theorem apart_nav : ∀ r ∈ Nav.rels, r.kind ≠ "settings.appearance" := by decide

/-- A key of these relations is none of them, if none shares the name. -/
theorem not_relKey {F : Type} {rels : List (Rel F)} (hr : ∀ r ∈ rels, r.kind ≠ "settings.appearance")
    (f : F) : appearance.all.key [] ∉ keysOf rels f := by
  intro hk
  rw [keysOf, List.mem_filterMap] at hk
  obtain ⟨r, hr', he⟩ := hk
  cases ha : r.args f with
  | none => rw [ha] at he; cases he
  | some as =>
    rw [ha] at he
    exact hr r hr' (Rel.key_names (Option.some.inj he)).1

theorem key_ne_opKey (y : Id) : query.key ≠ opKey y := Rel.key_ne_opKey _ (by decide) [] y

/-- The appearance list holds only the app's facts, in the node's store:
no op's own key is its key, nor any of Community's or Connection's. -/
theorem query_right {C : Community.Crypto} {K : Connection.Keys} {s : DB Quiet.F}
    (h : Inv (Quiet.node C K) s) : RightKey s query.key := by
  refine rightKey_of h key_ne_opKey fun f => ?_
  cases f with
  | inl c => exact not_relKey apart_community c
  | inr x => exact not_relKey apart_connection x

/-- **The appearance list holds only appearances,** in the node's store:
nor is it any of Nav's keys. -/
theorem query_only {C : Community.Crypto} {K : Connection.Keys} {s : DB Quiet.F}
    (h : Inv (Quiet.node C K) s) {x : Id} (hx : x ∈ s.idx query.key) :
    ∃ f, s.status x = some (.valid (.inr (.inl (.ofAppearance f)))) := by
  obtain ⟨g, hg⟩ := query_right h x hx
  cases g with
  | inl sf => cases sf with | ofAppearance f => exact ⟨f, hg⟩
  | inr nf =>
    exfalso
    obtain ⟨f0, hf0, hk⟩ := (h.idx _ x).1 hx
    rw [hg] at hf0; cases hf0
    rcases List.mem_cons.1 hk with e | e
    · exact key_ne_opKey x e
    · exact not_relKey apart_nav nf e

/-- **The preference is the newest appearance** (THEME01). In the node's
store, once appearance y is stored, the preference the app reads
(`current`, run by `Data.appearance`) is a stored appearance's: at or
after y in its list's order, by revision and then by id. -/
theorem current_newest {C : Community.Crypto} {K : Connection.Keys} {s : DB Quiet.F}
    (h : Inv (Quiet.node C K) s) {y : Id} {f : Appearance.Fact}
    (hy : s.status y = some (.valid (.inr (.inl (.ofAppearance f))))) :
    ∃ y' f', (current.liftL.liftR : View Quiet.F _).eval s = (f'.setting, f'.rev) ∧
      s.status y' = some (.valid (.inr (.inl (.ofAppearance f')))) ∧
      Pos.cmp (sortKey f, y) (sortKey f', y') ≠ .gt := by
  have hx : y ∈ s.idx query.key := (h.idx _ y).2 ⟨_, hy, by
    simp [Family.fileKeys, Quiet.node, Family.sum, Quiet.app, Quiet.appOwns, Settings.owns, Settings.keys, keysOf,
      Settings.rels, Settings.appearance.all, query, Rel.query, Appearance.all]⟩
  obtain ⟨y', g', ht, hy', hg', hle⟩ := top_right (lim := some 1) (query_right h) (by decide) hx hy
  obtain ⟨f', hf'⟩ := query_only h hy'
  rw [hf'] at hg'
  cases hg'
  refine ⟨y', f', ?_, hf', hle⟩
  have hq : ({ key := query.key, limit := some 1 } : ListQ) = query := rfl
  rw [hq] at ht
  obtain ⟨rest, hrows⟩ : ∃ rest, (Engine.eval s query).rows =
      ((sortKey f', y'), .inr (.inl (.ofAppearance f'))) :: rest := by
    cases hr : (Engine.eval s query).rows with
    | nil => rw [hr] at ht; cases ht
    | cons t rest => rw [hr] at ht; cases ht; exact ⟨rest, rfl⟩
  simp only [current, View.read, bind, View.bind, View.liftL, View.liftR, View.eval, pure]
  rw [Answer.rights, hrows]
  rfl

end Appearance

end Settings
