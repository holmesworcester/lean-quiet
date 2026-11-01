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
  simp [Quiet.node, Family.sum, Quiet.app, Settings.scopeOf, Appearance.choose, Settings.mkOp,
    Settings.Body.kind, Settings.owns]

/-- No relation of Community's or Connection's is named `settings.appearance`. -/
theorem apart_community : ∀ r ∈ Community.rels, r.kind ≠ "settings.appearance" := by decide
theorem apart_connection : ∀ r ∈ Connection.rels, r.kind ≠ "settings.appearance" := by decide

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

/-- **The appearance list holds only appearances,** in the node's store:
no op's own key is its key, nor any of Community's or Connection's. -/
theorem query_right {C : Community.Crypto} {K : Connection.Keys} {s : DB Quiet.F}
    (h : Inv (Quiet.node C K) s) : RightKey s query.key := by
  refine rightKey_of h (fun y => Rel.key_ne_opKey _ (by decide) [] y) fun f => ?_
  cases f with
  | inl c => exact not_relKey apart_community c
  | inr x => exact not_relKey apart_connection x

/-- **The preference is the newest appearance** (THEME01). In the node's
store, once appearance y is stored, the preference the app reads
(`current`, run by `Data.appearance`) is a stored appearance's: at or
after y in its list's order, by revision and then by id. -/
theorem current_newest {C : Community.Crypto} {K : Connection.Keys} {s : DB Quiet.F}
    (h : Inv (Quiet.node C K) s) {y : Id} {f : Appearance.Fact}
    (hy : s.status y = some (.valid (.inr (.ofAppearance f)))) :
    ∃ y' f', (current.liftR : View Quiet.F _).eval s = (f'.setting, f'.rev) ∧
      s.status y' = some (.valid (.inr (.ofAppearance f'))) ∧
      Pos.cmp (sortKey f, y) (sortKey f', y') ≠ .gt := by
  have hx : y ∈ s.idx query.key := (h.idx _ y).2 ⟨_, hy, by
    simp [Family.fileKeys, Quiet.node, Family.sum, Quiet.app, Settings.owns, Settings.keys, keysOf,
      Settings.rels, Settings.appearance.all, query, Rel.query, Appearance.all]⟩
  obtain ⟨y', g', ht, hg', hle⟩ := top_right (lim := some 1) (query_right h) (by decide) hx hy
  cases g' with
  | ofAppearance f' =>
    refine ⟨y', f', ?_, hg', hle⟩
    have hq : ({ key := query.key, limit := some 1 } : ListQ) = query := rfl
    rw [hq] at ht
    obtain ⟨rest, hrows⟩ : ∃ rest, (Engine.eval s query).rows = ((sortKey f', y'), .inr (.ofAppearance f')) :: rest := by
      cases hr : (Engine.eval s query).rows with
      | nil => rw [hr] at ht; cases ht
      | cons t rest => rw [hr] at ht; cases ht; exact ⟨rest, rfl⟩
    show pick (Answer.rights (Engine.eval s query)) = _
    rw [Answer.rights, hrows]
    rfl

end Appearance

end Settings
