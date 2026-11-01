import app.Screen
import engine.sync.Ephemeral
import app.nav.View
import app.nav.Commands

/-
Nav's laws over the running app: a change of page writes its nav op into
the app's ephemeral log (`Data.placeIn`), and the log's newest nav op is
exactly that one (`placeIn_newest`). So the frame's page and back stack
are a cache of the log (`withNav_cache`): what `App.St.withNav` sets them
to is what the newest nav op names.
-/

namespace Nav
open Engine Engine.Sync Codec

/-- No relation of Community's, Connection's or the settings' is named `nav`. -/
theorem apart_community : ∀ r ∈ Community.rels, r.kind ≠ "nav" := by decide
theorem apart_connection : ∀ r ∈ Connection.rels, r.kind ≠ "nav" := by decide
theorem apart_settings : ∀ r ∈ Settings.rels, r.kind ≠ "nav" := by decide

theorem not_relKey {G : Type} {rels : List (Rel G)} (hr : ∀ r ∈ rels, r.kind ≠ "nav") (f : G) :
    all.key [] ∉ keysOf rels f := by
  intro hk
  rw [keysOf, List.mem_filterMap] at hk
  obtain ⟨r, hr', he⟩ := hk
  cases ha : r.args f with
  | none => rw [ha] at he; cases he
  | some as =>
    rw [ha] at he
    exact hr r hr' (Rel.key_names (Option.some.inj he)).1

theorem key_ne_opKey (y : Id) : query.key ≠ opKey y := Rel.key_ne_opKey _ (by decide) [] y

section
variable {C : Community.Crypto} {K : Connection.Keys} {s : DB Quiet.F}

/-- **Nav's list holds only nav facts,** in a store of the node's family. -/
theorem query_only (h : Engine.Inv (Quiet.node C K) s) {x : Id} (hx : x ∈ s.idx query.key) :
    ∃ nf, s.status x = some (.valid (.inr (.inr nf))) := by
  have hk : RightKey s query.key := rightKey_of h key_ne_opKey fun f => by
    cases f with
    | inl c => exact not_relKey apart_community c
    | inr x => exact not_relKey apart_connection x
  obtain ⟨g, hg⟩ := hk x hx
  cases g with
  | inr nf => exact ⟨nf, hg⟩
  | inl sf =>
    exfalso
    obtain ⟨f0, hf0, hk⟩ := (h.idx _ x).1 hx
    rw [hg] at hf0; cases hf0
    rcases List.mem_cons.1 hk with e | e
    · exact key_ne_opKey x e
    · exact not_relKey apart_settings sf e
end

theorem place_kind (gen page : Nat) (stack : List Nat) : (place gen page stack).kind = 48 := rfl

end Nav

namespace Data
open Engine Engine.Sync

/-- The ops the log is rebuilt from when this window is placed. -/
def placed (h : Held SF) (gen page : Nat) (stack : List Nat) : List Op :=
  h.log.filter (fun o => !Nav.owns o.kind) ++ [Nav.place gen page stack]

/-- **A change of page is the log's newest nav op.** Once the log is
rebuilt with the nav op for `page` over `stack` (its ops' ids distinct),
this window's place read from it is exactly that op's. -/
theorem placeIn_newest (h : Held SF) (gen page : Nat) (stack : List Nat) (hd : Distinct (placed h gen page stack)) :
    navOf (placeIn h gen page stack) = some ((Nav.place gen page stack).id, ⟨gen, page, stack⟩) := by
  let op := Nav.place gen page stack
  let L := placed h gen page stack
  let H := Held.ofOps fam L
  let nf : Nav.Fact := ⟨gen, page, stack⟩
  have hop : op ∈ L := List.mem_append_right _ (List.mem_singleton.2 rfl)
  have hv : fam.validate op [] = some (.inr (.inr nf)) := by
    have := Quiet.node_nav (C := C) (K := Connection.sodium) (o := op)
      (by show Settings.owns 48 = false; decide) (by show Nav.owns 48 = true; decide) []
    simp only [List.map_nil] at this
    rw [show fam = Quiet.node C Connection.sodium from rfl, this, Nav.place_valid]; rfl
  have hst : H.db.status op.id = some (.valid (.inr (.inr nf))) := ofOps_valid fam hd hop rfl hv
  have hinv := ofOps_inv fam L
  have hx : op.id ∈ H.db.idx Nav.query.key := (hinv.idx _ op.id).2 ⟨_, hst, by
    simp [Family.fileKeys, fam, Quiet.node, Family.sum, Quiet.app, Quiet.appOwns, Settings.owns, Nav.owns,
      Nav.keys, keysOf, Nav.rels, Nav.query, Rel.query, op]⟩
  have hk : RightKey H.db Nav.query.key := fun x hx => by
    obtain ⟨nf', h'⟩ := Nav.query_only hinv hx; exact ⟨_, h'⟩
  obtain ⟨y', g', ht, hy', hg', -⟩ := top_right (lim := some 1) hk (by decide) hx hst
  obtain ⟨nf', hnf'⟩ := Nav.query_only hinv hy'
  rw [hnf'] at hg'
  cases hg'
  -- the op behind y' is in the log and makes a nav fact, so it is op
  obtain ⟨o, fs, ho, hid, hvo⟩ := ofOps_from fam hd hnf'
  have hown := Quiet.node_nav_kind hvo
  have hoeq : o = op := by
    rcases List.mem_append.1 ho with hr | hr
    · have := (List.mem_filter.1 hr).2
      rw [hown] at this; cases this
    · exact List.mem_singleton.1 hr
  subst hoeq
  rw [← hid] at hnf'
  rw [hst] at hnf'
  cases hnf'
  have hq : ({ key := Nav.query.key, limit := some 1 } : ListQ) = Nav.query := rfl
  rw [hq] at ht
  obtain ⟨rest, hrows⟩ : ∃ rest, (Engine.eval H.db Nav.query).rows =
      ((SortKey.sortOf (Sum.inr nf : Quiet.AppFact), op.id), .inr (.inr nf)) :: rest := by
    cases hr : (Engine.eval H.db Nav.query).rows with
    | nil => rw [hr, ← hid] at ht; cases ht
    | cons t rest => rw [hr, ← hid] at ht; cases ht; exact ⟨rest, rfl⟩
  show ((((Nav.current.liftR.liftR : View SF _).run : HeldM SF _).run H).1) = _
  rw [run_eval]
  simp only [Nav.current, View.read, bind, View.bind, View.liftR, View.eval, pure, Answer.rights]
  rw [hrows]
  rfl

end Data

namespace App
open Engine Engine.Sync Data

/-- **The page and back stack are the log's cache** (LAYOUT: a cache
derived from ops, cache = f(ops)). After a change of page, the newest nav
op in the app's ephemeral log names exactly the page and back stack the
frame shows. -/
theorem withNav_cache (s : St) (n : Nav.Nav PageId)
    (hd : Distinct (placed s.eph (s.navGen + 1) n.page.code (n.stack.map PageId.code))) :
    ∃ x f, navOf (s.withNav n).eph = some (x, f) ∧ (s.withNav n).page = PageId.ofCode f.page ∧
      (s.withNav n).backStack = f.stack.map PageId.ofCode := by
  refine ⟨_, _, placeIn_newest s.eph (s.navGen + 1) n.page.code (n.stack.map PageId.code) hd, ?_, ?_⟩
  · exact (page_round n.page).symm
  · show n.stack = (n.stack.map PageId.code).map PageId.ofCode
    rw [List.map_map]
    conv => lhs; rw [← List.map_id n.stack]
    exact List.map_congr_left fun p _ => (page_round p).symm

end App
