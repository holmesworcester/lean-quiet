import app.nav.Proofs
import app.settings.appearance.Proofs

/-
Nav's laws, witnessed. The app starts with an empty ephemeral log
(`App.St.eph`), and its log only ever holds nav ops (the one ephemeral op
type so far), so each change of page rebuilds it from exactly one op: the
new nav op. Its ids are then trivially distinct, and the laws apply.
-/

namespace Vacuity.Nav
open Engine Engine.Sync Data

/-- A one-op list's ids are distinct. -/
theorem distinct_one (o : Op) : Distinct [o] := by
  intro a ha b hb _
  rw [List.mem_singleton] at ha hb
  rw [ha, hb]

/-- Placing the window on the empty log rebuilds it from the new op alone. -/
theorem placed_empty (gen page : Nat) (stack : List Nat) :
    placed {} gen page stack = [_root_.Nav.place gen page stack] := rfl

/-- The first change of page, Home (page 0) with nothing under it: the
log's newest nav op is exactly that one. -/
theorem first :
    navOf (placeIn {} 1 0 []) = some ((_root_.Nav.place 1 0 []).id, ⟨1, 0, []⟩) :=
  placeIn_newest {} 1 0 [] (by rw [placed_empty]; exact distinct_one _)

/-- A log holding only nav ops (the app's, before any draft) is rebuilt
from the new nav op alone. -/
theorem placed_navOnly (h : Held SF) (hn : ∀ o ∈ h.log, _root_.Nav.owns o.kind = true) (gen page : Nat)
    (stack : List Nat) : placed h gen page stack = [_root_.Nav.place gen page stack] := by
  unfold placed
  rw [List.filter_eq_nil_iff.2 fun o ho => by simp [hn o ho]]
  rfl

/-- **The cache law's premise holds of a log holding only nav ops.** -/
theorem cache (s : App.St) (n : _root_.Nav.Nav App.PageId) (hn : ∀ o ∈ s.eph.log, _root_.Nav.owns o.kind = true) :
    ∃ x f, navOf (s.withNav n).eph = some (x, f) ∧ (s.withNav n).page = App.PageId.ofCode f.page ∧
      (s.withNav n).backStack = f.stack.map App.PageId.ofCode :=
  App.withNav_cache s n (by rw [placed_navOnly _ hn]; exact distinct_one _)

/-- A nav op is ephemeral in the node's running family. -/
theorem ephemeral : (Quiet.node Data.C Connection.sodium).scope (_root_.Nav.place 1 0 []) = .ephemeral :=
  Quiet.node_nav_ephemeral (by show Settings.owns 48 = false; decide) (by show _root_.Nav.owns 48 = true; decide)

/-- This node's own job of one nav op stores nothing. -/
theorem dropped : intake Data.fam true [_root_.Nav.place 1 0 []] = [] := by
  simp [intake, Family.durable, Data.fam, ephemeral]

/-- A durable op of the app's own: an appearance choice. -/
def opA : Op := Settings.Appearance.choose 1 .dark

theorem keptA : intake Data.fam true [opA] = [opA] := by
  have : Data.fam.scope opA = .local := Settings.Appearance.choose_local 1 .dark
  have hc : opA.capped = true := by
    simp [Op.capped, opA, Settings.Appearance.choose, Settings.mkOp, Op.make, maxReqs]
  simp [intake, Family.durable, this, hc]

theorem inA : opA ∈ intake Data.fam true [opA] := by rw [keptA]; exact List.mem_singleton.2 rfl

/-- What this node's own job keeps is not ephemeral. -/
theorem takenDurable : Data.fam.scope opA ≠ .ephemeral := intake_durable Data.fam inA

/-- The store fed that job holds the choice, which is not ephemeral. -/
theorem storedDurable : Data.fam.scope opA ≠ .ephemeral := by
  have hf := Fed.job (fam := Data.fam) true [opA] Fed.empty
  refine stored_durable hf (x := opA.id) ?_
  rw [keptA]
  simp [ingestS, DB.empty, DB.putOp, DB.push]

end Vacuity.Nav
