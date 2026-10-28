/-
The people list is the community's present members, over the running
code (Kinds.Profile.present, which the people list and its count read):

- `present_iff`: at rest, a user is listed exactly when one of their
  devices is admitted into the community and the user is not removed
  (by the engine's `mem_live_all`): a removed member is in neither the
  list nor the count;
- `present_nodup`: each user is listed once, so the count is the number
  of people, not of devices.
-/
import Quiet.Kinds.Profile
import Quiet.RowLaws

namespace PeopleLaws
open Engine Community Kinds

theorem byUser_mem (ls : List (Id × Key × Key)) (u : Id) :
    u ∈ (Profile.byUser ls).map (·.1) ↔ ∃ d e, (u, d, e) ∈ ls := by
  simp only [Profile.byUser, List.map_map, Function.comp_def, List.map_id']
  rw [RowLaws.uniq_mem]
  simp only [List.mem_map]
  constructor
  · rintro ⟨⟨u', d, e⟩, hm, rfl⟩; exact ⟨d, e, hm⟩
  · rintro ⟨d, e, hm⟩; exact ⟨(u, d, e), hm, rfl⟩

/-- **The people list is exactly the present members.** -/
theorem present_iff {C : Community.Crypto} {s : DB Fact} (h : Inv (family C) s) (hq : s.queue = [])
    (c u : Id) :
    u ∈ ((Profile.present c).eval s).map (·.1) ↔ ∃ d e, Admitted C s.ops c u d e ∧ ¬ Removed C s.ops c u := by
  simp only [Profile.present, View.eval_bind, View.eval_read, View.eval_pure]
  rw [byUser_mem]
  constructor
  · rintro ⟨d, e, hm⟩; exact ⟨d, e, (mem_live_all h hq c u d e).1 hm⟩
  · rintro ⟨d, e, hm⟩; exact ⟨d, e, (mem_live_all h hq c u d e).2 hm⟩

/-- **Each person is listed once.** -/
theorem present_nodup (s : DB Fact) (c : Id) : (((Profile.present c).eval s).map (·.1)).Nodup := by
  simp only [Profile.present, View.eval_bind, View.eval_read, View.eval_pure, Profile.byUser,
    List.map_map, Function.comp_def, List.map_id']
  exact RowLaws.uniq_nodup _

end PeopleLaws
