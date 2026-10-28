/-
What a removed person's device shows, over the running code
(Kinds.Accepted.listed, newlyGone, landing; App.forgetEntry), once the
removal is in its store (the engine's last notice delivers it):

- `listed_iff`: a community is listed exactly when this device's entry in
  it is not removed (A1); the entry's data stays in the store;
- `told_once`: a removal is announced once: after its notice, the same
  removal is never new again (A2); and `not_replayed`: a removal already
  in the store at launch is not announced;
- `landing_listed`: the app lands on a listed entry, or on none (Get
  started) (A5);
- `forget_clears`: nothing the app holds names the forgotten entry: no
  invite link of it, no pasted link to its community, and, if it was
  current, no composer text or photos (A4).
-/
import Quiet.App

namespace RemovedLaws
open Kinds.Accepted

/-- **Listed exactly when not removed.** -/
theorem listed_iff (ms : Array Me) (m : Me) : m ∈ listed ms ↔ m ∈ ms ∧ m.removed = false := by
  simp [listed, Array.mem_filter]

theorem any_eq (l : List Engine.Id) (x : Engine.Id) : l.any (fun y => decide (y = x)) = true ↔ x ∈ l := by
  simp [List.any_eq_true]

/-- **Told once.** Once the newly removed entries are added to what has
been told, none of them (and nothing else) is new again. -/
theorem told_once (seen : List Engine.Id) (ms : Array Me) :
    newlyGone ((newlyGone seen ms).map (·.acc) ++ seen) ms = [] := by
  apply List.eq_nil_iff_forall_not_mem.2
  intro m hm
  simp only [newlyGone, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true', any_eq] at hm
  obtain ⟨hmem, hrm, hnot⟩ := hm
  have hin : m ∈ newlyGone seen ms := by
    simp only [newlyGone, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨hmem, hrm, ?_⟩
    cases h : seen.any (fun y => decide (y = m.acc)) with
    | false => rfl
    | true => exact absurd (List.mem_append_right _ ((any_eq seen m.acc).1 h)) (by
        intro h'; rw [Bool.eq_false_iff] at hnot; exact hnot ((any_eq _ _).2 h'))
  have : m.acc ∈ (newlyGone seen ms).map (·.acc) ++ seen := List.mem_append_left _ (List.mem_map_of_mem hin)
  rw [Bool.eq_false_iff] at hnot
  exact hnot ((any_eq _ _).2 this)

/-- **Not replayed.** What was already removed at launch is told. -/
theorem not_replayed (ms : Array Me) :
    newlyGone ((ms.toList.filter (·.removed)).map (·.acc)) ms = [] := by
  apply List.eq_nil_iff_forall_not_mem.2
  intro m hm
  simp only [newlyGone, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true', any_eq] at hm
  obtain ⟨hmem, hrm, hnot⟩ := hm
  rw [Bool.eq_false_iff] at hnot
  exact hnot ((any_eq _ _).2 (List.mem_map_of_mem (List.mem_filter.2 ⟨hmem, hrm⟩)))

/-- **The app lands on a listed entry, or on none.** -/
theorem landing_listed (cs : Array Me) (cur : Engine.Id) (m : Me) (h : landing cs cur = some m) : m ∈ cs := by
  unfold landing select at h
  cases hs : cs.find? (fun m => decide (m.acc = cur)) with
  | some x =>
    rw [hs] at h; simp at h; subst h; exact Array.mem_of_find?_eq_some hs
  | none =>
    rw [hs] at h; simp at h
    exact Array.mem_of_getElem? h

/-- **Nothing is left of the forgotten entry.** -/
theorem forget_clears (s : App.St) (a c : Engine.Id) :
    ((App.forgetEntry s a c).links.all (·.1 != a)) = true ∧
    ((App.forgetEntry s a c).invite.map (·.community == c)) ≠ some true ∧
    (s.me.acc == a → (App.forgetEntry s a c).text = "" ∧ (App.forgetEntry s a c).chips = #[]) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [App.forgetEntry, List.all_filter]
  · simp only [App.forgetEntry]
    split <;> rename_i h
    · simp
    · intro h'; exact h (by rw [h']; rfl)
  · intro h; simp [App.forgetEntry, h]

end RemovedLaws
