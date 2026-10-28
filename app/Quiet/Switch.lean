/-
The community switcher's laws, over the running code (Kinds.Accepted's
`dedupe` and `select`, which App's `switchToAcc` and `refreshComms` call):

- `dedupe_nodup`: no two entries share an acceptance (op id);
- `select_tapped`: selecting the acceptance of the entry tapped gives
  exactly that entry, however many entries share its community or name.

Before, entries were told apart by community id, and a device that had
joined one community twice could not reach its second entry.
-/
import Quiet.Kinds.Accepted

namespace Switch
open Kinds.Accepted

theorem dedupeL_fresh : ∀ (ms : List Me) (seen : List Engine.Id) (m : Me),
    m ∈ dedupeL ms seen → m.acc ∉ seen
  | [], _, _, h => by simp [dedupeL] at h
  | x :: t, seen, m, h => by
    unfold dedupeL at h
    split at h
    · exact dedupeL_fresh t seen m h
    · rename_i hx
      rcases List.mem_cons.1 h with rfl | h
      · intro hm; exact hx (List.any_eq_true.2 ⟨_, hm, by simp⟩)
      · have := dedupeL_fresh t (x.acc :: seen) m h
        exact fun hm => this (List.mem_cons_of_mem _ hm)

theorem dedupeL_nodup : ∀ (ms : List Me) (seen : List Engine.Id),
    ((dedupeL ms seen).map (·.acc)).Nodup
  | [], _ => by simp [dedupeL]
  | x :: t, seen => by
    unfold dedupeL
    split
    · exact dedupeL_nodup t seen
    · simp only [List.map_cons, List.nodup_cons, List.mem_map]
      refine ⟨?_, dedupeL_nodup t (x.acc :: seen)⟩
      rintro ⟨m, hm, he⟩
      exact dedupeL_fresh t (x.acc :: seen) m hm (he ▸ List.mem_cons_self)

/-- **No two entries share an acceptance.** -/
theorem dedupe_nodup (ms : Array Me) : ((dedupe ms).toList.map (·.acc)).Nodup := by
  simpa [dedupe] using dedupeL_nodup ms.toList []

theorem find_nodup : ∀ (l : List Me) (i : Nat) (hi : i < l.length), (l.map (·.acc)).Nodup →
    l.find? (fun m => decide (m.acc = l[i].acc)) = some l[i]
  | [], _, hi, _ => by simp at hi
  | x :: t, 0, _, _ => by simp
  | x :: t, i + 1, hi, hn => by
    have hi' : i < t.length := by simp at hi; omega
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    have hne : x.acc ≠ t[i].acc := fun he => hn.1 ⟨t[i], List.getElem_mem hi', he.symm⟩
    simp only [List.find?_cons, List.getElem_cons_succ, hne, decide_false]
    exact find_nodup t i hi' hn.2

/-- **A tap selects the entry tapped.** -/
theorem select_tapped (ms : Array Me) (hn : (ms.toList.map (·.acc)).Nodup) (i : Nat) (hi : i < ms.size) :
    select ms ms[i].acc = some ms[i] := by
  unfold select
  rw [← Array.find?_toList]
  have := find_nodup ms.toList i (by simpa using hi) hn
  simpa using this

/-- And on the entries the app holds (`Accepted.read` returns `dedupe`'s). -/
theorem select_tapped_dedupe (ms : Array Me) (i : Nat) (hi : i < (dedupe ms).size) :
    select (dedupe ms) (dedupe ms)[i].acc = some (dedupe ms)[i] :=
  select_tapped _ (dedupe_nodup ms) i hi

end Switch
