/-
What a row shows is what the store holds, over the running code:

- `picBox_aspect`: a picture's box is within its bounds, one side at the
  bound and the other the first scaled by the picture's aspect (floored):
  a picture keeps its shape;
- `tally_nodup` and `tally_mem`: each reaction pill's reactors are
  distinct, and are exactly the people who reacted with its emoji; so its
  count is the number of distinct reactors;
- `time_shown`: the row's clock is `clock` of the message's claimed time
  (or "pending" while its op is in the outbox).
-/
import engine.renderer.Row
import ops.community.reaction.View

namespace RowLaws
open Row Engine

/-- **A picture keeps its shape.** Its box has one side at its bound (240
dp high, or 280 dp and the text's width wide) and the other that side
scaled by the picture's aspect (floored, at least 1 px). -/
theorem picBox_aspect (dm : Dim) (maxW : Nat) (p : Pic) :
    ((picBox dm maxW p).2 = dm.px 240 ∧
      (picBox dm maxW p).1 = max 1 (max p.w 1 * dm.px 240 / max p.h 1) ∧
      max p.w 1 * dm.px 240 ≤ max p.h 1 * min (dm.px 280) maxW) ∨
    ((picBox dm maxW p).1 = min (dm.px 280) maxW ∧
      (picBox dm maxW p).2 = max 1 (max p.h 1 * min (dm.px 280) maxW / max p.w 1) ∧
      max p.h 1 * min (dm.px 280) maxW < max p.w 1 * dm.px 240) := by
  unfold picBox
  by_cases hc : max p.w 1 * dm.px 240 ≤ max p.h 1 * min (dm.px 280) maxW
  · left; simp [hc]
  · right; simp only [hc, if_false]; exact ⟨trivial, trivial, by omega⟩

open Kinds.React

theorem uniq_mem {α : Type} [DecidableEq α] (x : α) : ∀ l : List α, x ∈ uniq l ↔ x ∈ l
  | [] => by simp [uniq]
  | y :: t => by
    rw [uniq]
    have ih := uniq_mem x (t.filter fun z => !decide (z = y))
    simp only [List.mem_cons, ih, List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not]
    by_cases h : x = y <;> simp [h]
termination_by l => l.length
decreasing_by all_goals (simp_wf; exact Nat.lt_succ_of_le (Nat.le_trans (List.length_filter_le _ _) (by simp)))

theorem uniq_nodup {α : Type} [DecidableEq α] : ∀ l : List α, (uniq l).Nodup
  | [] => by simp [uniq]
  | y :: t => by
    rw [uniq]
    refine List.nodup_cons.2 ⟨?_, uniq_nodup _⟩
    rw [uniq_mem]
    simp
termination_by l => l.length
decreasing_by all_goals (simp_wf; exact Nat.lt_succ_of_le (Nat.le_trans (List.length_filter_le _ _) (by simp)))

/-- **A pill's reactors are distinct**, so its count is how many people
reacted with its emoji, not how many reactions; and **each emoji has one
pill.** -/
theorem tally_nodup (xs : List (String × Id)) :
    ((tally xs).map (·.1)).Nodup ∧ ∀ p ∈ tally xs, p.2.Nodup := by
  refine ⟨?_, ?_⟩
  · simpa [tally, Function.comp_def] using uniq_nodup (xs.map (·.1))
  · intro p hp
    simp only [tally, List.mem_map] at hp
    obtain ⟨e, _, rfl⟩ := hp
    exact uniq_nodup _

/-- **A pill's reactors are exactly who reacted with its emoji**, and
every emoji reacted with has a pill. -/
theorem tally_mem (xs : List (String × Id)) (e : String) (w : Id) :
    (∃ us, (e, us) ∈ tally xs ∧ w ∈ us) ↔ (e, w) ∈ xs := by
  simp only [tally, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨us, ⟨e', _, rfl, rfl⟩, hw⟩
    rw [uniq_mem] at hw
    simp only [List.mem_map, List.mem_filter, decide_eq_true_eq] at hw
    obtain ⟨⟨e'', w'⟩, ⟨hm, rfl⟩, rfl⟩ := hw
    exact hm
  · intro h
    refine ⟨_, ⟨e, ?_, rfl, rfl⟩, ?_⟩
    · rw [uniq_mem]; exact List.mem_map.2 ⟨(e, w), h, rfl⟩
    · rw [uniq_mem]; exact List.mem_map.2 ⟨(e, w), List.mem_filter.2 ⟨h, by simp⟩, rfl⟩

/-- **The row's clock is the message's claimed time** (or "pending"
while its op waits in the outbox): what layout places is `oneLine` of it. -/
theorem time_shown (f : Font.Font) (dm : Dim) (W : Nat) (d : RowData) :
    (layout f dm W d).time = Text.oneLine f (dm.cell * 4) (if d.pending then "pending" else clock d.time) := rfl

/-- **The row's name is the author's name as read**, every character drawn (an
invisible one as its own glyph: Text.name_shows), cut as `oneLine`
cuts (a logical prefix: Text.oneLine_prefix). -/
theorem name_placed (f : Font.Font) (dm : Dim) (W : Nat) (d : RowData) :
    (layout f dm W d).name = Text.oneLine f ((W - dm.textX - dm.pad) / 2) d.name (reveal := true) := rfl

end RowLaws
