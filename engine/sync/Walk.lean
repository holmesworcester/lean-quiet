/-
The closure walk a windowed round reads S with (engine/sync/WindowLaws):
breadth first from a window's ids, through a `next` function (an op's
stored requirements in its room), k levels, each id visited once.

- `walk_near`: the walk holds exactly the ids within k steps of the
  window (`Near`), a function of `next` and the window only.
- `walk_cost`: its lookups are at most `M · (|window| + |result|)` when
  each id costs at most M: each id is expanded on one level at most.
-/
import Std.Data.HashSet

namespace Engine.Sync
open Std

section
variable {α : Type} [BEq α] [Hashable α] (next : α → List α) (cost : α → Nat)

/-- Add q to a level's new ids, once, unless seen. -/
def visit (acc : List α × HashSet α) (q : α) : List α × HashSet α :=
  if acc.2.contains q then acc else (q :: acc.1, acc.2.insert q)

/-- One level: the ids `front` leads to that `seen` lacks, each once;
`seen` with them; and the lookups made (`cost` of each id expanded). -/
def level (front : List α) (seen : HashSet α) : List α × HashSet α × Nat :=
  front.foldl (fun acc x => let p := (next x).foldl visit (acc.1, acc.2.1); (p.1, p.2, acc.2.2 + cost x))
    ([], seen, 0)

/-- At most j levels from `front`: `seen` grown by every id within j
steps, and the lookups made. -/
def walk : Nat → List α → HashSet α → HashSet α × Nat
  | 0, _, seen => (seen, 0)
  | j + 1, front, seen =>
    let p := level next cost front seen
    let q := walk j p.1 p.2.1
    (q.1, p.2.2 + q.2)

/-- x is within j steps of the ids w. -/
def Near (w : List α) : Nat → α → Prop
  | 0, x => x ∈ w
  | j + 1, x => Near w j x ∨ ∃ y, Near w j y ∧ x ∈ next y

/-- Within j steps is within j + m. -/
theorem Near.mono {w : List α} {x : α} : ∀ {j : Nat} (m : Nat), Near next w j x → Near next w (j + m) x
  | _, 0, h => h
  | j, m + 1, h => Or.inl (Near.mono m h)

/-- With nothing to follow, what is near the window is the window. -/
theorem Near.of_none {w : List α} (hn : ∀ y, next y = []) : ∀ {j : Nat} {x : α}, Near next w j x → x ∈ w
  | 0, _, h => h
  | _ + 1, _, .inl h => Near.of_none hn h
  | _ + 1, _, .inr ⟨y, _, hy⟩ => by rw [hn y] at hy; cases hy

/-- The ids first reached at level j. -/
def Fresh (w : List α) : Nat → α → Prop
  | 0, x => Near next w 0 x
  | j + 1, x => Near next w (j + 1) x ∧ ¬ Near next w j x

end

section
variable {α : Type} [BEq α] [Hashable α] [LawfulBEq α] (next : α → List α) (cost : α → Nat)

theorem visit_fold : ∀ (qs : List α) (acc : List α × HashSet α) (z : α),
    (z ∈ (qs.foldl visit acc).2 ↔ z ∈ acc.2 ∨ z ∈ qs) ∧
    (z ∈ (qs.foldl visit acc).1 ↔ z ∈ acc.1 ∨ (z ∉ acc.2 ∧ z ∈ qs)) ∧
    (qs.foldl visit acc).2.size + acc.1.length = acc.2.size + (qs.foldl visit acc).1.length
  | [], acc, z => by simp
  | q :: qs, acc, z => by
    obtain ⟨h1, h2, h3⟩ := visit_fold qs (visit acc q) z
    rw [List.foldl_cons]
    refine ⟨?_, ?_, ?_⟩
    · rw [h1]
      unfold visit
      split
      · rename_i hq
        simp only [List.mem_cons]
        constructor
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
        · rintro (h | rfl | h)
          · exact Or.inl h
          · exact Or.inl (HashSet.mem_iff_contains.2 hq)
          · exact Or.inr h
      · simp only [HashSet.mem_insert, beq_iff_eq, List.mem_cons]
        constructor
        · rintro ((rfl | h) | h)
          · exact Or.inr (Or.inl rfl)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
        · rintro (h | rfl | h)
          · exact Or.inl (Or.inr h)
          · exact Or.inl (Or.inl rfl)
          · exact Or.inr h
    · rw [h2]
      unfold visit
      split
      · rename_i hq
        simp only [List.mem_cons]
        constructor
        · rintro (h | ⟨hn, h⟩)
          · exact Or.inl h
          · exact Or.inr ⟨hn, Or.inr h⟩
        · rintro (h | ⟨hn, rfl | h⟩)
          · exact Or.inl h
          · exact absurd (HashSet.mem_iff_contains.2 hq) hn
          · exact Or.inr ⟨hn, h⟩
      · rename_i hq
        simp only [HashSet.mem_insert, beq_iff_eq, List.mem_cons, not_or]
        constructor
        · rintro ((rfl | h) | ⟨⟨hne, hn⟩, h⟩)
          · exact Or.inr ⟨fun h' => hq (HashSet.mem_iff_contains.1 h'), Or.inl rfl⟩
          · exact Or.inl h
          · exact Or.inr ⟨hn, Or.inr h⟩
        · rintro (h | ⟨hn, rfl | h⟩)
          · exact Or.inl (Or.inr h)
          · exact Or.inl (Or.inl rfl)
          · by_cases e : q = z
            · exact Or.inl (Or.inl e.symm)
            · exact Or.inr ⟨⟨e, hn⟩, h⟩
    · have hv : (visit acc q).2.size + acc.1.length = acc.2.size + (visit acc q).1.length := by
        unfold visit
        split
        · rfl
        · rename_i hq
          simp only [List.length_cons]
          rw [HashSet.size_insert]
          simp only [HashSet.mem_iff_contains, hq, Bool.false_eq_true, ite_false]
          omega
      omega
theorem level_fold : ∀ (front : List α) (acc : List α × HashSet α × Nat) (z : α),
    (z ∈ (front.foldl (fun acc x => let p := (next x).foldl visit (acc.1, acc.2.1); (p.1, p.2, acc.2.2 + cost x)) acc).2.1 ↔
      z ∈ acc.2.1 ∨ ∃ x ∈ front, z ∈ next x) ∧
    (z ∈ (front.foldl (fun acc x => let p := (next x).foldl visit (acc.1, acc.2.1); (p.1, p.2, acc.2.2 + cost x)) acc).1 ↔
      z ∈ acc.1 ∨ (z ∉ acc.2.1 ∧ ∃ x ∈ front, z ∈ next x)) ∧
    (front.foldl (fun acc x => let p := (next x).foldl visit (acc.1, acc.2.1); (p.1, p.2, acc.2.2 + cost x)) acc).2.1.size
        + acc.1.length =
      acc.2.1.size + (front.foldl (fun acc x => let p := (next x).foldl visit (acc.1, acc.2.1); (p.1, p.2, acc.2.2 + cost x)) acc).1.length ∧
    (front.foldl (fun acc x => let p := (next x).foldl visit (acc.1, acc.2.1); (p.1, p.2, acc.2.2 + cost x)) acc).2.2 =
      acc.2.2 + (front.map cost).sum
  | [], acc, z => by simp
  | x :: front, acc, z => by
    rw [List.foldl_cons]
    obtain ⟨h1, h2, h3, h4⟩ := level_fold front
      (((next x).foldl visit (acc.1, acc.2.1)).1, ((next x).foldl visit (acc.1, acc.2.1)).2, acc.2.2 + cost x) z
    obtain ⟨v1, v2, v3⟩ := visit_fold (next x) (acc.1, acc.2.1) z
    simp only at h1 h2 h3 h4 v1 v2 v3
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [h1, v1]
      simp only [List.mem_cons, exists_eq_or_imp, or_assoc]
    · rw [h2, v2, v1]
      simp only [List.mem_cons, exists_eq_or_imp]
      by_cases hz : z ∈ next x <;> by_cases ha : z ∈ acc.2.1 <;> simp [hz, ha]
    · dsimp only
      omega
    · dsimp only
      rw [h4]; simp only [List.map_cons, List.sum_cons]; omega

theorem level_mem (front : List α) (seen : HashSet α) (z : α) :
    (z ∈ (level next cost front seen).2.1 ↔ z ∈ seen ∨ ∃ x ∈ front, z ∈ next x) ∧
    (z ∈ (level next cost front seen).1 ↔ z ∉ seen ∧ ∃ x ∈ front, z ∈ next x) ∧
    (level next cost front seen).2.1.size = seen.size + (level next cost front seen).1.length ∧
    (level next cost front seen).2.2 = (front.map cost).sum := by
  obtain ⟨h1, h2, h3, h4⟩ := level_fold next cost front ([], seen, 0) z
  unfold level
  simp only [List.not_mem_nil, false_or, List.length_nil, Nat.add_zero, Nat.zero_add] at h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

theorem level_size (front : List α) (seen : HashSet α) :
    (level next cost front seen).2.1.size = seen.size + (level next cost front seen).1.length := by
  cases front with
  | nil => simp [level]
  | cons x _ => exact (level_mem next cost (x :: _) seen x).2.2.1

theorem level_sum (front : List α) (seen : HashSet α) :
    (level next cost front seen).2.2 = (front.map cost).sum := by
  cases front with
  | nil => simp [level]
  | cons x _ => exact (level_mem next cost (x :: _) seen x).2.2.2

/-- A predecessor of an id first reached past level L was on level L's front. -/
theorem fresh_pred (w : List α) (L : Nat) {y z : α} (hy : Near next w L y) (hz : z ∈ next y)
    (hn : ¬ Near next w L z) : Fresh next w L y := by
  cases L with
  | zero => exact hy
  | succ L =>
    refine ⟨hy, fun hL => hn (Or.inr ⟨y, hL, hz⟩)⟩

theorem fresh_near (w : List α) : ∀ (L : Nat) (y : α), Fresh next w L y → Near next w L y
  | 0, _, h => h
  | _ + 1, _, h => h.1

/-- **The walk holds exactly the ids within its levels.** From `seen`,
the ids within L steps, and `front`, those first reached at L, j more
levels hold those within L + j. -/
theorem walk_near (w : List α) : ∀ (j L : Nat) (front : List α) (seen : HashSet α),
    (∀ z, z ∈ seen ↔ Near next w L z) → (∀ z, z ∈ front ↔ Fresh next w L z) →
    ∀ z, z ∈ (walk next cost j front seen).1 ↔ Near next w (L + j) z
  | 0, L, _, _, hs, _, z => by simp [walk, hs]
  | j + 1, L, front, seen, hs, hf, z => by
    simp only [walk]
    rw [walk_near w j (L + 1) _ _ ?_ ?_ z, show L + 1 + j = L + (j + 1) by omega]
    · intro z
      rw [(level_mem next cost front seen z).1, hs]
      constructor
      · rintro (h | ⟨x, hx, h⟩)
        · exact Or.inl h
        · exact Or.inr ⟨x, fresh_near next w L x ((hf x).1 hx), h⟩
      · rintro (h | ⟨y, hy, h⟩)
        · exact Or.inl h
        · by_cases hn : Near next w L z
          · exact Or.inl hn
          · exact Or.inr ⟨y, (hf y).2 (fresh_pred next w L hy h hn), h⟩
    · intro z
      rw [(level_mem next cost front seen z).2.1, hs]
      constructor
      · rintro ⟨hn, x, hx, h⟩
        exact ⟨Or.inr ⟨x, fresh_near next w L x ((hf x).1 hx), h⟩, hn⟩
      · rintro ⟨h | ⟨y, hy, h⟩, hn⟩
        · exact absurd h hn
        · exact ⟨hn, y, (hf y).2 (fresh_pred next w L hy h hn), h⟩

/-- **From a window, the walk holds exactly what lies within k steps.** -/
theorem walk_from (w : List α) (k : Nat) (z : α) :
    z ∈ (walk next cost k w (HashSet.ofList w)).1 ↔ Near next w k z := by
  have := walk_near next cost w k 0 w (HashSet.ofList w)
    (fun z => by simp [Near, HashSet.mem_ofList]) (fun z => by simp [Fresh, Near]) z
  simpa using this

theorem sum_le (M : Nat) (hc : ∀ x, cost x ≤ M) : ∀ l : List α, (l.map cost).sum ≤ M * l.length
  | [] => by simp
  | x :: l => by
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_add, Nat.mul_one]
    have := sum_le M hc l
    have := hc x
    omega

/-- **The walk's lookups are bounded by what it reaches**: when each
expanded id costs at most M, j levels from `front` cost at most M times
the front's length plus the ids the walk ends with (each id is expanded
on one level at most). -/
theorem walk_cost (M : Nat) (hc : ∀ x, cost x ≤ M) : ∀ (j : Nat) (front : List α) (seen : HashSet α),
    (walk next cost j front seen).2 + M * seen.size ≤ M * (front.length + (walk next cost j front seen).1.size)
  | 0, front, seen => by
    simp only [walk, Nat.zero_add, Nat.mul_add]
    omega
  | j + 1, front, seen => by
    simp only [walk]
    have hsz := level_size next cost front seen
    have hsum := level_sum next cost front seen
    have ih := walk_cost M hc j (level next cost front seen).1 (level next cost front seen).2.1
    have hs := sum_le cost M hc front
    rw [hsum] at *
    rw [hsz, Nat.mul_add] at ih
    rw [Nat.mul_add] at ih ⊢
    omega
end

end Engine.Sync
