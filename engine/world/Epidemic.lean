/-
The epidemic step, proven: per-edge progress gives convergence over any
connected knows-graph, with the bound d · B for a node d edges away
(`hops`). With stores that only grow, an op reaches every node and
stays (`converge_of_edge`). Everyone knowing everyone is d = 1
(`converge_all_of`), two peers a case of it (`converge_two_of`), and
three peers on a line d = 2 (`converge_three_of`).

None of this names node code: it is about the world's `Holds` and an
execution's times, so it applies to the running nodes as soon as the
per-edge bound (`edge_stmt`) and growth (`grows_stmt`) are proven of
them.
-/
import engine.world.Statements

namespace Engine.World
open Engine Engine.Sync

variable {F : Type} {M : Type → Type} {S : Type} [Monad M] [Store F M] [Turn F M]
variable {P : Setup F M S} {adv : World S P.n → ByteArray → Prop} {w₀ : World S P.n}

/-- **Hops.** Under the per-edge bound B, an op a node holds at step
k ≥ k₀, the node d edges away holds within d · B. -/
theorem hops (E : Exec P adv w₀) {G : Fin P.n → Fin P.n → Prop} {r : Id} {k₀ B : Nat}
    (hE : Edge E G r k₀ B) : ∀ {d : Nat} {i j : Fin P.n}, Path G d i j → ∀ k x, k₀ ≤ k →
      Holds P (E.world k) i r x →
        ∃ k', k ≤ k' ∧ (E.world k').now ≤ (E.world k).now + d * B ∧ Holds P (E.world k') j r x := by
  intro d i j hp
  induction hp with
  | refl i => intro k x _ hx; exact ⟨k, Nat.le_refl _, by omega, hx⟩
  | @step d i j l hij _ ih =>
    intro k x hk hx
    obtain ⟨k₁, hk₁, ht₁, hx₁⟩ := hE k i j x hk hij hx
    obtain ⟨k₂, hk₂, ht₂, hx₂⟩ := ih k₁ x (by omega) hx₁
    refine ⟨k₂, by omega, ?_, hx₂⟩
    rw [Nat.succ_mul]; omega

/-- Growth along an execution: what a store holds at step k it holds at
every later step. -/
theorem held_on (E : Exec P adv w₀) {i : Fin P.n} {r x : Id}
    (hg : ∀ k, Holds P (E.world k) i r x → Holds P (E.world (k + 1)) i r x) :
    ∀ k k', k ≤ k' → Holds P (E.world k) i r x → Holds P (E.world k') i r x := by
  intro k k' hle hx
  induction k' with
  | zero => rw [Nat.le_zero.1 hle] at hx; exact hx
  | succ k' ih =>
    rcases Nat.lt_or_ge k (k' + 1) with h | h
    · exact hg k' (ih (by omega))
    · rw [show k = k' + 1 by omega] at hx; exact hx

/-- **The reduction, proven:** the per-edge bound and growth give
convergence over any connected knows-graph. -/
theorem converge_of_edge : converge_of_edge_stmt := by
  intro hedge hgrow F fam cfg n addr rooms E G r d Δ τ k₀ N hf hd k i j x hk hx
  obtain ⟨e, he, hp⟩ := hd i j
  obtain ⟨k', hk', ht, hx'⟩ := hops E (hedge F fam cfg n addr rooms E G r Δ τ k₀ N hf) hp k x hk hx
  refine ⟨k', hk', ?_, fun k'' hk'' => held_on E (fun m hm => ?_) k' k'' hk'' hx'⟩
  · have := Nat.mul_le_mul_right (epoch cfg Δ τ (depth cfg N)) he; omega
  · exact hgrow F fam cfg n addr rooms noAdv _ _ j r x (E.reachable m) (E.legal m) hm

/-- Everyone knowing everyone is diameter one. -/
theorem diam_allKnow {α : Type} {G : α → α → Prop} [DecidableEq α] (h : AllKnow G) : Diam G 1 := by
  intro i j
  by_cases e : i = j
  · subst e; exact ⟨0, by omega, .refl i⟩
  · exact ⟨1, Nat.le_refl _, .step (h i j e) (.refl j)⟩

/-- **When everyone knows everyone, one epoch.** -/
theorem converge_all_of (h : converge_stmt) : converge_all_stmt := by
  intro F fam cfg n addr rooms E G r Δ τ k₀ N hf hall k i j x hk hx
  obtain ⟨k', hk', ht, hx'⟩ := h F fam cfg n addr rooms E G r 1 Δ τ k₀ N hf (diam_allKnow hall) k i j x hk hx
  exact ⟨k', hk', by simpa using ht, hx'⟩

/-- **Two peers.** -/
theorem converge_two_of (h : converge_stmt) : converge_two_stmt := by
  intro F fam cfg addr rooms E r Δ τ k₀ N hf k i j x hk hx
  exact converge_all_of h F fam cfg 2 addr rooms E (fun i j => i ≠ j) r Δ τ k₀ N hf (fun _ _ e => e)
    k i j x hk hx

/-- The line 0 — 1 — 2 has diameter two. -/
theorem diam_line3 : Diam line3 2 := by
  have e01 : line3 0 1 := Or.inl rfl
  have e10 : line3 1 0 := Or.inr rfl
  have e12 : line3 1 2 := Or.inl rfl
  have e21 : line3 2 1 := Or.inr rfl
  intro i j
  match i, j with
  | 0, 0 => exact ⟨0, by omega, .refl _⟩
  | 1, 1 => exact ⟨0, by omega, .refl _⟩
  | 2, 2 => exact ⟨0, by omega, .refl _⟩
  | 0, 1 => exact ⟨1, by omega, .step e01 (.refl _)⟩
  | 1, 0 => exact ⟨1, by omega, .step e10 (.refl _)⟩
  | 1, 2 => exact ⟨1, by omega, .step e12 (.refl _)⟩
  | 2, 1 => exact ⟨1, by omega, .step e21 (.refl _)⟩
  | 0, 2 => exact ⟨2, by omega, .step e01 (.step e12 (.refl _))⟩
  | 2, 0 => exact ⟨2, by omega, .step e21 (.step e10 (.refl _))⟩

/-- **Three peers who know each other transitively.** -/
theorem converge_three_of (h : converge_stmt) : converge_three_stmt := by
  intro F fam cfg addr rooms E r Δ τ k₀ N hf k i j x hk hx
  exact h F fam cfg 3 addr rooms E line3 r 2 Δ τ k₀ N hf diam_line3 k i j x hk hx

end Engine.World
