/- A quiet round ends in logarithmically many batches, proven of the
actual handler run (`RoundRun.Run`), not of the `exchange` model.

While neither index changes during the round (the two ends alternate
over fixed items X and Y), every claim carries a budget: the levels i
and j with its range holding at most leaf·fanⁱ of the receiver's items
and leaf·fanʲ of the claimant's. Answering a fingerprint either lists
ids (the range holds at most leaf of the receiver's items), which ends
that path at the next answer, or cuts the range into pieces holding at
most a run (`runLen`) of the cutter's items each, one level less
(`runLen_le`). So each batch lowers every pending claim's budget
i + j + [fingerprint] (`answer_level`), and a round over rooms of at
most leaf·fanᵏ items ends within 2k + 2 batches (`quiet_round_log`):
with the defaults (leaf 128, fan 16), 12 batches for 134 million items.

Under concurrent writes a side's count in a piece can grow between its
cut and its next answer, so only the linear bound `RoundRun.terminates`
is proven then. -/
import engine.sync.RoundRun

namespace Engine.Sync

/-- One for a fingerprint, which still has a conversion to ids ahead. -/
def Claim.fpBit : Claim → Nat
  | .fp .. => 1
  | .ids .. => 0

namespace RoundRun
attribute [local instance] byteArray_lawfulBEq

/-- **Every answer lowers a claim's budget.** X answers claim cl, whose
range holds at most leaf·fanⁱ of X's items and leaf·fanʲ of Z's: every
claim it sends back is over a range holding at most leaf·fanʲ of Z's
items and leaf·fanⁱ' of X's, with i' + [fingerprint] ≤ i; and cl was a
fingerprint (ids are answered without claims). -/
theorem answer_level (cfg : Config) (X Z : List Item) (sx : Sorted Prod.fst X) (cl child : Claim)
    (hc : Out.claim child ∈ answer Prod.fst Prod.snd sha256 cfg.params X cl) (i j : Nat)
    (hi : (within Prod.fst cl.range X).length ≤ cfg.params.leaf * cfg.params.fan ^ i)
    (hj : (within Prod.fst cl.range Z).length ≤ cfg.params.leaf * cfg.params.fan ^ j) :
    cl.fpBit = 1 ∧ ∃ i', i' + child.fpBit ≤ i ∧
      (within Prod.fst child.range X).length ≤ cfg.params.leaf * cfg.params.fan ^ i' ∧
      (within Prod.fst child.range Z).length ≤ cfg.params.leaf * cfg.params.fan ^ j := by
  cases cl with
  | ids q ids => simp [answer] at hc
  | fp q n l =>
    refine ⟨rfl, ?_⟩
    simp only [answer] at hc
    split at hc
    · simp at hc
    · split at hc
      · simp only [List.mem_singleton, Out.claim.injEq] at hc
        subst child
        exact ⟨i, by simp [Claim.fpBit], by simpa [Claim.range] using hi, by simpa [Claim.range] using hj⟩
      · rename_i hf hl
        obtain ⟨piece, hp, he⟩ := List.mem_map.mp hc
        cases he
        have hp : piece ∈ pieces q (cutsOf Prod.fst cfg.params (within Prod.fst q X)) := by simpa using hp
        have hsub := (pieces_shrink (P := cfg.params) sx (Nat.lt_of_not_ge hl) piece hp).2
        have hle := Tree.pieces_le cfg.params sx piece hp
        simp only [Claim.range] at hi hj
        -- the range held more than leaf of X's items, so i ≥ 1
        obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := by
          cases i with
          | zero => simp at hi; omega
          | succ i' => exact ⟨i', rfl⟩
        refine ⟨i', by simp [Claim.fpBit], ?_, ?_⟩
        · exact Nat.le_trans hle (Tree.runLen_le cfg.params hi)
        · have := filter_len_le (l := Z) (fun a ha => hsub (Prod.fst a) ha)
          change (within Prod.fst piece Z).length ≤ (within Prod.fst q Z).length at this
          exact Nat.le_trans this hj

/-- **A quiet round's batches end within its claims' budgets.** Along a
run that stays current while the two ends' items stay X (even steps)
and Y (odd steps): if every claim pending at step t has a budget
i + j + [fingerprint] ≤ n, levels of the receiver's and the claimant's
items in its range, then the round's claims run out within n + 1 more
batches. -/
theorem quiet_terminates (cfg : Config) (r : Id) (k : Nat) (times : Nat → Nat) (states : Nat → State)
    (run : Run cfg r k times states) (cur : Current r k states) (X Y : List Item)
    (hX : ∀ t, (states (2 * t)).items r = X) (hY : ∀ t, (states (2 * t + 1)).items r = Y)
    (sx : Sorted Prod.fst X) (sy : Sorted Prod.fst Y) :
    ∀ n t, (∀ cl ∈ (states t).pending, ∃ i j,
        (within Prod.fst cl.range ((states t).items r)).length ≤ cfg.params.leaf * cfg.params.fan ^ i ∧
        (within Prod.fst cl.range ((states (t + 1)).items r)).length ≤ cfg.params.leaf * cfg.params.fan ^ j ∧
        i + j + cl.fpBit ≤ n) →
      ∃ s, t ≤ s ∧ s ≤ t + n + 1 ∧ (states s).pending = [] := by
  have par := items_par hX hY
  have swap : ∀ t, (states (t + 2)).items r = (states t).items r := by
    intro t; rw [par, par]
    have : (t + 2) % 2 = t % 2 := by omega
    rw [this]
  have sorted : ∀ t, Sorted Prod.fst ((states t).items r) := by
    intro t; rw [par t]; split
    · exact sx
    · exact sy
  intro n
  induction n with
  | zero =>
    intro t budget
    by_cases empty : (states t).pending = []
    · exact ⟨t, Nat.le_refl _, by omega, empty⟩
    have next : (states (t + 1)).pending = [] := by
      rw [next_pending cfg r k times states run cur t empty]
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro child hc
      obtain ⟨cl, hcl, hchild⟩ := (next_mem cfg _ _ child).mp hc
      obtain ⟨i, j, hi, hj, hb⟩ := budget cl hcl
      have := (answer_level cfg _ _ (sorted t) cl child hchild i j hi hj).1
      omega
    exact ⟨t + 1, by omega, by omega, next⟩
  | succ n ih =>
    intro t budget
    by_cases empty : (states t).pending = []
    · exact ⟨t, Nat.le_refl _, by omega, empty⟩
    have nextBudget : ∀ cl ∈ (states (t + 1)).pending, ∃ i j,
        (within Prod.fst cl.range ((states (t + 1)).items r)).length ≤ cfg.params.leaf * cfg.params.fan ^ i ∧
        (within Prod.fst cl.range ((states (t + 1 + 1)).items r)).length ≤ cfg.params.leaf * cfg.params.fan ^ j ∧
        i + j + cl.fpBit ≤ n := by
      rw [next_pending cfg r k times states run cur t empty]
      intro child hc
      obtain ⟨cl, hcl, hchild⟩ := (next_mem cfg _ _ child).mp hc
      obtain ⟨i, j, hi, hj, hb⟩ := budget cl hcl
      obtain ⟨hfp, i', hi', cx, cz⟩ :=
        answer_level cfg _ ((states (t + 1)).items r) (sorted t) cl child hchild i j hi hj
      -- at t + 1 the claimant's items become the receiver's, and the
      -- receiver's at t the claimant's
      refine ⟨j, i', cz, ?_, by omega⟩
      rw [show t + 1 + 1 = t + 2 by omega, swap t]
      exact cx
    obtain ⟨s, hs, hb, hdone⟩ := ih (t + 1) nextBudget
    exact ⟨s, by omega, by omega, hdone⟩

/-- **A quiet round ends within 2k + 2 batches.** Along a run of the
actual handler that stays current while neither end's index changes in
the room (items X on even steps, Y on odd), with both holding at most
leaf·fanᵏ items, the round's claims run out within 2k + 2 batches. With
the defaults (leaf 128, fan 16): 12 batches for 134 million items.
Under concurrent writes only the linear `RoundRun.terminates` holds. -/
theorem quiet_round_log (cfg : Config) (r : Id) (k : Nat) (times : Nat → Nat) (states : Nat → State)
    (run : Run cfg r k times states) (cur : Current r k states) (X Y : List Item)
    (hX : ∀ t, (states (2 * t)).items r = X) (hY : ∀ t, (states (2 * t + 1)).items r = Y)
    (sx : Sorted Prod.fst X) (sy : Sorted Prod.fst Y) (w : Nat)
    (hxw : X.length ≤ cfg.params.leaf * cfg.params.fan ^ w)
    (hyw : Y.length ≤ cfg.params.leaf * cfg.params.fan ^ w) :
    ∃ s, s ≤ 2 * w + 2 ∧ (states s).pending = [] := by
  have par := items_par hX hY
  have small : ∀ t (q : Range),
      (within Prod.fst q ((states t).items r)).length ≤ cfg.params.leaf * cfg.params.fan ^ w := by
    intro t q
    have hle := List.length_filter_le (fun a : Item => q.has a.1) ((states t).items r)
    change (within Prod.fst q ((states t).items r)).length ≤ ((states t).items r).length at hle
    rw [par t] at hle ⊢
    by_cases h : t % 2 = 0
    · rw [if_pos h] at hle ⊢; exact Nat.le_trans hle hxw
    · rw [if_neg h] at hle ⊢; exact Nat.le_trans hle hyw
  obtain ⟨s, _, hs, hdone⟩ := quiet_terminates cfg r k times states run cur X Y hX hY sx sy (2 * w + 1) 0
    (fun cl _ => ⟨w, w, small 0 _, small 1 _, by cases cl <;> simp only [Claim.fpBit] <;> omega⟩)
  exact ⟨s, by omega, hdone⟩

end RoundRun
end Engine.Sync
