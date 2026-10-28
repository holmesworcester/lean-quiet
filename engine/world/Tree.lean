/-
Claim trees, one hop (docs/PROOFS.md, "Claim trees"): what a side's
answer to an honest claim does with an item of the two sides'
difference over the claim's range, proven of holmes-a3's `answer`, the
function `Conn.onRbsr` runs. Either the answer settles it (a have of it,
or a want of it, when the claim listed ids), or it passes it on in a
claim of its own that is honest for the answering side: an id claim over
the same range, or a fingerprint over a piece of it that holds fewer of
the two sides' items (`answer_step`). Sound fingerprints rule out an
empty answer (`same_of_fp`). So every item of the difference is settled
within the tree's depth on its path, which `exchange_complete` bounds.
-/
import engine.world.Leaf
namespace Engine.World
open Engine Engine.Sync
variable {F : Type}

section
variable {α : Type} {key : α → Key} {ident : α → ByteArray} {h : ByteArray → ByteArray} {P : Params}

/-- Id i is in the two sides' difference over range q, either way. -/
def Diff (key : α → Key) (ident : α → ByteArray) (X Y : List α) (q : Range) (i : ByteArray) : Prop :=
  (named ident (within key q X) i = true ∧ named ident (within key q Y) i = false) ∨
  (named ident (within key q Y) i = true ∧ named ident (within key q X) i = false)

/-- **One hop of a claim tree.** X's answer to Y's honest claim over q,
for an id i of the two sides' difference over q: a have of i, a want of
i, an id claim over q honest for X, or a fingerprint over a piece of q,
honest for X, whose difference still holds i and which holds fewer of
the two sides' items. -/
theorem answer_step (X Y : List α) (q : Range) (c : Claim) (sX : Engine.Sync.Sorted key X)
    (nm : Engine.Sync.Named key ident (X ++ Y)) (so : Sound key ident h X Y) (hc : Honest key ident h Y q c)
    (i : ByteArray) (hd : Diff key ident X Y q i) :
    (∃ xs, Out.hold xs ∈ answer key ident h P X c ∧ i ∈ xs) ∨
    (∃ xs, Out.want xs ∈ answer key ident h P X c ∧ i ∈ xs) ∨
    (Out.claim (.ids q ((within key q X).map ident)) ∈ answer key ident h P X c) ∨
    (∃ q', Out.claim (.fp q' (fp key ident h (within key q' X)).1 (fp key ident h (within key q' X)).2) ∈
        answer key ident h P X c ∧ (∀ k, q'.has k = true → q.has k = true) ∧ Diff key ident X Y q' i ∧
        (within key q' X).length + (within key q' Y).length < (within key q X).length + (within key q Y).length) := by
  cases c with
  | ids r xs =>
    obtain ⟨rfl, rfl⟩ := hc
    simp only [answer, List.mem_cons, List.not_mem_nil, or_false]
    rcases hd with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      refine ⟨_, Or.inl rfl, ?_⟩
      obtain ⟨a, ha, rfl⟩ := named_iff.1 h1
      refine List.mem_map.2 ⟨a, List.mem_filter.2 ⟨ha, ?_⟩, rfl⟩
      simp only [Bool.not_eq_true', List.any_eq_false, decide_eq_true_eq, List.mem_map]
      rintro _ ⟨b, hb, rfl⟩ e
      exact absurd (named_iff.2 ⟨b, hb, e.symm⟩) (by rw [h2]; simp)
    · right; left
      refine ⟨_, Or.inr rfl, ?_⟩
      obtain ⟨a, ha, rfl⟩ := named_iff.1 h1
      exact List.mem_filter.2 ⟨List.mem_map.2 ⟨a, ha, rfl⟩, by simp [h2]⟩
  | fp r n l =>
    obtain ⟨rfl, hfp⟩ := hc
    by_cases hf : fp key ident h (within key r X) = (n, l)
    · exfalso
      have hs := same_of_fp nm so (hf.trans hfp)
      rcases hd with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [hs i, h2] at h1; cases h1
      · rw [← hs i, h2] at h1; cases h1
    · by_cases hl : (within key r X).length ≤ P.leaf
      · right; right; left
        simp [answer, hf, hl]
      · right; right; right
        have hl' : P.leaf < (within key r X).length := by omega
        have hcut : ∀ c ∈ cutsOf key P (within key r X), r.has c = true := by
          intro c hc
          simp only [cutsOf, List.mem_map] at hc
          obtain ⟨p, hp, rfl⟩ := hc
          exact (mem_within.mp (pick_sub _ _ _ p hp)).2
        have hq : ∃ q' ∈ pieces r (cutsOf key P (within key r X)), Diff key ident X Y q' i := by
          rcases hd with hd | hd
          · obtain ⟨q', hq', hq''⟩ := (pieces_diff nm hcut i).2 hd
            exact ⟨q', hq', Or.inl hq''⟩
          · obtain ⟨q', hq', hq''⟩ := (pieces_diff (named_symm nm) hcut i).2 hd
            exact ⟨q', hq', Or.inr hq''⟩
        obtain ⟨q', hq', hdq⟩ := hq
        obtain ⟨hlt, hsub⟩ := pieces_shrink (P := P) sX hl' q' hq'
        have hY : (within key q' Y).length ≤ (within key r Y).length :=
          filter_len_le (fun a ha => hsub _ ha)
        refine ⟨q', ?_, hsub, hdq, by omega⟩
        simp only [answer, hf, hl, ite_false]
        exact List.mem_map.2 ⟨q', hq', rfl⟩

end

end Engine.World
