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


/-! ## One hop at a connection -/

/-- **One hop of a claim tree, at a connection**: `onRbsr` answers a
round message whose claim cl is honest for the claimant's items Y over q,
from its snapshot X of the round, for an id i of the difference over q:
it sends a have of i, or a want of i (not yet asked, with room), or the
round's reply carrying an id claim over q honest for X, or a fingerprint
over a smaller piece of q honest for X whose difference holds i. -/
theorem onRbsr_step (cfg : Config) (ix : Index) (c : Conn) (r : Id) (k : Nat) (cs : List Claim) (now : Nat)
    (hr : r ∈ c.rooms) (cl : Claim) (hcl : cl ∈ cs) (Y : List Item) (q : Range)
    (sX : Engine.Sync.Sorted Prod.fst (Conn.snap ix c r k))
    (nm : Engine.Sync.Named Prod.fst Prod.snd (Conn.snap ix c r k ++ Y))
    (so : Sound Prod.fst Prod.snd sha256 (Conn.snap ix c r k) Y)
    (hc : Honest Prod.fst Prod.snd sha256 Y q cl) (i : Id) (hd : Diff Prod.fst Prod.snd (Conn.snap ix c r k) Y q i)
    (hmax : 0 < cfg.maxIds) (ha : i ∉ c.asked) (hroom : c.asked.size + (claimIds cs).length ≤ cfg.maxKnown) :
    (∃ H, i ∈ H ∧ (Msg.hold r H).op ∈ (c.onRbsr cfg ix r k cs now).send) ∨
    (∃ W, i ∈ W ∧ (Msg.want W).op ∈ (c.onRbsr cfg ix r k cs now).send) ∨
    ∃ claims, (Msg.rbsr r k claims).op ∈ (c.onRbsr cfg ix r k cs now).send ∧
      ((.ids q ((within Prod.fst q (Conn.snap ix c r k)).map Prod.snd)) ∈ claims ∨
       ∃ q', .fp q' (fp Prod.fst Prod.snd sha256 (within Prod.fst q' (Conn.snap ix c r k))).1
          (fp Prod.fst Prod.snd sha256 (within Prod.fst q' (Conn.snap ix c r k))).2 ∈ claims ∧
        (∀ kk, q'.has kk = true → q.has kk = true) ∧ Diff Prod.fst Prod.snd (Conn.snap ix c r k) Y q' i ∧
        (within Prod.fst q' (Conn.snap ix c r k)).length + (within Prod.fst q' Y).length <
          (within Prod.fst q (Conn.snap ix c r k)).length + (within Prod.fst q Y).length) := by
  have hne : cs.isEmpty = false := by
    cases cs with
    | nil => cases hcl
    | cons _ _ => rfl
  rcases answer_step (P := cfg.params) _ Y q cl sX nm so hc i hd with ⟨xs, hxs, hi⟩ | ⟨xs, hxs, hi⟩ | hids | ⟨q', hq', hsub, hdq, hlt⟩
  · -- a have
    left
    have hh : i ∈ (cs.flatMap (answer Prod.fst Prod.snd sha256 cfg.params (c.snap ix r k))).flatMap
        (fun | .hold xs => xs | _ => [] : Out → List Id) :=
      List.mem_flatMap.2 ⟨_, List.mem_flatMap.2 ⟨cl, hcl, hxs⟩, hi⟩
    obtain ⟨H, hxH, -, hm⟩ := chunks_cover cfg _ (Msg.hold r) hmax hh
    refine ⟨H, hxH, ?_⟩
    unfold Conn.onRbsr
    simp only [has_of_mem hr, Bool.not_true, Bool.false_eq_true, ite_false, hne, Step.limit_send]
    split
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ hm)
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ hm)
  · -- a want
    right; left
    have hw : i ∈ (cs.flatMap (answer Prod.fst Prod.snd sha256 cfg.params (c.snap ix r k))).flatMap
        (fun | .want xs => xs | _ => [] : Out → List Id) :=
      List.mem_flatMap.2 ⟨_, List.mem_flatMap.2 ⟨cl, hcl, hxs⟩, hi⟩
    have hlen := answer_wants_len cfg.params (Conn.snap ix c r k) cs
    obtain ⟨W, hxW, -, hm⟩ := chunks_cover cfg _ Msg.want hmax (admit_mem cfg.maxKnown c.asked _ i hw ha
      (Nat.le_trans (Nat.add_le_add_left hlen _) hroom))
    refine ⟨W, hxW, ?_⟩
    unfold Conn.onRbsr
    simp only [has_of_mem hr, Bool.not_true, Bool.false_eq_true, ite_false, hne, Step.limit_send]
    split
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ hm)
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ hm)
  · -- an id claim over q
    right; right
    refine ⟨((cs.flatMap (answer Prod.fst Prod.snd sha256 cfg.params (c.snap ix r k))).filterMap
      (fun | .claim x => some x | _ => none : Out → Option Claim)), ?_, Or.inl ?_⟩
    · unfold Conn.onRbsr
      simp only [has_of_mem hr, Bool.not_true, Bool.false_eq_true, ite_false, hne, Step.limit_send]
      split <;> exact List.mem_cons_self ..
    · exact List.mem_filterMap.2 ⟨_, List.mem_flatMap.2 ⟨cl, hcl, hids⟩, rfl⟩
  · -- a fingerprint over a smaller piece
    right; right
    refine ⟨((cs.flatMap (answer Prod.fst Prod.snd sha256 cfg.params (c.snap ix r k))).filterMap
      (fun | .claim x => some x | _ => none : Out → Option Claim)), ?_, Or.inr ⟨q', ?_, hsub, hdq, hlt⟩⟩
    · unfold Conn.onRbsr
      simp only [has_of_mem hr, Bool.not_true, Bool.false_eq_true, ite_false, hne, Step.limit_send]
      split <;> exact List.mem_cons_self ..
    · exact List.mem_filterMap.2 ⟨_, List.mem_flatMap.2 ⟨cl, hcl, hq'⟩, rfl⟩

end Engine.World
