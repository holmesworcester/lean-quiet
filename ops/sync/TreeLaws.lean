/-
Claim trees, one hop (docs/SYNC.md, "Claim trees"): what a side's
answer to an honest claim does with an item of the two sides'
difference over the claim's range, proven of the running `answer`, the
function `Conn.onRbsr` runs. Either the answer settles it (a have of it,
or a want of it, when the claim listed ids), or it passes it on in a
claim of its own that is honest for the answering side: an id claim over
the same range, or a fingerprint over a piece of it that holds fewer of
the two sides' items (`answer_step`). Sound fingerprints rule out an
empty answer (`same_of_fp`). So every item of the difference is settled
within the tree's depth on its path, which `exchange_complete` bounds
linearly and `exchange_log` logarithmically (each cut divides by `fan`).
-/
import ops.sync.RoundLaws
namespace Engine.Sync.Tree
open Engine Engine.Sync

/-! ## How deep a claim tree goes: each cut divides by `fan` -/

section
variable {α : Type} {key : α → Key}

theorem pick_keys_gt (s : Nat) (a : α) : ∀ (k : Nat) (t : List α), Engine.Sync.Sorted key (a :: t) →
    ∀ c ∈ (pick s k t).map key, key a < c := by
  intro k t hs c hc
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hc
  exact (List.pairwise_cons.1 hs).1 b (pick_sub s k t b hb)

/-- Cut every s items, a list's items fall at most s into each piece. -/
theorem pieces_le_aux (s : Nat) (hs : 1 ≤ s) : ∀ (l pre : List α) (lo : Key) (hi : Option Key) (k : Nat),
    Engine.Sync.Sorted key (pre ++ l) → (∀ p ∈ pre, ∀ b ∈ l, key p < key b) → pre.length + k ≤ s →
    ∀ q ∈ pieces ⟨lo, hi⟩ ((pick s k l).map key), (within key q (pre ++ l)).length ≤ s := by
  intro l
  induction l with
  | nil =>
    intro pre lo hi k _ _ hk q hq
    simp only [pick, List.map_nil, pieces, List.mem_singleton] at hq
    subst hq
    have := List.length_filter_le (fun a => (Range.mk lo hi).has (key a)) (pre ++ [])
    simp only [List.append_nil] at this ⊢
    unfold within; omega
  | cons a t ih =>
    intro pre lo hi k hsort hlt hk q hq
    cases k with
    | zero =>
      simp only [pick, List.map_cons, pieces, List.mem_cons] at hq
      have hsa : Engine.Sync.Sorted key (a :: t) := (List.pairwise_append.1 hsort).2.1
      rcases hq with rfl | hq
      · -- the first piece holds only pre
        have : within key ⟨lo, some (key a)⟩ (pre ++ a :: t) = within key ⟨lo, some (key a)⟩ pre := by
          unfold within
          rw [List.filter_append]
          have hnil : (a :: t).filter (fun b => (Range.mk lo (some (key a))).has (key b)) = [] := by
            rw [List.filter_eq_nil_iff]
            intro b hb
            simp only [Range.has, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq,
              not_and]
            intro _ hlt'
            rcases List.mem_cons.1 hb with rfl | hb
            · exact Key.lt_irrefl _ hlt'
            · exact Key.lt_asymm ((List.pairwise_cons.1 hsa).1 b hb) hlt'
          rw [hnil, List.append_nil]
        rw [this]
        have := List.length_filter_le (fun b => (Range.mk lo (some (key a))).has (key b)) pre
        unfold within; omega
      · -- the rest: [a] is the next piece's prefix
        have hsub : ∀ q' ∈ pieces ⟨key a, hi⟩ ((pick s (s - 1) t).map key), ∀ kk, q'.has kk = true → ¬ kk < key a := by
          intro q' hq' kk hkk
          obtain ⟨h1, -⟩ := pieces_ends _ _ q' hq'
          rw [Engine.Sync.has_iff] at hkk
          rcases h1 with h1 | h1
          · rw [h1] at hkk; exact hkk.1
          · intro hk'; exact hkk.1 (Key.lt_trans hk' (pick_keys_gt s a (s - 1) t hsa _ h1))
        have heq : within key q (pre ++ a :: t) = within key q ([a] ++ t) := by
          unfold within
          rw [List.filter_append]
          have hnil : pre.filter (fun b => q.has (key b)) = [] := by
            rw [List.filter_eq_nil_iff]
            intro p hp hq'
            exact hsub q hq (key p) hq' (hlt p hp a (List.mem_cons_self ..))
          rw [hnil, List.nil_append]; rfl
        rw [heq]
        apply ih [a] (key a) hi (s - 1) (by simpa using hsa)
        · intro p hp b hb
          rw [List.mem_singleton] at hp; subst hp
          exact (List.pairwise_cons.1 hsa).1 b hb
        · simp; omega
        · exact hq
    | succ k =>
      simp only [pick] at hq
      have := ih (pre ++ [a]) lo hi k (by simpa using hsort) ?_ (by simp; omega) q hq
      · simpa using this
      · intro p hp b hb
        rcases List.mem_append.1 hp with hp | hp
        · exact hlt p hp b (List.mem_cons_of_mem _ hb)
        · rw [List.mem_singleton] at hp; subst hp
          exact (List.pairwise_cons.1 (List.pairwise_append.1 hsort).2.1).1 b hb


/-- A piece of a range cut at `cutsOf` holds at most a run of the
cutter's items: each cut divides by `fan`. -/
theorem pieces_le (P : Params) {X : List α} {r : Range} (sX : Engine.Sync.Sorted key X) :
    ∀ q ∈ pieces r (cutsOf key P (within key r X)),
      (within key q X).length ≤ runLen P (within key r X).length := by
  intro q hq
  have hcut : ∀ c ∈ cutsOf key P (within key r X), r.has c = true := by
    intro c hc
    simp only [cutsOf, List.mem_map] at hc
    obtain ⟨p, hp, rfl⟩ := hc
    exact (mem_within.mp (pick_sub _ _ _ p hp)).2
  have hsub := pieces_sub _ r hcut q hq
  have heq : within key q X = within key q (within key r X) := by
    unfold within
    rw [List.filter_filter]
    apply List.filter_congr
    intro a _
    cases hqa : q.has (key a)
    · simp
    · simp [hsub _ hqa]
  rw [heq]
  generalize hx : within key r X = x at hq
  have sx : Engine.Sync.Sorted key x := hx ▸ List.Pairwise.filter _ sX
  cases x with
  | nil => simp [within]
  | cons e0 rest =>
    have hf := P.fan_two
    have hs : 1 ≤ runLen P (e0 :: rest).length := by
      unfold runLen
      exact (Nat.le_div_iff_mul_le (by omega)).mpr (by simp only [List.length_cons, Nat.one_mul]; omega)
    have hcuts : cutsOf key P (e0 :: rest) =
        (pick (runLen P (e0 :: rest).length) (runLen P (e0 :: rest).length) (e0 :: rest)).map key := rfl
    rw [hcuts] at hq
    have := pieces_le_aux (key := key) _ hs (e0 :: rest) [] r.lo r.hi (runLen P (e0 :: rest).length)
      (by simpa using sx) (by simp) (by simp) q (by simpa using hq)
    simpa using this

/-- A run of at most `leaf · fan^(j+1)` items is at most `leaf · fan^j`. -/
theorem runLen_le (P : Params) {a j : Nat} (ha : a ≤ P.leaf * P.fan ^ (j + 1)) :
    runLen P a ≤ P.leaf * P.fan ^ j := by
  have hf := P.fan_two
  unfold runLen
  apply Nat.le_of_lt_succ
  rw [Nat.div_lt_iff_lt_mul (by omega)]
  rw [Nat.pow_succ, ← Nat.mul_assoc] at ha
  rw [Nat.succ_mul]
  omega

theorem fold_congr (s1 s2 : Claim → List ByteArray × List ByteArray) : ∀ (os : List Out),
    (∀ c, Out.claim c ∈ os → s1 c = s2 c) →
    os.foldr (fun o acc => (Engine.Sync.give s1 o ++ acc.1, Engine.Sync.get s1 o ++ acc.2)) ([], []) =
      os.foldr (fun o acc => (Engine.Sync.give s2 o ++ acc.1, Engine.Sync.get s2 o ++ acc.2)) ([], [])
  | [], _ => rfl
  | o :: os, hs => by
    simp only [List.foldr_cons]
    rw [fold_congr s1 s2 os (fun c hc => hs c (List.mem_cons_of_mem _ hc))]
    cases o with
    | claim c => simp only [Engine.Sync.give, Engine.Sync.get, hs c (List.mem_cons_self ..)]
    | hold xs => rfl
    | want xs => rfl

variable (ident : α → ByteArray) (h : ByteArray → ByteArray) (P : Params)

/-- An answer to ids ends the round: one answer deep on every path. -/
theorem exchange_ids_stable (n m : Nat) (X Y : List α) (r : Range) (xs : List ByteArray) :
    exchange key ident h P (n + 1) X Y (.ids r xs) = exchange key ident h P (m + 1) X Y (.ids r xs) := by
  simp only [exchange]
  apply fold_congr
  intro c hc
  simp [answer] at hc

/-- **A round's depth is logarithmic.** From a fingerprint over r that X
answers, where X holds at most `leaf · fanʲ` items of r and Y at most
`leaf · fanⁱ`, the round has ended after `i + j + 2` answers on every
path: any deeper bound computes the same exchange. -/
theorem exchange_stable : ∀ (n m : Nat) (X Y : List α) (r : Range) (cn : Nat) (cl : ByteArray) (i j : Nat),
    Engine.Sync.Sorted key X → Engine.Sync.Sorted key Y →
    (within key r X).length ≤ P.leaf * P.fan ^ j → (within key r Y).length ≤ P.leaf * P.fan ^ i →
    i + j + 2 ≤ n → n ≤ m →
    exchange key ident h P n X Y (.fp r cn cl) = exchange key ident h P m X Y (.fp r cn cl) := by
  intro n
  induction n with
  | zero => intros; omega
  | succ n ih =>
    intro m X Y r cn cl i j sX sY hX hY hn hm
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [exchange]
    apply fold_congr
    intro c hc
    by_cases hf : fp key ident h (within key r X) = (cn, cl)
    · simp [answer, hf] at hc
    by_cases hl : (within key r X).length ≤ P.leaf
    · simp [answer, hf, hl] at hc
      subst hc
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      exact exchange_ids_stable ident h P n' m' Y X r _
    · simp [answer, hf, hl] at hc
      obtain ⟨q, hq, rfl⟩ := hc
      have hl' : P.leaf < (within key r X).length := by omega
      obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := by
        cases j with
        | zero => simp at hX; omega
        | succ j => exact ⟨j, rfl⟩
      have h1 : (within key q Y).length ≤ P.leaf * P.fan ^ i :=
        Nat.le_trans (filter_len_le (fun a ha => (pieces_shrink (P := P) sX hl' q hq).2 _ ha)) hY
      have h2 : (within key q X).length ≤ P.leaf * P.fan ^ j :=
        Nat.le_trans (pieces_le P sX q hq) (runLen_le P hX)
      exact ih m Y X q _ _ j i sY sX h1 h2 (by omega) (by omega)

/-- **A round ends within `2k + 2` answers** when each side holds at most
`leaf · fanᵏ` items of the range: with the defaults (128, 16), 12 answers
for 134 million items. `exchange_complete`'s conclusion, at log depth. -/
theorem exchange_log (n : Nat) (X Y : List α) (r : Range) (c : Claim) (i j : Nat)
    (sX : Engine.Sync.Sorted key X) (sY : Engine.Sync.Sorted key Y) (nm : Engine.Sync.Named key ident (X ++ Y))
    (so : Sound key ident h X Y) (hc : Honest key ident h Y r c)
    (hX : (within key r X).length ≤ P.leaf * P.fan ^ j) (hY : (within key r Y).length ≤ P.leaf * P.fan ^ i)
    (hn : i + j + 2 ≤ n) (x : ByteArray) :
    (x ∈ (exchange key ident h P n X Y c).1 ↔
      named ident (within key r X) x = true ∧ named ident (within key r Y) x = false) ∧
    (x ∈ (exchange key ident h P n X Y c).2 ↔
      named ident (within key r Y) x = true ∧ named ident (within key r X) x = false) := by
  have hm := exchange_complete (key := key) (ident := ident) (h := h) (P := P)
    (max n ((within key r X).length + (within key r Y).length + 1)) X Y r c sX sY nm so hc (by omega) x
  have he : exchange key ident h P n X Y c =
      exchange key ident h P (max n ((within key r X).length + (within key r Y).length + 1)) X Y c := by
    cases c with
    | fp r' cn cl =>
      obtain ⟨rfl, -⟩ := hc
      exact exchange_stable ident h P n _ X Y r' cn cl i j sX sY hX hY hn (by omega)
    | ids r' xs =>
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      obtain ⟨m', hm'⟩ : ∃ m', max (n' + 1) ((within key r X).length + (within key r Y).length + 1) = m' + 1 :=
        ⟨max (n' + 1) ((within key r X).length + (within key r Y).length + 1) - 1, by omega⟩
      rw [hm']
      exact exchange_ids_stable ident h P n' m' X Y r' xs
  rw [he]
  exact hm

end

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
    (∃ xs, Out.hold xs ∈ answer key ident h P X c ∧ i ∈ xs ∧ named ident (within key q X) i = true) ∨
    (∃ xs, Out.want xs ∈ answer key ident h P X c ∧ i ∈ xs ∧ named ident (within key q Y) i = true) ∨
    ((∃ n l, c = .fp q n l) ∧ Out.claim (.ids q ((within key q X).map ident)) ∈ answer key ident h P X c) ∨
    ((∃ n l, c = .fp q n l) ∧ ∃ q', Out.claim (.fp q' (fp key ident h (within key q' X)).1 (fp key ident h (within key q' X)).2) ∈
        answer key ident h P X c ∧ (∀ k, q'.has k = true → q.has k = true) ∧ Diff key ident X Y q' i ∧
        (within key q' X).length + (within key q' Y).length < (within key q X).length + (within key q Y).length ∧
        (within key q' X).length ≤ runLen P (within key q X).length ∧ (within key q' Y).length ≤ (within key q Y).length ∧
        P.leaf < (within key q X).length) := by
  cases c with
  | ids r xs =>
    obtain ⟨rfl, rfl⟩ := hc
    simp only [answer, List.mem_cons, List.not_mem_nil, or_false]
    rcases hd with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      refine ⟨_, Or.inl rfl, ?_, h1⟩
      obtain ⟨a, ha, rfl⟩ := named_iff.1 h1
      refine List.mem_map.2 ⟨a, List.mem_filter.2 ⟨ha, ?_⟩, rfl⟩
      simp only [Bool.not_eq_true', List.any_eq_false, decide_eq_true_eq, List.mem_map]
      rintro _ ⟨b, hb, rfl⟩ e
      exact absurd (named_iff.2 ⟨b, hb, e.symm⟩) (by rw [h2]; simp)
    · right; left
      refine ⟨_, Or.inr rfl, ?_, h1⟩
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
        exact ⟨⟨n, l, rfl⟩, by simp [answer, hf, hl]⟩
      · right; right; right
        refine ⟨⟨n, l, rfl⟩, ?_⟩
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
        refine ⟨q', ?_, hsub, hdq, by omega, pieces_le P sX q' hq', hY, hl'⟩
        simp only [answer, hf, hl, ite_false]
        exact List.mem_map.2 ⟨q', hq', rfl⟩

end



end Engine.Sync.Tree
