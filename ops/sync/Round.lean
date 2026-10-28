/-
One RBSR round, as Meyer's Protocol 1: claims about ranges go back and
forth until every range is settled.

- A claim is a range's fingerprint, or all of the claimant's ids in it.
- `answer` is what a side does with a claim, from its own items (a
  snapshot taken when the round began): a matching fingerprint settles
  the range; a range it holds few items in it answers with its ids; a
  range it holds many items in it is cut into up to `fan` pieces of
  nearly equal count, each claimed by its fingerprint. A claim of ids is
  answered with what this side holds that the claimant lacks (`hold`)
  and what it lacks (`want`).
- `exchange` runs a round to its end by composing the two sides'
  `answer`s, and returns what each side sends the other.

Laws:
- `exchange_complete`: from an honest opening claim over r, the round
  sends each side exactly the ids the other holds in r and it lacks, if
  fingerprints do not collide (`lbl_inj`).
- `exchange_ends`: the claims shrink: each piece of a range holds fewer
  of the cutting side's items, and no more of the other's, so a round
  over r ends within |X ∩ r| + |Y ∩ r| + 1 answers on any path.
-/
import Engine.Sync.Fp

namespace Engine.Sync

/-- A claim about a range: its fingerprint, or every id the claimant
holds in it. -/
inductive Claim where
  | fp (r : Range) (n : Nat) (l : ByteArray)
  | ids (r : Range) (xs : List ByteArray)
  deriving Inhabited

/-- What answering a claim produces: a claim back, ids this side holds
that the peer lacks, ids this side lacks. -/
inductive Out where
  | claim (c : Claim)
  | hold (xs : List ByteArray)
  | want (xs : List ByteArray)
  deriving Inhabited

/-- How a range is cut: ids are listed at `leaf` items or fewer;
otherwise it is cut into up to `fan` pieces. -/
structure Params where
  leaf : Nat := 128
  fan : Nat := 16
  leaf_pos : 0 < leaf := by decide
  fan_two : 2 ≤ fan := by decide

/-! ## Cutting a range -/

section
variable {α : Type} (key : α → Key)

/-- The items at positions k, k + s, k + 2s, … of l (0-based). -/
def pick (s : Nat) : Nat → List α → List α
  | _, [] => []
  | 0, a :: t => a :: pick s (s - 1) t
  | k + 1, _ :: t => pick s k t

theorem pick_sub (s : Nat) : ∀ (k : Nat) (l : List α), ∀ b ∈ pick s k l, b ∈ l
  | _, [] => by simp [pick]
  | 0, a :: t => by
    intro b hb
    simp only [pick, List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (pick_sub s _ t b hb)
  | k + 1, _ :: t => by
    intro b hb
    exact List.mem_cons_of_mem _ (pick_sub s k t b hb)

theorem pick_ne (s : Nat) : ∀ (k : Nat) (l : List α), k < l.length → pick s k l ≠ []
  | _, [], h => by simp at h
  | 0, a :: t, _ => by simp [pick]
  | k + 1, _ :: t, h => by
    simp only [pick]
    exact pick_ne s k t (by simp at h; omega)

/-- The ranges r is cut into at these keys: `[lo, c₁)`, `[c₁, c₂)`, …,
`[cₖ, hi)`. -/
def pieces (r : Range) : List Key → List Range
  | [] => [r]
  | c :: cs => ⟨r.lo, some c⟩ :: pieces ⟨c, r.hi⟩ cs

/-- Each piece starts at r's start or at a cut, and ends at r's end or
at a cut. -/
theorem pieces_ends : ∀ (cs : List Key) (r : Range), ∀ q ∈ pieces r cs,
    (q.lo = r.lo ∨ q.lo ∈ cs) ∧ (q.hi = r.hi ∨ ∃ c ∈ cs, q.hi = some c)
  | [], r => by intro q hq; simp [pieces] at hq; subst hq; simp
  | c :: cs, r => by
    intro q hq
    simp only [pieces, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact ⟨Or.inl rfl, Or.inr ⟨c, List.mem_cons_self .., rfl⟩⟩
    · obtain ⟨h1, h2⟩ := pieces_ends cs ⟨c, r.hi⟩ q hq
      refine ⟨?_, ?_⟩
      · rcases h1 with h1 | h1
        · exact Or.inr (by rw [h1]; exact List.mem_cons_self ..)
        · exact Or.inr (List.mem_cons_of_mem _ h1)
      · rcases h2 with h2 | ⟨c', hc', e⟩
        · exact Or.inl h2
        · exact Or.inr ⟨c', List.mem_cons_of_mem _ hc', e⟩

theorem has_iff (r : Range) (k : Key) :
    r.has k = true ↔ ¬ k < r.lo ∧ (∀ h, r.hi = some h → k < h) := by
  rcases r with ⟨lo, hi⟩
  cases hi <;> simp [Range.has]

/-- **The pieces cover r.** -/
theorem pieces_cover : ∀ (cs : List Key) (r : Range) (k : Key), r.has k = true →
    ∃ q ∈ pieces r cs, q.has k = true
  | [], r, k, hk => ⟨r, by simp [pieces], hk⟩
  | c :: cs, r, k, hk => by
    rw [has_iff] at hk
    by_cases hc : k < c
    · refine ⟨⟨r.lo, some c⟩, List.mem_cons_self .., ?_⟩
      rw [has_iff]; exact ⟨hk.1, fun h e => by cases e; exact hc⟩
    · obtain ⟨q, hq, hq'⟩ := pieces_cover cs ⟨c, r.hi⟩ k (by rw [has_iff]; exact ⟨hc, hk.2⟩)
      exact ⟨q, List.mem_cons_of_mem _ hq, hq'⟩

/-- **Each piece lies in r**, when every cut does. -/
theorem pieces_sub (cs : List Key) (r : Range) (hcs : ∀ c ∈ cs, r.has c = true) :
    ∀ q ∈ pieces r cs, ∀ k, q.has k = true → r.has k = true := by
  intro q hq k hk
  obtain ⟨h1, h2⟩ := pieces_ends cs r q hq
  rw [has_iff] at hk ⊢
  refine ⟨?_, ?_⟩
  · rcases h1 with h1 | h1
    · rw [← h1]; exact hk.1
    · intro hlo
      have := (has_iff r q.lo).mp (hcs _ h1)
      rcases Key.not_lt.mp hk.1 with h | h
      · exact this.1 (Key.lt_trans h hlo)
      · exact this.1 (h ▸ hlo)
  · intro hh e
    rcases h2 with h2 | ⟨c, hc, e2⟩
    · exact hk.2 hh (h2 ▸ e)
    · have := (has_iff r c).mp (hcs c hc)
      exact Key.lt_trans (hk.2 c e2) (this.2 hh e)

end

/-! ## Answering a claim -/

section
variable {α : Type} (key : α → Key) (ident : α → ByteArray) (h : ByteArray → ByteArray) (P : Params)

/-- These items in r. -/
def within (r : Range) (l : List α) : List α := l.filter fun a => r.has (key a)

/-- Whether an id is one of these items'. -/
def named (l : List α) (i : ByteArray) : Bool := l.any fun a => Decidable.decide (ident a = i)

/-- The run length that cuts n items into at most `fan` runs. -/
def runLen (n : Nat) : Nat := (n + P.fan - 1) / P.fan

/-- Where the items x of a range are cut: at every `runLen`-th item. -/
def cutsOf (x : List α) : List Key := (pick (runLen P x.length) (runLen P x.length) x).map key

/-- What this side, holding `mine`, answers to a claim. -/
def answer (mine : List α) : Claim → List Out
  | .fp r n l =>
    let x := within key r mine
    if fp key ident h x = (n, l) then []
    else if x.length ≤ P.leaf then [.claim (.ids r (x.map ident))]
    else (pieces r (cutsOf key P x)).map fun q => .claim (.fp q (fp key ident h (within key q mine)).1
      (fp key ident h (within key q mine)).2)
  | .ids r xs =>
    let x := within key r mine
    [.hold ((x.filter fun a => !xs.any fun i => Decidable.decide (ident a = i)).map ident),
     .want (xs.filter fun i => !named ident x i)]

/-- How a side opens a round over r. -/
def opening (mine : List α) (r : Range) : Claim :=
  let x := within key r mine
  if x.length ≤ P.leaf then .ids r (x.map ident) else .fp r (fp key ident h x).1 (fp key ident h x).2

/-- The ids an answer sends the peer, given what the peer's own round
from each claim sends (`sub`, as (peer → this side, this side → peer)). -/
def give (sub : Claim → List ByteArray × List ByteArray) : Out → List ByteArray
  | .hold xs => xs
  | .want _ => []
  | .claim c => (sub c).2

/-- The ids an answer gets from the peer. -/
def get (sub : Claim → List ByteArray × List ByteArray) : Out → List ByteArray
  | .hold _ => []
  | .want xs => xs
  | .claim c => (sub c).1

/-- A round from claim c, which X answers, run to its end within n
answers on any path: what X sends Y, and what Y sends X. -/
def exchange : Nat → List α → List α → Claim → List ByteArray × List ByteArray
  | 0, _, _, _ => ([], [])
  | n + 1, X, Y, c => (answer key ident h P X c).foldr
      (fun o acc => (give (exchange n Y X) o ++ acc.1, get (exchange n Y X) o ++ acc.2)) ([], [])

end

end Engine.Sync
