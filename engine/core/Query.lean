/-
Reading the index: one query shape for every list a screen shows.

A list is the Valid facts filed under a key (and, optionally, under
other keys too: a conjunction), in sort order (`SortKey`, ties by id),
within a range, newest or oldest first, at most `limit` of them. Its
answer also counts the matches inside the range (`inRange`, up to a
cap) and under the keys at all (`total`), so a screen can size what it
does not draw, and a badge can ask for counts alone (`limit = 0`).

Every row comes with its fact. `eval` is the meaning, over the model's
tables; `listSql` is what runs, on SQLite: the conjunct with the fewest rows (its counter row, kept
exact by a trigger) is walked as one index range, and each row is kept
if the other keys hold it too. The differential test checks the two
agree; QTests in the app checks it on real workloads. A read never
sorts: SQLite walks the index in the list's order, and what a read runs
is a few statements computed as data (`readPlan`), so its cost is a law
under a stated assumption about SQLite's B-trees (`SeekCost`): a one-key
read costs two seeks and a step and a seek per row it returns, however
long the list (`readPlan_cost`, `readPlan_cost_range`).

Watching: every row the index gains, or a purge takes from it, is
recorded, per connection, in a temp table (`watchFiled`), so after a
write the writer reads exactly the keys it filed or unfiled
(`takeFiled`) and the op ids it decided or purged.
-/
import engine.core.Sqlite
import engine.core.Model
import engine.core.Cost

namespace Engine

/-- Bytes from offset i on compared as memcmp does: the first differing
byte, then length. -/
def bcmpFrom (a b : ByteArray) (i : Nat) : Ordering :=
  if h : i < a.size ∧ i < b.size then
    if a[i] < b[i] then .lt else if b[i] < a[i] then .gt else bcmpFrom a b (i + 1)
  else compare a.size b.size
termination_by a.size - i

/-- Bytes compared as memcmp does: the first differing byte, then length. -/
def bcmp (a b : ByteArray) : Ordering := bcmpFrom a b 0

/-- A position in a list: a row's sort key and id. -/
abbrev Pos := ByteArray × Id

def Pos.cmp (p q : Pos) : Ordering := (bcmp p.1 q.1).then (bcmp p.2 q.2)

/-- What a list asks for. `after` and `before` bound the range,
exclusive; `desc` lists newest first; `limit` caps the rows (`none`: all
of them; `some 0`: counts only); `cap` bounds the range count (0: no
cap). -/
structure ListQ where
  key : ByteArray
  also : List ByteArray := []
  after : Option Pos := none
  before : Option Pos := none
  desc : Bool := true
  limit : Option Nat := some 0
  cap : Nat := 0
  deriving Inhabited, BEq, Hashable

/-- A list's answer: its rows, each a position with its Valid fact; the
matches inside the range (capped); the matches under the keys at all. -/
structure Answer (F : Type) where
  rows : List (Pos × F)
  inRange : Nat
  total : Nat
  deriving Inhabited, BEq

def ListQ.inside (q : ListQ) (p : Pos) : Bool :=
  (match q.after with | some a => p.cmp a == .gt | none => true) &&
  (match q.before with | some b => p.cmp b == .lt | none => true)

def ListQ.cut {α} (q : ListQ) (l : List α) : List α :=
  match q.limit with
  | none => l
  | some n => l.take n

/-! ## The meaning, over the model -/

section
variable {F : Type} [SortKey F]

def insertBy {α} (p : Pos × α) : List (Pos × α) → List (Pos × α)
  | [] => [p]
  | q :: t => if p.1.cmp q.1 == .gt then q :: insertBy p t else p :: q :: t

def sortPos {α} (l : List (Pos × α)) : List (Pos × α) := l.foldr insertBy []

/-! ### What runs: a merge sort

`sortPos` is an insertion sort, and the laws (`perm_sortPos`,
`mem_sortPos`, and through them every list's) are about it. It costs
O(n²) comparisons: a union of a thousand rows, newest first, is half a
million. What runs is the library's stable merge sort (`List.mergeSort`)
under the same comparison, through `@[csimp] sortPos_eq_fast`, proven:
positions compare as a total order (bytes lexicographically, `lexCmp`),
so inserting each row into the sorted rest puts it where the stable
merge sort does (`List.mergeSort_cons`). -/

/-- Byte lists compared lexicographically, a shorter prefix first:
what `bcmp` computes (`bcmp_eq_lexCmp`). -/
def lexCmp : List UInt8 → List UInt8 → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | x :: xs, y :: ys => if x < y then .lt else if y < x then .gt else lexCmp xs ys

theorem drop_data_nil {a : ByteArray} {i : Nat} (h : a.size ≤ i) : a.data.toList.drop i = [] :=
  List.drop_eq_nil_of_le (by simpa using h)

theorem drop_data_cons {a : ByteArray} {i : Nat} (h : i < a.size) :
    a.data.toList.drop i = a[i] :: a.data.toList.drop (i + 1) :=
  List.drop_eq_getElem_cons (by simpa using h)

theorem bcmpFrom_eq (a b : ByteArray) (i : Nat) (h : i ≤ a.size ∧ i ≤ b.size) :
    bcmpFrom a b i = lexCmp (a.data.toList.drop i) (b.data.toList.drop i) := by
  obtain ⟨h1, h2⟩ := h
  rw [bcmpFrom]
  by_cases hi : i < a.size ∧ i < b.size
  · rw [dite_eq_left hi, drop_data_cons hi.1, drop_data_cons hi.2, lexCmp,
      bcmpFrom_eq a b (i + 1) ⟨hi.1, hi.2⟩]
  · rw [dite_eq_right hi]
    by_cases ha : i < a.size
    · have hb : ¬ i < b.size := fun hb => hi ⟨ha, hb⟩
      rw [drop_data_cons ha, drop_data_nil (Nat.le_of_not_lt hb), lexCmp]
      exact Nat.compare_eq_gt.2 (by omega)
    · by_cases hb : i < b.size
      · rw [drop_data_nil (Nat.le_of_not_lt ha), drop_data_cons hb, lexCmp]
        exact Nat.compare_eq_lt.2 (by omega)
      · rw [drop_data_nil (Nat.le_of_not_lt ha), drop_data_nil (Nat.le_of_not_lt hb), lexCmp]
        exact Nat.compare_eq_eq.2 (by omega)
termination_by a.size - i

theorem bcmp_eq_lexCmp (a b : ByteArray) : bcmp a b = lexCmp a.data.toList b.data.toList := by
  rw [bcmp, bcmpFrom_eq a b 0 ⟨Nat.zero_le _, Nat.zero_le _⟩]
  simp

theorem lexCmp_swap : ∀ xs ys : List UInt8, lexCmp ys xs = (lexCmp xs ys).swap
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
    simp only [lexCmp]
    by_cases h1 : x < y
    · have : ¬ y < x := by simp only [UInt8.lt_iff_toNat_lt] at *; omega
      simp [h1, this]
    · by_cases h2 : y < x
      · simp [h1, h2]
      · simp [h1, h2, lexCmp_swap xs ys]

theorem lexCmp_eq : ∀ {xs ys : List UInt8}, lexCmp xs ys = .eq → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [lexCmp] at h
  | _ :: _, [], h => by simp [lexCmp] at h
  | x :: xs, y :: ys, h => by
    simp only [lexCmp] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i h1 h2
        have : x = y := by
          apply UInt8.toNat_inj.1
          simp only [UInt8.lt_iff_toNat_lt] at h1 h2; omega
        rw [this, lexCmp_eq h]

theorem lexCmp_trans : ∀ {xs ys zs : List UInt8}, lexCmp xs ys ≠ .gt → lexCmp ys zs ≠ .gt →
    lexCmp xs zs ≠ .gt
  | [], _, [], _, _ => by simp [lexCmp]
  | [], _, _ :: _, _, _ => by simp [lexCmp]
  | _ :: _, [], _, h, _ => by simp [lexCmp] at h
  | _ :: _, _ :: _, [], _, h => by simp [lexCmp] at h
  | x :: xs, y :: ys, z :: zs, h1, h2 => by
    simp only [lexCmp, UInt8.lt_iff_toNat_lt] at h1 h2 ⊢
    have hxy : x.toNat ≤ y.toNat := by
      apply Nat.le_of_not_lt; intro hc
      rw [if_neg (by omega), if_pos hc] at h1; exact h1 rfl
    have hyz : y.toNat ≤ z.toNat := by
      apply Nat.le_of_not_lt; intro hc
      rw [if_neg (by omega), if_pos hc] at h2; exact h2 rfl
    by_cases c1 : x.toNat < z.toNat
    · rw [if_pos c1]; simp
    · rw [if_neg c1, if_neg (by omega)]
      rw [if_neg (by omega), if_neg (by omega)] at h1
      rw [if_neg (by omega), if_neg (by omega)] at h2
      exact lexCmp_trans h1 h2

theorem bcmp_swap (a b : ByteArray) : bcmp b a = (bcmp a b).swap := by
  rw [bcmp_eq_lexCmp, bcmp_eq_lexCmp, lexCmp_swap]

theorem bcmp_eq {a b : ByteArray} (h : bcmp a b = .eq) : a = b := by
  rw [bcmp_eq_lexCmp] at h
  exact ByteArray.ext (Array.toList_inj.1 (lexCmp_eq h))

theorem bcmp_trans {a b c : ByteArray} (h1 : bcmp a b ≠ .gt) (h2 : bcmp b c ≠ .gt) : bcmp a c ≠ .gt := by
  rw [bcmp_eq_lexCmp] at *
  exact lexCmp_trans h1 h2

theorem bcmp_lt_trans {a b c : ByteArray} (h1 : bcmp a b = .lt) (h2 : bcmp b c ≠ .gt) : bcmp a c = .lt := by
  have hac := bcmp_trans (by rw [h1]; decide) h2
  cases e : bcmp a c
  · rfl
  · obtain rfl := bcmp_eq e
    have := bcmp_swap a b
    rw [h1] at this
    exact absurd this (by cases e' : bcmp b a <;> simp_all)
  · exact absurd e hac

theorem Pos.cmp_swap (p q : Pos) : q.cmp p = (p.cmp q).swap := by
  rw [Pos.cmp, Pos.cmp, bcmp_swap p.1, bcmp_swap p.2, Ordering.swap_then]

theorem Pos.cmp_trans {p q r : Pos} (h1 : p.cmp q ≠ .gt) (h2 : q.cmp r ≠ .gt) : p.cmp r ≠ .gt := by
  simp only [Pos.cmp, ne_eq, Ordering.then_eq_gt, not_or, not_and] at *
  obtain ⟨g1, e1⟩ := h1
  obtain ⟨g2, e2⟩ := h2
  cases a1 : bcmp p.1 q.1
  · have := bcmp_lt_trans a1 g2
    simp [this]
  · obtain hpq := bcmp_eq a1
    rw [hpq]
    refine ⟨g2, fun hq => ?_⟩
    exact bcmp_trans (e1 a1) (e2 hq)
  · exact absurd a1 g1

theorem Pos.cmp_eq {p q : Pos} (h : p.cmp q = .eq) : p = q := by
  simp only [Pos.cmp, Ordering.then_eq_eq] at h
  exact Prod.ext (bcmp_eq h.1) (bcmp_eq h.2)

theorem Pos.cmp_lt_le_trans {p q r : Pos} (h1 : p.cmp q = .lt) (h2 : q.cmp r ≠ .gt) : p.cmp r = .lt := by
  have hpr := Pos.cmp_trans (by rw [h1]; decide) h2
  cases e : p.cmp r
  · rfl
  · obtain rfl := Pos.cmp_eq e
    have := Pos.cmp_swap p q
    rw [h1] at this
    exact absurd this (by simp_all)
  · exact absurd e hpr

/-- p past y, and q not before p: q is past y. -/
theorem Pos.cmp_gt_of_le {p q y : Pos} (hpq : p.cmp q ≠ .gt) (hpy : p.cmp y = .gt) : q.cmp y = .gt := by
  have hyp : y.cmp p = .lt := by rw [Pos.cmp_swap p y, hpy]; rfl
  have := Pos.cmp_lt_le_trans hyp hpq
  rw [Pos.cmp_swap y q, this]; rfl

/-- `sortPos`'s comparison: p goes before q unless p's position is past q's. -/
def posLE {α} (p q : Pos × α) : Bool := !(p.1.cmp q.1 == .gt)

theorem posLE_iff {α} {p q : Pos × α} : posLE p q = true ↔ p.1.cmp q.1 ≠ .gt := by
  simp [posLE]

theorem posLE_trans {α} (p q r : Pos × α) (h1 : posLE p q) (h2 : posLE q r) : posLE p r :=
  posLE_iff.2 (Pos.cmp_trans (posLE_iff.1 h1) (posLE_iff.1 h2))

theorem posLE_total {α} (p q : Pos × α) : (posLE p q || posLE q p) = true := by
  rw [Bool.or_eq_true, posLE_iff, posLE_iff, Pos.cmp_swap p.1]
  cases p.1.cmp q.1 <;> simp

theorem insertBy_split {α} (a : Pos × α) :
    ∀ (l₁ l₂ : List (Pos × α)), (∀ b ∈ l₁, posLE a b = false) → (∀ b ∈ l₂, posLE a b = true) →
      insertBy a (l₁ ++ l₂) = l₁ ++ a :: l₂
  | [], [], _, _ => rfl
  | [], q :: t, _, h2 => by
    have := posLE_iff.1 (h2 q (List.mem_cons_self ..))
    simp [insertBy, this]
  | b :: t, l₂, h1, h2 => by
    have hb : a.1.cmp b.1 = .gt := by
      have := h1 b (List.mem_cons_self ..)
      simp only [posLE, Bool.not_eq_false', beq_iff_eq] at this
      exact this
    simp only [List.cons_append, insertBy, hb, beq_self_eq_true, ite_true]
    rw [insertBy_split a t l₂ (fun x hx => h1 x (List.mem_cons_of_mem _ hx)) h2]

/-- `sortPos`, as it runs: a stable merge sort. -/
def sortPosFast {α} (l : List (Pos × α)) : List (Pos × α) := l.mergeSort posLE

/-- **`sortPos` runs as a merge sort**, on every list. -/
@[csimp] theorem sortPos_eq_fast : @sortPos = @sortPosFast := by
  funext α l
  induction l with
  | nil => simp [sortPos, sortPosFast]
  | cons a t ih =>
    rw [sortPos, List.foldr_cons, ← sortPos, ih, sortPosFast]
    obtain ⟨l₁, l₂, hs, ht, hl⟩ := List.mergeSort_cons (le := posLE) posLE_trans posLE_total a t
    have hp := List.pairwise_mergeSort (le := posLE) posLE_trans posLE_total (a :: t)
    rw [hs, List.pairwise_append, List.pairwise_cons] at hp
    rw [sortPosFast, ht, hs]
    exact insertBy_split a l₁ l₂ (fun b hb => by simpa using hl b hb) (fun b hb => hp.2.1.1 b hb)

/-- The Valid ops under every key of q, with their positions and facts,
ascending. -/
def matching (s : DB F) (q : ListQ) : List (Pos × F) :=
  sortPos <| (s.idx q.key).filterMap fun x =>
    if q.also.all (fun k => has (s.idx k) x) then
      match s.status x with
      | some (.valid f) => some ((SortKey.sortOf f, x), f)
      | _ => none
    else none

def capped (cap n : Nat) : Nat := if cap = 0 then n else min cap n

def eval (s : DB F) (q : ListQ) : Answer F :=
  let all := matching s q
  let inR := all.filter (q.inside ·.1)
  let ordered := if q.desc then inR.reverse else inR
  ⟨q.cut ordered, capped q.cap inR.length, all.length⟩

/-- **A list's range, when it is all of the list, counts its total**
(capped): what lets a read take it from the counter (`listPlan`)
rather than walk the list. -/
theorem inRange_unbounded (s : DB F) {q : ListQ} (ha : q.after = none) (hb : q.before = none) :
    (eval s q).inRange = capped q.cap (eval s q).total := by
  have : (matching s q).filter (fun _ => true) = matching s q := List.filter_eq_self.2 (by simp)
  simp [eval, ListQ.inside, ha, hb, this]

end

/-! ## What runs, on SQLite

A list read is a few statements, each of one of three shapes (`Stmt`).
`listSql` computes them as data (`readPlan`) and runs exactly those, so
what is counted below is what runs. Every one is served by an index in
the order it reads (tests/engine/QueryDiff: SQLite's EXPLAIN QUERY PLAN
for each shows these indexes and no sort):
- `counter k`: k's row of `cnt` (its primary key), kept exact by a
  trigger: one seek.
- `rows k others after before desc limit`: k's rows of `idx` in (s, id)
  order (the index `idx_ks`), from one seek to the range's start, until
  `limit` are kept; each walked row is checked against each key of
  `others` (a seek of `idx`'s unique (k, id)), and each kept row is
  joined to its verdict (a seek of `status`'s primary key).
- `count k others after before cap`: as `rows`, counting, at most `cap`
  (0: all).
- `side k p above incl limit`: k's rows past p (`above`) or before it,
  p itself in or not (`incl`), counted, at most `limit`: one side of a
  range bounded on one side, for a count by its smaller side
  (`splitWalk`). -/

inductive Stmt where
  | counter (k : ByteArray)
  | rows (k : ByteArray) (others : List ByteArray) (after before : Option Pos) (desc : Bool)
      (limit : Option Nat)
  | count (k : ByteArray) (others : List ByteArray) (after before : Option Pos) (cap : Nat)
  | side (k : ByteArray) (p : Pos) (above incl : Bool) (limit : Option Nat)
  deriving Inhabited

/-- A WHERE clause and its parameters: key k, the range (after, before),
and each of `others` holding the row too. -/
def whereSql (k : ByteArray) (others : List ByteArray) (after before : Option Pos) :
    String × Array ByteArray := Id.run do
  let mut w := "i.k = ?"
  let mut ps := #[k]
  if let some (s, x) := after then
    w := w ++ " AND (i.s, i.id) > (?, ?)"; ps := ps.push s |>.push x
  if let some (s, x) := before then
    w := w ++ " AND (i.s, i.id) < (?, ?)"; ps := ps.push s |>.push x
  for o in others do
    w := w ++ " AND EXISTS (SELECT 1 FROM idx j WHERE j.k = ? AND j.id = i.id)"
    ps := ps.push o
  return (w, ps)

/-- A statement's SQL text and parameters. -/
def Stmt.sql : Stmt → String × Array ByteArray
  | .counter k => ("SELECT CAST(n AS TEXT) FROM cnt WHERE k = ?", #[k])
  | .rows k others after before desc limit =>
    let (w, ps) := whereSql k others after before
    let dir := if desc then "DESC" else "ASC"
    let lim := match limit with | none => "" | some n => s!" LIMIT {n}"
    (s!"SELECT i.s, i.id, st.verdict FROM idx i JOIN status st ON st.id = i.id WHERE {w} ORDER BY i.s {dir}, i.id {dir}{lim}", ps)
  | .count k others after before cap =>
    let (w, ps) := whereSql k others after before
    let capSql := if cap = 0 then "" else s!" LIMIT {cap}"
    (s!"SELECT CAST(count(*) AS TEXT) FROM (SELECT 1 FROM idx i WHERE {w}{capSql})", ps)
  | .side k p above incl limit =>
    let op := if above then (if incl then ">=" else ">") else (if incl then "<=" else "<")
    let lim := match limit with | none => "" | some n => s!" LIMIT {n}"
    (s!"SELECT CAST(count(*) AS TEXT) FROM (SELECT 1 FROM idx i WHERE i.k = ? AND (i.s, i.id) {op} (?, ?){lim})",
      #[k, p.1, p.2])

def Stmt.run {F} (st : Stmt) : SqlM F (Array (Array ByteArray)) :=
  let (sql, ps) := st.sql
  sqlQ (F := F) sql ps

def natOf (rows : Array (Array ByteArray)) : Nat :=
  match rows[0]? >>= (·[0]?) with
  | some b => (String.fromUTF8? b >>= String.toNat?).getD 0
  | none => 0

/-- The rows filed under k: its counter row (0 if none). -/
def countOf {F} (k : ByteArray) : SqlM F Nat := do
  return natOf (← (Stmt.counter k).run (F := F))

/-- The first key with the fewest rows: what a conjunction walks. -/
def pickMin : ByteArray × Nat → List (ByteArray × Nat) → ByteArray × Nat
  | best, [] => best
  | best, kn :: rest => pickMin (if kn.2 < best.2 then kn else best) rest

/-- **A conjunction walks its smallest conjunct**: the key `pickMin`
picks has no more rows than any key of the conjunction. -/
theorem pickMin_le : ∀ (best : ByteArray × Nat) (rest : List (ByteArray × Nat)),
    ∀ kn ∈ best :: rest, (pickMin best rest).2 ≤ kn.2
  | best, [], kn, h => by simp at h; subst h; exact Nat.le_refl _
  | best, x :: rest, kn, h => by
    have ih := pickMin_le (if x.2 < best.2 then x else best) rest
    have hb : (if x.2 < best.2 then x else best).2 ≤ best.2 := by split <;> omega
    have hx : (if x.2 < best.2 then x else best).2 ≤ x.2 := by split <;> omega
    simp only [pickMin]
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.le_trans (ih _ (List.mem_cons_self ..)) hb
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.le_trans (ih _ (List.mem_cons_self ..)) hx
    · exact ih kn (List.mem_cons_of_mem _ h)

/-- The conjunct with the fewest rows (by its counter), and the others. -/
def pickWalk {F} (q : ListQ) : SqlM F (ByteArray × List ByteArray × Nat) := do
  let n ← countOf (F := F) q.key
  let ns ← q.also.mapM fun k => do pure (k, ← countOf (F := F) k)
  let (best, bestN) := pickMin (q.key, n) ns
  return (best, (q.key :: q.also).filter (· != best), bestN)

/-- What a list runs once it has chosen the key it walks (k, with n
rows): its rows (none when it asks counts only), the range's count (none
when the range is all of k and nothing else filters: then it is n,
capped; or when it is counted by its smaller side, `split`), and the
total (none when nothing else filters: then it is n). -/
structure Plan where
  rows : Option Stmt
  inRange : Option Stmt
  /-- A range bounded on one side, uncapped, of k alone: counted by its
  smaller side (`splitWalk`), as its bound and whether it is above it. -/
  split : Option (ByteArray × Pos × Bool)
  total : Option Stmt

/-- A range of k alone, uncapped, bounded on one side: its bound, and
whether the range is above it. -/
def splitOf (q : ListQ) (others : List ByteArray) : Option (Pos × Bool) :=
  if others.isEmpty && q.cap == 0 then
    match q.after, q.before with
    | some a, none => some (a, true)
    | none, some b => some (b, false)
    | _, _ => none
  else none

def listPlan (q : ListQ) (k : ByteArray) (others : List ByteArray) : Plan where
  rows := if q.limit = some 0 then none else some (.rows k others q.after q.before q.desc q.limit)
  inRange := if (q.after.isNone && q.before.isNone && others.isEmpty) || (splitOf q others).isSome then none
    else some (.count k others q.after q.before q.cap)
  split := (splitOf q others).map fun (p, above) => (k, p, above)
  total := if others.isEmpty then none else some (.count k others none none 0)

def Plan.stmts (p : Plan) : List Stmt := p.rows.toList ++ p.inRange.toList ++ p.total.toList

/-- Everything a read of q runs, walking k: a counter for each key of q,
then its plan; and, for a split count, its walk (`splitWalk_cost`). -/
def readPlan (q : ListQ) (k : ByteArray) (others : List ByteArray) : List Stmt :=
  (q.key :: q.also).map .counter ++ (listPlan q k others).stmts

/-- How far a split count's first walk goes; each next goes twice as
far. -/
def walk0 : Nat := 64

/-- The doublings before a split count walks its range whole (64: past
any store). -/
def walkFuel : Nat := 64

/-- **A count by its smaller side.** A range bounded on one side splits
k's rows in two: the range and the rest. Count each, at most L, in turn,
L doubling, until one comes back under L: that one is exact, and the
range's count is it or the total less it (`splitWalk_exact`), for a
walk of about the smaller side (`splitWalk_cost`). `cnt true l` counts
the range, `cnt false l` the rest, at most l (none: all). -/
def splitWalk {m : Type → Type} [Monad m] (cnt : Bool → Option Nat → m Nat) (total : Nat) :
    Nat → Nat → m Nat
  | 0, _ => cnt true none
  | fuel + 1, L => do
    let a ← cnt true (some L)
    if a < L then return a
    let b ← cnt false (some L)
    if b < L then return total - b
    splitWalk cnt total fuel (2 * L)

/-- The range's count of a plan, given how to run a count statement: by
its smaller side when split (the range above or below p, the rest
across it, p included), else its statement, else the counter (n). -/
def Plan.countWith {m : Type → Type} [Monad m] (p : Plan) (cnt : Stmt → m Nat) (cap n : Nat) : m Nat :=
  match p.split, p.inRange with
  | some (k, b, above), _ =>
    splitWalk (fun s l => cnt (.side k b (if s then above else !above) (!s) l)) n walkFuel walk0
  | none, some st => cnt st
  | none, none => pure (capped cap n)

/-- A list on SQLite: its plan, run (`readPlan`). -/
def listSql {F} [Codec F] (q : ListQ) : SqlM F (Answer F) := do
  let (k, others, n) ← pickWalk (F := F) q
  let p := listPlan q k others
  let rows ← match p.rows with | some st => st.run (F := F) | none => pure #[]
  let inR ← p.countWith (fun st => do pure (natOf (← st.run (F := F)))) q.cap n
  let total ← match p.total with | some st => do pure (natOf (← st.run (F := F))) | none => pure n
  let pos := rows.toList.filterMap fun r => do
    match (← r[2]? >>= Codec.decode) with
    | Verdict.valid f => pure (((← r[0]?), (← r[1]?)), f)
    | .invalid => none
  return ⟨pos, inR, total⟩

/-! ## What a read costs

**The assumption** (`SeekCost`: docs/PERF.md's SQLite assumption,
`levels`, not proven): a seek costs at most c·(log₂ N + 1) for N rows,
and each next row of an index, in its order, at most `step`; a statement that reads in its
index's order with a LIMIT and nothing else filtering walks no row past
its limit, and a range bound is a seek, not a filter (`Stmt.walks`; the
join on `status` filters nothing, as every row of `idx` is a decided
op's). tests/engine/QueryDiff checks each statement's plan is such a
walk: an index search on the range, never a scan, never a sort. A
statement's cost is then counted on the rows it walks (`Stmt.cost`), m
being the rows under the key it walks (which the counters make the
smallest conjunct: `pickMin_le`).

The laws: a one-key read costs two seeks and, per row it returns, a step
and a seek, whatever m is (`readPlan_cost`): the range's count and the
total come from the counter. With a range, a capped count adds its cap
(`readPlan_cost_range`). A range of one key bounded on one side, with
no cap, is counted by its smaller side: about min(range, rest) rows
(`splitWalk_cost`, below). What is left walks the range, O(m) and no
more (`readPlan_cost_le`): a range bounded on both sides with no cap,
and a conjunction (its rows, as kept rows are not the walked ones, its
range's count and its total). -/

structure SeekCost where
  c : Nat
  step : Nat
  /-- The rows of the largest B-tree. -/
  N : Nat

/-- A seek's cost: c·(log₂ N + 1), c a page visit's (`levels`). -/
def SeekCost.seek (c : SeekCost) : Nat := c.c * levels c.N

/-- The most rows a statement walks when its key's range holds m rows:
up to its limit (or cap) when nothing else filters, else all of them. -/
def Stmt.walks (m : Nat) : Stmt → Nat
  | .counter _ => 0
  | .rows _ others _ _ _ (some n) => if others.isEmpty then min n m else m
  | .rows _ _ _ _ _ none => m
  | .count _ others _ _ cap => if others.isEmpty && cap != 0 then min cap m else m
  | .side _ _ _ _ (some n) => min n m
  | .side _ _ _ _ none => m

/-- A statement's cost: its seek, then per row walked a step and a seek
for each key it checks (and, for rows, the verdict's seek). -/
def Stmt.cost (c : SeekCost) (m : Nat) (st : Stmt) : Nat :=
  match st with
  | .counter _ => c.seek
  | .rows _ others _ _ _ _ => c.seek + st.walks m * (c.step + (others.length + 1) * c.seek)
  | .count _ others _ _ _ => c.seek + st.walks m * (c.step + others.length * c.seek)
  | .side .. => c.seek + st.walks m * c.step

def planCost (c : SeekCost) (m : Nat) (ss : List Stmt) : Nat := (ss.map (·.cost c m)).sum

/-- **A one-key read costs its limit, not its list**: with no other key
and no range, reading q costs two seeks and, per row it returns, a step
and a seek, however many rows the list holds (m). -/
theorem readPlan_cost (c : SeekCost) (m n : Nat) {q : ListQ} (ha : q.also = []) (hr : q.after = none)
    (hb : q.before = none) (hl : q.limit = some n) :
    planCost c m (readPlan q q.key []) ≤ 2 * c.seek + n * (c.step + c.seek) := by
  have hw := Nat.mul_le_mul_right (c.step + c.seek) (Nat.min_le_left n m)
  by_cases h0 : n = 0
  · subst h0
    simp [readPlan, listPlan, splitOf, Plan.stmts, planCost, ha, hr, hb, hl, Stmt.cost]
    omega
  · simp [readPlan, listPlan, splitOf, Plan.stmts, planCost, ha, hr, hb, hl, h0, Stmt.cost, Stmt.walks]
    omega

/-- **With a range, a capped count adds at most its cap.** -/
theorem readPlan_cost_range (c : SeekCost) (m n : Nat) {q : ListQ} (ha : q.also = [])
    (hl : q.limit = some n) (hc : q.cap ≠ 0) :
    planCost c m (readPlan q q.key []) ≤ 3 * c.seek + n * (c.step + c.seek) + q.cap * c.step := by
  rcases q with ⟨key, also, after, before, desc, limit, cap⟩
  simp only at ha hl hc ⊢
  subst ha hl
  have hw := Nat.mul_le_mul_right (c.step + c.seek) (Nat.min_le_left n m)
  have hm := Nat.mul_le_mul_right c.step (Nat.min_le_left cap m)
  cases after <;> cases before <;> by_cases h0 : n = 0 <;>
    simp [readPlan, listPlan, splitOf, Plan.stmts, planCost, Stmt.cost, Stmt.walks, h0, hc] <;> omega

theorem Stmt.walks_le (m : Nat) (st : Stmt) : st.walks m ≤ m := by
  unfold Stmt.walks
  split
  · exact Nat.zero_le _
  · split
    · exact Nat.min_le_right _ _
    · exact Nat.le_refl _
  · exact Nat.le_refl _
  · split
    · exact Nat.min_le_right _ _
    · exact Nat.le_refl _
  · exact Nat.min_le_right _ _
  · exact Nat.le_refl _

/-- One statement of a plan walking k, checking `others`. -/
theorem plan_stmt_cost (c : SeekCost) (m : Nat) {q : ListQ} {k : ByteArray} {others : List ByteArray}
    {st : Stmt} (h : st ∈ (listPlan q k others).stmts) :
    st.cost c m ≤ c.seek + m * (c.step + (others.length + 1) * c.seek) := by
  have hw := Stmt.walks_le m st
  simp only [Plan.stmts, listPlan, List.mem_append, Option.mem_toList] at h
  rcases h with (h | h) | h <;> (split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h) <;>
    subst h <;> simp only [Stmt.cost] at hw ⊢ <;>
    (apply Nat.add_le_add_left; apply Nat.mul_le_mul hw; apply Nat.add_le_add_left;
     apply Nat.mul_le_mul_right; omega)

/-- **No read walks more than its range**: every read costs a seek per
key, and at most three walks of the m rows under the key it walks, each
row a step and a seek per key it checks. -/
theorem readPlan_cost_le (c : SeekCost) (m : Nat) (q : ListQ) (k : ByteArray) (others : List ByteArray) :
    planCost c m (readPlan q k others) ≤
      (q.also.length + 1) * c.seek + 3 * (c.seek + m * (c.step + (others.length + 1) * c.seek)) := by
  have hst := fun st (h : st ∈ (listPlan q k others).stmts) => plan_stmt_cost c m h
  generalize c.seek + m * (c.step + (others.length + 1) * c.seek) = B at hst ⊢
  have hl : (listPlan q k others).stmts.length ≤ 3 := by
    have one : ∀ o : Option Stmt, o.toList.length ≤ 1 := fun o => by cases o <;> simp
    have h1 := one (listPlan q k others).rows
    have h2 := one (listPlan q k others).inRange
    have h3 := one (listPlan q k others).total
    simp only [Plan.stmts, List.length_append]
    omega
  have hs : ∀ l : List Stmt, (∀ st ∈ l, st.cost c m ≤ B) → (l.map (·.cost c m)).sum ≤ l.length * B := by
    intro l h
    induction l with
    | nil => simp
    | cons x t ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
      have := h x (List.mem_cons_self ..)
      have := ih fun st hst => h st (List.mem_cons_of_mem _ hst)
      omega
  have hc : ∀ l : List ByteArray, ((l.map Stmt.counter).map (·.cost c m)).sum = l.length * c.seek := by
    intro l; induction l with
    | nil => simp
    | cons x t ih =>
      rw [List.map_cons, List.map_cons, List.sum_cons, ih, List.length_cons, Nat.succ_mul]
      simp only [Stmt.cost]
      omega
  have h1 := hs _ hst
  have h2 := Nat.mul_le_mul_right B hl
  have h3 := hc (q.key :: q.also)
  simp only [List.length_cons] at h3
  simp only [planCost, readPlan, List.map_append, List.sum_append]
  omega

/-! ### A count by its smaller side

A range of one key bounded on one side, uncapped (a window's "newer than
the anchor"; "older" is the total less it), is counted by `splitWalk`.
Its cost is counted by running it as it runs, with a count of a side
that walks at most its limit of that side's rows (`SeekCost`): the
range holds r rows and the rest c, and each count is a statement
(`sideCount`). -/

/-- A count as `SeekCost` counts it: a statement, and at most its limit
of its side's rows (the range's r, or the rest's c). -/
def sideCount (r c : Nat) (s : Bool) (l : Option Nat) : StateM (Nat × Nat) Nat := do
  let n := if s then r else c
  let w := match l with | some L => min L n | none => n
  modify fun (calls, walked) => (calls + 1, walked + w)
  pure w

/-- A count, run: its rows, one statement more, its rows walked. -/
theorem sideCount_run (r c : Nat) (s : Bool) (l : Option Nat) (st : Nat × Nat) :
    (sideCount r c s l).run st =
      let w := match l with | some L => min L (if s then r else c) | none => if s then r else c
      (w, (st.1 + 1, st.2 + w)) := rfl

/-- Id's bind is application. -/
theorem id_bind {α β : Type} (x : α) (f : α → _root_.Id β) : (x >>= f : _root_.Id β) = f x := rfl

/-- **A split count is exact**: the range's r, whatever the walk's
start and its fuel. -/
theorem splitWalk_exact (r c : Nat) : ∀ (fuel L : Nat) (st : Nat × Nat),
    ((splitWalk (sideCount r c) (r + c) fuel L).run st).1 = r
  | 0, _, _ => rfl
  | fuel + 1, L, st => by
    simp only [splitWalk, StateT.run_bind, sideCount_run, id_bind]
    by_cases ha : min L r < L
    · simp only [ha, ite_true]; show min L r = r; omega
    · simp only [ite_true, ha, ite_false, StateT.run_bind, sideCount_run, id_bind, Bool.false_eq_true]
      by_cases hb : min L c < L
      · simp only [hb, ite_true]; show r + c - min L c = r; omega
      · simp only [hb, ite_false]
        exact splitWalk_exact r c fuel (2 * L) _

/-- What a split count adds to its statements and rows walked: two
statements a doubling, and about the smaller side's rows. -/
theorem splitWalk_steps (r c : Nat) : ∀ (fuel L k : Nat) (st : Nat × Nat), 0 < L →
    min r c < L * 2 ^ k → k < fuel →
    ((splitWalk (sideCount r c) (r + c) fuel L).run st).2.1 ≤ st.1 + 2 * k + 2 ∧
      ((splitWalk (sideCount r c) (r + c) fuel L).run st).2.2 ≤
        st.2 + (if min r c < L then L + min r c else 7 * min r c - 2 * L)
  | 0, _, _, _, _, _, hk => absurd hk (Nat.not_lt_zero _)
  | fuel + 1, L, k, st, hL, hμ, hk => by
    simp only [splitWalk, StateT.run_bind, sideCount_run, id_bind]
    by_cases ha : min L r < L
    · simp only [ite_true, ha]
      show st.1 + 1 ≤ _ ∧ st.2 + min L r ≤ _
      constructor
      · omega
      · split <;> omega
    · simp only [ite_true, ha, ite_false, StateT.run_bind, sideCount_run, id_bind, Bool.false_eq_true]
      by_cases hb : min L c < L
      · simp only [hb, ite_true]
        show st.1 + 1 + 1 ≤ _ ∧ st.2 + min L r + min L c ≤ _
        constructor
        · omega
        · split <;> omega
      · simp only [hb, ite_false]
        have hrL : L ≤ r := by omega
        have hcL : L ≤ c := by omega
        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := by
          cases k with
          | zero => simp at hμ; omega
          | succ k' => exact ⟨k', rfl⟩
        have hμ' : min r c < 2 * L * 2 ^ k' := by
          rw [Nat.pow_succ] at hμ
          rw [Nat.mul_comm 2 L, Nat.mul_assoc, Nat.mul_comm 2 (2 ^ k')]
          exact hμ
        have ih := splitWalk_steps r c fuel (2 * L) k' (st.1 + 1 + 1, st.2 + min L r + min L c) (by omega)
          hμ' (by omega)
        have e1 : min L r = L := Nat.min_eq_left hrL
        have e2 : min L c = L := Nat.min_eq_left hcL
        rw [e1, e2] at ih ⊢
        have hn : ¬ min r c < L := by omega
        rw [ite_eq_right_iff.2 (fun h => absurd h hn)]
        constructor
        · simp only at ih; omega
        · simp only at ih; split at ih <;> omega

/-- **A split count walks about its smaller side**: for any k with
min r c < L·2^k (k doublings reach past the smaller side; k < fuel),
it runs at most 2k + 2 statements and walks at most L + 7·min r c rows,
however many the range or the rest holds. -/
theorem splitWalk_cost (r c fuel L k : Nat) (hL : 0 < L) (hμ : min r c < L * 2 ^ k) (hk : k < fuel) :
    let st := ((splitWalk (sideCount r c) (r + c) fuel L).run (0, 0)).2
    st.1 ≤ 2 * k + 2 ∧ st.2 ≤ L + 7 * min r c := by
  have h := splitWalk_steps r c fuel L k (0, 0) hL hμ hk
  simp only [Nat.zero_add] at h
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  split at h2 <;> omega

/-- **A one-bound uncapped count of one key is split**: its plan counts
it by its smaller side, and runs it as `splitWalk` does. -/
theorem listPlan_split {q : ListQ} (k : ByteArray) (hc : q.cap = 0) {b : Pos} {above : Bool}
    (hb : (q.after = some b ∧ q.before = none ∧ above = true) ∨
      (q.after = none ∧ q.before = some b ∧ above = false)) :
    (listPlan q k []).split = some (k, b, above) := by
  rcases hb with ⟨ha, hb, rfl⟩ | ⟨ha, hb, rfl⟩ <;> simp [listPlan, splitOf, ha, hb, hc]

theorem countWith_split {m : Type → Type} [Monad m] {p : Plan} {k : ByteArray} {b : Pos} {above : Bool}
    (h : p.split = some (k, b, above)) (cnt : Stmt → m Nat) (cap n : Nat) :
    p.countWith cnt cap n =
      splitWalk (fun s l => cnt (.side k b (if s then above else !above) (!s) l)) n walkFuel walk0 := by
  unfold Plan.countWith
  simp only [h]

/-! ## The one read -/

/-- Where lists are read: the model (its meaning) or SQLite (what runs).
Every read a screen or the network makes is a list. -/
class Lists (F : outParam Type) (m : Type → Type) where
  list : ListQ → m (Answer F)

instance {F} [SortKey F] : Lists F (Model F) where
  list q := fun s => (eval s q, s)

instance {F} [Codec F] [SortKey F] : Lists F (SqlM F) where
  list q := listSql q

theorem run_list {F} [SortKey F] (q : ListQ) (s : DB F) :
    (Lists.list q : Model F (Answer F)).run s = (eval s q, s) := rfl

/-! ## Watching what a write filed -/

/-- Records, on this connection, every key the index gains or a purge
takes a row from, and every op decided or purged (as the key
`0xFF ++ id`). -/
def Db.watchFiled (db : Db) : IO Unit := db.exec "
CREATE TEMP TABLE IF NOT EXISTS filed (k BLOB NOT NULL);
CREATE TEMP TRIGGER IF NOT EXISTS filed_idx AFTER INSERT ON main.idx BEGIN
  INSERT INTO filed (k) VALUES (NEW.k);
END;
CREATE TEMP TRIGGER IF NOT EXISTS filed_status AFTER INSERT ON main.status BEGIN
  INSERT INTO filed (k) VALUES (X'FF' || NEW.id);
END;
CREATE TEMP TRIGGER IF NOT EXISTS unfiled_idx AFTER DELETE ON main.idx BEGIN
  INSERT INTO filed (k) VALUES (OLD.k);
END;
CREATE TEMP TRIGGER IF NOT EXISTS unfiled_status AFTER DELETE ON main.status BEGIN
  INSERT INTO filed (k) VALUES (X'FF' || OLD.id);
END;
"


/-- The keys filed since the last call, each once. -/
def Db.takeFiled (db : Db) : IO (List ByteArray) := do
  let rows ← db.query "SELECT DISTINCT k FROM filed" #[]
  db.exec "DELETE FROM filed"
  return rows.toList.filterMap (·[0]?)

end Engine
