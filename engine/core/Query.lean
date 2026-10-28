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
agree; QTests in the app checks it on real workloads.

Watching: every row the index gains, or a purge takes from it, is
recorded, per connection, in a temp table (`watchFiled`), so after a
write the writer reads exactly the keys it filed or unfiled
(`takeFiled`) and the op ids it decided or purged.
-/
import engine.core.Sqlite
import engine.core.Model

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
  /-- Whether whoever reads the answer uses its range count (`inRange`)
  beside its rows: what a watch on it must cover (`ListQ.watch`). -/
  counted : Bool := false
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

end

/-! ## What runs, on SQLite -/

/-- The rows filed under k: its counter row (0 if none). -/
def countOf {F} (k : ByteArray) : SqlM F Nat := do
  let rows ← sqlQ (F := F) "SELECT CAST(n AS TEXT) FROM cnt WHERE k = ?" #[k]
  return match rows[0]? >>= (·[0]?) with
    | some b => (String.fromUTF8? b >>= String.toNat?).getD 0
    | none => 0

def natOf (rows : Array (Array ByteArray)) : Nat :=
  match rows[0]? >>= (·[0]?) with
  | some b => (String.fromUTF8? b >>= String.toNat?).getD 0
  | none => 0

/-- The query's WHERE clause and parameters, walking key k. Every
statement here reads the index `idx_ks (k, s, id)` as one range. -/
def ListQ.whereSql (q : ListQ) (k : ByteArray) (others : List ByteArray) (range : Bool) :
    String × Array ByteArray := Id.run do
  let mut w := "i.k = ?"
  let mut ps := #[k]
  if range then
    if let some (s, x) := q.after then
      w := w ++ " AND (i.s, i.id) > (?, ?)"; ps := ps.push s |>.push x
    if let some (s, x) := q.before then
      w := w ++ " AND (i.s, i.id) < (?, ?)"; ps := ps.push s |>.push x
  for o in others do
    w := w ++ " AND EXISTS (SELECT 1 FROM idx j WHERE j.k = ? AND j.id = i.id)"
    ps := ps.push o
  return (w, ps)

/-- The conjunct with the fewest rows, and the others. -/
def pickWalk {F} (q : ListQ) : SqlM F (ByteArray × List ByteArray × Nat) := do
  let mut best := q.key
  let mut bestN ← countOf (F := F) q.key
  for k in q.also do
    let n ← countOf (F := F) k
    if n < bestN then best := k; bestN := n
  let all := q.key :: q.also
  return (best, all.filter (· != best), bestN)

/-- A list on SQLite: its rows with their facts in one statement (a join
on the verdicts' primary key), then its counts. -/
def listSql {F} [Codec F] (q : ListQ) : SqlM F (Answer F) := do
  let (k, others, n) ← pickWalk (F := F) q
  let (w, ps) := q.whereSql k others true
  let dir := if q.desc then "DESC" else "ASC"
  let lim := match q.limit with | none => "" | some n => s!" LIMIT {n}"
  let rows ← if q.limit = some 0 then pure #[] else
    sqlQ (F := F) s!"SELECT i.s, i.id, st.verdict FROM idx i JOIN status st ON st.id = i.id WHERE {w} ORDER BY i.s {dir}, i.id {dir}{lim}" ps
  let capSql := if q.cap = 0 then "" else s!" LIMIT {q.cap}"
  let inR := natOf (← sqlQ (F := F) s!"SELECT CAST(count(*) AS TEXT) FROM (SELECT 1 FROM idx i WHERE {w}{capSql})" ps)
  let total ← if others.isEmpty then pure n else do
    let (w2, ps2) := q.whereSql k others false
    pure (natOf (← sqlQ (F := F) s!"SELECT CAST(count(*) AS TEXT) FROM idx i WHERE {w2}" ps2))
  let pos := rows.toList.filterMap fun r => do
    match (← r[2]? >>= Codec.decode) with
    | Verdict.valid f => pure (((← r[0]?), (← r[1]?)), f)
    | .invalid => none
  return ⟨pos, inR, total⟩

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
