/-
Reading the index: one query shape for every list a screen shows.

A list is the Valid facts filed under a key (and, optionally, under
other keys too: a conjunction), in sort order (`SortKey`, ties by id),
within a range, newest or oldest first, at most `limit` of them. Its
answer also counts the matches inside the range (`inRange`, up to a
cap) and under the keys at all (`total`), so a screen can size what it
does not draw, and a badge can ask for counts alone (`limit = 0`).

`eval` is the meaning, over the model's tables; `listSql` is what runs,
on SQLite: the conjunct with the fewest rows (its counter row, kept
exact by a trigger) is walked as one index range, and each row is kept
if the other keys hold it too. The differential test checks the two
agree; QTests in the app checks it on real workloads.

Watching: every row the index gains is recorded, per connection, in a
temp table (`watchFiled`), so after a write the writer reads exactly the
keys it filed (`takeFiled`) and the op ids it decided.
-/
import Engine.Sqlite
import Engine.Model

namespace Engine

/-- Bytes compared as memcmp does: the first differing byte, then length. -/
def bcmp (a b : ByteArray) : Ordering := Id.run do
  let n := min a.size b.size
  for i in [0:n] do
    let x := a[i]!
    let y := b[i]!
    if x < y then return .lt
    if y < x then return .gt
  return compare a.size b.size

/-- A position in a list: a row's sort key and id. -/
abbrev Pos := ByteArray × Id

def Pos.cmp (p q : Pos) : Ordering := (bcmp p.1 q.1).then (bcmp p.2 q.2)

/-- What a list asks for. `after` and `before` bound the range,
exclusive; `desc` lists newest first; `limit` 0 asks for counts only;
`cap` bounds the range count (0: no cap). -/
structure ListQ where
  key : ByteArray
  also : List ByteArray := []
  after : Option Pos := none
  before : Option Pos := none
  desc : Bool := true
  limit : Nat := 0
  cap : Nat := 0
  deriving Inhabited, BEq, Hashable

structure Answer where
  rows : List Pos
  inRange : Nat
  total : Nat
  deriving Inhabited, BEq

def ListQ.inside (q : ListQ) (p : Pos) : Bool :=
  (match q.after with | some a => p.cmp a == .gt | none => true) &&
  (match q.before with | some b => p.cmp b == .lt | none => true)

/-! ## The meaning, over the model -/

section
variable {F : Type} [SortKey F]

def insertBy (p : Pos) : List Pos → List Pos
  | [] => [p]
  | q :: t => if p.cmp q == .gt then q :: insertBy p t else p :: q :: t

def sortPos (l : List Pos) : List Pos := l.foldr insertBy []

/-- The Valid ops under every key of q, with their positions, ascending. -/
def matching (s : DB F) (q : ListQ) : List Pos :=
  sortPos <| (s.idx q.key).filterMap fun x =>
    if q.also.all (fun k => has (s.idx k) x) then
      match s.status x with
      | some (.valid f) => some (SortKey.sortOf f, x)
      | _ => none
    else none

def capped (cap n : Nat) : Nat := if cap = 0 then n else min cap n

def eval (s : DB F) (q : ListQ) : Answer :=
  let all := matching s q
  let inR := all.filter q.inside
  let ordered := if q.desc then inR.reverse else inR
  ⟨ordered.take q.limit, capped q.cap inR.length, all.length⟩

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

def listSql {F} (q : ListQ) : SqlM F Answer := do
  let (k, others, n) ← pickWalk (F := F) q
  let (w, ps) := q.whereSql k others true
  let dir := if q.desc then "DESC" else "ASC"
  let rows ← if q.limit = 0 then pure #[] else
    sqlQ (F := F) s!"SELECT i.s, i.id FROM idx i WHERE {w} ORDER BY i.s {dir}, i.id {dir} LIMIT {q.limit}" ps
  let lim := if q.cap = 0 then "" else s!" LIMIT {q.cap}"
  let inR := natOf (← sqlQ (F := F) s!"SELECT CAST(count(*) AS TEXT) FROM (SELECT 1 FROM idx i WHERE {w}{lim})" ps)
  let total ← if others.isEmpty then pure n else do
    let (w2, ps2) := q.whereSql k others false
    pure (natOf (← sqlQ (F := F) s!"SELECT CAST(count(*) AS TEXT) FROM idx i WHERE {w2}" ps2))
  let pos := rows.toList.filterMap fun r => do pure ((← r[0]?), (← r[1]?))
  return ⟨pos, inR, total⟩

/-- The same list with each row's fact, read in the same statement (a
join on the verdicts' primary key): for lists whose rows are drawn
together, such as a message's reactions. -/
def listFactsSql {F} [Codec F] (q : ListQ) : SqlM F (Answer × List F) := do
  let a ← listSql (F := F) q
  if q.limit = 0 then return (a, [])
  let (k, others, _) ← pickWalk (F := F) q
  let (w, ps) := q.whereSql k others true
  let dir := if q.desc then "DESC" else "ASC"
  let rows ← sqlQ (F := F) s!"SELECT st.verdict FROM idx i JOIN status st ON st.id = i.id WHERE {w} ORDER BY i.s {dir}, i.id {dir} LIMIT {q.limit}" ps
  let fs := rows.toList.filterMap fun r => match r[0]? >>= Codec.decode with
    | some (Verdict.valid f) => some f
    | _ => none
  return (a, fs)

/-- The verdict of op x. -/
def getSql {F} [Codec F] (x : Id) : SqlM F (Option (Verdict F)) := do
  sqlOne "verdict" (← sqlQ (F := F) "SELECT verdict FROM status WHERE id = ?" #[x])

/-! ## Watching what a write filed -/

/-- Records, on this connection, every key the index gains and every op
decided (as the key `0xFF ++ id`). -/
def Db.watchFiled (db : Db) : IO Unit := db.exec "
CREATE TEMP TABLE IF NOT EXISTS filed (k BLOB NOT NULL);
CREATE TEMP TRIGGER IF NOT EXISTS filed_idx AFTER INSERT ON main.idx BEGIN
  INSERT INTO filed (k) VALUES (NEW.k);
END;
CREATE TEMP TRIGGER IF NOT EXISTS filed_status AFTER INSERT ON main.status BEGIN
  INSERT INTO filed (k) VALUES (X'FF' || NEW.id);
END;
"

/-- The watch key of op x's verdict. -/
def opKey (x : Id) : ByteArray := ByteArray.mk #[0xFF] ++ x

/-- The keys filed since the last call, each once. -/
def Db.takeFiled (db : Db) : IO (List ByteArray) := do
  let rows ← db.query "SELECT DISTINCT k FROM filed" #[]
  db.exec "DELETE FROM filed"
  return rows.toList.filterMap (·[0]?)

end Engine
