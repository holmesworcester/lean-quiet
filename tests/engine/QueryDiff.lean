/-
The list query on SQLite (`listSql`) against its meaning on the model
(`eval`), over a chat community: users joined by invitation, posts at
random times (ties included) with attachments, profiles and reactions,
some forged. For every message and user, and for whole-community lists,
it asks for pages in both directions, from cursors, bounded on both
sides, capped, counts only, and conjunctions (messages by one author),
and compares answers exactly. And the sort that runs for `sortPos` (a
merge sort, `sortPos_eq_fast`) against the insertion sort as written, on
random lists with ties, with `bcmp` against list order. It also checks that the filed keys a
write reports are exactly the keys its new index rows went under.
-/
import tests.engine.Lib

open Engine Community Tests Codec

def C := ed25519

structure World where
  ops : Array Op := #[]
  posts : Array Id := #[]
  users : Array (Id × Id × Device) := #[]

def build (seed : Nat) (nUsers nPosts : Nat) : Array Op × Id × Array Id × Array (Id × Id × Device) := Id.run do
  let f := Device.named s!"founder-{seed}"
  let r := root f
  let c := r.id
  let mut ops := #[r]
  -- Each user: the op admitting it (what its ops cite), its user id
  -- (the request's), and its device.
  let mut users : Array (Id × Id × Device) := #[(c, c, f)]
  for i in [0:nUsers] do
    let b := Device.named s!"bearer-{seed}-{i}"
    let d := Device.named s!"user-{seed}-{i}"
    let inv := invite c c f b.pk false
    let rq := request c inv.id d b.sk
    let ok := approve c rq.id c f
    let j := admit c rq.id [ok.id]
    ops := ops.push inv |>.push rq |>.push ok |>.push j
    users := users.push (j.id, rq.id, d)
  let mut g : Rng := ⟨seed.toUInt64⟩
  let mut posts : Array Id := #[]
  for i in [0:nPosts] do
    let (ui, g1) := g.below users.size
    let (tm, g2) := g1.below 50
    let (kind, g3) := g2.below 10
    g := g3
    let (u, _, d) := users[ui]!
    if kind < 6 then
      let o := post c u d "k".toUTF8 s!"post {i}".toUTF8 tm
      ops := ops.push o
      posts := posts.push o.id
    else if kind < 8 && !posts.isEmpty then
      let (pi, g4) := g.below posts.size
      let (ei, g5) := g4.below 3
      g := g5
      ops := ops.push (react c u posts[pi]! d (["👍", "🎉", "❤"][ei]!).toUTF8 tm)
    else if kind == 8 then
      ops := ops.push (profile c u d s!"name {i}".toUTF8 tm)
    else
      -- a forgery: signed by the wrong device
      let (vi, g4) := g.below users.size
      g := g4
      ops := ops.push (post c u users[vi]!.2.2 "k".toUTF8 "forged".toUTF8 tm)
  return (ops, c, posts, users)

def queries (c : Id) (posts : Array Id) (users : Array (Id × Id × Device)) (cursors : List Pos) :
    List ListQ := Id.run do
  let mut qs : List ListQ := []
  let all := message.all.key [c]
  for desc in [true, false] do
    for limit in [some 0, some 1, some 7, some 64, none] do
      qs := { key := all, desc, limit } :: qs
      for p in cursors do
        qs := { key := all, desc, limit, after := some p } :: { key := all, desc, limit, before := some p }
          :: { key := all, desc, limit, after := some p, cap := 5 } :: qs
  for (_, u, _) in users do
    qs := { key := all, also := [message.byAuthor.key [c, u]], limit := some 10 }
      :: { key := message.byAuthor.key [c, u], limit := some 0 }
      :: { key := profile.byUser.key [c, u], limit := some 1 }
      :: { key := message.byAuthor.key [c, u], limit := none } :: qs
  for m in posts.toList.take 40 do
    qs := { key := react.byMessage.key [c, m], limit := some 50, desc := false }
      :: { key := react.byMessageEmoji.key [c, m, "👍".toUTF8] }
      :: { key := opKey m, limit := some 1 } :: qs
  return qs

/-- SQLite's plan for a statement: EXPLAIN QUERY PLAN's detail lines. -/
def explain (db : Db) (sql : String) (ps : Array ByteArray) : IO (List String) := do
  let rows ← db.query ("EXPLAIN QUERY PLAN " ++ sql) ps
  return rows.toList.filterMap fun r => r[3]? >>= String.fromUTF8?

def mentions (l sub : String) : Bool := (l.splitOn sub).length > 1

/-- What the cost of a read assumes of a plan line (`Seeks`): a search
through an index or a primary key, or the subqueries that hold them;
never a scan of a table, never a sort. A key's range is searched in
`idx_ks` (in (s, id) order), or, for a count, where order does not
matter, in `idx`'s unique (k, id). -/
def lineOk (l : String) : Bool :=
  !mentions l "TEMP B-TREE" &&
  (mentions l "SEARCH i USING COVERING INDEX idx_ks (k=?" ||
   mentions l "SEARCH i USING COVERING INDEX sqlite_autoindex_idx_1 (k=?)" ||
   mentions l "SEARCH st USING PRIMARY KEY (id=?)" ||
   mentions l "SEARCH j USING COVERING INDEX sqlite_autoindex_idx_1 (k=? AND id=?)" ||
   mentions l "SEARCH cnt USING PRIMARY KEY (k=?)" ||
   mentions l "CORRELATED SCALAR SUBQUERY" ||
   mentions l "CO-ROUTINE" ||
   mentions l "SCAN (subquery")

/-- `sortPos` as written, under another name: the compiler runs a merge
sort for `sortPos` (`sortPos_eq_fast`), and this insertion sort as is. -/
def sortPosSpec {α} (l : List (Pos × α)) : List (Pos × α) := l.foldr insertBy []

example : @sortPosSpec = @sortPos := rfl

/-- Byte strings in list order (memcmp's): a reference for `bcmp`. -/
def refCmp (a b : ByteArray) : Ordering :=
  if a.toList < b.toList then .lt else if b.toList < a.toList then .gt else .eq

/-- Short byte strings over a small alphabet: ties, prefixes, and bytes
on both sides of 128. -/
def shortBytes (g : Rng) : ByteArray × Rng := Id.run do
  let (n, g) := g.below 4
  let mut g := g
  let mut b := ByteArray.empty
  for _ in [0:n] do
    let (k, g') := g.below 4
    g := g'
    b := b.push #[0, 1, 128, 255][k]!
  return (b, g)

/-- The sort that runs against the insertion sort, and `bcmp` against
list order. -/
def sortChecks (t : Checks) : IO Unit := do
  let mut g : Rng := ⟨77⟩
  let mut pool : Array ByteArray := #[]
  for _ in [0:60] do
    let (b, g') := shortBytes g
    g := g'
    pool := pool.push b
  let mut cmps := 0
  let mut bad := 0
  for a in pool do
    for b in pool do
      cmps := cmps + 1
      if bcmp a b != refCmp a b then bad := bad + 1
  t.ok s!"bcmp is list order on {cmps} pairs of short byte strings" (bad == 0)
  let mut trials := 0
  let mut differ := 0
  let mut unstable := 0
  for _ in [0:2000] do
    let (n, g1) := g.below 61
    g := g1
    let mut l : List (Pos × Nat) := []
    for i in [0:n] do
      let (s, g2) := shortBytes g
      let (x, g3) := shortBytes g2
      g := g3
      l := l ++ [((s, x), i)]
    trials := trials + 1
    if sortPos l != sortPosSpec l then differ := differ + 1
    -- negative control: a merge sort by strict order, which reverses ties
    if l.mergeSort (fun p q => p.1.cmp q.1 == .lt) != sortPosSpec l then unstable := unstable + 1
  t.ok s!"sortPos (a merge sort) is the insertion sort on {trials} random lists with ties" (differ == 0)
  IO.println s!"sorts: {trials} lists; an unstable sort differs from the insertion sort on {unstable}"
  t.ok "an unstable sort is caught (negative control)" (unstable > 0)

def main : IO UInt32 := do
  let t ← Checks.new
  let fam := family C
  let dir := "out/querydiff"
  IO.FS.createDirAll dir
  for seed in [1, 2, 3] do
    for f in ["q.db", "q.db-wal", "q.db-shm"] do
      if ← System.FilePath.pathExists (dir ++ "/" ++ f) then IO.FS.removeFile (dir ++ "/" ++ f)
    let (ops, c, posts, users) := build seed 6 300
    let db ← Db.openAt (dir ++ "/q.db")
    db.watchFiled
    let (shuffled, _) := (Rng.mk seed.toUInt64).shuffle ops.toList
    let m := modelRun fam shuffled
    -- Cursors: real positions from the middle of the list, and ties.
    let base := eval m { key := message.all.key [c], desc := false, limit := some 1000 }
    let cursors := [5, 17, 60].filterMap (fun i => base.rows[i]?.map (·.1)) ++ [(be64 25, ByteArray.empty)]
    let qs := queries c posts users cursors
    -- Notices are complete: after each commit, every list whose answer
    -- changed had its key filed (eval_stable, on SQLite).
    let mut filedAll : List ByteArray := []
    let mut before ← qs.mapM fun q => (listSql (F := Fact) q).run db
    let mut changed := 0
    let mut missed := 0
    for chunk in [shuffled.take 100, (shuffled.drop 100).take 150, shuffled.drop 250] do
      (receive fam chunk).run db
      let filed ← db.takeFiled
      filedAll := filedAll ++ filed
      let after ← qs.mapM fun q => (listSql (F := Fact) q).run db
      for ((q, a), b) in (qs.zip before).zip after do
        if a != b then
          changed := changed + 1
          if !filed.contains q.key then missed := missed + 1
      before := after
    t.ok s!"seed {seed}: every list that changed had its key filed ({changed} changed)"
      (missed == 0 && changed > 0)
    -- What was filed is exactly the index's keys, and every decided op.
    let idx ← (dumpIdx (F := Fact)).run db
    let st ← (dumpStatus (F := Fact)).run db
    t.ok s!"seed {seed}: filed keys cover the index" (idx.all fun (k, _) => filedAll.contains k)
    t.ok s!"seed {seed}: filed keys cover the verdicts" (st.all fun (x, _) => filedAll.contains (opKey x))
    t.ok s!"seed {seed}: nothing else filed" (filedAll.all fun k =>
      idx.any (·.1 == k) || st.any (fun (x, _) => opKey x == k))
    let mut n := 0
    for q in qs do
      let a ← (listSql (F := Fact) q).run db
      let b := eval m q
      n := n + 1
      if a != b then
        IO.eprintln s!"key {hex q.key} desc {q.desc} limit {q.limit}: sql {a.rows.length}/{a.inRange}/{a.total} model {b.rows.length}/{b.inRange}/{b.total}"
      t.ok s!"seed {seed}: query {n}" (a == b)
    -- The network's views on SQLite against their meaning.
    for (_, _, d) in users do
      let a ← ((allowPeer c d.pk).run : SqlM Fact Bool).run db
      t.ok s!"seed {seed}: allowPeer view" (a == (allowPeer c d.pk).eval m)
    let ms ← ((members c).run : SqlM Fact (List Key)).run db
    t.ok s!"seed {seed}: members view" (ms == (members c).eval m && ms.length == users.size)
    let rs ← ((recipients c).run : SqlM Fact (List Key)).run db
    t.ok s!"seed {seed}: recipients view" (rs == (recipients c).eval m)
    -- Every statement a read runs is served by an index in its order:
    -- its plan searches, never scans a table, never sorts.
    let mut stmts := 0
    let mut badPlans : List String := []
    for q in qs do
      let (k, others, _) ← (pickWalk (F := Fact) q).run db
      for st in readPlan q k others do
        let (sql, ps) := st.sql
        let lines ← explain db sql ps
        stmts := stmts + 1
        if lines.isEmpty || !lines.all lineOk then badPlans := (sql ++ " :: " ++ toString lines) :: badPlans
    for b in badPlans.take 3 do IO.eprintln s!"plan: {b}"
    t.ok s!"seed {seed}: every one of {stmts} statements is served by an index, unsorted" badPlans.isEmpty
    -- Negative controls: a sort the index cannot give, and a scan.
    let sorted ← explain db "SELECT i.s, i.id FROM idx i WHERE i.k = ? ORDER BY i.s DESC, i.id ASC LIMIT 5" #[c]
    let scan ← explain db "SELECT count(*) FROM idx i WHERE i.s = ?" #[c]
    t.ok s!"seed {seed}: a plan that sorts is caught" (!sorted.all lineOk)
    t.ok s!"seed {seed}: a plan that scans is caught" (!scan.all lineOk)
    -- Unions merge their lists (no sort): on SQLite as on the model.
    let lists := users.toList.map fun (_, u, _) => message.byAuthor.query [c, u]
    let mut unions := 0
    for desc in [true, false] do
      for limit in [some 0, some 5, some 30, none] do
        for v in [View.union (F := Fact) lists limit desc,
                  View.union (F := Fact) (lists.take 2 ++ lists.take 2) limit desc,
                  View.union (F := Fact) ((lists.map fun q => { q with after := cursors.head? }).take 3) limit desc] do
          let a ← ((v.run : SqlM Fact (Answer Fact))).run db
          unions := unions + 1
          t.ok s!"seed {seed}: union {unions} on SQLite is the model's" (a == v.eval m)
    IO.println s!"seed {seed}: {n} queries, {base.total} valid messages, {stmts} statements' plans, {unions} unions"
  sortChecks t
  t.finish "querydiff"
