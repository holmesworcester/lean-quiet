/-
The list query on SQLite (`listSql`) against its meaning on the model
(`eval`), over a chat community: users joined by invitation, posts at
random times (ties included) with attachments, profiles and reactions,
some forged. For every message and user, and for whole-community lists,
it asks for pages in both directions, from cursors, bounded on both
sides, capped, counts only, and conjunctions (messages by one author),
and compares answers exactly. It also checks that the filed keys a
write reports are exactly the keys its new index rows went under.
-/
import Tests.Lib

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
      ops := ops.push (profile c u d s!"name {i}".toUTF8 tm [])
    else
      -- a forgery: signed by the wrong device
      let (vi, g4) := g.below users.size
      g := g4
      ops := ops.push (post c u users[vi]!.2.2 "k".toUTF8 "forged".toUTF8 tm)
  return (ops, c, posts, users)

def queries (c : Id) (posts : Array Id) (users : Array (Id × Id × Device)) (cursors : List Pos) :
    List ListQ := Id.run do
  let mut qs : List ListQ := []
  let all := key 4 c c
  for desc in [true, false] do
    for limit in [some 0, some 1, some 7, some 64, none] do
      qs := { key := all, desc, limit } :: qs
      for p in cursors do
        qs := { key := all, desc, limit, after := some p } :: { key := all, desc, limit, before := some p }
          :: { key := all, desc, limit, after := some p, cap := 5 } :: qs
  for (_, u, _) in users do
    qs := { key := all, also := [key 6 c u], limit := some 10 } :: { key := key 6 c u, limit := some 0 }
      :: { key := key 7 c u, limit := some 1 } :: { key := key 6 c u, limit := none } :: qs
  for m in posts.toList.take 40 do
    qs := { key := key 8 c m, limit := some 50, desc := false } :: { key := key 9 c (encode (m, "👍".toUTF8)) }
      :: { key := opKey m, limit := some 1 } :: qs
  return qs

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
    let base := eval m { key := key 4 c c, desc := false, limit := some 1000 }
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
    IO.println s!"seed {seed}: {n} queries, {base.total} valid messages"
  t.finish "querydiff"
