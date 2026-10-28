/-
Purge on SQLite, against the model and on the file itself.

- **Differential.** Random op graphs mixing shared, conn and local ops
  (some citing ops that never arrive) arrive in random batches, with
  random purges in between, and purged ops sometimes arrive again. Each
  turn runs on SQLite (`receive`, `purgeSql`) and on the model
  (`ingestS`, `purgeS`, `drainS`), and after each one every table must
  match, the `reqs` and `cnt` tables included. After each purge: the
  purged ops are exactly the conn and local ops among the targets and
  their stored dependents (`mem_purgeSet`), computed here independently;
  none of them is in any table (`purge_gone`); every shared op is still
  stored (`purge_shared`); the queue is empty; and every verdict is the
  spec's over what remains, and a fresh node's that only ever received
  what remains.
- **Forward secrecy, on the file.** A local op holding a 32-byte secret,
  with a local op that cites it holding another and a peer's shared op
  that cites it, is stored among a few hundred others and purged. The
  database's files (the database, -wal, -shm, -journal), read raw, then
  hold no 16 bytes of either secret, with the database open and after it
  is closed; the peer's op is still stored, unresolved. Two controls show
  the scan can fail: without `secure_delete` the bytes stay in the
  database file, and without the checkpoint they stay in the WAL. Run on
  this family and on Community's device secret.
- **Purge, then again.** A purged local op written again is stored and
  judged as before, and purged again.
-/
import Tests.Lib

open Engine Tests

namespace PurgeTest

/-! ## A family with every scope -/

/-- The room every shared op here is in. -/
def room : Id := sha256 "purge-test-room".toUTF8

/-- An op's body is its scope (shared, conn or local: 0, 1 or 2 mod 3), a
verdict byte (Invalid when 0 mod 5), a key byte, then anything. Its fact
is its body, so its bytes are in its verdict and in its index rows' sort
key as well as in its op row. -/
def fam : Family ByteArray where
  validate o _ := if (o.body[1]?.getD 1) % 5 == 0 then none else some o.body
  keys f := [⟨#[1, (f[2]?.getD 0) % 3]⟩, ⟨#[2]⟩]
  scope o := match (o.body[0]?.getD 0) % 3 with
    | 0 => .shared room
    | 1 => .conn
    | _ => .local

instance : SortKey ByteArray := ⟨id⟩

def mk (scope verdict key : UInt8) (reqs : List Id) (rest : ByteArray) : Op :=
  Op.make 1 reqs (⟨#[scope, verdict, key]⟩ ++ rest)

def shared (o : Op) : Bool := (fam.room o).isSome

/-- Random ops: 40% shared, 30% conn, 30% local; a fifth Invalid; each
citing up to three earlier ops, and now and then an op that never comes. -/
def gen (seed n : Nat) : List Op := Id.run do
  let mut g := Rng.mk (7919 * seed + 13).toUInt64
  let mut ids : Array Id := #[]
  let mut ops : Array Op := #[]
  for i in [0:n] do
    let (sc, g1) := g.below 10
    let (v, g2) := g1.below 10
    let (k, g3) := g2.below 3
    let (nr, g4) := g3.below 4
    g := g4
    let mut reqs : List Id := []
    for j in [0:nr] do
      let (w, g5) := g.below 100
      let (pick, g6) := g5.below (max ids.size 1)
      g := g6
      reqs := reqs ++ [if w < 12 || ids.isEmpty then sha256 s!"never-{seed}-{i}-{j}".toUTF8 else ids[pick]!]
    let scope : UInt8 := if sc < 4 then 0 else if sc < 7 then 1 else 2
    let o := mk scope (v.toUInt8 + 1) k.toUInt8 reqs s!"op-{seed}-{i}".toUTF8
    ops := ops.push o
    ids := ids.push o.id
  return ops.toList

/-! ## The model's side -/

section
variable {F : Type}

/-- The steps a write turn drains with on the model: `budgetSql`, read
off the model's tables. -/
def fuel (s : DB F) : Nat :=
  s.queue.length + (s.stored.filter fun x => (s.status x).isNone).length * s.stored.length

def rest (fam : Family F) (s : DB F) : DB F := drainS fam (fuel s) s

def recvM (fam : Family F) (ops : List Op) (s : DB F) : DB F :=
  rest fam (ops.foldl (fun s o => ingestS o s) s)

end

/-! ## Comparing -/

def group {α} (rows : List (ByteArray × α)) (k : ByteArray) : List α :=
  rows.filterMap fun (k', a) => if k' == k then some a else none

def dumpReqs : SqlM ByteArray (List (Id × Id)) := do
  let rows ← sqlQ (F := ByteArray) "SELECT req, op FROM reqs" #[]
  return rows.toList.filterMap fun r => do pure ((← r[0]?), (← r[1]?))

def dumpCnt : SqlM ByteArray (List (ByteArray × Nat)) := do
  let rows ← sqlQ (F := ByteArray) "SELECT k, CAST(n AS TEXT) FROM cnt" #[]
  return rows.toList.filterMap fun r => do
    let n ← r[1]? >>= String.fromUTF8? >>= String.toNat?
    pure ((← r[0]?), n)

def sameSet (a b : List Id) : Bool := a.all b.contains && b.all a.contains

/-- Every table of the database equals the model's: ops (and the stored
list), verdicts, waits, queue, index, and the derived `reqs` and `cnt`. -/
def sameTables (t : Checks) (tag : String) (db : Db) (m : DB ByteArray) (ids0 : List Id) : IO Unit := do
  let run {α} (q : SqlM ByteArray α) : IO α := q.run db
  let ops ← run dumpOps
  let st ← run (dumpStatus (F := ByteArray))
  let waits ← run (dumpWaits (F := ByteArray))
  let queue ← run (dumpQueue (F := ByteArray))
  let idx ← run (dumpIdx (F := ByteArray))
  let reqs ← run dumpReqs
  let cnt ← run dumpCnt
  t.ok s!"{tag}: ops" (ops.all (fun o => m.ops o.id == some o) &&
    ops.length == (ids0.filter fun x => (m.ops x).isSome).length)
  t.ok s!"{tag}: stored list" (sameSet m.stored (ops.map (·.id)) && m.stored.length == ops.length)
  t.ok s!"{tag}: verdicts" (st.all (fun (x, v) => m.status x == some v) &&
    st.length == (ids0.filter fun x => (m.status x).isSome).length)
  t.ok s!"{tag}: waits" (ids0.all fun r => group waits r == m.waits r)
  t.ok s!"{tag}: queue" (queue == m.queue)
  let keysUsed := (ids0.foldl (fun acc x => match m.status x with
    | some (.valid f) => acc ++ fam.fileKeys x f
    | _ => acc) ([] : List ByteArray)).eraseDups
  t.ok s!"{tag}: index" (keysUsed.all (fun k => group idx k == m.idx k) &&
    idx.all fun (k, _) => keysUsed.contains k)
  let edges := ops.flatMap fun o => o.reqs.eraseDups.map (·, o.id)
  t.ok s!"{tag}: reqs" (reqs.length == edges.length && edges.all reqs.contains)
  t.ok s!"{tag}: counts" (cnt.length == keysUsed.length &&
    keysUsed.all fun k => cnt.contains (k, (m.idx k).length))

/-- The conn and local ops among targets and their stored dependents,
by a plain fixpoint over the stored ops: the meaning `mem_purgeSet`
states, computed without `closeUp`. -/
def expected (stored : List Op) (targets : List Id) : List Id := Id.run do
  let mut s := targets
  for _ in [0:stored.length + 1] do
    s := s ++ (stored.filter fun o => !s.contains o.id && o.reqs.any s.contains).map (·.id)
  return (stored.filter fun o => s.contains o.id && !shared o).map (·.id)

/-! ## The differential -/

structure Stats where
  purges : Nat := 0
  purged : Nat := 0
  again : Nat := 0
  changed : Nat := 0
  back : Nat := 0

def differential (t : Checks) (dir : String) (seed : Nat) (st : Stats) : IO Stats := do
  let mut st := st
  let ops := gen seed 150
  let ids0 := (ops.map (·.id) ++ ops.flatMap (·.reqs)).eraseDups
  let byId (x : Id) : Option Op := ops.find? (·.id == x)
  let path := s!"{dir}/d{seed}.db"
  for suffix in ["", "-wal", "-shm"] do
    if ← System.FilePath.pathExists (path ++ suffix) then IO.FS.removeFile (path ++ suffix)
  let db ← Db.openAt path
  let mut g := Rng.mk (31 * seed + 7).toUInt64
  let (order, g1) := g.shuffle ops
  g := g1
  let mut pending := order
  let mut m : DB ByteArray := DB.empty
  let mut turn := 0
  while !pending.isEmpty do
    turn := turn + 1
    let (k, g1) := g.below 8
    g := g1
    let batch := pending.take (k + 1)
    pending := pending.drop (k + 1)
    (receive fam batch).run db
    m := recvM fam batch m
    sameTables t s!"seed {seed} turn {turn} receive" db m ids0
    let (p, g1) := g.below 3
    g := g1
    if p != 0 then continue
    -- A purge: one to three targets, mostly ops held, sometimes any id.
    let (nt, g1) := g.below 3
    g := g1
    let held := ids0.filter fun x => (m.ops x).isSome
    let mut targets : List Id := []
    for _ in [0:nt + 1] do
      let (w, g1) := g.below 10
      let (i, g2) := g1.below held.length
      let (j, g3) := g2.below ids0.length
      g := g3
      targets := targets ++ [if w < 7 && !held.isEmpty then held[i]! else ids0[j]!]
    let pre := m
    let gone := purgeSet fam pre targets
    let again := rejudgeSet fam pre targets
    let storedPre := ids0.filterMap pre.ops
    (purgeSql fam targets).run db
    let undrained := purgeS fam targets pre
    m := rest fam undrained
    let tag := s!"seed {seed} turn {turn} purge"
    sameTables t tag db m ids0
    st := { st with purges := st.purges + 1, purged := st.purged + gone.eraseDups.length,
                    again := st.again + again.eraseDups.length }
    t.ok s!"{tag}: exactly the conn and local ops among the targets and their dependents"
      (sameSet gone (expected storedPre targets))
    let sqlOps := (← (dumpOps (F := ByteArray)).run db).map (·.id)
    let sqlIdx ← (dumpIdx (F := ByteArray)).run db
    let sqlWaits ← (dumpWaits (F := ByteArray)).run db
    let sqlSt ← (dumpStatus (F := ByteArray)).run db
    let sqlReqs ← dumpReqs.run db
    t.ok s!"{tag}: purge_gone (model)" (gone.all fun x =>
      m.ops x == none && ids0.all fun y => match m.status y with
        | some (.valid f) => (fam.fileKeys y f).all fun k => !(m.idx k).contains x
        | _ => true)
    -- A dependent kept may still wait on a purged id; nothing else names it.
    t.ok s!"{tag}: purge_gone (SQLite): no row of its own in any table" (gone.all fun x =>
      !sqlOps.contains x && !sqlIdx.any (·.2 == x) && !sqlSt.any (·.1 == x) &&
      !sqlWaits.any (·.2 == x) && !sqlReqs.any (·.2 == x))
    t.ok s!"{tag}: purge_shared" (storedPre.all fun o => !shared o || (m.ops o.id == some o && sqlOps.contains o.id))
    t.ok s!"{tag}: purge_undecides: each shared dependent stored, undecided, unfiled and queued"
      (again.all fun x => undrained.ops x == pre.ops x && undrained.status x == none &&
        undrained.queue.contains x && !(undrained.idx (opKey x)).contains x)
    t.ok s!"{tag}: queue empty" (m.queue.isEmpty && (← (dumpQueue (F := ByteArray)).run db).isEmpty)
    t.ok s!"{tag}: verdicts are the spec's over what remains"
      (ids0.all fun x => m.status x == specAt fam m.ops (ops.length + 1) x)
    let remaining := ids0.filterMap m.ops
    let (shuf, g1) := g.shuffle remaining
    g := g1
    let fresh := recvM fam shuf DB.empty
    t.ok s!"{tag}: a fresh node fed what remains agrees" (ids0.all fun x => m.status x == fresh.status x)
    st := { st with changed := st.changed + (again.eraseDups.filter fun x => pre.status x != m.status x).length }
    -- Purged ops arrive again, half of them.
    for x in gone.eraseDups do
      let (b, g1) := g.below 2
      g := g1
      if b == 0 then
        if let some o := byId x then
          pending := pending ++ [o]
          st := { st with back := st.back + 1 }
  t.ok s!"seed {seed}: all ops delivered and judged" (m.queue.isEmpty)
  return st

/-! ## Forward secrecy on the file -/

/-- Whether pat occurs in b. -/
def occurs (b pat : ByteArray) : Bool := Id.run do
  if b.size < pat.size then return false
  for i in [0:b.size - pat.size + 1] do
    let mut ok := true
    for j in [0:pat.size] do
      if b[i + j]! != pat[j]! then ok := false; break
    if ok then return true
  return false

/-- The database's files that hold any 16 bytes of a secret: either
half, or the whole. -/
def leaks (path : String) (secrets : List ByteArray) : IO (List String) := do
  let mut out := []
  for suf in ["", "-wal", "-shm", "-journal"] do
    let f := path ++ suf
    if ← System.FilePath.pathExists f then
      let b ← IO.FS.readBinFile f
      if secrets.any fun s => occurs b (s.extract 0 16) || occurs b (s.extract 16 32) then
        out := out ++ [f]
  return out

def clear (path : String) : IO Unit := do
  for suf in ["", "-wal", "-shm", "-journal"] do
    if ← System.FilePath.pathExists (path ++ suf) then IO.FS.removeFile (path ++ suf)

structure Seen where
  before : List String
  opened : List String
  stored : Bool
  queue : Bool
  verdict : Option String

/-- How a session purges: as `purgeSql` does; without its VACUUM; or
without the VACUUM and the checkpoint. -/
inductive Mode where
  | full
  | noScrub
  | noCheckpoint

/-- Open a database, take the batches, purge `target`, and scan the
files while it is still open. The database closes when this returns. -/
def session {F} [Codec F] [SortKey F] (fam : Family F) (path : String) (secure : Bool) (mode : Mode)
    (load : List (List Op)) (target : Id) (secrets : List ByteArray) (watch : Id) : IO Seen := do
  clear path
  let db ← Db.openAt path
  if !secure then db.exec "PRAGMA secure_delete = OFF"
  for b in load do (receive fam b).run db
  let before ← leaks path secrets
  match mode with
  | .full => (purgeSql fam [target]).run db
  | .noScrub => (purgeSql fam [target] (scrub := false)).run db
  | .noCheckpoint => (transact (purgeTx fam [target])).run db
  let stored := (← (Store.getOp (F := F) target : SqlM F _).run db).isSome
  let opened ← leaks path secrets
  -- The database is used after the scan, so it was open during it.
  let queue := (← (dumpQueue (F := F)).run db).isEmpty
  let v : Option (Verdict F) ← (Store.getStatus watch : SqlM F _).run db
  let w ← (Store.getOp (F := F) watch : SqlM F _).run db
  let verdict := if w.isNone then some "gone" else match v with
    | none => some "unresolved" | some .invalid => some "invalid" | some (.valid _) => some "valid"
  return ⟨before, opened, stored, queue, verdict⟩

def fsCase {F} [Codec F] [SortKey F] (t : Checks) (name : String) (fam : Family F) (dir : String)
    (load : List (List Op)) (secretOp : Op) (secrets : List ByteArray) (watch : Id) (watchAfter : String)
    (gapExpected : Bool) : IO Unit := do
  let path := s!"{dir}/fs-{name}.db"
  let s ← session fam path true .full load secretOp.id secrets watch
  let closed ← leaks path secrets
  t.ok s!"{name}: SQLite removed the WAL, so the database was closed for that scan"
    !(← System.FilePath.pathExists (path ++ "-wal"))
  IO.println s!"{name}: before purge in {s.before}; after, open: {s.opened}; closed: {closed}"
  t.ok s!"{name}: the secret is on disk before the purge" (!s.before.isEmpty)
  t.ok s!"{name}: the purged op is not stored" (!s.stored)
  t.ok s!"{name}: no file holds the secret after the purge, database open" s.opened.isEmpty
  t.ok s!"{name}: no file holds the secret once closed" closed.isEmpty
  t.ok s!"{name}: the queue is empty after the purge" s.queue
  t.ok s!"{name}: the op watched is {watchAfter}" (s.verdict == some watchAfter)
  -- Controls: the scan finds what the protections remove.
  let c1 := s!"{dir}/fs-{name}-nosecure.db"
  let a ← session fam c1 false .noScrub load secretOp.id secrets watch
  IO.println s!"{name} control, secure_delete off, no VACUUM: after the purge in {a.opened}"
  t.ok s!"{name} control: without secure_delete the database file keeps the secret" (a.opened.contains c1)
  let c2 := s!"{dir}/fs-{name}-nockpt.db"
  let b ← session fam c2 true .noCheckpoint load secretOp.id secrets watch
  IO.println s!"{name} control, no VACUUM, no checkpoint: after the purge in {b.opened}"
  t.ok s!"{name} control: without the checkpoint the WAL keeps the secret" (b.opened.contains (c2 ++ "-wal"))
  -- What secure_delete and the checkpoint leave without VACUUM: copies
  -- in the gaps of pages a split rebuilt. Whether there are any depends
  -- on the layout; this family's load leaves one.
  let c3 := s!"{dir}/fs-{name}-noscrub.db"
  let c ← session fam c3 true .noScrub load secretOp.id secrets watch
  IO.println s!"{name} control, no VACUUM: after the purge in {c.opened}"
  if gapExpected then
    t.ok s!"{name} control: without VACUUM a rebuilt page keeps the secret (why purgeSql runs it)"
      (c.opened.contains c3)
  -- Purge, then write it again: stored and judged as before.
  let db ← Db.openAt path
  let before : Option (Verdict F) ← (Store.getStatus secretOp.id : SqlM F _).run db
  (receive fam [secretOp]).run db
  let back ← (Store.getOp (F := F) secretOp.id : SqlM F _).run db
  let v : Option (Verdict F) ← (Store.getStatus secretOp.id : SqlM F _).run db
  t.ok s!"{name}: written again, it is stored again" (back == some secretOp && before.isNone)
  t.ok s!"{name}: and judged Valid again" (match v with | some (.valid _) => true | _ => false)
  (purgeSql fam [secretOp.id]).run db
  t.ok s!"{name}: and purged again" (← (Store.getOp (F := F) secretOp.id : SqlM F _).run db).isNone
  let again ← leaks path secrets
  t.ok s!"{name}: no file holds the secret after the second purge" again.isEmpty

def batchesOf (l : List Op) (n : Nat) : List (List Op) :=
  (List.range ((l.length + n - 1) / n)).map fun i => (l.drop (n * i)).take n

def forwardSecrecy (t : Checks) (dir : String) : IO Unit := do
  -- This family: a local secret, a local key that cites it, and a peer's
  -- shared op that cites it, among 400 others.
  let secret := "FORWARD-SECRECY:ephemeral-key-01".toUTF8
  let derived := "FORWARD-SECRECY:session-keys-002".toUTF8
  let eph := mk 2 1 0 [] secret
  let key := mk 2 1 1 [eph.id] derived
  let pin := mk 0 1 2 [eph.id] "a peer's op citing the secret".toUTF8
  let traffic := gen 99 400
  let load := batchesOf (traffic.take 200) 25 ++ [[eph, key, pin]] ++ batchesOf (traffic.drop 200) 25
  fsCase t "family" fam dir load eph [secret, derived] pin.id "unresolved" true
  -- Community: a device's secret seed, among a community's ops.
  let seed := "COMMUNITY-SEED:device-secret-01!".toUTF8
  let sop := Community.secret seed
  let cops := workload 7 300
  let cload := batchesOf (cops.take 150) 25 ++ [[sop]] ++ batchesOf (cops.drop 150) 25
  fsCase t "community" (Community.family Community.ed25519) dir cload sop [seed] cops.head!.id "valid" false

end PurgeTest

open PurgeTest in
def main (args : List String) : IO UInt32 := do
  let dir := args.headD "out/purge"
  let seeds := (args.drop 1).head?.bind String.toNat? |>.getD 12
  IO.FS.createDirAll dir
  let t ← Checks.new
  let mut st : Stats := {}
  for seed in [0:seeds] do
    st ← differential t dir seed st
  IO.println s!"differential: {st.purges} purges deleted {st.purged} ops and judged {st.again} shared ops again ({st.changed} verdicts changed); {st.back} purged ops arrived again"
  t.ok "purges deleted ops" (st.purged > 0)
  t.ok "purges judged shared dependents again, and some verdicts changed" (st.again > 0 && st.changed > 0)
  t.ok "purged ops arrived again" (st.back > 0)
  forwardSecrecy t dir
  t.finish "purge"
