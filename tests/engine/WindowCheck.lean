/-
Exact notices on SQLite: the store's journal (`Db.filings`, its
triggers), netted (`net`) and matched against the index (`Subs.notify`),
against the windows read again.

Random op graphs (shared, conn and local ops; a fifth Invalid; some
citing ops that never come) arrive in random batches, with random purges
in between (which delete conn and local ops and undecide shared ones,
which the drain files again). Between two reader passes, one to three
commits. At each pass, for random windows (keys, inclusive and exclusive
ends, open ends, ops' own keys) and random reads (newest or oldest
first, a limit, a range), each subscribed at its window from the last
pass's answer:
- **notice_iff**: a window is notified exactly when its rows, read again,
  differ;
- **read_notice_iff**: a read is notified exactly when its rows differ.

Negative controls, which must fail here: key-level notices (every watch
on a key the journal names) notify windows that did not change, and so
does matching the journal's rows without netting them.
-/
import tests.engine.Lib
import engine.core.WindowIndex

open Engine Tests

namespace WindowCheck

def room : Id := sha256 "window-check-room".toUTF8

/-- An op's body: its scope (shared, conn or local: 0, 1 or 2 mod 3), a
verdict byte (Invalid when 0 mod 5), a key byte, a sort byte, then a tag.
Its fact is its body; it sorts by its sort byte, ties by id. -/
def fam : Family ByteArray where
  validate o _ := if (o.body[1]?.getD 1) % 5 == 0 then none else some o.body
  keys f := [⟨#[1, (f[2]?.getD 0) % 3]⟩, ⟨#[2]⟩]
  scope o := match (o.body[0]?.getD 0) % 3 with
    | 0 => .shared room
    | 1 => .conn
    | _ => .local

instance : SortKey ByteArray := ⟨fun f => ⟨#[f[3]?.getD 0]⟩⟩

def gen (seed n : Nat) : List Op := Id.run do
  let mut g := Rng.mk (6151 * seed + 29).toUInt64
  let mut ids : Array Id := #[]
  let mut ops : Array Op := #[]
  for i in [0:n] do
    let (sc, g1) := g.below 10
    let (v, g2) := g1.below 10
    let (k, g3) := g2.below 3
    let (srt, g4) := g3.below 6
    let (nr, g5) := g4.below 3
    g := g5
    let mut reqs : List Id := []
    for j in [0:nr] do
      let (w, g6) := g.below 100
      let (pick, g7) := g6.below (max ids.size 1)
      g := g7
      reqs := reqs ++ [if w < 10 || ids.isEmpty then sha256 s!"never-{seed}-{i}-{j}".toUTF8 else ids[pick]!]
    let scope : UInt8 := if sc < 5 then 0 else if sc < 8 then 1 else 2
    let o := Op.make 1 reqs (⟨#[scope, v.toUInt8 + 1, k.toUInt8, srt.toUInt8]⟩ ++ s!"op-{seed}-{i}".toUTF8)
    ops := ops.push o
    ids := ids.push o.id
  return ops.toList

/-- A window's rows, read on SQLite: its key's whole list, in its range. -/
def readWin (db : Db) (w : Win) : IO (List (Pos × ByteArray)) := do
  let a ← (listSql (F := ByteArray) { key := w.key, limit := none, desc := false }).run db
  return a.rows.filter fun r => w.inside r.1

def readQ (db : Db) (q : ListQ) : IO (List (Pos × ByteArray)) := do
  return (← (listSql (F := ByteArray) q).run db).rows

def keysOf (ops : List Op) (g : Rng) : ByteArray × Rng :=
  let (i, g) := g.below 6
  match i with
  | 0 => (⟨#[1, 0]⟩, g)
  | 1 => (⟨#[1, 1]⟩, g)
  | 2 => (⟨#[1, 2]⟩, g)
  | 3 => (⟨#[2]⟩, g)
  | _ =>
    let (j, g) := g.below ops.length
    (opKey (ops[j]?.map (·.id) |>.getD .empty), g)

def posOf (ops : List Op) (g : Rng) : Pos × Rng :=
  let (s, g) := g.below 7
  let (j, g) := g.below (ops.length + 2)
  let id := if j < ops.length then (ops[j]?.map (·.id)).getD .empty else if j == ops.length then .empty else idTop
  ((⟨#[s.toUInt8]⟩, id), g)
where idTop : ByteArray := ⟨Array.replicate 33 0xFF⟩

def endOf (ops : List Op) (g : Rng) : Option End × Rng :=
  let (c, g) := g.below 3
  if c == 0 then (none, g) else
    let (p, g) := posOf ops g
    (some (p, c == 1), g)

def winOf (ops : List Op) (g : Rng) : Win × Rng :=
  let (k, g) := keysOf ops g
  let (lo, g) := endOf ops g
  let (hi, g) := endOf ops g
  ({ key := k, lo, hi }, g)

def qOf (ops : List Op) (g : Rng) : ListQ × Rng :=
  let (k, g) := keysOf ops g
  let (d, g) := g.below 2
  let (n, g) := g.below 5
  let (a, g) := g.below 3
  let (pa, g) := posOf ops g
  let (b, g) := g.below 3
  let (pb, g) := posOf ops g
  ({ key := k, desc := d == 0, limit := some (n + 1), after := if a == 0 then some pa else none,
     before := if b == 0 then some pb else none }, g)

/-- Notices by key: what the app's `Live` did. -/
def keyHit (fs : Array Filing) (w : Win) : Bool := fs.any (·.key == w.key)

/-- The journal's rows matched as they are, without netting. -/
def rawHit (fs : Array Filing) (w : Win) : Bool := fs.any fun e => w.has e.key e.pos

structure Counts where
  passes : Nat := 0
  notified : Nat := 0
  changed : Nat := 0
  keySpurious : Nat := 0
  rawSpurious : Nat := 0
  netCancelled : Nat := 0

def run (t : Checks) (dir : String) (seed : Nat) (c : IO.Ref Counts) : IO Unit := do
  let path := s!"{dir}/w{seed}.db"
  for suf in ["", "-wal", "-shm"] do
    try IO.FS.removeFile (path ++ suf) catch _ => pure ()
  let db ← Db.openAt path
  db.filings
  let ops := gen seed 60
  let mut g := Rng.mk (911 * seed + 7).toUInt64
  let mut pending := ops
  let mut seen := 0
  for pass in [0:25] do
    -- what the reader holds: windows and reads, as of now
    let mut wins : Array Win := #[]
    for _ in [0:24] do
      let (w, g') := winOf ops g
      g := g'
      wins := wins.push w
    let mut qs : Array ListQ := #[]
    for _ in [0:12] do
      let (q, g') := qOf ops g
      g := g'
      qs := qs.push q
    let before ← wins.mapM (readWin db)
    let answers ← qs.mapM fun q => (listSql (F := ByteArray) q).run db
    let subs : List (Nat × Win) :=
      (wins.toList.zipIdx.map fun (w, i) => (i, w)) ++
        (qs.toList.zip answers.toList).zipIdx.map fun ((q, a), i) => (1000 + i, q.win a)
    let I := Subs.ofList subs
    -- one to three commits: arrivals and purges
    let (nc, g1) := g.below 3
    g := g1
    for _ in [0:nc + 1] do
      let (kind, g2) := g.below 4
      g := g2
      if kind == 0 && pass > 2 then
        let (n, g3) := g.below 4
        g := g3
        let mut targets : List Id := []
        for _ in [0:n + 1] do
          let (j, g4) := g.below ops.length
          g := g4
          targets := (ops[j]?.map (·.id)).toList ++ targets
        (purgeSql fam targets (scrub := false)).run db
      else
        let (n, g3) := g.below 6
        g := g3
        let (batch, more) := (pending.take (n + 1), pending.drop (n + 1))
        -- purged ops come back now and then
        let (back, g4) := g.below 5
        g := g4
        let again := if back == 0 then (ops.take (pass + 1)).drop pass else []
        pending := more
        (receive fam (batch ++ again)).run db
    -- the reader's pass: the journal since the last, netted and matched
    let (fs, _, top) ← db.filingsSince seen
    seen := top
    let hit := I.notify fs
    let after ← wins.mapM (readWin db)
    for i in [0:wins.size] do
      let ch := after[i]! != before[i]!
      let nt := hit.contains i
      t.ok s!"seed {seed} pass {pass} window {i}: notified exactly when changed" (nt == ch)
      c.modify fun c => { c with notified := c.notified + (if nt then 1 else 0), changed := c.changed + (if ch then 1 else 0)
                                 keySpurious := c.keySpurious + (if keyHit fs wins[i]! && !ch then 1 else 0)
                                 rawSpurious := c.rawSpurious + (if rawHit fs wins[i]! && !ch then 1 else 0)
                                 netCancelled := c.netCancelled + (if rawHit fs wins[i]! && !nt then 1 else 0) }
    for i in [0:qs.size] do
      let now ← readQ db qs[i]!
      let ch := now != answers[i]!.rows
      let nt := hit.contains (1000 + i)
      t.ok s!"seed {seed} pass {pass} read {i}: notified exactly when its rows changed" (nt == ch)
      c.modify fun c => { c with keySpurious := c.keySpurious + (if keyHit fs (qs[i]!.win answers[i]!) && !ch then 1 else 0) }
    c.modify fun c => { c with passes := c.passes + 1 }
    db.pruneFilings seen

end WindowCheck

open WindowCheck in
def main (args : List String) : IO UInt32 := do
  let dir := args.headD "out/windows"
  let seeds := (args[1]? >>= String.toNat?).getD 8
  IO.FS.createDirAll dir
  let t ← Checks.new
  let c ← IO.mkRef ({} : Counts)
  for seed in [1:seeds + 1] do
    run t dir seed c
  let n ← c.get
  IO.println s!"windows: {n.passes} passes; notified {n.notified}, changed {n.changed}; key-level spurious {n.keySpurious}, unnetted spurious {n.rawSpurious}, cancelled by netting {n.netCancelled}"
  t.ok "some windows changed and were notified" (n.changed > 0 && n.notified > 0)
  t.ok "control: key-level notices notify windows that did not change" (n.keySpurious > 0)
  t.ok "control: unnetted journal rows notify windows that did not change" (n.rawSpurious > 0)
  t.finish "windows"
