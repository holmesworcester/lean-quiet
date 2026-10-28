/-
Two nodes syncing a real community (Ed25519, SQLite in memory) through
the engine's driver (`Node`) over the pair harness:

- full: each holds part of the history; both end with all of it and
  the same verdict for every op;
- windowed: a node with a floor ends with exactly the ops with no
  claimed time, the ops claimed at or after its floor, and their
  requirement closures, judged as its peer judges them;
- lossy: a quarter of frames lost; drops and redials; both converge;
- rooms: a peer allowed one community never sees another's ops, not
  even when it asks for them by id, and cannot push them in;
- garbage frames are ignored;
- stream: an op written after the round reaches the peer at once,
  without another round.
-/
import Tests.Lib

open Engine Engine.Sync Community Tests

def C := ed25519
def fam := family C

/-- A community's history: members admitted through invitations,
requests, approvals and admissions; timed posts by them; reactions,
some to old posts; one removal. Times start at 1000, 100 apart. -/
def history (tag : String) (members posts : Nat) : List Op × Id := Id.run do
  let f := Device.named s!"{tag}-founder"
  let r := root f
  let c := r.id
  let mut ops : Array Op := #[r]
  let mut adms : Array (Id × Device) := #[(c, f)]
  for j in [0:members] do
    let b := Device.named s!"{tag}-bearer-{j}"
    let d := Device.named s!"{tag}-member-{j}"
    let inv := invite c c f b.pk false
    let req := request c inv.id d b.sk
    let ok := approve c req.id c f
    let adm := admit c req.id [ok.id]
    ops := ops ++ #[inv, req, ok, adm]
    adms := adms.push (adm.id, d)
  let mut postIds : Array Id := #[]
  for i in [0:posts] do
    let (a, d) := adms[i % adms.size]!
    let p := post c a d "k".toUTF8 s!"{tag} post {i}".toUTF8 (1000 + 100 * i)
    ops := ops.push p
    postIds := postIds.push p.id
    if i % 4 == 3 then
      -- A reaction now to a post from long ago.
      let (a', d') := adms[(i + 1) % adms.size]!
      ops := ops.push (react c a' postIds[i / 4]! d' "+1".toUTF8 (1000 + 100 * i + 50))
  if members > 0 then
    ops := ops.push (remove c c c adms[1]!.1 f)
  return (ops.toList, c)

def memDb : IO Db := Db.openAt ":memory:"

def idsOf (db : Db) : IO (List Id) := do return (← (dumpOps (F := Fact)).run db).map (·.id)

def statusOf (db : Db) (x : Id) : IO (Option (Verdict Fact)) := (Store.getStatus x : SqlM Fact _).run db

def sameSet (a b : List Id) : Bool := a.all (has b) && b.all (has a)

def cfg : Config := { every := 30000, patience := 20000 }

/-- A node whose store holds these ops, with this floor. -/
def node (x : Sync Fact) (ops : List Op) (floor : Nat) : IO Node := do
  let db ← memDb
  (receive fam (intake fam true ops)).run db
  Node.boot x db floor

def sync (rooms : List Id) : Sync Fact := { fam, cfg, hooks := { rooms := fun _ => pure rooms } }

/-- Ops behind these ids among `all`: the ids, and every requirement of
theirs, recursively. -/
def closure (all : List Op) (ids : List Id) : List Id := Id.run do
  let mut seen : List Id := []
  let mut todo := ids
  for _ in [0:all.length * 4 + 10] do
    match todo with
    | [] => break
    | x :: rest =>
      todo := rest
      if !has seen x then
        match all.find? (·.id == x) with
        | some o => seen := x :: seen; todo := o.reqs ++ todo
        | none => pure ()
  return seen

def main : IO UInt32 := do
  let t ← Checks.new
  let (h, c) := history "acme" 6 60
  IO.println s!"history: {h.length} ops"
  let x := sync [c]
  let cid := sha256 "conn".toUTF8

  -- Full: each side holds part of it.
  let mut g := Rng.mk 7
  let mut sa : List Op := []
  let mut sb : List Op := []
  for o in h do
    let (k, g') := g.below 3
    g := g'
    if k != 1 then sa := sa ++ [o]
    if k != 0 then sb := sb ++ [o]
  let p : Pair := { a := ← node x sa 0, b := ← node x sb 0, cid }
  let p ← (← p.connect x x).run x x 200000 1000 100000
  let ia ← idsOf p.a.db
  let ib ← idsOf p.b.db
  t.ok "full: a holds the whole history" (sameSet ia (h.map (·.id)))
  t.ok "full: b holds the whole history" (sameSet ib (h.map (·.id)))
  let mut agree := true
  for o in h do
    if (← statusOf p.a.db o.id) != (← statusOf p.b.db o.id) then agree := false
  t.ok "full: same verdict for every op" agree
  t.ok "full: both report the room settled" (
    (p.a.conn? cid).any (has ·.settled c) && (p.b.conn? cid).any (has ·.settled c))
  IO.println s!"full: {p.frames} frames"

  -- Stream: a new op reaches the peer without another round.
  let a1 := (h.find? fun o => o.kind == 11).map (·.id) |>.getD c
  let late := post c c (Device.named "acme-founder") "k".toUTF8 "late news".toUTF8 99999
  let rounds := (p.a.conn? cid).map (·.round) |>.getD 0
  let p ← p.writeA x x [late]
  let p ← p.run x x (p.now + 50) 1000 1000
  t.ok "stream: the new op arrives" (has (← idsOf p.b.db) late.id)
  t.ok "stream: without another round" ((p.a.conn? cid).map (·.round) == some rounds)
  let _ := a1

  -- Windowed: b holds nothing and keeps posts from time 4000 on.
  let floor := 4000
  let pw : Pair := { a := ← node x h 0, b := ← node x [] floor, cid }
  let pw ← (← pw.connect x x).run x x 200000 1000 100000
  let inWindow := h.filter fun o => orderOf o == 0 || orderOf o ≥ floor
  let want := closure h (inWindow.map (·.id))
  let iw ← idsOf pw.b.db
  t.ok "windowed: b holds exactly its window and the closure" (sameSet iw want)
  t.ok "windowed: older posts stay behind" (iw.length < h.length)
  t.ok "windowed: a reaction brought its old post along" (h.any fun o =>
    orderOf o != 0 && orderOf o < floor && has iw o.id)
  let mut wagree := true
  for i in iw do
    if (← statusOf pw.a.db i) != (← statusOf pw.b.db i) then wagree := false
  t.ok "windowed: b judges every op it holds as a does" wagree
  IO.println s!"windowed: {iw.length} of {h.length} ops, {pw.frames} frames"

  -- Lossy: a quarter of frames lost.
  let pl : Pair := { a := ← node x sa 0, b := ← node x sb 0, cid, loss := 25 }
  let pl ← (← pl.connect x x).run x x 3000000 1000 400000
  t.ok "lossy: a converges" (sameSet (← idsOf pl.a.db) (h.map (·.id)))
  t.ok "lossy: b converges" (sameSet (← idsOf pl.b.db) (h.map (·.id)))
  t.ok "lossy: frames were lost and the connection redialed" (pl.lost > 0 && pl.reconnects > 0)
  IO.println s!"lossy: {pl.frames} frames, {pl.lost} lost, {pl.reconnects} redials"

  -- Rooms: a holds two communities; b may see only the first.
  let (h2, c2) := history "other" 2 10
  let xa := sync [c]
  let xb := sync [c, c2]
  let pr : Pair := { a := ← node xa (h ++ h2) 0, b := ← node xb [] 0, cid }
  let pr ← (← pr.connect xa xb).run xa xb 200000 1000 100000
  let ir ← idsOf pr.b.db
  t.ok "rooms: b holds the community it may see" (sameSet ir (h.map (·.id)))
  t.ok "rooms: b holds nothing of the other" (!h2.any fun o => has ir o.id)
  -- b asks for the other's ops by id: a ignores it.
  let (_, e) ← pr.a.onBytes xa cid (Msg.want (h2.map (·.id))).op.bytes pr.now
  t.ok "rooms: a want for another room's ops is ignored" (e.send.isEmpty)
  -- b pushes another room's op: a does not take it.
  let foreign := (history "third" 0 1).1.head!
  let (_, _) ← pr.a.onBytes xa cid foreign.bytes pr.now
  t.ok "rooms: an op of another room is not taken" (!has (← idsOf pr.a.db) foreign.id)
  -- Garbage, and a local op, are ignored.
  let (_, e2) ← pr.a.onBytes xa cid "not an op".toUTF8 pr.now
  let (_, e3) ← pr.a.onBytes xa cid (secret "seed".toUTF8).bytes pr.now
  t.ok "garbage: ignored" (e2.send.isEmpty && e2.drop.isEmpty)
  t.ok "a peer's local op: not taken" (e3.send.isEmpty && !has (← idsOf pr.a.db) (secret "seed".toUTF8).id)

  t.finish "syncpair"
