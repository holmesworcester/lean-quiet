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
  even when it asks for them by id, and cannot push them in; and every
  id offered to it, in a have or an id claim, names a stored op of the
  community it may see (`have_shown`), new ops of the other included;
  and its haves learn nothing of the other community or of local ops:
  a have of an id held only there is answered as one of an id held
  nowhere, and a have for the other room is ignored (`hold_reply_local`);
- garbage frames are ignored;
- stream: an op written after the round reaches the peer at once,
  without another round.
-/
import tests.engine.Lib

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
    let p := post c a d "k".toUTF8 s!"{tag} post {i}".toUTF8 (i + 1) (1000 + 100 * i)
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

/-- A side whose store holds these ops, with this floor. -/
def node (x : Sync Fact (SqlM Fact)) (ops : List Op) (floor : Nat) (addr : String) : IO Side := do
  let db ← memDb
  (receive fam (intake fam true ops)).run db
  return { db, node := Node.boot x.fam (← (dumpOps (F := Fact)).run db) floor, addr := addr.toUTF8 }

def sync (rooms : List Id) : Sync Fact (SqlM Fact) :=
  { fam, cfg, hooks := { rooms := fun _ => pure rooms, sealFor := plainSeal, openFrame := plainOpen } }

/-- A payload as the session's sealed frame (the harness's plain one). -/
def frameOf (cid : Id) (b : ByteArray) : ByteArray :=
  tagged sealedTag (Codec.encode (cid, Codec.encode [b]))

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

/-- What a frame of the harness's plain seal offers, as its peer reads
it: the ids of its haves and id claims, and the data ops it carries. -/
def offeredIn (f : ByteArray) : List Id × List Op := Id.run do
  let some (_, bundle) := (Codec.decode (f.extract 1 f.size) : Option (Id × ByteArray)) | return ([], [])
  let some inner := (Codec.decode bundle : Option (List ByteArray)) | return ([], [])
  let mut ids : List Id := []
  let mut data : List Op := []
  for b in inner do
    let some o := Op.decode b | continue
    match Msg.ofOp o with
    | some (.hold _ xs) => ids := ids ++ xs
    | some (.rbsr _ _ cs) => ids := ids ++ cs.flatMap fun | .ids _ xs => xs | .fp .. => []
    | some _ => pure ()
    | none => data := data ++ [o]
  return (ids, data)

/-- The ids a frame of the harness's plain seal wants. -/
def wantedIn (f : ByteArray) : List Id := Id.run do
  let some (_, bundle) := (Codec.decode (f.extract 1 f.size) : Option (Id × ByteArray)) | return []
  let some inner := (Codec.decode bundle : Option (List ByteArray)) | return []
  let mut ids : List Id := []
  for b in inner do
    let some o := Op.decode b | continue
    if let some (.want xs) := Msg.ofOp o then ids := ids ++ xs
  return ids

/-- Run the pair as `Pair.run` does, keeping every frame a sends to b. -/
def runWatch (xa xb : Sync Fact (SqlM Fact)) (p : Pair) (stop fuel : Nat) : IO (Pair × List ByteArray) := do
  let mut p := p
  let mut seen : List ByteArray := []
  for _ in [0:fuel] do
    if p.now ≥ stop then break
    if let some f := p.toB.head? then seen := f :: seen
    p ← p.step xa xb 1000
  return (p, seen.reverse)

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
  let p : Pair := { a := ← node x sa 0 "a", b := ← node x sb 0 "b", cid }
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
    (p.a.node.conn? cid).any (has ·.settled c) && (p.b.node.conn? cid).any (has ·.settled c))
  IO.println s!"full: {p.frames} frames"

  -- Stream: a new op reaches the peer without another round.
  let a1 := (h.find? fun o => o.kind == 11).map (·.id) |>.getD c
  let late := post c c (Device.named "acme-founder") "k".toUTF8 "late news".toUTF8 1 99999
  let rounds := (p.a.node.conn? cid).map (·.round) |>.getD 0
  let p ← p.writeA x x [late]
  let p ← p.run x x (p.now + 50) 1000 1000
  t.ok "stream: the new op arrives" (has (← idsOf p.b.db) late.id)
  t.ok "stream: without another round" ((p.a.node.conn? cid).map (·.round) == some rounds)
  let _ := a1

  -- Windowed: b holds nothing and keeps posts from time 4000 on.
  let floor := 4000
  let pw : Pair := { a := ← node x h 0 "a", b := ← node x [] floor "b", cid }
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
  let pl : Pair := { a := ← node x sa 0 "a", b := ← node x sb 0 "b", cid, loss := 25 }
  let pl ← (← pl.connect x x).run x x 3000000 1000 400000
  t.ok "lossy: a converges" (sameSet (← idsOf pl.a.db) (h.map (·.id)))
  t.ok "lossy: b converges" (sameSet (← idsOf pl.b.db) (h.map (·.id)))
  t.ok "lossy: frames were lost and the connection redialed" (pl.lost > 0 && pl.reconnects > 0)
  IO.println s!"lossy: {pl.frames} frames, {pl.lost} lost, {pl.reconnects} redials"

  -- Rooms: a holds two communities; b may see only the first.
  let (h2, c2) := history "other" 2 10
  let xa := sync [c]
  let xb := sync [c, c2]
  let pr : Pair := { a := ← node xa (h ++ h2) 0 "a", b := ← node xb [] 0 "b", cid }
  let pr ← pr.connect xa xb
  let first := pr.toB
  let (pr, seen) ← runWatch xa xb pr 200000 100000
  let ir ← idsOf pr.b.db
  t.ok "rooms: b holds the community it may see" (sameSet ir (h.map (·.id)))
  t.ok "rooms: b holds nothing of the other" (!h2.any fun o => has ir o.id)
  -- What a offered b: new ops of both communities are written at a too.
  let f2 := Device.named "other-founder"
  let news := [post c c (Device.named "acme-founder") "k".toUTF8 "news here".toUTF8 99990,
    post c2 c2 f2 "k".toUTF8 "news there".toUTF8 99991]
  let pr ← pr.writeA xa xb news
  let (pr, seen2) ← runWatch xa xb pr (pr.now + 5000) 10000
  let shown := (h ++ news.take 1).map (·.id)
  let aIds ← idsOf pr.a.db
  let mut offered := 0
  let mut ok := true
  for f in first ++ seen ++ seen2 do
    let (ids, data) := offeredIn f
    offered := offered + ids.length
    ok := ok && ids.all (fun i => has shown i && has aIds i) && data.all (fun o => has shown o.id)
  t.ok "rooms: a offered b ids" (offered > 0)
  t.ok "rooms: every id offered to b names a stored op of the community it may see" ok
  t.ok "rooms: the new op b may see reached it" (has (← idsOf pr.b.db) (news.head!).id)
  IO.println s!"rooms: {offered} ids offered to b"
  -- b's haves, answered by a: a holds x2 only in the other room, the
  -- secret only locally, and nothing named y.
  let (a', _) ← pr.a.run fun n => n.onWrite xa [secret "a seed".toUTF8] pr.now
  let pr := { pr with a := a' }
  let x2 := (h2.getLast!).id
  let sec := (secret "a seed".toUTF8).id
  let y := sha256 "held nowhere".toUTF8
  let x1 := (h.getLast!).id
  let reply (r : Id) (i : Id) : IO (List Id × Bool) := do
    let (_, e) ← pr.a.run fun n => n.onFrame xa "b".toUTF8 (frameOf cid (Msg.hold r [i]).op.bytes) (pr.now + 1)
    return (e.send.flatMap fun (_, f) => wantedIn f, e.send.isEmpty)
  t.ok "holds: a holds the secret, only locally" (has (← idsOf pr.a.db) sec)
  t.ok "holds: an id held nowhere is wanted" ((← reply c y).1 == [y])
  t.ok "holds: an id a holds only in the other room is wanted, as if held nowhere" ((← reply c x2).1 == [x2])
  t.ok "holds: an id a holds only locally is wanted, as if held nowhere" ((← reply c sec).1 == [sec])
  t.ok "holds: an id a holds in b's room is not wanted" ((← reply c x1).1 == [])
  t.ok "holds: a have for the other room is ignored" ((← reply c2 x2).2 && (← reply c2 y).2)
  -- b asks for the other's ops by id: a ignores it.
  let (_, e) ← pr.a.run fun n => n.onFrame xa "b".toUTF8 (frameOf cid (Msg.want (h2.map (·.id))).op.bytes) pr.now
  t.ok "rooms: a want for another room's ops is ignored" (e.send.isEmpty)
  -- b pushes another room's op: a does not take it.
  let foreign := (history "third" 0 1).1.head!
  let (_, _) ← pr.a.run fun n => n.onFrame xa "b".toUTF8 (frameOf cid foreign.bytes) pr.now
  t.ok "rooms: an op of another room is not taken" (!has (← idsOf pr.a.db) foreign.id)
  -- Garbage, and a local op, are ignored.
  let (_, e2) ← pr.a.run fun n => n.onFrame xa "b".toUTF8 "not an op".toUTF8 pr.now
  let (_, e3) ← pr.a.run fun n => n.onFrame xa "b".toUTF8 (frameOf cid (secret "seed".toUTF8).bytes) pr.now
  t.ok "garbage: ignored" (e2.send.isEmpty && e2.drop.isEmpty)
  t.ok "a peer's local op: not taken" (e3.send.isEmpty && !has (← idsOf pr.a.db) (secret "seed".toUTF8).id)

  t.finish "syncpair"
