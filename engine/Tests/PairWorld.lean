/-
The pure two-node world (Connection/World.lean) run with libsodium's
Keys and Ed25519: the same `World.step` the pair laws are stated over,
here with an honest scheduler that delivers every payload to the node
it is addressed to and ticks both nodes. It checks that the harness is
the running code and that an honest execution does what the laws need
to be non-vacuous: A founds and invites, B joins over the bare wire,
A approves, both establish one session, and a post crosses it each way.
Then it replays every payload already sent, once more, to both nodes,
and checks what the replay adds.
-/
import Tests.Lib
import Connection.World

open Engine Engine.Sync Community Tests Connection Connection.Pair

def P : Setup :=
  { C := ed25519, K := sodium, cfg := { every := 30000, patience := 20000 }
    addrA := "A:7001".toUTF8, addrB := "B:7001".toUTF8
    entA := fun i => sha256 (Codec.encode ("A entropy".toUTF8, i))
    entB := fun i => sha256 (Codec.encode ("B entropy".toUTF8, i))
    seedA := sha256 "seed A".toUTF8, seedB := sha256 "seed B".toUTF8 }

def seedA := P.seedA
def seedB := P.seedB

/-- The honest scheduler: deliver everything sent since `from`, each to
the node it was addressed to (from its sender's address), then tick
both nodes. -/
def round (w : World) (now : Nat) : World := Id.run do
  let mut w := w
  let pending := w.wire.drop w.delivered.length
  let mut acts : List Act := []
  for (fromA, to, bytes) in pending do
    let toA := to == P.addrA
    let src := P.addr fromA
    acts := acts ++ [.deliver toA src bytes now]
  w := w.run P acts
  w.run P [.tick true now, .tick false now]

/-- Rounds, 200 ms apart. -/
def rounds (w : World) (start n : Nat) : World := Id.run do
  let mut w := w
  for i in [0:n] do w := round w (start + 200 * (i + 1))
  return w

def onSide (w : World) (isA : Bool) {α : Type} (m : NodeM α) : α := (m (w.side isA).box).1

def stored (w : World) (isA : Bool) (x : Id) : Bool := (onSide w isA (Store.getOp (F := F) x)).isSome
def ests (w : World) (isA : Bool) : List Connection.Fact := (onSide w isA (rows established.all [])).map (·.2)
def opCount (w : World) (isA : Bool) : Nat := (w.side isA).box.held.log.length

def main : IO UInt32 := do
  let t ← Checks.new
  let dA := Device.ofSeed seedA
  let dB := Device.ofSeed seedB
  let mut w := World.init P
  w := w.step P (.write true (found seedA "Acme".toUTF8 "Ann".toUTF8 1 (sha256 "key".toUTF8)
    (sha256 "esk".toUTF8)).ops 0)
  let c := (root dA).id
  let (wi, link) := inviteTo c c seedA (sha256 "bearer".toUTF8) [P.addrA]
  w := w.step P (.write true wi.ops 0)
  w := w.step P (.write false (joinOps link seedB "Bea".toUTF8).ops 0)
  let req := link.request dB
  w := rounds w 0 20
  t.ok "A stored B's join request, from the hello" (stored w true req.id)
  t.ok "no session before approval" ((ests w true).isEmpty && (ests w false).isEmpty)
  let wr := onSide w true ((approveReq c req.id c seedA).liftL.run : NodeM Community.Write)
  w := w.step P (.write true wr.ops 4000)
  w := rounds w 4000 20
  match ests w true, ests w false with
  | [.established ca _ pa ha sa ra da], [.established cb _ pb hb sb rb db] =>
    t.ok "one session, the same id at both ends" (ca == cb)
    t.ok "each names the other" (pa == dB.pk && pb == dA.pk)
    t.ok "the same handshake hash, crossed keys" (ha == hb && sa == rb && ra == sb)
    t.ok "B dialed, A answered" (db && !da)
  | _, _ => t.ok "each end holds one session" false
  w := rounds w 8000 40
  let pA := post c c dA "k".toUTF8 "from A".toUTF8 5
  w := w.step P (.write true [pA] 20000)
  let pB := post c c dB "k".toUTF8 "from B".toUTF8 6
  w := w.step P (.write false [pB] 20000)
  w := rounds w 20000 10
  t.ok "a post crosses the session from A to B" (stored w false pA.id)
  t.ok "and from B to A" (stored w true pB.id)
  -- Replay: every payload sent so far, again, to both nodes.
  let before := (opCount w true, opCount w false, ests w true, ests w false)
  let seen := w.wire
  let mut wr := w
  for (_, _, bytes) in seen do
    wr := wr.step P (.deliver true "X:1".toUTF8 bytes 23000)
    wr := wr.step P (.deliver false "X:1".toUTF8 bytes 23000)
  let ests' := (ests wr true, ests wr false)
  t.ok "replaying everything opens no session at either end" (ests'.1 == before.2.2.1 && ests'.2 == before.2.2.2)
  let shared (w : World) (isA : Bool) : Nat :=
    ((w.side isA).box.held.log.filter fun o => match P.fam.scope o with | .shared _ => true | _ => false).length
  t.ok "and adds no shared op at either end" (shared wr true == shared w true && shared wr false == shared w false)
  IO.println s!"replay: ops A {before.1} -> {opCount wr true}, B {before.2.1} -> {opCount wr false}"
  -- FINDING: a replayed frame that opens rebinds its session's return
  -- address (`Node.onFrame`'s `setAddr`), so the session's frames now go
  -- to the replayer's address. Frame counters (`Frame.fresh`) are the fix.
  let liveCid := (ests w true).head?.bind fun | .established i .. => some i | _ => none
  t.ok "FINDING: a replayed frame diverts the session's frames to the replayer's address"
    (match liveCid with
      | some cid => (wr.side true).node.addr? cid == some "X:1".toUTF8 && (w.side true).node.addr? cid == some P.addrB
      | none => false)
  for isA in [true, false] do
    let old := (w.side isA).box.held.log.map (·.id)
    let added := (wr.side isA).box.held.log.filter fun o => !old.contains o.id
    let gone := (w.side isA).box.held.log.filter fun o => !((wr.side isA).box.held.log.map (·.id)).contains o.id
    let desc (o : Op) : String :=
      let what := match (Codec.decode o.body : Option Connection.Body) with
        | some (.recv onConn _ a _) => s!"recv(onConn={onConn}, addr={String.fromUTF8! a}) of kind " ++
            (match o.reqs.head? with
              | some r => match (Store.getOp (F := F) r : NodeM _) (wr.side isA).box with
                | (some x, _) => toString x.kind
                | _ => "?"
              | none => "?")
        | _ => ""
      s!"{o.kind} {what}"
    IO.println s!"{if isA then "A" else "B"} added: {added.map desc}  purged: {gone.map (·.kind)}"
  IO.println s!"replay sent {wr.wire.length - w.wire.length} payloads"
  -- A second dial from B (a fresh ephemeral) supersedes the first
  -- session at both ends, which purges it; then the first request is
  -- replayed to A.
  let firstReq := (w.wire.find? fun (fromA, _, bytes) => !fromA && bytes[0]? == some 0).map (·.2.2)
  let e2 := sha256 "second ephemeral".toUTF8
  let some ro2 := Request.op sodium seedB dA.pk e2 (hello c P.addrB []) | t.ok "a second request" false; return 1
  w := w.step P (.write false [ro2, Eph.op e2 ro2.id, Send.op P.addrA ro2] 24000)
  w := rounds w 24000 20
  let live := ests w true
  t.ok "after the redial, each end keeps one session, the same" (live.length == 1 && (ests w false).length == 1)
  match firstReq with
  | none => t.ok "the first request was on the wire" false
  | some rq =>
    let w2 := w.step P (.deliver true P.addrB rq 30000)
    let w2 := rounds w2 30000 5
    IO.println s!"after replaying the first request to A: A holds {(ests w2 true).length} sessions, B {(ests w2 false).length}"
    let cids (l : List Connection.Fact) : List ByteArray := l.filterMap fun | .established i .. => some i | _ => none
    -- FINDING: the pair's replay law fails today. The first request's
    -- session was purged, so A opens and answers it afresh, and the
    -- one-per-peer choice keeps the newest arrival: the new session,
    -- which no one else holds. A drops the live one; B still holds it.
    t.ok "FINDING: a replayed purged request makes A answer it and drop the live session"
      (!(cids live |>.all fun x => (cids (ests w2 true)).contains x) && (ests w2 false).length == 1)
    let kept := onSide w2 true (sessions : NodeM _)
    IO.println s!"A keeps {kept.length}: live kept = {(cids live).all fun x => kept.any (·.1 == x)}"
    let all := onSide (w.step P (.deliver true P.addrB rq 30000)) true (allSessions : NodeM _)
    for (cid, _, dialer, a, at_) in all do
      IO.println s!"  A after the replay step: session {hex (cid.extract 0 4)} dialer={dialer} from {String.fromUTF8! a} at {at_}"
  t.finish "pairworld"
