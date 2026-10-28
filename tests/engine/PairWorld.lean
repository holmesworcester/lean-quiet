/-
The pure two-node world (ops/connection/World.lean) run with libsodium's
Keys and Ed25519: the same `World.step` the pair laws are stated over,
here with an honest scheduler that delivers every payload to the node
it is addressed to and ticks both nodes. It checks that the harness is
the running code and that an honest execution does what the laws need
to be non-vacuous: A founds and invites, B joins over the bare wire,
A approves, both establish one session, and a post crosses it each way.
Then it replays every payload already sent, once more, to both nodes,
and checks what the replay adds.

Then B redials (a fresh ephemeral supersedes the first session at both
ends, which purges it), and the first request is replayed to A. A
answers it afresh, but keeps the live session (`kept_heard`): the new
one has not heard its peer and never will, and patience drops it. The
same run with the one-per-peer rule before `heard` (a mutant) loses the
live session at A: the negative control.
-/
import tests.engine.Lib
import ops.connection.World

open Engine Engine.Sync Community Tests Connection Connection.Pair

def base : Setup :=
  { C := ed25519, K := sodium, cfg := { every := 30000, patience := 20000 }
    addrA := "A:7001".toUTF8, addrB := "B:7001".toUTF8
    entA := fun i => sha256 (Codec.encode ("A entropy".toUTF8, i))
    entB := fun i => sha256 (Codec.encode ("B entropy".toUTF8, i))
    seedA := sha256 "seed A".toUTF8, seedB := sha256 "seed B".toUTF8 }

/-- The rule before `heard`: per peer and side the latest, then the
smaller id, among every session. -/
def mutantKept (all : List Cand) : List Id := (onePer (bestOf all)).map (·.2)

/-- The honest scheduler: deliver everything not yet delivered, each to
the node it was addressed to (from its sender's address), then tick
both nodes. -/
def round (P : Setup) (w : World) (now : Nat) : World := Id.run do
  let pending := w.wire.drop w.delivered.length
  let acts := pending.map fun (fromA, to, bytes) => Act.deliver (to == P.addrA) (P.addr fromA) bytes now
  (w.run P acts).run P [.tick true now, .tick false now]

/-- Rounds, 200 ms apart. -/
def rounds (P : Setup) (w : World) (start n : Nat) : World := Id.run do
  let mut w := w
  for i in [0:n] do w := round P w (start + 200 * (i + 1))
  return w

def onSide (w : World) (isA : Bool) {α : Type} (m : NodeM α) : α := (m (w.side isA).box).1

def stored (w : World) (isA : Bool) (x : Id) : Bool := (onSide w isA (Store.getOp (F := F) x)).isSome
def ests (w : World) (isA : Bool) : List Connection.Fact := (onSide w isA (rows established.all [])).map (·.2)
def cids (l : List Connection.Fact) : List ByteArray := l.filterMap fun | .established i .. => some i | _ => none
def opCount (w : World) (isA : Bool) : Nat := (w.side isA).box.held.log.length

/-- A founds and invites, B joins, A approves, both run 60 rounds. -/
def joined (P : Setup) : World × Id := Id.run do
  let dA := Device.ofSeed P.seedA
  let dB := Device.ofSeed P.seedB
  let mut w := World.init P
  w := w.step P (.write true (found P.seedA "Acme".toUTF8 "Ann".toUTF8 1 (sha256 "key".toUTF8)
    (sha256 "esk".toUTF8)).ops 0)
  let c := (root dA).id
  let (wi, link) := inviteTo c c P.seedA (sha256 "bearer".toUTF8) [P.addrA]
  w := w.step P (.write true wi.ops 0)
  w := w.step P (.write false (joinOps link P.seedB "Bea".toUTF8).ops 0)
  w := rounds P w 0 20
  let wr := onSide w true ((approveReq c (link.request dB).id c P.seedA).liftL.run : NodeM Community.Write)
  w := w.step P (.write true wr.ops 4000)
  return (rounds P w 4000 60, c)

/-- After `joined`: B redials, both run 20 rounds, then the first
request is replayed to A (as from B's address) and both run `n` more
rounds. The world before the replay, and after. -/
def redialReplay (P : Setup) (n : Nat) : Option (World × World) := do
  let (w, c) := joined P
  let first ← (w.wire.find? fun (fromA, _, bytes) => !fromA && bytes[0]? == some 0).map (·.2.2)
  let e2 := sha256 "second ephemeral".toUTF8
  let ro2 ← Request.op sodium P.seedB (Device.ofSeed P.seedA).pk e2 (hello c P.addrB [])
  let w := w.step P (.write false [ro2, Eph.op e2 ro2.id, Send.op P.addrA ro2] 24000)
  let w := rounds P w 24000 20
  let w2 := w.step P (.deliver true P.addrB first 30000)
  return (w, rounds P w2 30000 n)

def main : IO UInt32 := do
  let t ← Checks.new
  let P := base
  let dA := Device.ofSeed P.seedA
  let dB := Device.ofSeed P.seedB
  let (w, c) := joined P
  t.ok "A stored B's join request, from the hello" (stored w true ((inviteTo c c P.seedA (sha256 "bearer".toUTF8) [P.addrA]).2.request dB).id)
  match ests w true, ests w false with
  | [.established ca _ pa ha sa ra da], [.established cb _ pb hb sb rb db] =>
    t.ok "one session, the same id at both ends" (ca == cb)
    t.ok "each names the other" (pa == dB.pk && pb == dA.pk)
    t.ok "the same handshake hash, crossed keys" (ha == hb && sa == rb && ra == sb)
    t.ok "B dialed, A answered" (db && !da)
  | _, _ => t.ok "each end holds one session" false
  let pA := post c c dA "k".toUTF8 "from A".toUTF8 5
  let pB := post c c dB "k".toUTF8 "from B".toUTF8 6
  let w := (w.step P (.write true [pA] 20000)).step P (.write false [pB] 20000)
  let w := rounds P w 20000 10
  t.ok "a post crosses the session from A to B" (stored w false pA.id)
  t.ok "and from B to A" (stored w true pB.id)
  -- Replay: every payload sent so far, again, to both nodes.
  let mut wr := w
  for (_, _, bytes) in w.wire do
    wr := wr.step P (.deliver true "X:1".toUTF8 bytes 23000)
    wr := wr.step P (.deliver false "X:1".toUTF8 bytes 23000)
  t.ok "replaying everything opens no session at either end"
    (ests wr true == ests w true && ests wr false == ests w false)
  let shared (w : World) (isA : Bool) : Nat :=
    ((w.side isA).box.held.log.filter fun o => match P.fam.scope o with | .shared _ => true | _ => false).length
  t.ok "and adds no shared op at either end" (shared wr true == shared w true && shared wr false == shared w false)
  t.ok "and adds at either end only arrival records (recv, kind 38)"
    ([true, false].all fun isA =>
      ((wr.side isA).box.held.log.filter fun o => !((w.side isA).box.held.log.map (·.id)).contains o.id).all (·.kind == 38))
  -- FINDING: a replayed frame that opens rebinds its session's return
  -- address (`Node.onFrame`'s `setAddr`), so the session's frames now go
  -- to the replayer's address. Frame counters (`Frame.fresh`) are the fix.
  let liveCid := (cids (ests w true)).head?
  t.ok "FINDING: a replayed frame diverts the session's frames to the replayer's address"
    (match liveCid with
      | some cid => (wr.side true).node.addr? cid == some "X:1".toUTF8 && (w.side true).node.addr? cid == some P.addrB
      | none => false)
  -- A replayed request whose session was purged.
  match redialReplay P 5, redialReplay P 110, redialReplay { P with keepRule := mutantKept } 5 with
  | some (w, w2), some (_, w3), some (m, m2) =>
    let live := cids (ests w true)
    t.ok "after the redial, each end keeps one session, the same"
      (live.length == 1 && cids (ests w false) == live)
    t.ok "a replayed purged request: A answers it, and still holds the live session"
      (live.all (cids (ests w2 true)).contains && (ests w2 true).length == 2 && cids (ests w2 false) == live)
    t.ok "the answer has not heard its peer; the live session has"
      (let all := onSide w2 true (allSessions : NodeM _)
       all.all fun s => s.heard == live.contains s.cid)
    -- 110 rounds: past the answer's patience (it opened at 30000), and
    -- before B's next round on the idle live session (every 30000 ms).
    t.ok "once patience passes, A has dropped the answer and holds the live session alone, as B does"
      (cids (ests w3 true) == live && cids (ests w3 false) == live)
    let mlive := cids (ests m true)
    t.ok "negative control: under the rule before heard, the same replay makes A drop the live session"
      (mlive.length == 1 && !(mlive.all (cids (ests m2 true)).contains) && cids (ests m2 false) == mlive)
  | _, _, _ => t.ok "the redial and replay runs" false
  if (← IO.getEnv "DUMP").isSome then
    match redialReplay P 5, redialReplay P 110 with
    | some (w, w2), some (_, w3) =>
      for (nm, x) in [("before", w), ("after5", w2), ("after110", w3)] do
        for isA in [true, false] do
          let all := onSide x isA (allSessions : NodeM _)
          IO.println (s!"{nm} {if isA then "A" else "B"}: " ++ String.intercalate "; " (all.map fun s =>
            s!"{hex (s.cid.extract 0 4)} heard={s.heard} dialer={s.dialer} at={s.at_}"))
          let conns := (x.side isA).node.conns.map fun (cid, c) => s!"{hex (cid.extract 0 4)} pf={c.peerFloor} heard={c.heard}"
          IO.println s!"   conns {conns} dropped {(x.side isA).node.dropped.map fun c => hex (c.extract 0 4)}"
    | _, _ => pure ()
  t.finish "pairworld"
