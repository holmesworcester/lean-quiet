/- Real Node/SQLite/Runner/TCP admission regression. Three distinct fixed
authorized peer identities share one transport. Plain sealing is explicit;
production Noise/established-hook reachability is a separate audit. -/
import tests.engine.Lib
import tests.engine.RetryReachability
import engine.wire.Tcp
import engine.core.Exit

namespace RetryMultiplex
open Engine Engine.Sync Community Tests Std.Async Std.Net

def fam : Family Fact := family ed25519
def author := Device.named "multiplex-author"
def rootOp := root author (keyOf author) .empty
def cid (i : Nat) := sha256 s!"multiplex-session-{i}".toUTF8
def peer (i : Nat) := cryptoSeal.pub (Bytes.digest s!"multiplex-node-key-{i}".toUTF8)

def setup (address : ByteArray) (established : Bool := true) (order : List Nat := [2,1,0]) : Sync Fact (SqlM Fact) :=
  { fam, cfg := { live := 1000000000, safety := 1000000000 },
    hooks := {
      rooms := fun c => pure (if (List.range 3).any (fun i => c == cid i) then [.sync rootOp.id] else [])
      sealFor := plainSeal, openFrame := plainOpen
      retryKey := fun c => pure ((List.range 3).find? (fun i => c == cid i) |>.map peer)
      established := pure (if established then order.map (fun i => (cid i, address, true)) else []) },
    catalog := some Catalog.sql, retryStore := some RetryStore.sql,
    deferredRetries := true, retryRoom := fun _ => some maxFrame }

def waitFor (ms : Nat) (p : IO Bool) : IO Bool := do
  let start ← IO.monoMsNow
  while (← IO.monoMsNow) < start + ms do
    if ← p then return true
    IO.sleep 5
  return false

def pureOrder (t : Checks) : IO Unit := do
  let db ← Db.openAt ":memory:"
  (receive fam [rootOp]).run db
  let x := setup "same-transport".toUTF8
  let (initial, _) ← ((Node.boot fam [rootOp] 0).finish x {} 0).run db
  t.ok "actual follow opens the expected A B C order" (initial.conns.map Prod.fst == (List.range 3).map cid)
  let mut n := initial
  let mut trace : List Nat := []
  let mut stable := true
  for tick in [1:41] do
    let (next, out) ← (n.onTick x tick).run db
    n := next
    stable := stable && n.conns.map Prod.fst == initial.conns.map Prod.fst
    for ticket in out.retry do
      if let some i := (List.range 3).find? (fun i => ticket.peer == peer i) then trace := trace ++ [i]
      -- Isolate the scheduling recurrence with an immediate successful native
      -- completion. The separate Runner case below verifies real wire attempts.
      ((RetryStore.sql (F := Fact)).commit ticket).run db
  t.ok "actual apply and serveOwed preserve connection order over 40 ticks" stable
  t.ok "actual Node retry admission rotates A B C over 40 opportunities"
    (trace == (List.range 40).map (· % 3))
  let c ← ((RetryStore.sql (F := Fact)).load (peer 2)).run db
  t.ok "authorized late session makes durable catalog progress" (c.after == 1)
  IO.println s!"actual Node retry admission trace: {trace}"

def decode (bytes : ByteArray) : Option (Id × List Op) := do
  if bytes[0]? != some sealedTag then none else do
    let (c, inner) ← (Codec.decode (bytes.extract 1 bytes.size) : Option (Id × ByteArray))
    let ops ← (Codec.decode inner : Option (List ByteArray))
    return (c, ops.filterMap Op.decode)

/-- These cases exercise the actual Node pass and SQLite, including the
nonproduction in-memory cursor fallback and the preserved direct interpreter. -/
def nodeCases (t : Checks) : IO Unit := do
  let db ← Db.openAt ":memory:"
  (receive fam [rootOp]).run db
  let x := setup "shared".toUTF8
  let (initial, _) ← ((Node.boot fam [rootOp] 0).finish x {} 0).run db
  let fallback := { x with retryStore := none }
  let (queued, offered) ← (initial.onTick fallback 1).run db
  let cursor := fun i => ((queued.sweeps.find? (fun p => p.1 == cid i)).map Prod.snd).getD {}
  t.ok "refused candidates retain in-memory fallback positions"
    ((cursor 0).after == 1 && (cursor 1).after == 0 && (cursor 2).after == 0 && offered.retry.length == 1)
  let blocked := { fallback with retryRoom := fun _ => some 0 }
  let mut waiting := queued
  let mut quiet := true
  for tick in [2:20] do
    let (next, output) ← (waiting.onTick blocked tick).run db
    waiting := next
    quiet := quiet && output.retry.isEmpty && next.retryOrder == queued.retryOrder
  t.ok "busy socket ticks do not rotate pending retry order" quiet
  let split := initial.setAddr (cid 2) "independent".toUTF8
  let (_, output) ← (split.onTick fallback 1).run db
  t.ok "one scan admits independent sockets without consuming another socket share"
    (output.retry.length == 2 && output.retry.any (·.peer == peer 0) && output.retry.any (·.peer == peer 2))
  let denied := { fallback with hooks := { fallback.hooks with
    rooms := fun c => pure (if c == cid 2 then [] else [.sync rootOp.id]) } }
  let (_, output) ← (({ initial with retryOrder := [cid 2, cid 0, cid 1] }).onTick denied 1).run db
  t.ok "current authorization still excludes a first-position revoked room"
    (!output.retry.any (·.peer == peer 2))
  let direct := { fallback with deferredRetries := false, room := fun _ => some 10000 }
  let (wrapped, wo) ← (initial.onTick direct 1).run db
  let (legacy, lo) ← (initial.onTickDirect direct 1).run db
  t.ok "direct cursor interpreter retains exact prior clock output and cursor order"
    (wo.send == lo.send && wo.retry.isEmpty && decide (wrapped.sweeps = legacy.sweeps) &&
      wrapped.conns.map Prod.fst == legacy.conns.map Prod.fst)

/-- Every tick admits a new session before the next pass. Newcomers must
not jump ahead of C, which was already waiting behind exactly A and B. -/
def churn (t : Checks) : IO Unit := do
  let db ← Db.openAt ":memory:"
  (receive fam [rootOp]).run db
  let address := "churning-shared-transport".toUTF8
  let established ← IO.mkRef ([2,1,0].map (fun i => (cid i, address, true)))
  let x := { setup address with hooks := {
    rooms := fun _ => pure [.sync rootOp.id], sealFor := plainSeal, openFrame := plainOpen,
    retryKey := fun id => pure (some id), established := established.get } }
  let (initial, _) ← ((Node.boot fam [rootOp] 0).finish x {} 0).run db
  let mut node := initial
  let mut when := 0
  for tick in [1:13] do
    established.modify (· ++ [(cid (tick+2), address, true)])
    let (next, output) ← (node.onTick x tick).run db
    node := next
    if when == 0 && output.retry.any (·.peer == cid 2) then when := tick
    for ticket in output.retry do ((RetryStore.sql (F := Fact)).commit ticket).run db
  t.ok "continuing session arrivals cannot overtake an existing pending retry" (when == 3)
  t.ok "actual retry queue retains each live session exactly once"
    (node.retryOrder.eraseDups.length == node.retryOrder.length && node.retryOrder.length ≤ node.conns.length)

def runner (t : Checks) (preferLate : Bool := false) : IO Unit := do
  let source ← Db.openAt ":memory:"
  (receive fam [rootOp]).run source
  let first ← Db.openAt ":memory:"
  let second ← Db.openAt ":memory:"
  let third ← Db.openAt ":memory:"
  let receivers := [first, second, third]
  let server ← TCP.Socket.Server.mk
  server.bind (.v4 ⟨IPv4Addr.ofParts 127 0 0 1, 0⟩)
  server.listen 1
  let address := (addrText (← server.getSockName)).toUTF8
  let cfg : RunConfig := { tickMs := 10, window := 0, stallMs := 5000, idle := 1000000000 }
  let run ← Runner.start (setup address true (if preferLate then [1,0,2] else [2,1,0])) source 0 0 (fun _ => pure ()) cfg
  let mut accepted := none
  for _ in [0:1000] do
    accepted ← server.tryAccept
    if accepted.isSome then break
    IO.sleep 5
  let some client := accepted | run.stop; throw (IO.userError "multiplex runner failed to dial")
  let aborter ← SocketAbort.capture client
  let stopped ← StopFlag.new
  let counts ← IO.mkRef (#[0,0,0] : Array Nat)
  let seen ← IO.mkRef ([] : List Nat)
  let reader ← IO.asTask (prio := .dedicated) do
    let mut buffered := ByteArray.empty
    while !(← stopped.get) do
      let some bytes ← readSocket client stopped 65536 | break
      let (packets, rest) := frames (buffered ++ bytes)
      buffered := rest.getD .empty
      for packet in packets do
        if let some (c, ops) := decode packet then
          if ops.any (fun op => op.id == rootOp.id) then
            if let some i := (List.range 3).find? (fun i => c == cid i) then
              counts.modify fun a => a.set! i (a[i]! + 1)
              seen.modify (· ++ [i])
              if let some db := receivers[i]? then (receive fam ops).run db
  let started ← IO.monoMsNow
  let enough ← waitFor 5000 do return (← counts.get).foldl (· + ·) 0 ≥ 120
  let elapsed := (← IO.monoMsNow) - started
  let count ← counts.get
  let lanes ← run.lanes
  let counters ← run.counters
  stopped.request
  if let some cap := aborter then discard <| cap.abort
  if let .error e ← IO.wait reader then throw e
  run.stop
  closeListener server.native
  t.ok "real runner uses one shared TCP transport" (lanes.length == 1)
  t.ok "120 actual native retry payloads complete while the process keeps stepping"
    (enough && counters.ticks.toNat ≥ 100)
  t.ok s!"both leading sessions repeatedly reach the real TCP receiver, rotated={preferLate}"
    (count.all (· ≥ 35))
  t.ok "both serviced peers derive a valid signed root in real SQLite"
    ((← receivers.allM fun db => do return (← (Store.getStatus rootOp.id : SqlM Fact _).run db).any (fun v => match v with | .valid _ => true | _ => false)))
  t.ok "every admitted authorized session receives catalog service" (count.all (· > 0))
  t.ok "actual native order rotates all three sessions from either initial position"
    ((← seen.get).take 9 == (List.range 9).map (fun i => if preferLate then [2,0,1][i % 3]! else i % 3))
  IO.println s!"actual TCP rotated={preferLate} counts {count}; completed ticks {counters.ticks}; elapsed {elapsed} ms"
  IO.println s!"actual TCP first 24 data sessions: {(← seen.get).take 24}"

end RetryMultiplex

def mainBody : IO UInt32 := do
  let t ← Tests.Checks.new
  RetryReachability.run t
  RetryMultiplex.pureOrder t
  RetryMultiplex.nodeCases t
  RetryMultiplex.churn t
  RetryMultiplex.runner t
  RetryMultiplex.runner t true
  t.finish "retry-multiplex"

/-- Leaves by `IO.Process.exit` (Engine.exitAfter): returning from
`main` with a runner's threads alive would wait for them for good. -/
def main : IO UInt32 := Engine.exitAfter mainBody
