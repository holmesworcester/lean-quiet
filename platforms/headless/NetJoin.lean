/-
Two apps joined over real TCP, each its own database and its own node
(the engine's Runner with the Connection family, as the phones run it),
on loopback ports: nothing is carried by hand.

A founds "club" and opens Add members: its link dials A's node. B pastes
the link, names itself and agrees: its node dials A with the request. A
sees it under Waiting to join and approves; the session opens, sync admits
B, B's home shows the community, and B's post reaches A's conversation.

    net_join <outdir>
-/
import Quiet
import platforms.headless.Sim

open App Engine Community Data

def tapAct (sm : Sim) (a : Pages.Act) : M Bool := do
  let s ← get
  let some pg := s.pageNow | return false
  match pg.taps.find? (·.2 == a) with
  | some (b, _) =>
    sm.cmds.modify (·.push s!"page {b.x + b.w / 2} {b.y + b.h / 2}")
    steps 3
    return true
  | none => return false

def fresh (dir : String) : IO Unit := do
  IO.FS.createDirAll dir
  for f in ["quiet.db", "quiet.db-wal", "quiet.db-shm"] do
    if ← System.FilePath.pathExists (dir ++ "/" ++ f) then IO.FS.removeFile (dir ++ "/" ++ f)

/-- Both apps step, in real time, until `p` holds of them (or `ms` pass). -/
def both (a b : St) (ms : Nat) (p : St → St → Bool) : IO (St × St × Bool) := do
  let mut a := a
  let mut b := b
  let t0 ← IO.monoMsNow
  while (← IO.monoMsNow) - t0 < ms do
    if p a b then return (a, b, true)
    a := (← (steps 1).run a).2
    b := (← (steps 1).run b).2
    IO.sleep 5
  return (a, b, p a b)

def main (args : List String) : IO UInt32 := do
  let dir := args[0]?.getD "out/net"
  fresh (dir ++ "/a"); fresh (dir ++ "/b")
  let fails ← IO.mkRef 0
  let check (name : String) (ok : Bool) : IO Unit := do
    IO.println s!"{if ok then "ok  " else "FAIL"} {name}"
    (← IO.getStdout).flush
    if !ok then fails.modify (· + 1)
  let screen : Array UInt32 := #[1080, 2400, 128, 63, 420]
  let sa ← Sim.new
  let sb ← Sim.new
  let pa := 47211
  let pb := 47212
  let a0 ← App.start sa.io screen (dir ++ "/a/quiet.db") (some (pa, true))
  let b0 ← App.start sb.io screen (dir ++ "/b/quiet.db") (some (pb, true))
  -- A founds "club"; its node starts; Add members gives the link
  let (link, a1) ← (show M String from do
    sa.cmds.modify (·.push "found club|Ann")
    steps 3
    waitIdle sa
    steps 3
    sa.cmds.modify (·.push "open invite")
    steps 3
    let s ← get
    return ((s.links.find? (·.1 == s.me.acc)).map (·.2)).getD "").run a0
  check s!"A's node runs ({a1.net.map (·.port)})" (a1.net.map (·.port.toNat) == some pa)
  let hints := ((Invite.parse link).map (·.hints.map fun h => (String.fromUTF8? h).getD "?")).getD []
  check s!"A's link dials A's node ({hints})" (hints == [s!"127.0.0.1:{pa}"])
  -- B pastes it, names itself, agrees
  let ((), b1) ← (show M Unit from do
    steps 2
    let _ ← tapAct sb .joinCommunity
    let _ ← tapAct sb .inviteLink
    let _ ← tapAct sb .pasteLink
    modify fun s => { s with field := link }
    steps 1
    let _ ← tapAct sb .continue_
    modify fun s => { s with field := "Bea" }
    steps 1
    let _ ← tapAct sb .continue_
    check "Agree & Join" (← tapAct sb .agree)
    waitIdle sb
    steps 3).run b0
  check "B waits to join" (b1.page == .waiting && b1.me.waiting)
  check s!"B's Waiting says where its request goes ({b1.me.dialing})" (b1.me.dialing == s!"127.0.0.1:{pa}")
  -- B's node dials A with the request: it shows under Waiting to join
  let (a2, b2, asked) ← both a1 b1 20000 fun a _ => a.asking.size == 1
  check s!"A sees B's request over TCP (B's node {b2.net.map (·.port)})" asked
  let ((), a3) ← (show M Unit from do
    sa.cmds.modify (·.push "switch club")
    steps 3
    let _ ← tapAct sa .requests
    check "A approves it" (← tapAct sa (.approve 0))
    steps 3).run a2
  -- the session opens; sync admits B
  let (a4, b4, inB) ← both a3 b2 30000 fun _ b => !b.me.waiting && b.me.name == "club"
  check s!"B is admitted and named \"{b4.me.name}\", page {repr b4.page}" inB
  let ((), b5) ← (show M Unit from do
    sb.cmds.modify (·.push "channel")
    steps 2
    sb.cmds.modify (·.push "send hello over tcp")
    steps 3).run b4
  let (a6, _, got) ← both a4 b5 20000 fun a _ =>
    a.rows.toList.any (·.2.data.text == "hello over tcp")
  let ((), a7) ← (show M Unit from do
    sa.cmds.modify (·.push "channel")
    for _ in [0:200] do
      if (← get).rows.toList.any (·.2.data.text == "hello over tcp") then break
      steps 1; IO.sleep 10).run a6
  let rows := a7.rows.toList.map (·.2.data)
  check s!"B's post reaches A under B's name ({(rows.find? (·.text == "hello over tcp")).map (·.name)})"
    (got || rows.any fun d => d.text == "hello over tcp" && d.name == "Bea")
  -- A's home: Bea, with the online dot (a session with her node's key)
  let ((), a8) ← (show M Unit from do
    sa.cmds.modify (·.push "switch club")
    for _ in [0:100] do
      if (← get).online.toList == [false, true] then break
      steps 1; IO.sleep 10).run a7
  check s!"A's home shows Bea online ({a8.members.toList.zip a8.online.toList})"
    (a8.members.toList.map (·.1) == ["Ann", "Bea"] && a8.online.toList == [false, true])
  if let some r := a8.net then r.stop
  if let some r := b5.net then r.stop
  (← IO.getStdout).flush
  IO.Process.exit (if (← fails.get) == 0 then 0 else 1)
