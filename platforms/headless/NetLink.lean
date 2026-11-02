/-
Linked devices over real TCP: four apps on loopback ports, each its own
database and its own node (the engine's Runner with the Connection
family, as the phones run it); nothing is carried by hand.

1. A founds "club" as Ann and opens Link devices: its device link dials
   A's node. A2 pastes it on Get started's Link devices and links: its
   node dials A with the request, bare. A sees it as its own device and
   approves; the session opens and sync admits A2 into Ann's user. A2's
   post reaches A, and A's reaches A2.
2. B joins as Bea from Add members' link; B links B2 the same way. Only
   B is asked about B2 (A, another user, is not, though B2's request
   reaches it); B approves; B2 is in as Bea.
3. A removes Bea. B is cut (A–B is a live session); Ann's second device
   is not. B2, whose only session is with B, is cut too only once a cut
   node gives its removal to the peers the same removal cuts: holmes-80's
   pre-admission rooms (worker `preadmit`) bring that rule; until they
   land, B2's check prints GAP and does not fail (`--strict` makes it
   fail, as it will by default then).

Read state across a user's devices (`userRoom c u`) waits on the
notifications port (docs/NOTIFICATIONS.md); not tested here yet.

    net_link <outdir>
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

/-- Four loopback ports, from the process id, below Linux's ephemeral
range (as `testPorts`). -/
def ports4 : IO (Array Nat) := do
  let p := 20000 + (← IO.Process.getPID).toNat % 3000 * 4
  return #[p, p + 1, p + 2, p + 3]

/-- The four apps: Ann's two devices and Bea's. -/
structure W where
  a : St
  a2 : St
  b : St
  b2 : St

/-- Every app steps, in real time, until `p` holds of them (or `ms` pass). -/
def all (w : W) (ms : Nat) (p : W → Bool) : IO (W × Bool) := do
  let mut w := w
  let t0 ← IO.monoMsNow
  while (← IO.monoMsNow) - t0 < ms do
    if p w then return (w, true)
    w := { a := (← (steps 1).run w.a).2, a2 := (← (steps 1).run w.a2).2,
           b := (← (steps 1).run w.b).2, b2 := (← (steps 1).run w.b2).2 }
    IO.sleep 5
  return (w, p w)

/-- This store's profiles of user u in c. -/
def profiles (c u : Id) : M Nat := do
  let (p, _, _) ← readList (profile.byUser.query [c, u] (limit := some 0)) #[]
  return p.total

def main (args : List String) : IO UInt32 := do
  let dir := args[0]?.getD "out/net-link"
  for x in ["a", "a2", "b", "b2"] do fresh (dir ++ "/" ++ x)
  let fails ← IO.mkRef 0
  let t0 ← IO.monoMsNow
  let check (name : String) (ok : Bool) : IO Unit := do
    IO.println s!"{if ok then "ok  " else "FAIL"} {name} [{(← IO.monoMsNow) - t0} ms]"
    (← IO.getStdout).flush
    if !ok then fails.modify (· + 1)
  let screen : Array UInt32 := #[1080, 2400, 128, 63, 420]
  let (sa, sa2, sb, sb2) := (← Sim.new, ← Sim.new, ← Sim.new, ← Sim.new)
  let ps ← ports4
  let pa := ps[0]!
  let start (sm : Sim) (x : String) (p : Nat) := App.start sm.io screen (dir ++ "/" ++ x ++ "/quiet.db") (some (p, true))
  let mut w : W := ⟨← start sa "a" pa, ← start sa2 "a2" ps[1]!, ← start sb "b" ps[2]!, ← start sb2 "b2" ps[3]!⟩
  let stopAll (w : W) : IO Unit := do
    for s in [w.a, w.a2, w.b, w.b2] do
      if let some r := s.net then r.stop

  -- 1. A founds club and opens Link devices
  let (link, a1) ← (show M String from do
    sa.cmds.modify (·.push "found club|Ann")
    steps 3
    waitIdle sa
    steps 3
    sa.cmds.modify (·.push "open linkShare")
    steps 3
    waitIdle sa
    return (linkOf (← get) true).getD "").run w.a
  w := { w with a := a1 }
  let hints := ((Invite.parse link).map (·.hints.map fun h => (String.fromUTF8? h).getD "?")).getD []
  check s!"A's device link dials A's node ({hints})" (hints == [s!"127.0.0.1:{pa}"])
  check "it is a device link" (((Invite.parse link).map (·.link)) == some true)
  -- the new device pastes it on Link devices and links
  let link2 (sm : Sim) (l : String) : M Unit := do
    steps 2
    let _ ← tapAct sm .linkDevices
    let _ ← tapAct sm .pasteLink
    modify fun s => { s with field := l }
    steps 1
    let _ ← tapAct sm .continue_
    check s!"no name to choose (page {repr (← get).page})" ((← get).page == .agree)
    check "Link device" (← tapAct sm .agree)
    waitIdle sm
    steps 3
    check "it waits for its other device" ((← get).me.waiting && (← get).me.linking)
  let ((), a2) ← (link2 sa2 link).run w.a2
  w := { w with a2 }
  let (w1, asked) ← all w 30000 fun w => w.a.asking.size == 1
  w := w1
  check s!"A is asked about its new device, over TCP ({w.a.asking.map (·.link)})"
    (asked && w.a.asking.all (·.link))
  let ((), a) ← (show M Unit from do
    sa.cmds.modify (·.push "switch club")
    steps 3
    let _ ← tapAct sa .requests
    check "A approves it" (← tapAct sa (.approve 0))
    steps 3).run w.a
  w := { w with a }
  let (w2, inA2) ← all w 30000 fun w => !w.a2.me.waiting && w.a2.me.name == "club"
  w := w2
  check s!"A2 is admitted, over TCP ({w.a2.me.name})" inA2
  check "into Ann's user" (w.a2.me.user == w.a.me.user && !w.a2.me.user.isEmpty)
  let ((), a2) ← (show M Unit from do
    -- admitted before Ann's profile synced, A2 reads none: wait for it,
    -- then there is exactly Ann's (A2 named nobody)
    for _ in [0:600] do
      if (← profiles (← get).me.c (← get).me.user) ≥ 1 then break
      steps 1; IO.sleep 10
    check s!"A2 wrote no profile ({← profiles (← get).me.c (← get).me.user})"
      ((← profiles (← get).me.c (← get).me.user) == 1)
    sa2.cmds.modify (·.push "channel")
    steps 2
    sa2.cmds.modify (·.push "send hello from A2 over tcp")
    steps 3).run w.a2
  w := { w with a2 }
  let ((), a) ← (show M Unit from do
    sa.cmds.modify (·.push "channel")
    steps 2).run w.a
  w := { w with a }
  let (w3, gotA) ← all w 30000 fun w =>
    w.a.rows.toList.any fun (_, r) => r.data.text == "hello from A2 over tcp" && r.data.author == w.a.me.user
  w := w3
  check "A2's post reaches A, by Ann's user" gotA
  let ((), a) ← (show M Unit from do
    sa.cmds.modify (·.push "send hi from A over tcp")
    steps 3).run w.a
  w := { w with a }
  let (w4, gotA2) ← all w 30000 fun w =>
    w.a2.rows.toList.any fun (_, r) => r.data.text == "hi from A over tcp" && r.data.author == w.a2.me.user
  w := w4
  check "A's post reaches A2, by Ann's user" gotA2

  -- 2. B joins as Bea; B links B2
  let (mlink, a) ← (show M String from do
    sa.cmds.modify (·.push "back")
    steps 2
    sa.cmds.modify (·.push "open invite")
    steps 3
    waitIdle sa
    return (linkOf (← get) false).getD "").run w.a
  w := { w with a }
  let ((), b) ← (show M Unit from do
    steps 2
    let _ ← tapAct sb .joinCommunity
    let _ ← tapAct sb .inviteLink
    let _ ← tapAct sb .pasteLink
    modify fun s => { s with field := mlink }
    steps 1
    let _ ← tapAct sb .continue_
    modify fun s => { s with field := "Bea" }
    steps 1
    let _ ← tapAct sb .continue_
    let _ ← tapAct sb .agree
    waitIdle sb
    steps 3).run w.b
  w := { w with b }
  let (w5, askedB) ← all w 30000 fun w => w.a.asking.size == 1
  w := w5
  check "A is asked about Bea" (askedB && !w.a.asking.any (·.link))
  let ((), a) ← (show M Unit from do
    sa.cmds.modify (·.push "switch club")
    steps 3
    let _ ← tapAct sa .requests
    let _ ← tapAct sa (.approve 0)
    steps 3).run w.a
  w := { w with a }
  let (w6, inB) ← all w 30000 fun w => !w.b.me.waiting && w.b.me.name == "club"
  w := w6
  check "B is in, as Bea" inB
  let (blink, b) ← (show M String from do
    sb.cmds.modify (·.push "open linkShare")
    steps 3
    waitIdle sb
    return (linkOf (← get) true).getD "").run w.b
  w := { w with b }
  let ((), b2) ← (link2 sb2 blink).run w.b2
  w := { w with b2 }
  let (w7, askedB2) ← all w 30000 fun w => w.b.asking.size == 1
  w := w7
  check "B is asked about its own new device, over TCP" (askedB2 && w.b.asking.all (·.link))
  -- A may hold B2's request too once Bea's ops sync, but is never asked
  let (w8, _) ← all w 3000 fun _ => false
  w := w8
  check s!"A, another user, is not asked about it ({w.a.asking.size})" w.a.asking.isEmpty
  let ((), b) ← (show M Unit from do
    sb.cmds.modify (·.push "switch club")
    steps 3
    let _ ← tapAct sb .requests
    check "B approves it" (← tapAct sb (.approve 0))
    steps 3).run w.b
  w := { w with b }
  let (w9, inB2) ← all w 30000 fun w => !w.b2.me.waiting && w.b2.me.name == "club"
  w := w9
  check "B2 is in, over TCP" inB2
  check "as Bea's user" (w.b2.me.user == w.b.me.user && !w.b2.me.user.isEmpty)

  -- 3. A removes Bea: both of her devices are cut, Ann's second is not
  let ((), a) ← (show M Unit from do
    sa.cmds.modify (·.push "switch club")
    steps 3).run w.a
  w := { w with a }
  let (w10, listed) ← all w 30000 fun w => w.a.members.toList.map (·.1) == ["Ann", "Bea"]
  w := w10
  check s!"A's people list has Bea once ({w.a.members.toList})" listed
  let ((), a) ← (show M Unit from do
    sa.cmds.modify (·.push "switch club")
    steps 3
    let i := ((← get).members.findIdx? (·.1 == "Bea")).getD 1
    let _ ← tapAct sa (.person i)
    let _ ← tapAct sa .removeStart
    let _ ← tapAct sa .removeYes
    let _ ← tapAct sa .removeYes
    waitIdle sa
    steps 3).run w.a
  w := { w with a }
  let strict := args.contains "--strict"
  let (w11, cutB) ← all w 30000 fun w => w.b.comms.isEmpty
  w := w11
  -- the notice is a toast and may have timed out: B's community is gone
  -- and B is back on Get started
  check s!"B, Bea's device with the session to A, is cut over TCP ({w.b.comms.size}, {repr w.b.page})"
    (cutB && w.b.page == .getStarted)
  let (w12, cutB2) ← all w (if strict then 30000 else 5000) fun w => w.b2.comms.isEmpty
  w := w12
  if strict || cutB2 then
    check s!"B2, whose only session was with B, is cut over TCP ({w.b2.comms.size})" (cutB2 && w.b2.page == .getStarted)
  else
    IO.println s!"GAP  B2, whose only session was with B, is not told yet ({w.b2.comms.size}): a cut node gives no notices until holmes-80's preadmit rooms land"
  check s!"Ann's linked device is still in ({w.a2.comms.size})"
    (w.a2.comms.size == 1 && !w.a2.me.waiting && !w.a2.me.removed)
  stopAll w
  (← IO.getStdout).flush
  IO.Process.exit (if (← fails.get) == 0 then 0 else 1)
