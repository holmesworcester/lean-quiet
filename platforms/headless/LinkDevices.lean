/-
Linked devices, app to app, each its own database and app, with
everything a link does carried as ops between them as sync carries them
(each offers its stored shared ops; the other takes them as a peer's
job), by taps on each app's own pages. One-way, as the user decided
(2026-11-01): the existing device shows a device link, the new device
scans or pastes it, and asks; the existing device approves it under
Waiting to join.

1. A founds "club" as Ann and opens You > Link a device: a device link
   (`leanquiet://link/`, the site's link# page) and its QR code, which
   scans back to it. A2, on Get started's Link devices, pastes it: the
   device link under the join page is refused (the scheme must match);
   the link itself skips Choose a name and asks Agree & join (Link
   device); A2 waits for its other device.
2. A sees A2's request as its own device and approves it. A2 is in, as
   Ann's user, with no profile of its own; each device's post reaches
   the other under Ann's name; A's Link devices lists two devices.
3. B joins as Bea (a member link) and links B2 the same way. Only Bea's
   devices are asked about B2's request: A, another user, is not. B
   approves; B2 is in as Bea. A's people list has Bea once.
4. A removes Bea: both of Bea's devices are cut (the community hidden,
   each told once); Ann's linked device is not.

Read state across a user's devices (`userRoom c u`) waits on the
notifications port (docs/NOTIFICATIONS.md); not tested here yet.

    link_devices <outdir>
-/
import Quiet
import platforms.headless.Sim
import tests.engine.Stream

open App Engine Community Data

/-- Every shared op one node has stored, offered as sync offers it, taken
by the other as a peer's (not its own) job. -/
def carry (src dst : St) : IO Nat := do
  let ops ← Tests.streamOps Data.fam src.rd
  dst.wr.submit ⟨ops, false⟩
  return ops.length

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

/-- The screen as a camera's Y plane, and what a scan of it reads. -/
def scanScreen (sm : Sim) : IO (Option String) := do
  let scr ← screenOf sm 1080 2400 63
  let mut luma := ByteArray.emptyWithCapacity (1080 * 2400)
  for r in scr do
    for i in [0:1080] do
      luma := luma.push ((r[4*i]!.toNat + r[4*i+1]!.toNat + r[4*i+2]!.toNat) / 3).toUInt8
  return (Qr.decodeLuma 1080 2400 1080 luma).bind fun (b, _) => String.fromUTF8? b

/-- This store's profiles of user u in c. -/
def profiles (c u : Id) : M Nat := do
  let (p, _, _) ← readList (profile.byUser.query [c, u] (limit := some 0)) #[]
  return p.total

/-- Settle: wait for the writer, then a few frames. -/
def settle (sm : Sim) : M Unit := do
  waitIdle sm
  steps 5

/-- On Get started, Link devices, paste `link`: what it asks next. The
device link under the join page is refused first. -/
def pasteDeviceLink (sm : Sim) (check : String → Bool → IO Unit) (link : String) : M Unit := do
  steps 2
  check "the new device opens on Get started" ((← get).page == .getStarted)
  check "Link devices" ((← tapAct sm .linkDevices) && (← get).page == .linkReceive)
  check "Paste link" ((← tapAct sm .pasteLink) && (← get).page == .paste && (← get).linking)
  -- the same code behind the member's join page: refused
  let code := String.ofList (link.toList.drop "https://holmesworcester.github.io/lean-quiet/link#".length)
  modify fun s => { s with field := "https://holmesworcester.github.io/lean-quiet/join#" ++ code }
  steps 1
  let _ ← tapAct sm .continue_
  check s!"a device link behind the join page is refused ({(← get).refusal})"
    ((← get).page == .paste && (← get).refusal.isSome && (← get).invite.isNone)
  modify fun s => { s with field := link ++ "\n", refusal := none }
  steps 1
  check "Continue with the device link" (← tapAct sm .continue_)
  check s!"no name to choose: Agree & join asks to link this device (page {repr (← get).page})"
    ((← get).page == .agree && ((← get).invite.map (·.link)) == some true)
  check "Link device" (← tapAct sm .agree)
  settle sm
  let s ← get
  check s!"the new device waits for its other device ({repr s.page}, linking {s.me.linking})"
    (s.page == .waiting && s.me.waiting && s.me.linking)

def main (args : List String) : IO UInt32 := do
  let dir := args[0]?.getD "out/link"
  for x in ["a", "a2", "b", "b2"] do fresh (dir ++ "/" ++ x)
  let fails ← IO.mkRef 0
  let t0 ← IO.monoMsNow
  let check (name : String) (ok : Bool) : IO Unit := do
    IO.println s!"{if ok then "ok  " else "FAIL"} {name} [{(← IO.monoMsNow) - t0} ms]"
    (← IO.getStdout).flush
    if !ok then fails.modify (· + 1)
  let screen : Array UInt32 := #[1080, 2400, 128, 63, 420]
  let sa ← Sim.new
  let sa2 ← Sim.new
  let sb ← Sim.new
  let sb2 ← Sim.new
  let a0 ← App.start sa.io screen (dir ++ "/a/quiet.db")
  let a20 ← App.start sa2.io screen (dir ++ "/a2/quiet.db")
  let b0 ← App.start sb.io screen (dir ++ "/b/quiet.db")
  let b20 ← App.start sb2.io screen (dir ++ "/b2/quiet.db")

  -- 1. A founds club and opens You > Link a device
  let ((link, scanned), a1) ← (show M (String × Option String) from do
    sa.cmds.modify (·.push "found club|Ann")
    steps 3
    waitIdle sa
    sa.cmds.modify (·.push "open you")
    steps 3
    check "You offers Link a device" (← tapAct sa .linkShare)
    settle sa
    check s!"Link devices is up (page {repr (← get).page})" ((← get).page == .linkShare)
    writePpm (dir ++ "/a-link.ppm") 1080 (← screenOf sa 1080 2400 63)
    let scanned ← scanScreen sa
    return ((linkOf (← get) true).getD "", scanned)).run a0
  check s!"A's Link devices shows a device link ({link.take 52}…)"
    (link.startsWith "https://holmesworcester.github.io/lean-quiet/link#")
  check "its QR code on screen scans back to that link" (scanned == some link)
  check "it parses as a device link of A's community"
    (((Invite.parse link).map fun i => i.link && i.community == a1.me.c) == some true)
  check s!"A's Link devices lists this device ({a1.ownDeviceKeys})"
    (a1.ownDeviceKeys.size == 1 && a1.ownDeviceKeys.all (·.endsWith "(this device)"))
  let ((), a21) ← (pasteDeviceLink sa2 check link).run a20
  writePpm (dir ++ "/a2-waiting.ppm") 1080 (← screenOf sa2 1080 2400 63)

  -- 2. A approves its own new device
  let _ ← carry a21 a1
  let ((), a2) ← (show M Unit from do
    settle sa
    sa.cmds.modify (·.push "switch club")
    steps 3
    let s ← get
    check s!"A is asked about its new device ({s.asking.size})"
      (s.asking.size == 1 && s.asking.all (·.link))
    check "under Waiting to join" ((← tapAct sa .requests) && (← get).page == .requests)
    writePpm (dir ++ "/a-requests.ppm") 1080 (← screenOf sa 1080 2400 63)
    check s!"labelled as A's own device ({(← get).asking.map (·.row.device)})"
      ((← get).asking.all (·.row.device.startsWith "Your device"))
    check "A approves it" (← tapAct sa (.approve 0))
    settle sa
    check "and nobody waits any more" ((← get).asking.isEmpty)).run a1
  let _ ← carry a2 a21
  let ((), a22) ← (show M Unit from do
    settle sa2
    let s ← get
    writePpm (dir ++ "/a2-in.ppm") 1080 (← screenOf sa2 1080 2400 63)
    check s!"A2 is in club, on its home ({s.me.name}, {repr s.page})"
      (!s.me.waiting && s.me.name == "club" && s.page == .home)
    check "as Ann's user, the same as A's" (s.me.user == a2.me.user && !s.me.user.isEmpty)
    check "a device of its own" (s.me.dev.pk != a2.me.dev.pk)
    steps 10
    check s!"A2 wrote no profile: Ann's user has one ({← profiles s.me.c s.me.user})"
      ((← profiles s.me.c s.me.user) == 1)
    check s!"A2's people list is Ann, as me ({(← get).members.toList})" ((← get).members.toList == [("Ann", true)])
    sa2.cmds.modify (·.push "channel")
    steps 2
    sa2.cmds.modify (·.push "send hello from A2")
    steps 2
    waitIdle sa2).run a21
  let _ ← carry a22 a2
  let ((), a3) ← (show M Unit from do
    settle sa
    sa.cmds.modify (·.push "switch club")
    steps 2
    sa.cmds.modify (·.push "channel")
    steps 3
    let rows := (← get).rows.toList.map (·.2.data)
    check s!"A shows A2's post under Ann's name ({(rows.find? (·.text == "hello from A2")).map (·.name)})"
      (rows.any fun d => d.text == "hello from A2" && d.name == "Ann")
    sa.cmds.modify (·.push "send hi from A")
    steps 2
    waitIdle sa
    sa.cmds.modify (·.push "back")
    steps 2
    sa.cmds.modify (·.push "open linkShare")
    settle sa
    check s!"A's Link devices lists two devices ({(← get).ownDeviceKeys})" ((← get).ownDeviceKeys.size == 2)
    check "the same device link as before (one per session)" (linkOf (← get) true == some link)
    sa.cmds.modify (·.push "open you")
    settle sa
    check s!"You counts two devices ({(← get).ownDevices})" ((← get).ownDevices == 2)
    sa.cmds.modify (·.push "back")
    steps 2).run a2
  let _ ← carry a3 a22
  let ((), a23) ← (show M Unit from do
    settle sa2
    sa2.cmds.modify (·.push "channel")
    steps 3
    -- one user's posts clump: A's post continues A2's, under its header,
    -- whose author component reads Ann's profile on the reader's pass
    for _ in [0:200] do
      if (← get).rows.toList.any (fun (_, r) => r.data.text == "hello from A2" && r.data.name == "Ann") &&
        (← get).rows.toList.any (fun (_, r) => r.data.text == "hi from A") then break
      steps 1; IO.sleep 10
    let s ← get
    let rows := s.rows.toList.map (·.2.data)
    check s!"A2 shows A's post, by Ann's user ({rows.map fun d => (d.text, d.name)})"
      (rows.any fun d => d.text == "hi from A" && d.author == s.me.user)
    check "clumped with A2's own under one header, Ann's: one user, two devices"
      (rows.any fun d => d.text == "hello from A2" && d.name == "Ann" && d.author == s.me.user)
    sa2.cmds.modify (·.push "back")
    steps 2).run a22

  -- 3. B joins as Bea and links B2
  let (mlink, a4) ← (show M String from do
    sa.cmds.modify (·.push "open invite")
    settle sa
    return (linkOf (← get) false).getD "").run a3
  check s!"Add members' link is a member's ({mlink.take 52}…)"
    (mlink.startsWith "https://holmesworcester.github.io/lean-quiet/join#")
  let ((), b1) ← (show M Unit from do
    steps 2
    let _ ← tapAct sb .joinCommunity
    let _ ← tapAct sb .inviteLink
    let _ ← tapAct sb .pasteLink
    modify fun s => { s with field := mlink }
    steps 1
    let _ ← tapAct sb .continue_
    check "a member's link asks for a name" ((← get).page == .name)
    modify fun s => { s with field := "Bea" }
    steps 1
    let _ ← tapAct sb .continue_
    let _ ← tapAct sb .agree
    settle sb
    check "B waits to join" ((← get).me.waiting && !(← get).me.linking)).run b0
  let _ ← carry b1 a4
  let ((), a5) ← (show M Unit from do
    settle sa
    sa.cmds.modify (·.push "switch club")
    steps 3
    check s!"A is asked about B, a member ({(← get).asking.size})"
      ((← get).asking.size == 1 && !(← get).asking.any (·.link))
    let _ ← tapAct sa .requests
    check "A approves B" (← tapAct sa (.approve 0))
    settle sa).run a4
  let _ ← carry a5 b1
  let (blink, b2) ← (show M String from do
    settle sb
    check s!"B is in, as Bea ({(← get).me.name})" (!(← get).me.waiting)
    sb.cmds.modify (·.push "open linkShare")
    settle sb
    return (linkOf (← get) true).getD "").run b1
  check s!"B's device link ({blink.take 52}…)" (blink.startsWith "https://holmesworcester.github.io/lean-quiet/link#")
  let ((), b21) ← (pasteDeviceLink sb2 check blink).run b20
  -- B2's request reaches both A and B
  let _ ← carry b21 a5
  let _ ← carry b21 b2
  let ((), a6) ← (show M Unit from do
    settle sa
    sa.cmds.modify (·.push "switch club")
    steps 3
    check s!"A, another user, is not asked about Bea's new device ({(← get).asking.size})"
      (← get).asking.isEmpty).run a5
  let ((), b3) ← (show M Unit from do
    settle sb
    sb.cmds.modify (·.push "switch club")
    steps 3
    check s!"B is asked about its own new device ({(← get).asking.size})"
      ((← get).asking.size == 1 && (← get).asking.all (·.link))
    let _ ← tapAct sb .requests
    check "B approves it" (← tapAct sb (.approve 0))
    settle sb).run b2
  let _ ← carry b3 b21
  let _ ← carry b3 a6
  let ((), b22) ← (show M Unit from do
    settle sb2
    let s ← get
    check s!"B2 is in, as Bea's user ({s.me.name})" (!s.me.waiting && s.me.user == b3.me.user)
    steps 5
    check s!"B2 wrote no profile: Bea's user has one ({← profiles s.me.c s.me.user})"
      ((← profiles s.me.c s.me.user) == 1)).run b21
  let ((), a7) ← (show M Unit from do
    settle sa
    sa.cmds.modify (·.push "switch club")
    steps 3
    let ms := (← get).members.toList
    check s!"A's people list has Bea once ({ms})" (ms == [("Ann", true), ("Bea", false)])).run a6

  -- 4. A removes Bea: both of her devices are cut; Ann's second is not
  let ((), a8) ← (show M Unit from do
    let i := ((← get).members.findIdx? (·.1 == "Bea")).getD 1
    check "A opens Bea's profile" ((← tapAct sa (.person i)) && (← get).page == .profile)
    let _ ← tapAct sa .removeStart
    let _ ← tapAct sa .removeYes
    let _ ← tapAct sa .removeYes
    settle sa
    let ms := (← get).members.toList
    check s!"Bea leaves A's people list ({ms})" (ms == [("Ann", true)])).run a7
  for (sm, st, who) in [(sb, b3, "B"), (sb2, b22, "B2")] do
    let _ ← carry a8 st
    let ((), _) ← (show M Unit from do
      settle sm
      let s ← get
      check s!"{who}: cut, the community hidden, on Get started ({s.comms.size}, {repr s.page})"
        (s.comms.isEmpty && s.page == .getStarted)
      check s!"{who}: told \"{s.notices.head?.getD ""}\"" (s.notices == ["You’ve been removed from club."])).run st
  let _ ← carry a8 a23
  let ((), _) ← (show M Unit from do
    settle sa2
    let s ← get
    check s!"A2, Ann's linked device, is still in ({s.comms.size}, removed {s.me.removed})"
      (s.comms.size == 1 && !s.me.waiting && !s.me.removed)).run a23
  (← IO.getStdout).flush
  IO.Process.exit (if (← fails.get) == 0 then 0 else 1)
