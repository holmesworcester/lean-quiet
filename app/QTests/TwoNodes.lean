/-
Two nodes, each its own database and app, joined by link: everything a
join does is ops, carried between them as sync carries them (each node
offers its stored shared ops; the other takes them as a peer's job,
through intake), by taps on each app's own pages.

A founds "club" and opens Add members: its link. B, on Get started,
pastes the link and agrees: it waits. B's request reaches A; A sees it
under Join requests and approves it there. A's ops reach B: B is in, its
community named, its conversation showing, and its post reaches A.

    two_nodes <outdir>
-/
import Quiet
import QTests.Sim

open App Engine Community Data

/-- Every shared op one node has stored, offered as sync offers it, taken
by the other as a peer's (not its own) job. -/
def carry (src dst : St) : IO Nat := do
  let rows ← src.rd.query "SELECT id FROM ops" #[]
  let ids := rows.toList.filterMap (·[0]?)
  let ops ← (offer (family ed25519) ids : SqlM Fact (List Op)).run src.rd
  dst.wr.submit ⟨ops, [], false⟩
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

def main (args : List String) : IO UInt32 := do
  let dir := args[0]?.getD "out/two"
  fresh (dir ++ "/a"); fresh (dir ++ "/b")
  let fails ← IO.mkRef 0
  let check (name : String) (ok : Bool) : IO Unit := do
    IO.println s!"{if ok then "ok  " else "FAIL"} {name}"
    (← IO.getStdout).flush
    if !ok then fails.modify (· + 1)
  let screen : Array UInt32 := #[1080, 2400, 128, 63, 420]
  let sa ← Sim.new
  let sb ← Sim.new
  let a0 ← App.start sa.io screen (dir ++ "/a/quiet.db")
  let b0 ← App.start sb.io screen (dir ++ "/b/quiet.db")
  -- A founds "club" and opens Add members
  let (link, a1) ← (show M String from do
    sa.cmds.modify (·.push "found club|Ann")
    steps 3
    waitIdle sa
    sa.cmds.modify (·.push "open invite")
    steps 3
    waitIdle sa
    let s ← get
    writePpm (dir ++ "/a-invite.ppm") 1080 (← screenOf sa 1080 2400 63)
    return ((s.links.find? (·.1 == s.me.c)).map (·.2)).getD "").run a0
  check s!"A's Add members shows a link ({link.take 24}…)" (link.startsWith "quiet://join/")
  -- B pastes it and agrees
  let ((), b1) ← (show M Unit from do
    steps 2
    check "B opens on Get started" ((← get).page == .getStarted)
    check "Join a community" (← tapAct sb .joinCommunity)
    check "Join with invite link" (← tapAct sb .inviteLink)
    check "Paste a link" (← tapAct sb .pasteLink)
    modify fun s => { s with field := "  " ++ link ++ "\n" }
    steps 1
    check "Continue with the link" (← tapAct sb .continue_)
    check "Choose a name asks" ((← get).page == .name)
    modify fun s => { s with field := "Bea" }
    steps 1
    check "Continue with a name" (← tapAct sb .continue_)
    check "Agree & join asks" ((← get).page == .agree)
    check "Agree & Join" (← tapAct sb .agree)
    waitIdle sb
    steps 5
    let s ← get
    writePpm (dir ++ "/b-waiting.ppm") 1080 (← screenOf sb 1080 2400 63)
    check s!"B waits to join ({s.comms.size} community, page {repr s.page})"
      (s.comms.size == 1 && s.me.waiting && s.page == .waiting)).run b0
  -- B's request reaches A; A approves it from Join requests
  let nb ← carry b1 a1
  let ((), a2) ← (show M Unit from do
    waitIdle sa
    steps 3
    check s!"A sees one request ({nb} ops carried from B)" ((← get).asking.size == 1)
    -- A's home shows Waiting to join with its count; its row opens the page
    sa.cmds.modify (·.push "switch club")
    steps 3
    writePpm (dir ++ "/a-home.ppm") 1080 (← screenOf sa 1080 2400 63)
    check "A's home shows Waiting to join (count 1)"
      ((← get).page == .home && (← get).asking.size == 1 && ((← get).pageNow.map fun pg => pg.taps.any (·.2 == .requests)).getD false)
    check "its row opens Waiting to join" ((← tapAct sa .requests) && (← get).page == .requests)
    writePpm (dir ++ "/a-requests.ppm") 1080 (← screenOf sa 1080 2400 63)
    check "A approves it" (← tapAct sa (.approve 0))
    waitIdle sa
    steps 5
    check "and nobody waits any more" ((← get).asking.isEmpty)).run a1
  -- A's ops reach B: B is in
  let na ← carry a2 b1
  let ((), b2) ← (show M Unit from do
    waitIdle sb
    steps 5
    let s ← get
    writePpm (dir ++ "/b-in.ppm") 1080 (← screenOf sb 1080 2400 63)
    check s!"B is admitted, named \"{s.me.name}\", on its home ({na} ops carried from A)"
      (!s.me.waiting && s.me.name == "club" && s.page == .home)
    steps 10
    let s ← get
    let (adm, _, _) ← (show M _ from readList (admission.byDevice.query [s.me.c, (Device.ofSeed s.me.seed).pk]) #[])
    let u := match adm.rows.head? with | some (_, .admission _ u _ _) => u | _ => .empty
    let (p, _, _) ← (show M _ from readList (profile.byUser.query [s.me.c, u] (limit := some 0)) #[])
    check s!"B wrote one first profile, however many frames ran ({p.total})" (p.total == 1)
    sb.cmds.modify (·.push "channel")
    steps 2
    sb.cmds.modify (·.push "send hello from B")
    steps 2
    waitIdle sb).run b1
  -- B's post reaches A
  let _ ← carry b2 a2
  let ((), _) ← (show M Unit from do
    waitIdle sa
    steps 5
    sa.cmds.modify (·.push "switch club")
    steps 2
    sa.cmds.modify (·.push "channel")
    steps 3
    let s ← get
    writePpm (dir ++ "/a-chat.ppm") 1080 (← screenOf sa 1080 2400 63)
    let rows := s.rows.toList.map (·.2.data)
    check s!"A shows B's message ({s.total} messages)" (rows.any (·.text == "hello from B"))
    check s!"under the name B chose ({(rows.find? (·.text == "hello from B")).map (·.name)})"
      (rows.any fun d => d.text == "hello from B" && d.name == "Bea")
    -- and A's own post goes under the founder's name
    sa.cmds.modify (·.push "send hi from A")
    steps 2
    waitIdle sa
    steps 5
    let rows := (← get).rows.toList.map (·.2.data)
    check s!"A's own post is under the founder's name ({(rows.find? (·.text == "hi from A")).map (·.name)})"
      (rows.any fun d => d.text == "hi from A" && d.name == "Ann")).run a2
  -- C joins with the same link, then stops waiting: back on Get started
  fresh (dir ++ "/c")
  let sc ← Sim.new
  let c0 ← App.start sc.io screen (dir ++ "/c/quiet.db")
  let ((), _) ← (show M Unit from do
    steps 2
    let _ ← tapAct sc .joinCommunity
    let _ ← tapAct sc .inviteLink
    let _ ← tapAct sc .pasteLink
    modify fun s => { s with field := link }
    steps 1
    let _ ← tapAct sc .continue_
    modify fun s => { s with field := "Cy" }
    steps 1
    let _ ← tapAct sc .continue_
    let _ ← tapAct sc .agree
    waitIdle sc
    steps 3
    check "C waits to join" ((← get).page == .waiting && (← get).comms.size == 1)
    writePpm (dir ++ "/c-waiting.ppm") 1080 (← screenOf sc 1080 2400 63)
    check "Stop waiting" (← tapAct sc .stopWaiting)
    waitIdle sc
    steps 3
    check s!"C is back on Get started, waiting on nothing ({(← get).comms.size} communities)"
      ((← get).page == .getStarted && (← get).comms.isEmpty)).run c0
  (← IO.getStdout).flush
  IO.Process.exit (if (← fails.get) == 0 then 0 else 1)
