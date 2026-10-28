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
    sa.cmds.modify (·.push "found club")
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
    sa.cmds.modify (·.push "open requests")
    steps 3
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
    check s!"B is admitted, named \"{s.me.name}\", on its conversation ({na} ops carried from A)"
      (!s.me.waiting && s.me.name == "club" && s.page == .chat)
    sb.cmds.modify (·.push "send hello from B")
    steps 2
    waitIdle sb).run b1
  -- B's post reaches A
  let _ ← carry b2 a2
  let ((), _) ← (show M Unit from do
    waitIdle sa
    steps 5
    sa.cmds.modify (·.push "back")
    steps 3
    let s ← get
    writePpm (dir ++ "/a-chat.ppm") 1080 (← screenOf sa 1080 2400 63)
    let texts := s.rows.toList.map (·.2.data.text)
    check s!"A shows B's message ({s.total} messages)" (texts.contains "hello from B")).run a2
  (← IO.getStdout).flush
  IO.Process.exit (if (← fails.get) == 0 then 0 else 1)
