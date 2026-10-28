/-
Two phones, two communities, each phone in both, over real TCP on
loopback (each app its own database and node): everything named alike.
Both communities are "club", and everyone calls themself "Ann", so
nothing a screen shows tells the entries apart but their ops.

A founds one club and B the other; each joins the other's by its link,
and each approves the other. Then, on each phone: the switcher has two
entries, a tap on each lands on that very entry (its acceptance and its
community), its home lists its two members with exactly this device's
user as "you", and its page key differs from the other entry's.

Last, A joins B's club a second time (a second device for the same
community): three entries, two of them B's club, each reachable by a
tap; Stop waiting on the new one leaves the admitted one as it was.

    cross <outdir>
-/
import Quiet
import QTests.Sim

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

/-- Make the entry satisfying `p` current, by tapping it in the switcher. -/
def tapEntry (sm : Sim) (p : Kinds.Accepted.Me → Bool) : M Bool := do
  sm.cmds.modify (·.push "open switcher")
  steps 3
  let some i := (← get).comms.findIdx? p | return false
  tapAct sm (.switchTo i)

/-- The link Add members gives on the current entry. -/
def linkHere (sm : Sim) : M String := do
  sm.cmds.modify (·.push "open invite")
  steps 3
  let s ← get
  sm.cmds.modify (·.push "back")
  steps 2
  return ((s.links.find? (·.1 == s.me.acc)).map (·.2)).getD ""

/-- Join from a link, named n, through the pages. -/
def joinBy (sm : Sim) (link n : String) : M Unit := do
  sm.cmds.modify (·.push "open join")
  steps 2
  let _ ← tapAct sm .inviteLink
  let _ ← tapAct sm .pasteLink
  modify fun s => { s with field := link }
  steps 1
  let _ ← tapAct sm .continue_
  modify fun s => { s with field := n }
  steps 1
  let _ ← tapAct sm .continue_
  let _ ← tapAct sm .agree
  waitIdle sm
  steps 3

/-- On the founder's own entry, approve the one waiting request. -/
def approveHere (sm : Sim) : M Bool := do
  let _ ← tapEntry sm fun m => m.adm == m.c
  let _ ← tapAct sm .requests
  tapAct sm (.approve 0)

def main (args : List String) : IO UInt32 := do
  let dir := args[0]?.getD "out/cross"
  fresh (dir ++ "/a"); fresh (dir ++ "/b")
  let fails ← IO.mkRef 0
  let check (name : String) (ok : Bool) : IO Unit := do
    IO.println s!"{if ok then "ok  " else "FAIL"} {name}"
    (← IO.getStdout).flush
    if !ok then fails.modify (· + 1)
  let screen : Array UInt32 := #[1080, 2400, 128, 63, 420]
  let sa ← Sim.new
  let sb ← Sim.new
  let a0 ← App.start sa.io screen (dir ++ "/a/quiet.db") (some (47221, true))
  let b0 ← App.start sb.io screen (dir ++ "/b/quiet.db") (some (47222, true))
  -- each founds "club" as "Ann", and gives its link
  let (la, a1) ← (show M String from do
    sa.cmds.modify (·.push "found club|Ann"); steps 3; waitIdle sa; steps 3
    linkHere sa).run a0
  let (lb, b1) ← (show M String from do
    sb.cmds.modify (·.push "found club|Ann"); steps 3; waitIdle sb; steps 3
    linkHere sb).run b0
  check "both clubs give links" (la.startsWith "quiet://join/" && lb.startsWith "quiet://join/" && la != lb)
  -- each joins the other's, as "Ann"
  let ((), a2) ← (joinBy sa lb "Ann").run a1
  let ((), b2) ← (joinBy sb la "Ann").run b1
  -- each on its own club, where the other's request will show
  let (_, a2) ← (tapEntry sa fun m => m.adm == m.c).run a2
  let (_, b2) ← (tapEntry sb fun m => m.adm == m.c).run b2
  let (a3, b3, asked) ← both a2 b2 30000 fun a b => a.asking.size == 1 && b.asking.size == 1
  let (okA, a4) ← (approveHere sa).run a3
  let (okB, b4) ← (approveHere sb).run b3
  check s!"each sees the other's request and approves it ({asked}, {okA}, {okB})" (asked && okA && okB)
  let (a5, b5, inBoth) ← both a4 b4 40000 fun a b =>
    a.comms.size == 2 && b.comms.size == 2 && a.comms.all (!·.waiting) && b.comms.all (!·.waiting)
  check s!"each phone is in both clubs ({a5.comms.size}, {b5.comms.size})" inBoth
  -- let profiles and names settle on both
  let (a5, b5, _) ← both a5 b5 5000 fun _ _ => false
  -- on each phone: both entries reachable, each home right
  let phone (sm : Sim) (who : String) (s : St) : IO St := do
    let s := s
    check s!"{who}: two entries named alike, two acceptances, two communities"
      (s.comms.size == 2 && s.comms.all (·.name == "club") &&
       s.comms[0]!.acc != s.comms[1]!.acc && s.comms[0]!.c != s.comms[1]!.c)
    let mut s := s
    let mut keys : Array PageIn := #[]
    for i in [0:2] do
      let e := s.comms[i]!
      let (ok, s') ← (show M Bool from do
        let ok ← tapEntry sm (·.acc == e.acc)
        sm.cmds.modify (·.push "back")  -- the switcher → home
        for _ in [0:100] do
          if (← get).page == .home && (← get).members.size == 2 && (← get).members.all (·.1 != "…") then break
          steps 1; IO.sleep 10
        return ok).run s
      s := s'
      check s!"{who}: a tap on entry {i} lands on it (acc and community)"
        (ok && s.me.acc == e.acc && s.me.c == e.c && s.cur == e.acc)
      let ms := s.members.toList
      check s!"{who}: entry {i}'s home lists Ann twice, exactly one is me ({ms})"
        (ms.length == 2 && ms.all (·.1 == "Ann") && (ms.filter (·.2)).length == 1)
      if let some k := s.pageKey then keys := keys.push k
    check s!"{who}: the two homes have different page keys" (keys.size == 2 && keys[0]! != keys[1]!)
    return s
  let a6 ← phone sa "A" a5
  let b6 ← phone sb "B" b5
  -- A joins B's club a second time: a second device there
  let ((), a7) ← (joinBy sa lb "Ann").run a6
  let twins := a7.comms.filter fun m => a7.comms.any fun n => n.acc != m.acc && n.c == m.c
  check s!"A: three entries, two of them one community ({a7.comms.size}, {twins.size})"
    (a7.comms.size == 3 && twins.size == 2)
  let mut a8 := a7
  for m in twins do
    let (ok, s') ← (tapEntry sa (·.acc == m.acc)).run a8
    a8 := s'
    check s!"A: the {if m.waiting then "waiting" else "admitted"} twin is reachable by a tap"
      (ok && a8.me.acc == m.acc && a8.page == (if m.waiting then .waiting else .home))
  -- stop waiting on the new one: the admitted twin is untouched
  let ((), a9) ← (show M Unit from do
    let _ ← tapEntry sa (·.waiting)
    let _ ← tapAct sa .stopWaiting
    waitIdle sa; steps 3).run a8
  check s!"A: Stop waiting drops only the new twin ({a9.comms.size} entries, all admitted)"
    (a9.comms.size == 2 && a9.comms.all (!·.waiting))
  for s in [a9, b6] do
    if let some r := s.net then r.stop
  (← IO.getStdout).flush
  IO.Process.exit (if (← fails.get) == 0 then 0 else 1)
