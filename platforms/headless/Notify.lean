/-
Notifications on the headless twin: two apps joined by link, ops carried
between them as sync carries them. B's cards are the packets its `Io`
gets (what Android's Notifications.java renders):

- a post from A alerts B with one card for the conversation (its title,
  body, count and a link that parses back to the message);
- A's own posts never alert A; B's own never alert B;
- the conversation on screen is quiet, and opening it withdraws its card;
- the level Off silences, All restores;
- the card's link opens exactly its message;
- Sync in the background on: a post arriving while B is in the background
  alerts, and nothing is drawn; off: nothing runs in the background, so
  nothing alerts until B is in front again;
- B's removal withdraws its standing card;
- and `Notify.policy` agrees with libquiet's on 20,736 reference cases.

    notify <outdir>
-/
import Quiet
import platforms.headless.Sim
import tests.engine.Stream

open App Engine Community Data

/-- Every shared op one node has stored, taken by the other as a peer's;
returns once the other's writer has committed them (its busy count is
back to zero), so what follows waits on the store, not on a clock. -/
def carry (src dst : St) : IO Nat := do
  let ops ← Tests.streamOps Data.fam src.rd
  dst.wr.submit ⟨ops, false⟩
  let mut k := 0
  while (← dst.wr.busy.get) > 0 && k < 60000 do
    IO.sleep 2
    k := k + 1
  return ops.length

/-- A tap on the page's button for an act, as a finger would (two_nodes'). -/
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

/-- A packet's string field, as Java reads it. -/
def field (p key : String) : String :=
  match (p.splitOn s!"\"{key}\":\"")[1]? with
  | some rest => (rest.splitOn "\"").headD ""
  | none => ""

def isPost (p : String) : Bool := field p "action" == "post"
def alerts (p : String) : Bool := isPost p && (p.splitOn "\"alert\":true").length > 1
def count (p : String) : Nat :=
  match (p.splitOn "\"count\":")[1]? with
  | some rest => (String.ofList (rest.toList.takeWhile Char.isDigit)).toNat!
  | none => 0

/-- libquiet's own policy over every message-policy input: 20,736
cases its unmodified effective/follow/decide functions computed at
ab3d244cf (tests/app/notify_oracle.py), in this nesting order, against
the `Notify.policy` the app runs. -/
def policyFixture : IO (Nat × Bool) := do
  let expected := (← IO.FS.readFile "tests/app/notify-policy.txt").trimAscii.toString.toList.toArray
  let levels := [none, some Notice.Level.all, some .mentions, some .off]
  let choices := [none, some false, some true]
  let mut i := 0
  let mut ok := true
  for community in levels do
    for conversation in levels do
      for communityReplies in choices do
        for replies in choices do
          for kind in [0, 1, 2] do
            for manualFollow in choices do
              for reply in [false, true] do
                for mentioned in [false, true] do
                  for rootAuthor in [false, true] do
                    for replied in [false, true] do
                      let actual := Notify.policy { community, conversation, communityReplies, replies }
                        { direct := kind != 0, oneToOne := kind == 2, manualFollow, reply, mentioned, rootAuthor, replied }
                      if expected[i]? != some (if actual then '1' else '0') then ok := false
                      i := i + 1
  return (i, ok && i == expected.size)

/-- Whether the notification turn has considered a post with this text
(it is in a snapshot the last turn ran over). -/
def holds (s : St) (text : String) : Bool :=
  s.notesKey.any fun (_, _, xs) => xs.any fun (_, sn) => sn.rows.any (·.text == text)

/-- Steps until everything this app wrote is committed: its writer idle,
nothing pending in its outbox, nothing parked for the node, no act
waiting (the reader caught up, its done queue applied). It waits on
the app's own state, not a clock (the bound only ends a hung run). -/
def settle : M Bool := do
  for _ in [0:60000] do
    let s ← get
    if (← s.wr.busy.get) == 0 && (← s.wr.jobs.get).isEmpty && s.out.isEmpty && s.toNode.isEmpty &&
        s.doneQ.isEmpty && (← s.sh.acts.get).isEmpty && (← s.sh.done.get).isEmpty && (← readerCaughtUp) then
      steps 2
      return true
    discard <| step []
    IO.sleep 2
  return false

/-- How many readable posts the store holds in the current community:
read through the store, not the frame (it runs in the background too). -/
def heldTotal : M Nat := do
  let (a, _) ← readView (Community.readable (← get).me.c (limit := some 0)) #[]
  return a.total

/-- How many ops the store has committed (SQL, outside any read snapshot). -/
def opsCount : M Nat := do
  let rows ← (← get).rd.query "SELECT CAST(count(*) AS TEXT) FROM ops" #[]
  return (rows[0]? >>= (·[0]?) >>= fun b => (String.fromUTF8? b).bind String.toNat?).getD 0

/-- Steps until the store holds more than `n` posts (the carried ones
are committed), at most `k` steps. -/
def untilHeld (n k : Nat) (evs : List Event := []) : M Bool := do
  for _ in [0:k] do
    if (← heldTotal) > n then return true
    discard <| step evs
    IO.sleep 5
  return (← heldTotal) > n

/-- Steps until the packets since `from` satisfy `ok`, at most `n`. -/
def packetsUntil (sm : Sim) (from_ n : Nat) (ok : Array String → Bool) (evs : List Event := []) : M Bool := do
  for _ in [0:n] do
    let _ ← step evs
    if ok ((← sm.notes.get).extract from_ (← sm.notes.get).size) then return true
  return false

def main (args : List String) : IO UInt32 := do
  let dir := args[0]?.getD "out/notify"
  fresh (dir ++ "/a"); fresh (dir ++ "/b")
  let fails ← IO.mkRef 0
  let check (name : String) (ok : Bool) : IO Unit := do
    IO.println s!"{if ok then "ok  " else "FAIL"} {name}"
    (← IO.getStdout).flush
    if !ok then fails.modify (· + 1)
  let (n, ok) ← policyFixture
  check s!"the policy is libquiet's on all {n} reference cases" (ok && n == 20736)
  let screen : Array UInt32 := #[1080, 2400, 128, 63, 420]
  let sa ← Sim.new
  let sb ← Sim.new
  -- B is an Android phone: it has the background service (the twin has none)
  let a0 ← App.start sa.io screen (dir ++ "/a/quiet.db")
  let b0 ← App.start sb.ioWithService screen (dir ++ "/b/quiet.db")
  check "the twin has the background service, off by default" (b0.canKeep && !b0.keepSync)
  -- A founds "club"; its link reaches B as the OS hands it over
  let (link, a1) ← (show M String from do
    sa.cmds.modify (·.push "found club|Ann")
    steps 3
    discard <| settle
    sa.cmds.modify (·.push "open invite")
    steps 3
    discard <| settle
    let s ← get
    return ((s.links.find? (·.1 == s.me.acc)).map (·.2)).getD "").run a0
  -- B pastes it and agrees, page by page (as two_nodes does)
  let ((), b1) ← (show M Unit from do
    steps 2
    check "Join a community" (← tapAct sb .joinCommunity)
    check "Join with invite link" (← tapAct sb .inviteLink)
    check "Paste a link" (← tapAct sb .pasteLink)
    modify fun s => { s with field := "  " ++ link ++ "\n" }
    steps 1
    check "Continue with the link" (← tapAct sb .continue_)
    modify fun s => { s with field := "Bea" }
    steps 1
    check "Continue with a name" (← tapAct sb .continue_)
    check "Agree & Join" (← tapAct sb .agree)
    waitIdle sb
    steps 5
    check "B waits to join" ((← get).me.waiting && (← get).page == .waiting)).run b0
  let _ ← carry b1 a1
  -- A approves it from Join requests
  let ((), a2) ← (show M Unit from do
    waitIdle sa
    steps 3
    sa.cmds.modify (·.push "switch club")
    steps 3
    check s!"A sees B's request ({(← get).asking.size})" ((← get).asking.size == 1)
    check "its row opens Waiting to join" ((← tapAct sa .requests) && (← get).page == .requests)
    check "A approves it" (← tapAct sa (.approve 0))
    waitIdle sa
    steps 5
    check "and nobody waits any more" ((← get).asking.isEmpty)
    sa.cmds.modify (·.push "switch club")
    steps 3).run a1
  let _ ← carry a2 b1
  let ((), b2) ← (show M Unit from do
    waitIdle sb
    steps 5
    let s ← get
    check s!"B is in, on its home (page {repr s.page})" (!s.me.waiting && s.page == .home)
    check "and nothing alerted for the community's history" ((← sb.notes.get).all (!alerts ·))).run b1
  -- A posts from its home (not the conversation, which is quiet anyway):
  -- A's own post never alerts A
  let ((), a3) ← (show M Unit from do
    sa.cmds.modify (·.push "switch club")
    steps 2
    check s!"A is on its home (page {repr (← get).page})" ((← get).page == .home)
    sa.cmds.modify (·.push "send hello there")
    steps 2
    discard <| settle
    steps 5
    check "A's own post does not alert A" ((← sa.notes.get).all (!alerts ·))).run a2
  let _ ← carry a3 b2
  let (hello, b3) ← (show M String from do
    let n0 := (← sb.notes.get).size
    let got ← packetsUntil sb n0 200 (·.any alerts)
    let ps := (← sb.notes.get).extract n0 (← sb.notes.get).size
    let p := (ps.find? alerts).getD ""
    check s!"A's post alerts B, once: one card ({ps.size} packets)" (got && (ps.filter alerts).size == 1)
    check s!"titled with the conversation and community ({field p "title"})" (field p "title" == "#general (club)")
    check s!"its body is the post ({field p "body"})" (field p "body" == "hello there")
    check "for one message" (count p == 1)
    let t := Community.Target.parse (field p "link")
    let s ← get
    check "its link parses back to the post, in B's community"
      (t.any fun t => t.community == s.me.c && t.conversation == s.me.c && t.message.size == 32)
    -- steps more: a repeat never alerts again
    let n1 := (← sb.notes.get).size
    steps 20
    check "a post alerts once, however many turns run" (((← sb.notes.get).extract n1 (← sb.notes.get).size).all (!alerts ·))
    return field p "link").run b2
  -- a second post: the same card, two messages
  let ((), a4) ← (show M Unit from do
    sa.cmds.modify (·.push "send second")
    steps 2
    waitIdle sa).run a3
  let _ ← carry a4 b3
  let ((), b4) ← (show M Unit from do
    let n0 := (← sb.notes.get).size
    let _ ← packetsUntil sb n0 200 (·.any alerts)
    let ps := (← sb.notes.get).extract n0 (← sb.notes.get).size
    let p := (ps.find? alerts).getD ""
    check s!"a second post updates the same card: two messages (count {count p})" (count p == 2 && field p "body" == "second")
    -- B's own post never alerts B
    sb.cmds.modify (·.push "channel")
    let n1 := (← sb.notes.get).size
    let quiet ← packetsUntil sb n1 50 (·.any fun p => field p "action" == "cancel")
    check "opening the conversation withdraws its card" quiet
    check "and leaves none standing" (!(← get).notes.active.any (·.community == (← get).me.c))).run b3
  -- while B reads the conversation, A's post does not alert
  let ((), a5) ← (show M Unit from do
    sa.cmds.modify (·.push "send while reading")
    steps 2
    waitIdle sa).run a4
  let _ ← carry a5 b4
  let ((), b5) ← (show M Unit from do
    let n0 := (← sb.notes.get).size
    for _ in [0:200] do
      if holds (← get) "while reading" then break
      discard <| step []
    check "the post reaches B while it reads, and is considered" (holds (← get) "while reading")
    steps 10
    check "the conversation on screen is quiet" (((← sb.notes.get).extract n0 (← sb.notes.get).size).all (!alerts ·))
    -- B leaves the conversation; its own post, from its home, never alerts it
    sb.cmds.modify (·.push "back")
    steps 3
    check s!"B is on its home (page {repr (← get).page})" ((← get).page == .home)
    let n1 := (← sb.notes.get).size
    sb.cmds.modify (·.push "send from B")
    steps 2
    discard <| settle
    for _ in [0:200] do
      if holds (← get) "from B" then break
      discard <| step []
    check "B's own post, considered on its home, does not alert B"
      (holds (← get) "from B" && ((← sb.notes.get).extract n1 (← sb.notes.get).size).all (!alerts ·))
    -- Off
    sb.cmds.modify (·.push "notify off")
    steps 2
    discard <| settle
    steps 5
    check s!"the level is Off (code {(← get).notifyLevel})" ((← get).notifyLevel == 3)).run b4
  let ((), a6) ← (show M Unit from do
    sa.cmds.modify (·.push "send muted")
    steps 2
    discard <| settle
    -- 120 more posts: the history a link must open through
    -- each send is an act the reader runs, and the outbox is bounded: one
    -- at a time, each committed before the next (an act can still refuse)
    let before ← heldTotal
    for k in [0:120] do
      -- a refused act leaves nothing written: send again until the store
      -- has committed one more op (counted in SQL, as two_nodes does)
      let ops0 ← opsCount
      for _ in [0:20] do
        discard <| sendText s!"history {k}"
        discard <| settle
        if (← opsCount) > ops0 then break
    let sent := (← heldTotal) - before
    check s!"A sends 120 more posts ({sent})" (sent == 120)
    discard <| settle
    steps 3).run a5
  let _ ← carry a6 b5
  let ((), b6) ← (show M Unit from do
    let n0 := (← sb.notes.get).size
    -- "muted" and the 120 posts after it arrive together: the newest is
    -- the last of them
    for _ in [0:400] do
      if holds (← get) "history 119" then break
      discard <| step []
    check "the posts reach B and are considered" (holds (← get) "history 119")
    steps 10
    check "Off silences" (((← sb.notes.get).extract n0 (← sb.notes.get).size).all (!alerts ·))
    sb.cmds.modify (·.push "notify all")
    steps 2
    discard <| settle
    steps 5
    check "All again" ((← get).notifyLevel == 1)
    -- the first card's link opens exactly its message, however much
    -- history is newer than it (A wrote 120 posts since: see below)
    sb.urls.modify (·.push hello)
    let mut seen := false
    for _ in [0:300] do
      discard <| step []
      let s ← get
      let some t := Community.Target.parse hello | break
      if s.page == .chat then
        if let some i := s.ids.findIdx? (·.2 == t.message) then
          let (bots, _) := bottoms s
          let x := t.message
          -- wholly in the viewport: its bottom at or above the viewport's
          -- bottom edge (offset b), its top below the top edge
          if bots[i]! ≥ s.b && bots[i]! + heightOf s x ≤ s.b + (geom s).viewNow && s.rows.contains x then
            seen := true
            break
    let s ← get
    check s!"the card's link opens the conversation with its message wholly on screen ({s.total} messages; page {repr s.page})"
      (seen && s.total > 100)
    writePpm (dir ++ "/b-link.ppm") 1080 (← screenOf sb 1080 2400 63)
    sb.cmds.modify (·.push "back")
    steps 3
    -- Sync in the background, on
    sb.cmds.modify (·.push "keep on")
    steps 2
    check "Sync in the background turns the service on" ((← get).keepSync && (← sb.service.get).back? == some true)
    discard <| step [.background]
    check "the background keeps the node's parked writes and the setting" ((← get).keepSync)).run b5
  let ((), a7) ← (show M Unit from do
    sa.cmds.modify (·.push "send while away")
    steps 2
    waitIdle sa).run a6
  let _ ← carry a7 b6
  let (held, b7) ← (show M Nat from do
    let n0 := (← sb.notes.get).size
    let f0 ← sb.frames.get
    let got ← packetsUntil sb n0 100 (·.any fun p => alerts p && field p "body" == "while away")
    if !got then
      let s ← get
      IO.println s!"  diag: held {← heldTotal} mounted {s.life.mounted} rst {s.rst.isSome} active {s.active} keep {s.keepSync} netStop {s.netStop.isSome}"
      IO.println s!"  diag: last turn held {(s.notesKey.map fun (_, _, xs) => xs.map fun (_, sn) => sn.rows.map fun (r : Kinds.Notify.Row) => r.text).getD []}"
      IO.println s!"  diag: packets since {((← sb.notes.get).extract n0 (← sb.notes.get).size).toList}"
    check "with Sync in the background on, a post arriving in the background alerts" got
    check "and nothing is drawn" ((← sb.frames.get) == f0)
    -- in front again; then off
    discard <| step [.foreground]
    steps 5
    sb.cmds.modify (·.push "keep off")
    steps 2
    check "off turns the service off" (!(← get).keepSync && (← sb.service.get).back? == some false)
    let held ← heldTotal
    discard <| step [.background]
    return held).run b6
  let ((), a8) ← (show M Unit from do
    sa.cmds.modify (·.push "send unheard")
    steps 2
    waitIdle sa).run a7
  let _ ← carry a8 b7
  let ((), b8) ← (show M Unit from do
    let n0 := (← sb.notes.get).size
    -- the post is in B's store (its writer runs in the background), yet
    -- nothing of B's turns runs there
    check "the post is stored while B is in the background" (← untilHeld held 4000)
    let got ← packetsUntil sb n0 60 (·.any alerts)
    check "with it off, nothing alerts while in the background" (!got)
    let got ← packetsUntil sb n0 200 (·.any fun p => alerts p && field p "body" == "unheard") [.foreground]
    check "and the post alerts once B is in front (on another page)" got).run b7
  -- A removes B: B's standing card goes
  let ((), a9) ← (show M Unit from do
    let s ← get
    let (bs, _, _) ← (show M _ from readList (admission.all.query [s.me.c]) #[])
    let bUser := bs.rows.filterMap fun (_, f) => match f with
      | .admission _ u _ _ _ => if u != s.me.c then some u else none
      | _ => none
    let some u := bUser.head? | check "A finds B's user" false
    let ok ← removeWrite u
    discard <| settle
    waitIdle sa
    steps 5
    check "A removes B" ok).run a8
  let _ ← carry a9 b8
  let ((), _) ← (show M Unit from do
    let n0 := (← sb.notes.get).size
    waitIdle sb
    steps 5
    let got ← packetsUntil sb n0 200 (·.any fun p => field p "action" == "cancel")
    if !got then
      let s ← get
      IO.println s!"  diag: comms {s.comms.size} page {repr s.page} active {s.notes.active.length} packets {((← sb.notes.get).extract n0 (← sb.notes.get).size).toList}"
    check "B's removal withdraws its standing card" got
    check "and no card stands" (← get).notes.active.isEmpty).run b8
  check "over the whole run, A's own posts never alerted A" ((← sa.notes.get).all (!alerts ·))
  IO.FS.writeFile (dir ++ "/b-notes.jsonl") (String.intercalate "\n" (← sb.notes.get).toList)
  let n ← fails.get
  IO.println (if n == 0 then "notify: all pass" else s!"notify: {n} failed")
  IO.Process.exit (if n == 0 then 0 else 1)
