/- Actual local-send admission, Reader windows and native presentation.
The FIFO proof uses the runtime representation; tests use signed sends and
SQLite, with finite worker barriers only where an ordering must be forced. -/
import platforms.headless.Sim
import tests.engine.Checks
import tests.engine.Lib

open App Engine Community Data Tests

namespace PresentationTests

def exampleEntry (i : Nat) : Presentation.Entry :=
  ⟨"accepted".toUTF8, "community".toUTF8,
   (msgKey i 1, ⟨#[i.toUInt8]⟩), (msgKey i 1, ⟨#[i.toUInt8]⟩)⟩

def pair : Presentation.Queue := ⟨[exampleEntry 1, exampleEntry 2], by decide⟩
def triple : Presentation.Queue := ⟨[exampleEntry 1, exampleEntry 2, exampleEntry 3], by decide⟩
def full : Presentation.Queue :=
  ⟨(List.range Presentation.capacity).map exampleEntry, by simp⟩

theorem boundWitness : pair.entries.length ≤ Presentation.capacity := Presentation.bounded pair

theorem appendWitness : triple.entries = pair.entries ++ [exampleEntry 3] :=
  Presentation.offer_append pair triple (exampleEntry 3) (by rfl)

theorem fullWitness : full.offer (exampleEntry 9) = none :=
  Presentation.offer_full full (exampleEntry 9) (by simp [full])

theorem completionWitness : ∃ frame : UInt64,
    some (4294967297, (exampleEntry 1).message.2) = some (frame, (exampleEntry 1).message.2) ∧
    some 4294967297 = some frame :=
  Presentation.acknowledge_matches _ _ _ (by rfl)


def await (what : String) (ready : IO Bool) : IO Unit := do
  let deadline := (← IO.monoMsNow) + 10000
  while !(← ready) do
    if (← IO.monoMsNow) > deadline then throw (IO.userError s!"timeout: {what}")
    IO.sleep 1

def run (ck : Checks) : IO Unit := do
  ck.ok "native completion decoder keeps full publication identity and explicit absence"
    (Session.completed #[21, 0, 1, 0, 1, 1, 0, 0] 0 == some (4294967297, 0) &&
     Session.completed #[21, 0, 0, 0, 0, 0, 0, 0] 99 == none)
  let dir := s!"out/component-demand/presentation-{← IO.Process.getPID}"
  IO.FS.createDirAll dir
  let sm ← Sim.new
  sm.viewport.set #[420, 900, 20, 20, 160]
  let initial ← App.start sm.io (← sm.viewport.get) (dir ++ "/quiet.db")
  let (_, final) ← (show App.M Unit from do
    found "Presentation FIFO" "Alice"
    openPage .chat
    waitIdle sm
    let writer := (← get).wr
    writer.setPaused true
    for i in [0:Presentation.capacity] do
      modify fun s => { s with text := s!"Accepted own message {i}" }
      sendNow
    let queued ← get
    let ids := queued.ownSends.entries.map (·.message.2)
    ck.ok "eight sequential signed sends enter a bounded FIFO while their first ancestor is uncommitted"
      (ids.length == Presentation.capacity && ids.eraseDups.length == ids.length &&
       queued.out.size == Presentation.capacity && (← writer.busy.get) == Presentation.capacity)
    let some first := queued.ownSends.head | throw (IO.userError "presentation FIFO was empty")
    ck.ok "pending child sends retain their actual common root and their own positions"
      (queued.ownSends.entries.all (·.root.2 == first.message.2) &&
       queued.ownSends.entries.tail.all (fun e => e.message.2 != first.message.2))
    let bytes := queued.queuedWrites
    let pending := queued.out.toList.map (·.op.id)
    modify fun s => { s with text := "Do not lose this draft" }
    sendNow
    let refused ← get
    ck.ok "full presentation capacity refuses the ninth send without replacing an obligation or draft"
      (refused.text == "Do not lose this draft" && refused.queuedWrites == bytes &&
       refused.out.toList.map (·.op.id) == pending &&
       refused.ownSends.entries.map (·.message.2) == ids)
    let mut optimistic := false
    for _ in [0:300] do
      steps 1
      if (← get).rows[first.message.2]?.any (fun r => r.data.pending && r.shown.isSome) then
        optimistic := true; break
      IO.sleep 2
    ck.ok "an actual optimistic native presentation leaves all eight obligations pending"
      (optimistic && (← get).ownSends.entries.map (·.message.2) == ids)
    let entered ← IO.mkRef false
    let release ← IO.mkRef false
    let pool := (← get).raster
    let blocker ← pool.request
      ⟨["presentation-barrier".toUTF8], .row 0 "barrier".toUTF8 0 [] .dark, true⟩ fun _ => do
        entered.set true
        await "presentation worker release" release.get
        return some default
    await "presentation worker entered" entered.get
    writer.setPaused false
    let mut committedFlight : Option Raster.RowPaint.Flight := none
    for _ in [0:300] do
      steps 1
      if let some r := (← get).rows[first.message.2]? then
        if !r.data.pending && r.task.isSome then committedFlight := r.paintFlight; break
      IO.sleep 2
    let some flight := committedFlight | throw (IO.userError "committed presentation paint missing")
    release.set true
    await "presentation barrier completes" (IO.hasFinished blocker.result)
    await "committed presentation paint completes" (IO.hasFinished flight.handle.result)
    modify fun s => { s with rasterNeeds := #[] }
    paintRow first.message.2
    let collected ← get
    ck.ok "collecting a committed bitmap alone cannot discharge a visible presentation"
      (collected.rows[first.message.2]?.any (fun r => r.shownCommitted && r.task.isNone) &&
       collected.ownSends.entries.map (·.message.2) == ids)
    let before ← sm.frames.get
    discard <| present (Array.replicate (viewH collected + 2 * over) collected.bgRow) collected.b false
    ck.ok "a real native frame containing blank pixels does not acknowledge the message"
      ((← sm.frames.get) > before && (← get).ownSends.entries.map (·.message.2) == ids)
    let originalIme := (← get).imeH
    modify fun s => { s with imeH := s.Hs - topH s - botH s - 1 }
    let occluded ← get
    discard <| present (listFrame occluded occluded.b (bottoms occluded).1) occluded.b false
    ck.ok "keyboard-occluded body pixels do not count as visible presentation"
      ((geom occluded).viewNow < occluded.dim.lineH &&
       (← get).ownSends.entries.map (·.message.2) == ids)
    modify fun s => { s with imeH := originalIme }
    let shown ← get
    sm.raw.set #[20, 0, 0, 0, 0, 0, 0, 0]
    discard <| present (listFrame shown shown.b (bottoms shown).1) shown.b false
    ck.ok "a native rejected publication cannot acknowledge otherwise visible body pixels"
      ((← get).ownSends.entries.map (·.message.2) == ids && (← get).presenting.isNone)
    -- Asynchronous completion is separate from successful staging. The
    -- publication token intentionally exceeds the wrapped input-frame range.
    sm.raw.set #[20, 1, 1, 1, 0, 0, 0, 0, 21, 0, 0, 0, 0, 0, 0, 0]
    discard <| present (listFrame shown shown.b (bottoms shown).1) shown.b false
    ck.ok "accepted asynchronous staging records one candidate without releasing an obligation"
      ((← get).ownSends.entries.map (·.message.2) == ids &&
       (← get).presenting.any (fun p => p.frame == 4294967297))
    -- The input serial matches zero here, but the completed ticket is old.
    sm.raw.set #[20, 1, 2, 1, 0, 0, 0, 0, 21, 0, 1, 0, 1, 0, 0, 0]
    discard <| present (listFrame shown shown.b (bottoms shown).1) shown.b false
    ck.ok "a wrapped frame serial cannot alias a distinct old publication ticket"
      ((← get).ownSends.entries.map (·.message.2) == ids &&
       (← get).presenting.any (fun p => p.frame == 4294967298))
    sm.raw.set #[20, 1, 3, 1, 0, 0, 0, 0, 21, 0, 1, 700, 2, 1, 0, 0]
    discard <| present (listFrame shown shown.b (bottoms shown).1) shown.b false
    ck.ok "a matching native completion shifted off the recorded viewport does not release"
      ((← get).ownSends.entries.map (·.message.2) == ids)
    for _ in [0:3] do
      sm.raw.set #[20, 0, 3, 1, 0, 0, 0, 0, 21, 0, 0, 0, 0, 0, 0, 0]
      discard <| present (listFrame shown shown.b (bottoms shown).1) shown.b false
    ck.ok "three rejected publications retain the exact candidate for its delayed completion"
      ((← get).ownSends.entries.map (·.message.2) == ids &&
       (← get).presenting.any (fun p => p.frame == 4294967299))
    let before ← sm.frames.get
    sm.raw.set #[20, 1, 4, 1, 0, 0, 0, 0, 21, 0, 1, 0, 3, 1, 0, 0]
    discard <| present (listFrame shown shown.b (bottoms shown).1) shown.b false
    ck.ok "the actual visible committed frame removes only the FIFO head"
      ((← sm.frames.get) > before && (← get).ownSends.entries.map (·.message.2) == ids.tail)
    let mut order := [first.message.2]
    for _ in [0:300] do
      let old := (← get).ownSends.entries.map (·.message.2)
      if old.isEmpty then break
      steps 1
      let next := (← get).ownSends.entries.map (·.message.2)
      if next.length < old.length then order := order ++ [old.head!]
      IO.sleep 2
    ck.ok "all accepted sends receive committed presentations in their original order"
      ((← get).ownSends.entries.isEmpty && order == ids)
    -- Unknown/invalid ancestry must not be turned into an optimistic fact
    -- just to register a presentation obligation. The invite is valid;
    -- the post deliberately cites it where an admission is required.
    let s ← get
    let some key ← intentView (Community.currentKey s.me.c) | throw (IO.userError "fixture key missing")
    let bearer := Device.named "invalid presentation parent"
    let invitation := invite s.me.c s.me.adm s.me.dev bearer.pk false
    let bad := sealedPost s.me.c invitation.id s.me.dev key (← newBytes 24)
      "Invalid child must not display".toUTF8 1 1
    let validParent ← Reader.judgeWrite s.rd s.out ⟨[invitation]⟩
    let invalid ← Reader.judgeWrite s.rd s.out ⟨[invitation, bad]⟩
    let oldBytes := s.queuedWrites
    let oldOut := s.out.toList.map (·.op.id)
    let accepted ← writeAll ⟨[invitation, bad]⟩ (present := true)
    let afterBad ← get
    ck.ok "a valid pending parent of the wrong kind still refuses the entire write"
      (validParent.any (·.size == 1) && invalid.isNone && !accepted &&
       afterBad.queuedWrites == oldBytes && afterBad.out.toList.map (·.op.id) == oldOut &&
       afterBad.ownSends.entries.isEmpty &&
       (← (Store.getOp invitation.id : SqlM SF _).run s.rd).isNone)
    modify fun s => { s with text := "Navigation cancellation" }
    sendNow
    let navId := (← get).ownSends.head.map (·.message.2)
    openPage .home
    ck.ok "explicit page navigation cancels presentation demand without cancelling its accepted write"
      (navId.isSome && (← get).ownSends.entries.isEmpty &&
        (← get).queuedWrites.any (fun bytes => (Op.decode bytes).any fun o => some o.id == navId))
    let mut controls := 0
    for i in [0:Presentation.capacity + 2] do
      if ← sendText s!"Background control write {i}" then controls := controls + 1
    ck.ok "programmatic background writes do not create an invisible full presentation queue"
      (controls == Presentation.capacity + 2 && (← get).ownSends.entries.isEmpty)
    openPage .chat
    modify fun s => { s with text := "User scroll cancellation" }
    sendNow
    let scrollId := (← get).ownSends.head.map (·.message.2)
    discard <| onEvent (.scrolling true)
    ck.ok "an explicit native scroll gesture releases the send pin"
      (scrollId.isSome && (← get).ownSends.entries.isEmpty)
    modify fun s => { s with text := "Unreadable cancellation" }
    sendNow
    let s ← get
    let some entry := s.ownSends.head | throw (IO.userError "unreadable control missing")
    let unavailable := (← s.sh.board.get).put (.row s.me.c s.me.adm entry.message.2) (.row none)
    mount unavailable entry.message.2
    ck.ok "an explicit inaccessible-row answer releases its obligation and cached pixels"
      (!(← get).ownSends.contains entry.message.2 && !(← get).rows.contains entry.message.2)
    -- Saturated posts are positioned by actual receipt facts, including a
    -- saturated root's receipt when the next local write is its child.
    waitIdle sm
    let s ← get
    let predecessor := sealedPost s.me.c s.me.adm s.me.dev key (← newBytes 24)
      "Counter predecessor".toUTF8 (countCap - 1) 0
    unless ← writeAll ⟨[predecessor]⟩ do throw (IO.userError "saturation predecessor refused")
    waitIdle sm
    writer.setPaused true
    modify fun s => { s with text := "Saturated root" }
    sendNow
    modify fun s => { s with text := "Saturated child" }
    sendNow
    let saturated ← get
    let entries := saturated.ownSends.entries
    let receiptPos (id : Id) := (saturated.out.find? fun p => match p.fact with
      | .received _ _ m _ _ => m == id
      | _ => false).map fun p => (sortOf p.fact, id)
    ck.ok "saturated root and child pins use the same receipt positions as Reader windows"
      (entries.length == 2 && entries.head?.any (fun root =>
        root.root == root.message && receiptPos root.message.2 == some root.message &&
        entries[1]?.any (fun child => child.root == root.message &&
          child.message != root.message && receiptPos child.message.2 == some child.message)))
    writer.setPaused false
    for _ in [0:300] do
      steps 1
      if (← get).ownSends.entries.isEmpty then break
      IO.sleep 2
    ck.ok "saturated root and child both reach actual committed presentation"
      ((← get).ownSends.entries.isEmpty)
    let beforeInvisible ← get
    for text in [String.ofList [Char.ofNat 0x200b, Char.ofNat 0x2060],
        String.ofList [Char.ofNat 0xa0, '\n', Char.ofNat 0x200b]] do
      modify fun s => { s with text }
      sendNow
      let refused ← get
      ck.ok "a wholly inkless composer draft is refused before outbox or presentation admission"
        (refused.text == text && refused.out.toList.map (·.op.id) == beforeInvisible.out.toList.map (·.op.id) &&
          refused.queuedWrites == beforeInvisible.queuedWrites && refused.ownSends.entries.isEmpty)
    let enormousInvisible := String.ofList (List.replicate (Sync.maxFrame / 2 + 1) (Char.ofNat 0xa0))
    modify fun s => { s with text := enormousInvisible }
    sendNow
    let refused ← get
    ck.ok "an impossible-size inkless draft is refused before text raster validation"
      (refused.text == enormousInvisible && refused.out.toList.map (·.op.id) == beforeInvisible.out.toList.map (·.op.id) &&
        refused.queuedWrites == beforeInvisible.queuedWrites && refused.ownSends.entries.isEmpty &&
        refused.toast.any (fun t => t.1 == "This message is too large to send. Shorten it and try again."))
    -- ASCII trimming alone cannot erase a leading zero-width character.
    -- A tall inkless prefix must neither acknowledge a blank line nor
    -- leave the actual first glyph permanently below the pinned viewport.
    let inklessPrefix := String.ofList [Char.ofNat 0x200b] ++ String.ofList (List.replicate 45 '\n')
    modify fun s => { s with text := inklessPrefix ++ "The visible committed body" }
    sendNow
    let some blankEntry := (← get).ownSends.head | throw (IO.userError "blank-prefix send missing")
    for _ in [0:300] do
      steps 1
      if !(← get).ownSends.contains blankEntry.message.2 then break
      IO.sleep 2
    let shown ← get
    let some blankRow := shown.rows[blankEntry.message.2]? | throw (IO.userError "blank-prefix row missing")
    let expectedY := blankRow.lay.textY + Row.bodyHeight shown.dim blankRow.data (blankRow.lay.text.size - 1)
    let expectedTop := (rowBottom shown blankEntry.message.2).getD 0 + blankRow.lay.h - expectedY
    ck.ok "a tall inkless prefix is skipped and actual committed glyph pixels become visible"
      (!shown.ownSends.contains blankEntry.message.2 &&
        expectedY > (geom shown).viewNow &&
        shown.b + shown.dim.lineH ≤ expectedTop && expectedTop ≤ shown.b + (geom shown).viewNow &&
        (presentationBand shown blankRow).any (fun b => b.1 == expectedY))
    modify fun s => { s with text := "" }
    attachSamplePhoto
    sendNow
    let some photoEntry := (← get).ownSends.head | throw (IO.userError "photo-only send missing")
    for _ in [0:300] do
      steps 1
      if !(← get).ownSends.contains photoEntry.message.2 then break
      IO.sleep 2
    let shown ← get
    let some photoRow := shown.rows[photoEntry.message.2]? | throw (IO.userError "photo-only row missing")
    ck.ok "a photo-only send waits for its visible decoded preview rather than blank text or a placeholder"
      (!shown.ownSends.contains photoEntry.message.2 && photoRow.data.text.isEmpty &&
        photoRow.painted.2[1]?.getD false &&
        (presentationBand shown photoRow).any (fun b => photoRow.lay.pics[0]?.any (·.y == b.1)))
    ).run initial
  final.raster.reconcile []

end PresentationTests
