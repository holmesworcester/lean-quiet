/-
App lifecycle hooks: checkpoint local UI ops, revoke the mounted page,
restore drafts, rebuild geometry. Root reads run on the app thread;
unmount revokes the reader and retires its board and pure workers.
Only suspend polls for quiescence, with one absolute deadline. `page_round` checks the durable page tag.
-/
import ops.app.Wait

namespace App
open Engine Community Data Paint Font Row

def PageId.code : PageId → Nat
  | .home => 0 | .chat => 1 | .getStarted => 2 | .create => 3 | .createName => 4
  | .joinChoice => 5 | .openInvite => 6 | .paste => 7 | .scan => 8 | .name => 9
  | .agree => 10 | .waiting => 11 | .requests => 12 | .invite => 13 | .switcher => 14
  | .profile => 15 | .removeConfirm => 16 | .duplicate => 17

def PageId.ofCode : Nat → PageId
  | 0 => .home | 1 => .chat | 2 => .getStarted | 3 => .create | 4 => .createName
  | 5 => .joinChoice | 6 => .openInvite | 7 => .paste | 8 => .scan | 9 => .name
  | 10 => .agree | 11 => .waiting | 12 => .requests | 13 => .invite | 14 => .switcher
  | 15 => .profile | 16 => .removeConfirm | 17 => .duplicate | _ => .getStarted

theorem page_round (p : PageId) : PageId.ofCode p.code = p := by cases p <;> rfl

def fieldPage (p : PageId) : Bool :=
  p == .create || p == .createName || p == .paste || p == .name

/-- Bottom coordinates shared with the conversation's anchor. -/
def rowBottom (s : St) (x : Id) : Option Nat := Id.run do
  let mut y := bottomPad + s.newer * est
  for (_, m) in s.ids do
    if m == x then return some y
    y := y + s.heights.getD m est
  return none

def captureAnchor (s : St) : Option (Id × Nat) := Id.run do
  if s.page != .chat then return s.mark
  if s.b ≤ 4 then return none
  if let some (x, above) := s.mark then
    if let some bot := rowBottom s x then
      let top := bot + s.heights.getD x est
      if s.b ≤ top && top - s.b == above then return s.mark
  let mut y := bottomPad + s.newer * est
  for (_, x) in s.ids do
    let h := s.heights.getD x est
    if y ≤ s.b && s.b < y + h then return some (x, y + h - s.b)
    y := y + h
  return s.mark

def stashDraft (s : St) : St :=
  if s.me.acc.isEmpty then s else
  { s with drafts := (s.me.acc, s.text, s.chips.toList.map (·.1)) :: s.drafts.filter (·.1 != s.me.acc) }

def removalBytes (r : Remove.Step) : ByteArray :=
  Codec.encode (match r with
    | .idle => (0, .empty, ByteArray.empty) | .first u => (1, u, .empty)
    | .second u => (2, u, .empty) | .sending u => (3, u, .empty)
    | .failed u why => (4, u, why.toUTF8) : Nat × Id × ByteArray)

def removalFrom (b : ByteArray) : Remove.Step :=
  match (Codec.decode b : Option (Nat × Id × ByteArray)) with
  | some (1, u, _) => .first u | some (2, u, _) => .second u | some (3, u, _) => .sending u
  | some (4, u, why) => .failed u (String.fromUTF8! why) | _ => .idle

def checkpoint (s : St) : Lifecycle.Checkpoint :=
  let s := stashDraft s
  let a := s.mark.getD (.empty, 0)
  (1, s.page.code, s.cur, a.1, a.2,
    [Codec.encode (s.backStack.map PageId.code), s.field.toUTF8,
     ((s.invite.map (·.text)).getD "").toUTF8, s.joinName.toUTF8, s.newCommunity.toUTF8,
     removalBytes s.removal,
     Codec.encode (s.profileOf.toList.map fun (u, n, me) => (u, n.toUTF8, me)),
     Codec.encode (s.drafts.map fun (a, t, bs) => (a, t.toUTF8, bs)), Codec.encode s.anchor,
     Codec.encode (s.links.map fun (a, l) => (a, l.toUTF8)), Codec.encode s.queuedWrites,
     Codec.encode (s.mark.bind fun (x, _) => s.ids.find? (·.2 == x))])

/-- A changed checkpoint, handed to the writer's thread, which commits
it. The frame never commits: it holds its read transaction all turn, and
a node's `wal_checkpoint(TRUNCATE)` holds the write lock until every
reader finishes, so a commit here waited on the frame itself until
SQLite's busy timeout threw out of `step`. -/
def saveCheckpoint : M Unit := do
  let s ← get
  if s.dbPath.isEmpty then return
  let cp := checkpoint s
  if s.saved == some cp then return
  s.wr.save (Codec.encode cp)
  modify fun s => { s with saved := some cp }

/-- `saveCheckpoint` as it was: committed on the frame's thread while
its read transaction is open. The `block` rule's negative control (`waits` in
tests/wiring.txt); never run. -/
def saveWaits : M Unit := do
  let s ← get
  Lifecycle.save s.rd (Codec.encode (checkpoint s))

def restoreChips (s : St) (bs : List ByteArray) : Array (ByteArray × Nat × Nat × Composer.Chip) :=
  (bs.filterMap fun b => do
    let src ← Image.decode b
    return (b, src.w, src.h, ⟨Image.square src (s.dim.px 64) Row.bg, s!"{Arrival.humanBytes b.size}"⟩)).toArray

def useDraft (s : St) : St :=
  let (_, t, bs) := (s.drafts.find? (·.1 == s.me.acc)).getD (.empty, "", [])
  { s with text := t, chips := restoreChips s bs, sel := #[t.length.toUInt32, t.length.toUInt32, 0, 0] }

/-- Called after switchToAcc selected the saved acceptance. A removed or
missing acceptance is never restored by this function. -/
def applyCheckpoint (s : St) (cp : Lifecycle.Checkpoint) : St := Id.run do
  let (_, p, _, x, off, bs) := cp
  let b := fun i => bs[i]?.getD .empty
  let str := fun i => String.fromUTF8! (b i)
  let drafts := ((Codec.decode (b 7) : Option (List (Id × ByteArray × List ByteArray))).getD []).map
    fun (a, t, pics) => (a, String.fromUTF8! t, pics)
  let profile := ((Codec.decode (b 6) : Option (List (Id × ByteArray × Bool))).getD []).head?.map
    fun (u, n, me) => (u, String.fromUTF8! n, me)
  let stack := ((Codec.decode (b 0) : Option (List Nat)).getD []).map PageId.ofCode
  let nav := match stack.reverse with
    | [] => Nav.reset (PageId.ofCode p)
    | x :: xs => xs.foldl (fun n p => Nav.go p n) (Nav.reset x)
  let s := { s.withNav (Nav.go (PageId.ofCode p) nav) with
    field := str 1, invite := Community.Invite.parse (str 2), joinName := str 3, newCommunity := str 4,
    removal := removalFrom (b 5), profileOf := profile, drafts,
    mark := if x.isEmpty then none else some (x, off), restoreAnchor := !x.isEmpty,
    anchor := (Codec.decode (b 11) : Option (Option Pos)).getD
      ((Codec.decode (b 8) : Option (Option Pos)).getD none),
    links := ((Codec.decode (b 9) : Option (List (Id × ByteArray))).getD []).map fun (a, l) => (a, String.fromUTF8! l),
    saved := some cp, mountedPage := none }
  return useDraft s

/-- Pure workers may finish, but their results cannot publish after
revocation. Retain them for suspend's bounded quiescence check. -/
def retireRow (r : RowSt) : M Unit := do
  for t in r.task.toList ++ r.dimmed.toList do
    modify fun s => { s with paintStop := s.paintStop.push (t.map fun _ => ()) }

def retirePaints (s : St) : M Unit := do
  for (_, r) in s.rows.toList do retireRow r
  for (_, t) in s.imgs.toList do
    modify fun s => { s with paintStop := s.paintStop.push (t.map fun _ => ()) }
  if let some t := s.decoding then
    modify fun s => { s with paintStop := s.paintStop.push (t.map fun _ => ()) }

/-- Acts already judged by the reader belong to the store. Retiring a
page never discards their writes or runs their UI continuations. -/
def parkDone (sh : Reader.Shared) : M Unit := do
  let done ← sh.done.modifyGet fun ds => (ds, #[])
  let writes := done.filterMap fun (_, w) => w.map (·.ops)
  if writes.isEmpty then return
  modify fun s => { s with
    toNode := s.toNode ++ writes, queuedWrites := s.queuedWrites ++ writes.toList.flatten.map Op.bytes }
  saveCheckpoint

/-- A single nonblocking poll. A result is taken only after completion. -/
def pollRetired : M Unit := do
  let s ← get
  if let some t := s.netStop then
    if ← IO.hasFinished t then
      match t.get with
      | .ok _ => modify fun s => { s with netStop := none }
      | .error e => throw e
  if let some w := s.readerStop then
    if ← IO.hasFinished w.done then
      match w.done.get with
      | .ok r =>
        if let some sh := s.retiredBoard then parkDone sh
        modify fun s => { s with readerStop := none, retiredBoard := none, rst := some { rd := r.rd } }
      | .error e => throw e
  let mut pending := #[]
  for t in s.paintStop do
    unless ← IO.hasFinished t do pending := pending.push t
  modify fun s => { s with paintStop := pending }

def unmountState (s : St) : St :=
  { stashDraft s with
    mark := captureAnchor s, life := s.life.unmount, input := Input.revoke s.input,
    rows := {}, imgs := {}, imgRetry := {}, live := { reads := s.live.reads }, touched := {},
    sheet := none, selected := none, camOn := false, camView := none, decoding := none,
    pageNow := none, pageKey := none, chromeKey := "", imeH := 0, mountedPage := none,
    picWants := #[], retryWants := {}, lastSlices := none }

/-- Revoke before detaching the board. An issued SQLite read may finish
on the old refs, but no subsequent query or publication is authorized. -/
def stopReader : M Unit := do
  let s ← get
  if let some w := s.reader then w.stopped.set true
  parkDone s.sh
  let out ← s.sh.out.get
  s.sh.acts.set #[]
  s.sh.wants.set #[]
  s.sh.board.set {}
  s.sh.out.set #[]
  s.sh.notes.set #[]
  s.sh.seen.set 0
  let sh ← Reader.Shared.new s.wr.count
  sh.out.set out
  modify fun s => { s with
    sh, reader := none,
    readerStop := s.reader.orElse fun _ => s.readerStop,
    retiredBoard := if s.reader.isSome then some s.sh else s.retiredBoard,
    rst := s.rst.map fun r => { rd := r.rd } }
  pollRetired

def resumeReader : M Unit := do
  pollRetired
  let s ← get
  if !s.threaded || !s.active || !s.surface || s.netStop.isSome || s.reader.isSome then return
  if let some r := s.rst then
    let w ← Reader.Worker.start s.sh r
    modify fun s => { s with reader := some w, rst := none }

/-- The unmount barrier used by navigation and suspension. -/
def leavePage : M Unit := do
  let s ← get
  s.io.ime false
  if let some p := s.input.press then s.io.motion { p.first with phase := 3 }.words
  if s.camOn then s.io.scan false
  stopReader
  retirePaints s
  modify unmountState

/-- Mount after refreshing the viewport. -/
def mountPage : M Unit := do
  let s ← get
  if !s.active || !s.surface || s.netStop.isSome then return
  if s.mountedPage == some (s.page, s.cur) then resumeReader; return
  if s.mountedPage.isSome then leavePage
  modify fun s => { s with life := s.life.mount, mountedPage := some (s.page, s.cur) }
  let s ← get
  resumeReader
  let t := if fieldPage s.page then s.field else s.text
  s.io.setText t
  modify fun s => { s with native := t }

def pruneLive : M Unit := do
  modify fun s => { s with live := Lifecycle.prune (s.live.keep s.touched.contains) s.life, touched := {} }

/-- The callback's lease is captured when queued. -/
def owned (l : Lifecycle.Lease) (action : M α) : M (Option α) := do
  Lifecycle.owned (← get).life l action

/-- Re-layout every mounted row and invalidate its old pixels. -/
def resize (sc : Array UInt32) : M Unit := do
  let s ← get
  let w := (sc[0]?.getD s.W.toUInt32).toNat
  let h := (sc[1]?.getD s.Hs.toUInt32).toNat
  let it := (sc[2]?.getD s.insetTop.toUInt32).toNat
  let ib := (sc[3]?.getD s.insetBot.toUInt32).toNat
  let dpi := (sc[4]?.getD s.dim.dpi.toUInt32).toNat
  if w == s.W && h == s.Hs && it == s.insetTop && ib == s.insetBot && dpi == s.dim.dpi then return
  if let some p := s.input.press then s.io.motion { p.first with phase := 3 }.words
  retirePaints s
  let dm : Dim := ⟨dpi, s.font.cell⟩
  let mut rows := s.rows
  let mut heights := if w == s.W && dpi == s.dim.dpi then s.heights else {}
  for (x, r) in s.rows.toList do
    let lay := Row.layout s.font dm w r.data
    rows := rows.insert x { r with
      lay, ver := r.ver + 1, task := none, shown := none,
      dimmed := none, dimShown := none }
    heights := heights.insert x lay.h
  modify fun s => { s with
    W := w, Hs := h, insetTop := it, insetBot := ib, dim := dm, input := Input.revoke s.input,
    bgRow := solid Row.bg w, rows, heights, imgs := {}, imgRetry := {},
    picWants := #[], retryWants := {}, lastSlices := none,
    life := { s.life with generation := s.life.generation + 1 },
    mark := captureAnchor s, restoreAnchor := true, pageKey := none, pageNow := none,
    chromeKey := "", gridKey := "", gridRows := {} }

/-- The native field may have changed in the same poll as background.
Save its final text before hiding it; search text is not a composer draft. -/
def captureInput : M Unit := do
  let s ← get
  if !s.active || !s.surface || !s.life.mounted then return
  if fieldPage s.page then
    let (field, _) ← s.io.text
    modify fun s => { s with field }
  else if s.page == .chat && !(s.sheet.map (·.searching)).getD false then
    let (text, _) ← s.io.text
    modify fun s => { s with text }

/-- A finished producer's writes are store-owned, even after unmount. -/
def parkChaos : M Unit := do
  let s ← get
  if let some t := s.chaos then
    if ← IO.hasFinished t then
      let jobs := t.get
      let ops := jobs.toList.flatMap (·.ops)
      modify fun s => { s with
        chaos := none, toNode := s.toNode ++ jobs.map (·.ops), queuedWrites := s.queuedWrites ++ ops.map Op.bytes }
      s.wr.busy.modify (· - 1)
      saveCheckpoint

/-- Reap only finished work; used by background polls and foreground too. -/
def reap : M Unit := do
  pollRetired
  if !(← get).life.mounted then parkChaos

/-- One deadline, not one timeout per worker. On expiry, pending handles
and every parked write remain owned. Resume only polls; it never joins. -/
def suspend (budget : Nat := 250) : M Unit := do
  let deadline := (← IO.monoMsNow) + budget
  captureInput
  let s ← get
  if s.net.isSome || s.netBoot.isSome then
    let stopping ← IO.asTask (prio := .dedicated) (stopNodes s.netBoot s.net)
    modify fun s => { s with netStop := some stopping }
  modify fun s => { s with net := none, netBoot := none, restoreAnchor := s.mark.isSome }
  s.wr.paused.set false
  leavePage
  saveCheckpoint
  discard <| waitFor deadline do
    reap
    let s ← get
    return s.netStop.isNone && s.readerStop.isNone && s.paintStop.isEmpty &&
      s.chaos.isNone && (← s.wr.busy.get) == 0 && (← s.wr.saveDone)

end App
