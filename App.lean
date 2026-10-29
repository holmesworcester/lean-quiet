/-
The app: one conversation, bottom-anchored, with a header and a composer.

Each frame:
1. Takes the writer's notices: live answers go stale; outbox entries whose
   ops are now decided leave it (the store answers for them, same id).
2. Handles the twin's events and the control commands.
3. Reads the offset (the OS scrolls).
4. Reads again what is stale: the list's ids (one query, newest first,
   as many as the screen and the fetch distance need), and each mounted
   row's own answers (its message, author, pictures and reactions).
   Rows within the fetch distance of the frame are mounted: read and laid
   out, so their heights are known before they are drawn.
5. Keeps what is on screen still while heights change: the row at the
   viewport's bottom edge stays where it was (unless the view is pinned
   to the newest message, which then stays pinned).
6. Paints rows whose answers or decoded pictures changed, on worker
   tasks; the frame shows each row's last finished paint.
7. Assembles the list frame from the rows' own pixel rows (no copying:
   the frame holds the same row objects), and hands it over with the
   header and the composer.

Everything the platform does goes through `Io`, so tests drive the same
code without a window (QTests).
-/
import AppLife

namespace App
open Engine Community Data Paint Font Row

/-- Rebuild every colour-bearing cache from the new effective theme.
Old asynchronous tasks lose their references and cannot publish later. -/
def themed (s : St) (theme : Theme.State) : St :=
  let dm := s.dim
  let dm := { dm with theme := Theme.effective theme }
  { s with
    theme := theme
    dim := dm
    bgRow := solid (Palette.color (Theme.effective theme) .bg) s.W,
    rows := {}, imgs := {}, imgWaiting := {}, gridRows := {}, gridKey := "",
    chips := s.chips.map fun (bytes, w, h, chip) =>
      let thumb := match Image.decode bytes with
        | some src => Image.square src (s.dim.px 64) (Palette.color (Theme.effective theme) .bg)
        | none => Bitmap.blank (s.dim.px 64) (s.dim.px 64) (solid (Palette.color (Theme.effective theme) .bg) (s.dim.px 64))
      (bytes, w, h, { chip with thumb }),
    topBmp := default, botBmp := default, chromeKey := "", pageNow := none, pageKey := none }

def setTheme (setting : Theme.Setting) : M Unit := do
  let s ← get
  set (themed s { s.theme with setting })
  saveCheckpoint
  let s ← get
  s.io.appearance (Theme.effective s.theme == .dark) (Palette.color s.dim.theme .bg)

def systemTheme (system : Theme.Value) : M Unit := do
  let s ← get
  let theme := { s.theme with system }
  if Theme.effective theme != Theme.effective s.theme then
    set (themed s theme)
  else modify fun s => { s with theme }
  let s ← get
  s.io.appearance (Theme.effective s.theme == .dark) (Palette.color s.dim.theme .bg)

/-! ## Reading through live answers -/

def read (q : Q) : M Ans := do
  let s ← get
  if !s.life.allows s.life.lease then return default
  modify fun s => { s with touched := s.touched.insert q }
  modify fun s => { s with life := s.life.track s.owner q }
  let (a, live) ← (Live.readWith (fun q => q.run s.rd s.out) q).run s.live
  modify fun s => { s with live }
  return a

def fresh (q : Q) : M Bool := do return (← get).live.fresh q


instance : Reads M := ⟨read⟩

/-! ## The native text field

One native field edits one of the app's strings at a time. The `.text`
event writes the field's text into it (`textInto`), and each frame sets
the field to it (`syncText`), so the field and the app's string never
drift: a page change never empties the composer's draft by way of the
field (TextLaws in this file: `into_target`, `into_native`). -/

/-- Which string the native field edits: a page's one-line field, the
emoji sheet's search, the composer's draft, or none (the sheet open
without its search: the field is left as it is). -/
inductive TextTarget where
  | field | query | draft | none
  deriving BEq, DecidableEq

def textTarget (s : St) : TextTarget :=
  if fieldPage s.page then .field
  else match s.sheet with
    | some sh => if sh.searching then .query else .none
    | none => .draft

/-- What the native field is to hold now, if anything. -/
def nativeText (s : St) : Option String :=
  match textTarget s with
  | .field => some s.field
  | .query => s.sheet.map (·.query)
  | .draft => some s.text
  | .none => none

/-- A `.text` event's text and selection into the string the field edits. -/
def textInto (s : St) (t : String) (sel : Array UInt32) : St :=
  match textTarget s with
  | .field => { s with field := t, refusal := none, pageKey := none }
  | .query => match s.sheet with
    | some sh => { s with sheet := some { sh with query := t, scroll := 0 } }
    | none => s
  | .draft => { s with text := t, sel := if sel.size == 4 then sel else #[0, 0, 0, 0] }
  | .none => s

/-- **A text event edits the string the field edits, and nothing that
chooses it**: the target is the same after. -/
theorem into_target (s : St) (t : String) (sel : Array UInt32) : textTarget (textInto s t sel) = textTarget s := by
  unfold textInto
  cases hf : fieldPage s.page
  · cases hs : s.sheet with
    | none => simp [textTarget, hf, hs]
    | some sh => by_cases hq : sh.searching <;> simp [textTarget, hf, hs, hq]
  · simp [textTarget, hf]

/-- **After a text event the field holds what the app holds** (unless it
edits nothing), so `syncText` sets nothing back: no echo, no lost text. -/
theorem into_native (s : St) (t : String) (sel : Array UInt32) (h : textTarget s ≠ .none) :
    nativeText (textInto s t sel) = some t := by
  unfold nativeText
  rw [into_target]
  unfold textInto
  cases hf : fieldPage s.page
  · cases hs : s.sheet with
    | none => simp [textTarget, hf, hs]
    | some sh => by_cases hq : sh.searching <;> simp_all [textTarget]
  · simp [textTarget, hf]

/-- Set the native field to the string it edits, when they differ. -/
def syncText : M Unit := do
  let s ← get
  if let some t := nativeText s then
    if t != s.native then
      s.io.setText t
      modify fun s => { s with native := t }

/-- Message m's row: its view (Kinds.Message.read: the claimed time, in
UTC minutes), shown at the local time (the platform's timezone). -/
def readRow (m : Id) : M (Option (RowData × Array Q)) := do
  let s ← get
  let tz := (← s.io.wall).2
  return (← Kinds.Message.read s.me.c s.me.adm m).map fun (d, qs) =>
    ({ d with time := (d.time + tz).toNat }, qs)

/-! ## Writing -/

/-- Notices made by this node itself: a change to the outbox, at its ops'
positions under their keys. -/
def noticeLocal (ps : List Pending) : M Unit := do
  let fs := Pending.filings ps
  modify fun s => { s with live := s.live.notice fs }
  (← get).sh.notes.modify (· ++ fs)

/-- Offer writes to the node's inbound channel, in order, without waiting:
each that fits is in; the rest, from the first that did not fit, stay
(the dedicated local-write channel is bounded, so it can be full
while sync is busy). It is `NodeOffer.offerList` over the channel's
`trySend`: NodeOffer.offer_split and offer_runs say no write is lost,
sent twice or overtaken, whatever the channel answers. -/
def offerAll (ch : Std.CloseableChannel.Sync (List Op)) (q : Array (List Op)) : IO (Array (List Op)) := do
  return (← NodeOffer.offerList (fun w => (ch.trySend w : IO Bool)) q.toList).toArray

/-- Re-offer parked writes in submission order, only after teardown. -/
def flushNode : M Unit := do
  let s ← get
  if !s.active || !s.surface || s.netStop.isSome || s.toNode.isEmpty then return
  let some r := s.net | do
    if s.netCfg.isNone && s.netBoot.isNone then
      for ops in s.toNode do s.wr.submit ⟨ops, true⟩
      modify fun s => { s with toNode := #[] }
    return
  let rest ← offerAll r.writes s.toNode
  modify fun s => { s with toNode := rest }

/-- Store-owned writes survive unmount and are journaled before offering. -/
def submit (j : Job) : M Unit := do
  let s ← get
  modify fun s => { s with queuedWrites := s.queuedWrites ++ j.ops.map Op.bytes }
  saveCheckpoint
  if !s.active || !s.surface || s.net.isSome || s.netBoot.isSome || s.netStop.isSome then
    modify fun s => { s with toNode := s.toNode.push j.ops }
    flushNode
  else s.wr.submit j

/-- The negative control of the frame's no-wait rule (`block` and
`waits` in tests/wiring.txt): `submit` to the node as it was, through
`Runner.write`, which waits while the local channel is full. Never
run; the wiring check must catch it. -/
def submitWaits (j : Job) : M Unit := do
  if let some r := (← get).net then r.write j.ops

/-- A user action's write (an intent's ops): each op is
judged in order against what is decided and the ops before it in the
same write. Valid ops show at once, pending. An op whose requirements are
not all here yet (a join's request cites the community's ops, which come
by sync) shows nothing and waits in the store, as the engine waits for
any op. An Invalid op refuses the whole write. Otherwise the ops go in as one job
of this node's own (`submit`). -/
def writeAll (w : Community.Write) : M Bool := do
  let s ← get
  if !s.life.allows s.life.lease then return false
  let mut mine : Std.HashMap Id (Verdict SF) := {}
  let mut pend := #[]
  for o in w.ops do
    let mut sts := []
    for r in o.reqs do
      sts := sts ++ [← match mine[r]? with
        | some v => pure (some v)
        | none => Data.status s.rd r]
    match judge fam o sts with
    | some (.valid (.inl f)) =>
      mine := mine.insert o.id (.valid (.inl f))
      pend := pend.push (⟨o, f, opKey o.id :: keys f⟩ : Pending)
    | some (.valid v) => mine := mine.insert o.id (.valid v)
    | none => pure ()
    | some .invalid =>
      (← get).io.log s!"write refused: an op is Invalid"
      return false
  modify fun s => { s with out := s.out ++ pend }
  s.sh.out.modify (· ++ pend)
  noticeLocal pend.toList
  submit ⟨w.ops, true⟩
  return true

def write (o : Op) : M Bool := writeAll ⟨[o]⟩


/-- Chaos's writes, once made: each job one write, as a user's action is. -/
def chaosStep : M Unit := do
  let some t := (← get).chaos | return
  if !(← IO.hasFinished t) then return
  modify fun s => { s with chaos := none }
  for j in t.get do
    let _ ← writeAll ⟨j.ops⟩
  (← get).wr.busy.modify (· - 1)
  (← get).io.log s!"chaos: {t.get.size} writes of {t.get.foldl (· + ·.ops.length) 0} ops"

/-- n bytes of the OS's randomness (`randomBytes`: getrandom, through
engine/native/crypto): the one door every secret, key and nonce the app
makes goes through. Nothing derives one from the clock. -/
def newBytes (n : UInt32) : IO ByteArray := Engine.Crypto.randomBytes n

/-- A new secret seed: a device's, or an invitation's bearer secret. -/
def newSeed : IO ByteArray := newBytes 32

/-- Wall-clock minutes since the Unix epoch: the time a write claims. -/
def nowMin : M Nat := do return (← (← get).io.wall).1

/-- A user action for the reader: its intent runs in the next pass, in
its transaction and before the marks, and what it touches shows in the
frame that pass serves (ActsLaws.acts_shown). Its id, for `takeDone`. -/
def act (intent : Reader.RM Community.Write) : M Id := do
  if !(← get).life.mounted then return .empty
  let id ← newBytes 16
  (← get).sh.act id intent
  return id

/-- The acts the reader has run: each write submitted, as the frame's
own are (`submit`), in order; what each wrote, for its continuation. -/
def takeDone : M (Array (Id × Option Community.Write)) := do
  let ds ← (← get).sh.done.modifyGet fun a => (a, #[])
  for (_, w?) in ds do
    if let some w := w? then submit ⟨w.ops, true⟩
  return ds

def sendText (text : String) : M Bool := do
  let s ← get
  let t := text.trimAscii.toString
  if t.isEmpty then return false
  -- sealed under the community's current key, as the composer's send is
  let (k?, _) ← readView (Community.currentKey s.me.c) #[]
  let some k := k? | return false
  let (w, _) ← readView (Community.send s.me.c s.me.adm s.me.dev k (← newBytes 24) t.toUTF8
    (← nowMin)) #[]
  writeAll w

/-- `sendText` as an act: the reader reads the key and runs the send
intent in its next pass; none when there is nothing to send. -/
def sendTextAct (text : String) : M (Option Id) := do
  let s ← get
  let t := text.trimAscii.toString
  if t.isEmpty then return none
  let (c, adm, dev) := (s.me.c, s.me.adm, s.me.dev)
  let nonce ← newBytes 24
  let now ← nowMin
  some <$> act do
    let (k?, _) ← readView (Community.currentKey c) #[]
    let some k := k? | throw (IO.userError "this community's key hasn't arrived yet")
    let (w, _) ← readView (Community.send c adm dev k nonce t.toUTF8 now) #[]
    return w

def reactTo (m : Id) (e : String) : M Bool := do
  let s ← get
  write (react s.me.c s.me.adm m s.me.dev e.toUTF8 (← nowMin))

/-! ## Geometry -/

def topH (s : St) : Nat :=
  if s.page == .chat then s.insetTop + s.dim.px 16 + 2 * s.dim.lineH
  else if s.page == .home then s.insetTop + s.dim.px 64
  else s.insetTop + s.dim.px 56

/-- The composer's layout (Composer: the painter and the taps both read it). -/
def composerLayout (s : St) : Composer.Layout :=
  Composer.layout s.font s.dim s.W s.text s.chips.size

def sheetItems (s : St) (sh : SheetSt) : Array Nat := Sheet.shown s.catalog sh.cat sh.query

def catOf (s : St) (sh : SheetSt) : Sheet.Cat :=
  Sheet.cat s.dim s.font s.W s.Hs s.insetTop (sheetItems s sh).size

def botH (s : St) : Nat :=
  if s.page != .chat then 1 else
  match s.sheet with
  | some sh => if sh.catalog then (catOf s sh).h else (Sheet.quick s.dim s.W).h
  | none => (composerLayout s).h

/-- The screen's geometry as of this frame (Geometry: the theorems that
list content is never under the header, composer or keyboard are about
these numbers). -/
def geom (s : St) : Geometry.Geom := ⟨s.Hs, s.insetBot, s.imeH, topH s, botH s⟩

def viewH (s : St) : Nat := (geom s).view

def heightOf (s : St) (x : Id) : Nat := s.heights.getD x est

/-- The window's rows' bottoms (bottom-anchored), newest first, and the
content's height: the messages newer and older than the window at `est`
each, below and above it. -/
def bottoms (s : St) : Array Nat × Nat := Id.run do
  let mut out := Array.mkEmpty s.ids.size
  let mut y := bottomPad + s.newer * est
  for (_, x) in s.ids do
    out := out.push y
    y := y + heightOf s x
  return (out, y + s.older * est + 16)

/-! ## Mounting, measuring, painting -/

/-- An attachment's slices, read from its chunk ops in order (a chunk this
device sends may still be in the outbox); none while one is not here. -/
def slicesOf (p : Row.Pic) : M (Option (List ByteArray)) := do
  -- the chunk ops' bytes, read by the reader (Reader.Want.slices): wanted
  -- from the next frame, none until the board has them all; nothing is
  -- decoded here (a 64 KiB chunk is slow to decode; the frame must not wait)
  let w := Reader.Want.slices p.chunks
  match (← (← get).sh.board.get).get? w with
  | some (.slices raw, _) => return raw
  | _ => return none

/-- All expensive visual work passes through the shared component pool.
The declaration is retained for this frame even when its result is cached. -/
def rasterRequest (owner : Demand.Owner) (key : Raster.Key) (visible : Bool)
    (action : Work.Action Bitmap) : M (Work.Handle Raster.Key Bitmap) := do
  let need : Demand.Need Raster.Key := ⟨owner, key, visible⟩
  modify fun s => { s with rasterNeeds := s.rasterNeeds.push need }
  (← get).raster.request need action

/-- An attachment child owns its chunk request and both image stages.
Its parent supplies identity, metadata and bounds; it does not start its
work. No timer keeps an offscreen picture subscribed. -/
def image (p : Row.Pic) (w h : Nat) (owner : Demand.Owner := [])
    (visible : Bool := true) : M (Option Bitmap × Bool) := do
  let s ← get
  let stage (n : UInt8) (source : Unit → Option Image.Src) : M (Option Bitmap) := do
    let k : ImgKey := (p.hash.push n, w, h)
    let action ← Raster.image source w h s.dim.theme (n == 0)
    let handle ← rasterRequest owner (.image k s.dim.theme) visible action
    modify fun s => { s with imgs := s.imgs.insert k handle }
    handle.value
  let pre ← if p.preview.isEmpty then pure none else stage 0 (fun _ => Image.decode p.preview)
  let mut full := none
  if p.complete then
    let want := Reader.Want.slices p.chunks
    let need : Demand.Need Reader.Want := ⟨owner, want, visible⟩
    modify fun s => { s with pictureNeeds := s.pictureNeeds.push need }
    match (← s.sh.board.get).get? want with
    | some (.slices (some raw), _) => full ← stage 1 (fun _ => Raster.fileSource p raw)
    | _ =>
      -- Kept for diagnostics of a missing dependency, never as a timer
      -- authorizing work. The child's declaration alone owns the query.
      modify fun s => { s with imgWaiting := s.imgWaiting.insert (p.hash.push 1, w, h) }
  return p.shown pre full

/-- In the headless twins, the frame runs the reader's pass itself; on a
device the reader's thread runs them. The outbox is the reader's
(`Reader.Shared.out`): the frame's writes join it as they are made. -/
def readerPass : M Unit := do
  let s ← get
  if !s.life.mounted then return
  if let some r := s.rst then
    let (_, r) ← (Reader.pass s.sh).run r
    modify fun s => { s with rst := some r }

/-- Take the board's moved set in one swap. A mounted attachment checks
its answer every frame; this only clears its waiting diagnostic. -/
def takeBoard : M (_root_.Live.Board Reader.Want Reader.Val) := do
  let (moved, b) ← (← get).sh.board.modifyGet fun b => let (mv, b') := b.take; ((mv, b'), b')
  if moved.toList.any fun | .slices _ => true | _ => false then
    modify fun s => { s with imgWaiting := {} }
  return b

/-- Row x from the board (Reader's row want), laid out again when its
version moved; nothing while the board has none (the frame shows the
row's placeholder, Cover). Its time is shown in the local timezone. -/
def mount (bd : _root_.Live.Board Reader.Want Reader.Val) (x : Id) : M Unit := do
  let s ← get
  if s.page != .chat || !s.life.mounted then return
  let some (.row (some d), ver) := bd.get? (.row s.me.c s.me.adm x) | return
  if (s.rows[x]?.map (·.bver)) == some ver then return
  let tz := (← s.io.wall).2
  let d := { d with time := (d.time + tz).toNat }
  -- Preserve a child's already displayed value when an unrelated parent
  -- query changes. The child still refreshes from its own board entry.
  let d := match s.rows[x]? with
    | none => d
    | some r => { d with pics := d.pics.map fun p =>
        (r.data.pics.find? (fun old => old.attachment == p.attachment && old.hash == p.hash)).getD p }
  match s.rows[x]? with
  | some r =>
    if r.data == d then
      modify fun s => { s with rows := s.rows.insert x { r with bver := ver } }
    else
      let lay := Row.layout s.font s.dim s.W d
      modify fun s => { s with rows := s.rows.insert x { r with data := d, lay, bver := ver, ver := r.ver + 1 },
                                heights := s.heights.insert x lay.h }
  | none =>
    let lay := Row.layout s.font s.dim s.W d
    modify fun s => { s with
      rows := s.rows.insert x { data := d, lay, deps := #[], painted := (0, []), task := none, shown := none,
                                ver := 1, bver := ver },
      heights := s.heights.insert x lay.h }

/-- Start a paint of row x if what it shows changed; collect a finished one. -/
def paintRow (x : Id) (bottom offset viewport : Nat := 0) : M Unit := do
  let s ← get
  if s.page != .chat || !s.life.mounted then return
  let some r := s.rows[x]? | return
  let viewport := if viewport == 0 then viewH s else viewport
  let owner := Raster.messageOwner s.me.c x
  let visible := Raster.near bottom r.lay.h offset viewport 0
  let av : Option Bitmap := none
  let mut imgs := #[]
  let mut ready := [false]
  let mut data := r.data
  for i in [0:r.lay.pics.size] do
    let bx := r.lay.pics[i]!
    let childBottom := bottom + r.lay.h - (bx.y + bx.h)
    match r.data.pics[i]? with
    | some p =>
      if Raster.near childBottom bx.h offset viewport imageOver then
        let owner := Raster.pictureOwner s.me.c x p.attachment
        let visible := Raster.near childBottom bx.h offset viewport 0
        let want := Reader.Want.picture s.me.c p.attachment
        modify fun s => { s with pictureNeeds := s.pictureNeeds.push ⟨owner, want, visible⟩ }
        let p := match (← s.sh.board.get).get? want with
          | some (.picture (some current), _) => current
          | _ => p
        data := { data with pics := data.pics.set i p }
        let (b, isFile) ← image p bx.w bx.h owner visible
        imgs := imgs.push b
        ready := ready ++ [b.isSome, isFile]
      else
        imgs := imgs.push none
        ready := ready ++ [false, false]
    | none => imgs := imgs.push none
  let s ← get
  let mut r := r
  if data != r.data then r := { r with data, ver := r.ver + 1 }
  let selected := s.selected == some x
  if r.data.selected != selected then
    r := { r with data := { r.data with selected }, ver := r.ver + 1 }
  let key := Raster.Key.row s.life.generation x r.ver ready s.dim.theme
  let (f, dm, W, bgRow, d, l) := (s.font, s.dim, s.W, s.bgRow, r.data, r.lay)
  let handle ← rasterRequest owner key visible (fun _ => pure (some (Row.paint f dm W bgRow d l av imgs)))
  let value ← handle.value
  if r.painted != (r.ver, ready) then modify fun s => { s with paints := s.paints + 1 }
  r := { r with
    task := if value.isSome then none else some handle,
    painted := (r.ver, ready), shown := value.orElse fun _ => r.shown }
  if s.selected.isSome && !selected then
    if let some bmp := r.shown then
      let key := Raster.Key.dim s.life.generation x r.ver ready s.dim.theme
      let dimmed ← rasterRequest owner key visible (fun _ => pure (some (Row.Bitmap.dim bmp)))
      r := { r with dimmed := some dimmed, dimVer := r.ver, dimShown := ← dimmed.value }
  else r := { r with dimmed := none, dimShown := none }
  modify fun s => { s with rows := s.rows.insert x r }

/-! ## The frame -/

/-- A placeholder line: the background with a bar where a row's text
would be, in stripes (a row not painted yet, or older rows not loaded). -/
def holdLine (s : St) (li : Nat) : ByteArray :=
  Hold.holdLine ⟨s.bgRow, s.dim, s.W⟩ li

/-- The rows overlapping the list frame, from the first one up: the
first's index, and each one's height and the height of the paint it
shows (Cover.seen's rows), with the paints. -/
def frameSlice (s : St) (b : Nat) (bots : Array Nat) : Nat × Array (Nat × Option Nat) × Array (Option Bitmap) :=
  Id.run do
  let top := b + viewH s + over     -- content above the frame's first row
  let low := if b ≥ over then b - over else 0
  let mut i0 := s.ids.size
  let mut slice : Array (Nat × Option Nat) := #[]
  let mut bmps : Array (Option Bitmap) := #[]
  for i in [0:s.ids.size] do
    let bot := bots[i]!
    let x := s.ids[i]!.2
    let h := heightOf s x
    if bot ≥ top then break
    if bot + h ≤ low then continue
    if i0 == s.ids.size then i0 := i
    let pick := s.rows[x]? >>= fun r =>
      if s.selected.isSome && s.selected != some x then r.dimShown <|> r.shown else r.shown
    slice := slice.push (h, pick.map (·.h))
    bmps := bmps.push pick
  return (i0, slice, bmps)

/-- The list frame: row r shows content at b + viewH + over - 1 - r, as
Cover.seen says: a painted row's line, else a placeholder (Cover.covered:
nothing inside the content is left blank, however slow a read or a
decode is). -/
def listFrame (s : St) (b : Nat) (bots : Array Nat) : Array ByteArray := Id.run do
  let vh := viewH s
  let hgt := vh + 2 * over
  let top := b + vh + over     -- content above the frame's first row
  let (i0, slice, bmps) := frameSlice s b bots
  let bottom := if i0 < s.ids.size then bots[i0]! else
    match s.ids.back? with
    | some (_, x) => bots.back! + heightOf s x
    | none => bottomPad + s.newer * est
  -- messages outside the window: nothing past the loaded rows is blank
  let more := s.older > 0
  let pad := if s.newer > 0 then bottomPad else bottom
  let rows := slice.toList
  let mut fr := Array.mkEmpty hgt
  for r in [0:hgt] do
    let p := top - 1 - r
    fr := fr.push (match Cover.seen pad bottom more rows p with
      | .line j li => ((bmps[j]?).join.map (·.rows[li]!)).getD s.bgRow
      | .hold j => holdLine s (heightOf s (s.ids[i0 + j]?.map (·.2) |>.getD .empty) - 1 - (p - (bots[i0 + j]?.getD 0)))
      | .unloaded => holdLine s (p % est)
      | .blank => s.bgRow)
  return fr

def header (s : St) : Bitmap := Id.run do
  let h := topH s
  let hb := Palette.color s.dim.theme .panel
  let x := s.dim.pad
  let mut b := Bitmap.blank s.W h (solid hb s.W)
  let y := s.insetTop + s.dim.px 8
  -- back to the community's home on the left; the channel and the
  -- community's name, which opens the switcher
  let iy := y + (2 * s.dim.lineH - s.font.cell) / 2
  b := b.line s.font (Text.oneLine s.font s.font.cell "←") x iy (Palette.color s.dim.theme .fg)
  let tx := x + s.dim.px 40
  b := b.line s.font (Text.oneLine s.font (s.W - tx - x) s!"# general · {s.me.name} ▾") tx y (Palette.color s.dim.theme .fg) true
  let sub := s!"{s.total} messages · {s.people}{if s.peopleAll then "" else "+"} people"
  b := b.line s.font (Text.oneLine s.font (s.W - tx - x) sub) tx (y + s.dim.lineH) (Palette.color s.dim.theme .muted)
  b := b.fill 0 (h - max 2 (s.dim.px 1)) s.W h (Palette.color s.dim.theme .line)
  return b

/-- Where the header's controls are, in its own rows. -/
def headerHit (s : St) (x _y : Nat) : PageId :=
  if x < s.dim.pad + s.dim.px 40 then .home else .switcher

def cursorAt (s : St) (i : Nat) : Nat × Nat :=
  let pre := String.ofList (s.text.toList.take i)
  let ls := if pre.isEmpty then #[#[]] else Text.layout s.font (composerLayout s).textW pre
  let last := ls.back?.getD #[]
  -- a prefix ending in a newline puts the cursor on the next line
  if pre.endsWith "\n" then (ls.size, 0) else (ls.size - 1, Paint.Line.width s.font last)

def composer (s : St) : Bitmap :=
  Composer.paint s.font s.dim s.W s.bgRow (composerLayout s) s.text s!"Message {s.me.name}"
    (s.chips.map (·.2.2.2)) (some (cursorAt s s.sel[0]!.toNat))

/-! ## Events and commands -/

/-- The row at content position p, and p's row within it (top down). -/
def rowAt (s : St) (p : Nat) : Option (Id × Nat) := Id.run do
  let (bots, _) := bottoms s
  for i in [0:s.ids.size] do
    let bot := bots[i]!
    let x := s.ids[i]!.2
    let h := heightOf s x
    if bot ≤ p && p < bot + h then return some (x, bot + h - 1 - p)
  return none

/-! ## Pages and communities -/

def hexShort (b : ByteArray) : String :=
  String.join (b.toList.take 4 |>.map fun x =>
    let t := String.ofList (Nat.toDigits 16 x.toNat); if t.length < 2 then "0" ++ t else t)

/-- A toast, for about 3 s (libquiet's: an outcome stated, then gone). -/
def say (t : String) : M Unit := do
  let now := (← (← get).io.nowUs).toNat / 1000
  modify fun s => { s with toast := Toast.raise now t }

/-- Where this device is dialed: its LAN addresses at the node's port
(Link.hints, Wi-Fi first), or loopback in a one-machine test. -/
def listenHints : M (List ByteArray) := do
  let s ← get
  let (port, loop) := s.netCfg.getD (Link.port, false)
  if loop then return [s!"127.0.0.1:{port}".toUTF8]
  let addrs ← try Link.local? catch _ => pure []
  return Link.hints addrs port

/-! ## Navigation

The page and the back stack change only by Nav's steps (its laws in
engine/renderer/Nav.lean, the app's in ops/app/NavLaws.lean). -/

/-- Open p (Nav.go); the page's refusal is cleared. -/
def openSt (p : PageId) (s : St) : St := { s.withNav (Nav.go p s.nav) with refusal := none, pageKey := none }

/-- Back (Nav.back); the page's one-line field and refusal are cleared
(the native field's text with them), never the composer's draft. -/
def backSt (s : St) : St := { s.withNav (Nav.back s.nav) with field := "", refusal := none, pageKey := none }

/-- Open a page (the current one goes on the back stack). -/
def openPage (p : PageId) : M Unit := do
  let s ← get
  if s.page == p then return
  -- Add members issues this community's link once per session: an
  -- invitation op of mine, and the link that carries its bearer secret
  if p == .invite && !s.me.waiting && !(s.links.any (·.1 == s.me.acc)) then
    let bearer ← newSeed
    -- dial hints: this device's private LAN addresses (Link.hints)
    -- the link names this node's key (Community.inviteTo reads it)
    let (issued, _) ← readView (Community.inviteTo s.me.c s.me.adm s.me.dev bearer (← listenHints)) #[]
    if let some (w, i) := issued then
      if ← writeAll w then
        modify fun s => { s with links := (s.me.acc, i.text) :: s.links }
  leavePage
  s.io.scrollTo 0
  modify (openSt p)
  modify fun s => { s with restoreAnchor := p == .chat && s.mark.isSome }
  mountPage

/-- Back: the page before; at a root, it stays (Nav.back_root). -/
def back : M Unit := do
  leavePage
  let s ← get
  s.io.ime false
  s.io.scrollTo 0
  modify backSt

  modify fun s => { s with restoreAnchor := s.page == .chat && s.mark.isSome }
  mountPage

/-- What the app holds for an entry no longer listed, forgotten: its
invite link, a pasted link to its community, an open profile, and, if it
was current, the composer's text and photos. -/
def forgetEntry (s : St) (a c : Id) : St :=
  let cur := s.me.acc == a
  { s with links := s.links.filter (·.1 != a),
           invite := if (s.invite.map (·.community == c)).getD false then none else s.invite,
           profileOf := if cur then none else s.profileOf,
           text := if cur then "" else s.text, chips := if cur then #[] else s.chips }

/-- The communities, as read by the Community kind: those listed (a
removed entry hidden), the current one kept or, gone, the first (Get
started when none is left). -/
def applyComms (all : Array Chaos.Me) : M Unit := do
  let cs := Kinds.Accepted.listed all
  -- removed since last told: a standing notice each, and forgotten
  for g in Kinds.Accepted.newlyGone (← get).goneSeen all do
    modify fun s => { forgetEntry s g.acc g.c with
      goneSeen := g.acc :: s.goneSeen,
      notices := s.notices ++ [s!"You’ve been removed from {if g.name.isEmpty then "a community" else g.name}."] }
  modify fun s =>
    match Kinds.Accepted.landing cs s.cur with
    | some me => { s with comms := cs, me, cur := me.acc }
    | none =>
      -- nothing listed: Get started (unless a join is being made)
      { s.withNav (if s.comms.isEmpty then s.nav else Nav.reset .getStarted) with
          comms := cs, me := default, cur := .empty }

/-- The state a switch to acceptance `a` leaves: its home as a root (back
stays there: Nav.back_reset), and its conversation's window empty. -/
def switchSt (a : Id) (s : St) : St :=
  let s := { s.withNav (Nav.reset .home) with cur := a, me := (Kinds.Accepted.select s.comms a).getD s.me }
  let s := { s with ids := #[], total := 0, people := 0, peopleAll := true, anchor := none, newer := 0, older := 0 }
  let s := { s with heights := {}, rows := {}, selected := none, sheet := none }
  { s with asking := #[], hidden := [], chromeKey := "", pageKey := none }

/-- The communities as the reader's board has them (Reader.Want.comms):
each frame. -/
def refreshComms : M Unit := do
  if let some (.comms all, _) := (← (← get).sh.board.get).get? .comms then applyComms all

/-- The communities read now, on the frame: after an action that founds,
joins or stops waiting, which the next page shows at once. -/
def refreshCommsNow : M Unit := do
  let (all, _) ← Kinds.Accepted.read (← get).comms
  applyComms all

/-- Make the entry of acceptance `a` the current one (memory only): the
list starts again from its newest. An entry is its acceptance, never its
community id or name (Switch.select_tapped). -/
def switchToAcc (a : Id) : M Unit := do
  leavePage
  (← get).io.scrollTo 0
  modify (switchSt a)
  modify fun s => { useDraft s with mark := none, restoreAnchor := false }
  mountPage

def switchTo (i : Nat) : M Unit := do
  if let some m := (← get).comms[i]? then switchToAcc m.acc

/-- A link pasted or scanned: Choose a name, then Agree & join; but a link
to a community this device already holds (a member, or its join pending)
goes to that community instead, and joins nothing (libquiet's rule: a
node holds a community at most once). -/
def takeInvite (i : Community.Invite) : M Unit := do
  let s ← get
  if let some m := s.comms.find? (·.c == i.community) then
    s.io.ime false
    modify fun s => { s with invite := none, field := "", refusal := none }
    switchToAcc m.acc
    say (if m.waiting then "You're already waiting to join this community." else "You're already in this community.")
    return
  modify fun s => { s with invite := some i, field := "", refusal := none }
  openPage .name
  s.io.ime true

/-- The acceptance a write makes (found's, join's): its accept op. -/
def acceptOf (w : Community.Write) : Option Id :=
  (w.ops.find? fun o => match (Codec.decode o.body : Option Community.Body) with
    | some (.accept ..) => true
    | _ => false).map (·.id)

/-- Found a community named n: its root and my profile, and it becomes
current. -/
def found (n myName : String) : M Unit := do
  let seed ← newSeed
  -- the last fresh bytes are this node's key, if it has none yet
  let (w, _) ← readView (Community.found seed n.toUTF8 myName.toUTF8 (← nowMin)
    (← newBytes 32) (← newBytes 32) (← newBytes 32)) #[]
  if ← writeAll w then
    if let some a := acceptOf w then
      refreshCommsNow
      switchToAcc a

/-- The node: started at launch, once (it speaks for every device whose
secret this store holds: Connection.hooks reads them all, and picks the
device for each community from its acceptance). Its first frame waits
for the local writer to be idle, so it boots from everything written. -/
def netStep : M Unit := do
  let s ← get
  if !s.active || !s.surface || s.netStop.isSome then return
  let some (port, _) := s.netCfg | return
  if s.net.isSome then return
  -- started: taken once it is up (the frame never waits on it)
  if let some t := s.netBoot then
    if !(← IO.hasFinished t) then return
    modify fun s => { s with netBoot := none }
    match t.get with
    | .ok r =>
      s.io.log s!"node: listening on {r.port}"
      modify fun s => { s with net := some r }
      flushNode
    | .error e =>
      s.io.log s!"node: cannot start: {e}"
      modify fun s => { s with netCfg := none }
      let pending := (← get).toNode
      modify fun s => { s with toNode := #[] }
      if !pending.isEmpty then for ops in pending do s.wr.submit ⟨ops, true⟩
    return
  if (← s.wr.busy.get) > 0 then return
  let listen := ((← listenHints).head?).getD s!"127.0.0.1:{port}".toUTF8
  let x : Engine.Sync.Sync SF (SqlM SF) :=
    { fam, cfg := { every := 30000, askTime := 20000 },
      hooks := Connection.hooks fam Connection.sodium listen }
  let path := s.dbPath
  let sh := s.sh
  let t ← IO.asTask (prio := .dedicated) do
    let db ← Db.openAt path
    -- the node's commits move the reader's counter (Reader.Shared.commits)
    Engine.Sync.Runner.start x db 0 port.toUInt16 (notify := fun _ => sh.commits.modify (· + 1))
  s.io.log s!"node: starting, dialed as {(String.fromUTF8? listen).getD "?"}"
  modify fun s => { s with netBoot := some t }

/-- The rows every commit since the last call filed or unfiled (the
writer's and the node's alike), and the verdicts it recorded or cleared,
from the store's journal: read inside the frame's read transaction, they
are exactly the commits this frame's reads see. -/
def takeChanges : M (Array Filing × Array (Id × Bool)) := do
  let s ← get
  let (fs, vs, top) ← s.rd.filingsSince s.seen
  modify fun s => { s with seen := top }
  -- taken by the frame and the reader: the writer may delete them
  s.wr.read.set (min top (← s.sh.seen.get))
  return (fs, vs)

/-- Join with QR code: the camera on while the page shows; each new
frame drawn in the page's square (Camera.preview: it reads only inside the
frame, src_in) and, one at a time, decoded off the app's thread; a code
that is an invite is taken as a pasted link is. -/
def scanStep : M Unit := do
  let s ← get
  let on := s.page == .scan
  if on != s.camOn then
    s.io.scan on
    modify fun s => { s with camOn := on, camView := none, decoding := none }
  if !on then return
  let (hdr, px) ← s.io.luma
  if hdr.size == 4 && px.size > 0 then
    let fr : Camera.Frame := ⟨hdr[0]!.toNat, hdr[1]!.toNat, hdr[2]!.toNat, hdr[3]!.toNat, px⟩
    let side := (Pages.scanBox s.dim s.W (viewH s)).w
    modify fun s => { s with camView := some (Camera.preview fr side), camFrame := s.camFrame + 1 }
    if s.decoding.isNone then
      let t := Task.spawn fun _ =>
        (Qr.decodeLuma hdr[0]! hdr[1]! hdr[2]! px).bind fun (b, _) => String.fromUTF8? b
      modify fun s => { s with decoding := some t, scans := s.scans + 1 }
  match (← get).decoding with
  | some t =>
    if ← IO.hasFinished t then
      modify fun s => { s with decoding := none }
      if let some text := t.get then
        match Community.Invite.parse text with
        | some i => takeInvite i
        | none => say "That code isn't a Quiet invite."
  | none => pure ()

/-- Home owns a count subscription, not the hidden conversation's rows. -/
def refreshHomeCount : M Unit := do
  let s ← get
  if s.page != .home || s.me.c.isEmpty then return
  let (a, _) ← readView (Community.readable s.me.c (limit := some 0)) #[]
  modify fun s => { s with total := a.inRange }

/-- The people of the current community, for home's Direct messages:
its members (the Profile kind's), me first. -/
def refreshMembers : M Unit := do
  let s ← get
  if s.me.c.isEmpty || (s.page != .home && s.page != .profile && s.page != .removeConfirm) then return
  -- read by the reader (Reader.Want.members): nothing until it is
  let some (.members ms admin, _) := (← s.sh.board.get).get? (.members s.me.c s.me.user) | return
  let out := ms.map fun (u, _, name) => ((name, u == s.me.user), u)
  let sorted := out.filter (·.1.2) ++ out.filter (!·.1.2)
  modify fun s => { s with members := sorted.map (·.1), people := ms.size, peopleAll := true,
                           memberIds := sorted.map (·.2), amAdmin := admin }
  -- a removal being sent is done once its target is no longer present
  if let .sending u := (← get).removal then
    if !(← get).memberIds.contains u then
      let name := ((← get).profileOf.map (·.2.1)).getD "They"
      modify fun s => { s.withNav (Nav.reset .home) with
          removal := (Remove.step s.removal .done).1, profileOf := none }
      say s!"Removed {name} from the community."

/-- The requests to join the current community, read by the Request kind. -/
def refreshAsking : M Unit := do
  let s ← get
  if s.me.c.isEmpty then return
  if let some (.asking out, _) := (← s.sh.board.get).get? (.asking s.me.c) then
    modify fun s => { s with asking := out }

/-- My approval of request r (my device in this community signs it). -/
def approveReq (r : Id) : M Unit := do
  -- a fresh ephemeral secret for the wrap of the community's key to the
  -- requester's device
  let esk ← newBytes 32
  let s ← get
  -- the intent reads the request and its approvals: with mine, is the
  -- tally complete? then the admission goes in the same write
  let w ← ((Community.approveReq s.me.c r s.me.adm s.me.dev esk).liftL.run : SqlM SF _).run s.rd
  let _ ← writeAll w

/-- The current page's picture and taps (kept until what it shows changes). -/
def pageTitle : PageId → String × Bool
  | .you => ("You", false)
  | .appearance => ("Appearance", false)
  | .getStarted => ("", false) | .create => ("", false) | .joinChoice => ("", false)
  | .openInvite => ("", false) | .paste => ("", false) | .scan => ("Join with QR code", true)
  | .name => ("", false) | .createName => ("", false)
  | .agree => ("Agree & join", false) | .waiting => ("", false) | .requests => ("Waiting to join", true)
  | .invite => ("Add members", true) | .switcher => ("Communities", true) | .chat => ("", false)
  | .profile => ("", true) | .removeConfirm => ("", true) | .duplicate => ("Warning!", true)
  | .home => ("", false) | .label => ("Full label", true)

/-- A page and its bar, from its key alone (and the font, background and
camera frame): nothing else of the app's state can reach the pixels, so a
cached page whose key matches is the page (`drawPage_key`). -/
def drawPage (f : Font) (bg : ByteArray) (cam : Option Bitmap) (k : PageIn) : Pages.Page × Bitmap :=
  let dm := k.dim
  let W := k.W
  let h := k.h
  let me := k.me
  let pg : Pages.Page := match k.page with
    | .getStarted => Pages.getStarted f dm W h
    | .create => Pages.create f dm W h k.field true
    | .joinChoice => Pages.joinChoice f dm W h none
    | .openInvite => Pages.openInvite f dm W h
    | .paste => Pages.paste f dm W h k.field true k.refusal
    | .name => Pages.chooseName f dm W h k.field
    | .createName => Pages.chooseName f dm W h k.field
    | .scan => Pages.scan f dm W h cam "Starting the camera…"
    | .agree => Pages.agree f dm W h "this community"
    | .waiting => Pages.waiting f dm W h (Kinds.Request.hexShort me.c)
        -- the request is stored and waits for the community's ops; until the
        -- network says more, the first beat is where it is
        #[(if me.dialing.isEmpty then "Looking for someone to hand your join to" else s!"Sending your request to {me.dialing}",
            "Quiet sends it again until a member's device answers.", .now),
          ("Waiting for a member to let you in", "Quiet asks again whenever it finds one. They see you waiting the next time they open the app.", .next),
          ("Keys and history arrive", "Then the community opens, with what was shared before you got here.", .next)] #[]
    | .requests => Pages.requests f dm W h k.asking
    | .invite => Pages.invite f dm W h (k.link.bind fun l => Link.qr l (Pages.qrSide dm W h)) (k.link.getD "…")
    | .switcher => Pages.switcher f dm W h (k.comms.map fun m =>
        ({ name := m.name, id8 := Kinds.Request.hexShort m.c, unread := 0, current := m.acc == me.acc, waiting := m.waiting } : Pages.Entry))
        k.askingAll (!me.waiting && !me.c.isEmpty)
    | .home => Pages.home f dm W h (if me.waiting then 0 else k.askingAll) #["general"] k.members
    | .label => Pages.label f dm W h k.labelText k.labelPage
    | .profile => let (n, isMe, removed, can) := k.profile; Pages.profile f dm W h n isMe removed can
    | .removeConfirm => Pages.removeConfirm f dm W h k.profile.1 k.removeStage k.removeWhy
    | .duplicate => Pages.duplicate f dm W h
    | .you => Appearance.you f dm W h
    | .appearance => Appearance.page f dm W h k.setting
    | .chat => ⟨Bitmap.blank W h bg, #[]⟩
  let (t, cross) := pageTitle k.page
  -- a first launch's Get started has nowhere to go back to
  let top := if k.page == .home then
      Pages.homeBand f dm W k.insetTop me.name (Kinds.Request.hexShort me.c) ((k.members.find? (·.2)).map (·.1) |>.getD "Me")
    else if (k.page == .getStarted && k.backEmpty && k.comms.isEmpty) || k.page == .waiting
    then Bitmap.blank W (k.insetTop + dm.px 56) bg
    else Pages.bar f dm W k.insetTop t cross
  (pg, top)

/-- **A page is its key.** Two app states whose keys match draw the same
page and bar (with the same font, background and camera frame): what the
cache relies on to keep a page drawn earlier. -/
theorem drawPage_key (f : Font) (bg : ByteArray) (cam : Option Bitmap) {k k' : PageIn} (h : k = k') :
    drawPage f bg cam k = drawPage f bg cam k' := by rw [h]

/-- **The current entry is in the key.** Two states on different entries
(acceptances) have different keys, whatever their names: a switch always
redraws. -/
theorem pageIn_acc {k k' : PageIn} (h : k = k') : k.me.acc = k'.me.acc := by rw [h]

/-- The current state's page key. -/
def pageIn (s : St) : PageIn :=
  { page := s.page, setting := s.theme.setting, W := s.W, h := viewH s, insetTop := s.insetTop, dim := s.dim, field := s.field,
    refusal := s.refusal, me := s.me.key, comms := s.comms.map (·.key),
    asking := (s.asking.filter fun r => !s.hidden.contains r.id).map (·.row), askingAll := s.asking.size,
    link := (s.links.find? (·.1 == s.me.acc)).map (·.2), members := s.members,
    backEmpty := s.backStack.isEmpty, camFrame := s.camFrame, labelText := s.labelText, labelPage := s.labelPage,
    profile := match s.profileOf with
      | some (u, n, isMe) =>
        let present := s.memberIds.contains u
        (n, isMe, !present, Remove.offered s.amAdmin present s.me.user u)
      | none => ("", false, false, false),
    removeStage := match s.removal with
      | .first _ => 1 | .second _ => 2 | .sending _ => 3 | .failed _ _ => 4 | .idle => 0,
    removeWhy := match s.removal with | .failed _ why => why | _ => "" }

/-- Write the removal of user u (the engine's intent). -/
def removeWrite (u : Id) : M Bool := do
  let s ← get
  -- nothing when this device is no admin, u is its own user, already
  -- removed, or not admitted (removeMember_valid: what it writes is a
  -- Valid removal of u by an admin)
  let (w, _) ← readView (Community.removeMember s.me.c u s.me.dev) #[]
  if w.ops.isEmpty then return false
  writeAll w

/-- One step of the removal flow; a write happens only where Remove.step
says (the second yes, or a retry). -/
def removeEv (e : Remove.Ev) : M Unit := do
  let (s', w) := Remove.step (← get).removal e
  modify fun s => { s with removal := s' }
  if let some u := w then
    if !(← removeWrite u) then
      modify fun s => { s with removal := (Remove.step s.removal (.refused "The removal couldn't be written. Try again.")).1 }
  if (← get).removal == .idle then
    -- cancelled: back where it was opened
    if (← get).page == .removeConfirm then back

/-- A page's tap: what it does. -/
def onPageAct (a : Pages.Act) : M Unit := do
  let s ← get
  match a with
  | .back => back
  | .you => openPage .you
  | .appearance => openPage .appearance
  | .theme setting => setTheme setting
  | .copyLabel => s.io.copy (Label.copied s.labelText); say "Label copied."
  | .labelNext =>
    let n := (Label.lines s.font s.dim s.W s.labelText).size
    let last := (n - 1) / Label.capacity s.dim (viewH s)
    modify fun s => { s with labelPage := min last (s.labelPage + 1) }
  | .labelPrev => modify fun s => { s with labelPage := s.labelPage - 1 }
  | .joinCommunity => openPage .joinChoice
  | .createCommunity =>
    modify fun s => { s with field := "" }
    openPage .create
    s.io.ime true
  | .inviteLink => openPage .openInvite
  | .qrCode => openPage .scan
  | .pasteLink =>
    modify fun s => { s with field := "" }
    openPage .paste
    s.io.ime true
  | .field => s.io.ime true
  | .continue_ =>
    match s.page with
    | .create =>
      let n := s.field.trimAscii.toString
      if !n.isEmpty then
        modify fun s => { s with field := "", newCommunity := n }
        openPage .createName
        s.io.ime true
    | .createName =>
      let me := s.field.trimAscii.toString
      if !me.isEmpty then
        s.io.ime false
        modify fun s => { s with field := "" }
        found s.newCommunity me
    | .paste =>
      match Community.Invite.parse s.field with
      | some i => takeInvite i
      | none =>
        modify fun s => { s with refusal := some "That isn't a Quiet invite link. Check that you copied all of it.", pageKey := none }
    | .name =>
      let n := s.field.trimAscii.toString
      if !n.isEmpty then
        s.io.ime false
        modify fun s => { s with joinName := n }
        openPage .agree
    | _ => pure ()
  | .agree =>
    -- join: a device of its own for this community, the request the link
    -- asks for, and this device's accept and joining facts, as one write
    if let some i := s.invite then
      let seed ← newSeed
      -- the engine's join: nothing for a held community, the same request
      -- again for a stopped one, else a fresh join
      let (w, _) ← readView (Community.join i seed s.joinName.toUTF8 (← newBytes 32)) #[]
      if ← writeAll w then
        modify fun s => { s.withNav (Nav.reset s.page) with invite := none, field := "" }
        refreshCommsNow
        match acceptOf w, (← get).comms.find? (·.c == i.community) with
        | some a, _ => switchToAcc a
        | none, some m => switchToAcc m.acc
        | none, none => pure ()
  | .addMembers => openPage .invite
  | .share | .copy =>
    if let some (_, l) := s.links.find? (·.1 == s.me.acc) then
      s.io.copy l
      say "Invitation copied."
  | .stopWaiting =>
    -- a local op superseding my joining fact: the request stays with the
    -- members, and an approval would still let this device in
    if !s.me.joiningOp.isEmpty then
      if ← writeAll (Community.stopWaiting s.me.joiningOp) then
        refreshCommsNow
        if (← get).comms.isEmpty then
          modify fun s => { s.withNav (Nav.reset .getStarted) with pageKey := none }
        else switchTo 0
  | .approve i =>
    let shown := s.asking.filter fun r => !s.hidden.contains r.id
    if let some r := shown[i]? then
      approveReq r.id
      say s!"Approved <{Kinds.Request.hexShort r.device}>"
  | .hide i =>
    let shown := s.asking.filter fun r => !s.hidden.contains r.id
    if let some r := shown[i]? then modify fun s => { s with hidden := r.id :: s.hidden, pageKey := none }
  | .switchTo i => switchTo i
  | .addCommunity => openPage .getStarted
  | .requests => openPage .requests
  | .person i =>
    if let some u := s.memberIds[i]? then
      let (n, isMe) := s.members[i]!
      modify fun s => { s with profileOf := some (u, n, isMe) }
      openPage .profile
  | .removeStart =>
    if let some (u, _, _) := s.profileOf then
      if Remove.offered s.amAdmin (s.memberIds.contains u) s.me.user u then
        removeEv (.start u)
        openPage .removeConfirm
  | .removeYes => removeEv .yes
  | .removeCancel => removeEv .cancel
  | .openChannel _ =>
    s.io.scrollTo 0
    modify fun s => { openSt .chat s with chromeKey := "" }
  | .none => pure ()

def closeSheet : M Unit := do
  let s ← get
  if (s.sheet.map (·.searching)).getD false then
    s.io.ime false
  modify fun s => { s with sheet := none, selected := none }

/-- Send what the composer holds: its text and photos, as the engine's
send intent (the post sealed under the community's current key, then
each photo's attachment and chunks), one write. -/
def sendNow : M Unit := do
  let s ← get
  let t := s.text.trimAscii.toString
  if t.isEmpty && s.chips.isEmpty then return
  let (k?, _) ← readView (Community.currentKey s.me.c) #[]
  let some k := k? | say "This community's key hasn't arrived yet."; return
  let mut files := []
  for (bytes, w, h, _) in s.chips.toList do
    files := files ++ [({ info := { name := "photo.qoi".toUTF8, kind := "image/qoi".toUTF8, w, h,
                                    preview := Chaos.preview bytes },
                          bytes, key := ← newBytes 32, nonce := ← newBytes 24,
                          metaNonce := ← newBytes 24 } : Community.NewFile)]
  let nonce ← newBytes 24
  let (w, _) ← readView (Community.send s.me.c s.me.adm s.me.dev k nonce t.toUTF8 (← nowMin) files) #[]
  if ← writeAll w then
    modify fun s => { s with text := "", sel := #[0, 0, 0, 0], chips := #[], chromeKey := "" }

/-- A photo prepared for sending: at most 2048 px a side, as QOI, with its
chip (a 64 dp square crop) and how much smaller than its raw pixels it is. -/
def preparePhoto (dm : Dim) (src : Image.Src) : ByteArray × Nat × Nat × Composer.Chip :=
  let (w, h) := if src.w ≤ 2048 && src.h ≤ 2048 then (src.w, src.h) else Image.fit src 2048 2048
  let px := Chaos.cropPx src 0 0 src.w src.h w h
  let bytes := Image.encode w h px
  let raw := w * h * 4
  let pct := 100 - bytes.size * 100 / max raw 1
  let thumb := Image.square src (dm.px 64) (Palette.color dm.theme .bg)
  (bytes, w, h, ⟨thumb, s!"{Arrival.humanBytes bytes.size} · {pct}% smaller"⟩)

/-- Add photos: until the system picker lands in the twin, the bundled
test photos, one per tap. -/
def attachPhoto : M Unit := do
  let s ← get
  if s.chips.size ≥ Composer.maxChips then say "At most 4 photos in one message."; return
  let i := s.photoNext % 6
  match ← (IO.FS.readBinFile s!"assets/{i}.qoi").toBaseIO with
  | .ok b =>
    match Image.decode b with
    | some src => modify fun s => { s with chips := s.chips.push (preparePhoto s.dim src), photoNext := s.photoNext + 1, chromeKey := "" }
    | none => say "That photo could not be read."
  | .error _ => say "No photos here."

def mineOn (s : St) (m : Id) : List String :=
  ((s.rows[m]?.map (·.data.tallies)).getD []).filter (·.mine) |>.map (·.emoji)

/-- A tap on the sheet: the key under the finger (SheetGeom.hit_iff: the
one drawn there). -/
def onSheetTap (sh : SheetSt) (x y : Nat) : M Unit := do
  let s ← get
  let some m := s.selected | closeSheet
  if !sh.catalog then
    match Sheet.hitQuick s.dim s.W x y with
    | .react e =>
      if !(mineOn s m).contains e then let _ ← reactTo m e
      closeSheet
    | .browse =>
      let sh' := { sh with catalog := true, scroll := 0 }
      modify fun s => { s with sheet := some sh' }
    | .copy =>
      if let some r := s.rows[m]? then s.io.copy r.data.text
      closeSheet
    | .none => pure ()
  else
    let items := sheetItems s sh
    let c := catOf s sh
    match Sheet.hitCat c sh.scroll x y with
    | .back =>
      if sh.searching then s.io.ime false
      let sh' := { sh with catalog := false, searching := false, query := "" }
      modify fun s => { s with sheet := some sh' }
    | .search =>
      s.io.ime true
      modify fun s => { s with sheet := some { sh with searching := true } }
    | .tone t => modify fun s => { s with sheet := some { sh with tone := t } }
    | .category k =>
      if sh.searching then s.io.ime false
      let sh' := { sh with cat := k, scroll := 0, query := "", searching := false }
      modify fun s => { s with sheet := some sh' }
    | .pick i =>
      if let some it := items[i]? >>= (s.catalog[·]?) then
        let e := it.toned sh.tone
        if !(mineOn s m).contains e then let _ ← reactTo m e
      closeSheet
    | .none => pure ()

/-- A drag on the catalogue's grid scrolls it, and a release flings it. -/
def onSheetDrag (phase x y : Nat) : M Unit := do
  let s ← get
  let some sh := s.sheet | return
  if !sh.catalog then return
  let now := (← s.io.nowUs).toNat / 1000
  let c := catOf s sh
  match phase with
  | 0 =>
    let sh' := { sh with drag := some (y, sh.scroll), lastY := y, lastT := now, vel := 0 }
    modify fun s => { s with sheet := some sh' }
  | _ =>
    match sh.drag with
    | none => pure ()
    | some (y0, s0) =>
      let target := (Int.ofNat s0 + Int.ofNat y0 - Int.ofNat y).toNat
      let dt := max 1 (now - sh.lastT)
      let v := (Float.ofNat sh.lastY - Float.ofNat y) / Float.ofNat dt
      let vel := if phase == 2 then sh.vel else sh.vel * 0.5 + v * 0.5
      let sh' := { sh with scroll := c.grid.clamp target, lastY := y, lastT := now, vel := vel,
                           drag := if phase == 2 then none else sh.drag }
      modify fun s => { s with sheet := some sh' }
  let _ := x

/-- Long-press a compact label to read every line and copy its source. -/
def showLabel (text : String) : M Unit := do
  closeSheet
  modify fun s => { s with labelText := text, labelPage := 0 }
  openPage .label

/-- A long press on a compact label opens it in full: the community's
header (home or the conversation), a page's row naming a community or a
person, or a profile. True when it did. -/
def longLabel (r : Region) (x y : Nat) : M Bool := do
  let s ← get
  let name ← match r with
    | .header => pure (if s.page == .home || s.page == .chat then some s.me.name else none)
    | .list =>
      let vh := viewH s
      if s.page == .chat || y ≥ vh then pure none
      else if s.page == .profile then pure (s.profileOf.map (·.2.1))
      else
        let pg := (s.pageNow).getD (drawPage s.font s.bgRow s.camView (pageIn s)).1
        pure (Pages.fullLabel (pg.hit x (vh - 1 - y)) (s.comms.map (·.name)) (s.members.map (·.1)))
    | .composer => pure none
  let some name := name | return false
  showLabel name
  return true

def onTap (r : Region) (x y : Nat) (long : Bool) : M Unit := do
  let s ← get
  -- A transient toast never intercepts the underlying action.
  modify fun s => { s with toast := none, noticeClock := none }
  -- a tap puts a standing notice away
  if !s.notices.isEmpty then
    modify fun s => { s with notices := s.notices.drop 1 }
    return
  if long then if ← longLabel r x y then return
  -- a page: its bar's back, or its content's taps (rows from its top)
  if s.page != .chat then
    match r with
    | .header =>
      if s.page == .home then openPage .switcher
      else if (Pages.barBack s.dim s.insetTop).has x y then back
    | .list =>
      let vh := viewH s
      if y < vh then
        let pg := (s.pageNow).getD (drawPage s.font s.bgRow s.camView (pageIn s)).1
        onPageAct (pg.hit x (vh - 1 - y))
    | .composer => pure ()
    return
  if let some sh := s.sheet then
    if r == .composer then onSheetTap sh x y; return
    if r == .header then closeSheet; return
  if !Occlusion.active s.sheet.isSome .page then
    closeSheet
    return
  match r with
  | .composer =>
    match Composer.hit (composerLayout s) x y with
    | .text => s.io.ime true
    | .send => sendNow
    | .addPhotos => attachPhoto
    | .takePhoto => say "Taking a photo arrives with the native camera."
    | .emoji | .mention | .voice => say "Not yet."
    | .removeChip i => modify fun s => { s with chips := s.chips.eraseIdxIfInBounds i, chromeKey := "" }
    | .none => pure ()
  | .header =>
    match headerHit s x y with
    | .home => back
    | p => openPage p
  | .list =>
    if s.imeH > 0 && !long then s.io.ime false; return
    -- an open sheet: a tap on the list closes it
    if s.sheet.isSome && !long then
      closeSheet; return
    match rowAt s y with
    | none => pure ()
    | some (m, ry) =>
      match s.rows[m]? with
      | none => pure ()
      | some row =>
        if long then
          -- the long press: the sheet for this message
          if s.imeH > 0 then s.io.ime false
          modify fun s => { s with selected := some m, sheet := some {} }
        else match Row.hit row.lay x ry with
          | .pill e =>
            if !(row.data.tallies.any fun t => t.emoji == e && t.mine) then
              let _ ← reactTo m e
          | .twin => openPage .duplicate
          | _ => pure ()

/-- Shell coordinates are checked against the current safe rectangle,
then translated to the content coordinates used by the existing handlers. -/
def onScreenTap (r : Region) (x y : Nat) (long : Bool) : M Unit := do
  let s ← get
  let g := geom s
  let sy := match r with
    | .header => y
    | .composer => g.composerTop + y
    | .list => if s.page == .chat then (Int.ofNat g.composerTop - 1 - (Int.ofNat y - s.b)).toNat
      else g.composerTop + g.shift - 1 - y
  let i := { s.window with ime := ⟨0, 0, 0, s.imeH⟩ }
  if (Safe.target i ⟨x, sy, 1, 1⟩).isNone then return
  onTap r (x - (Safe.content i).x) y long

def onEvent : Event → M Bool
  | .close => do suspend; return false
  | .background => do
    suspend
    modify fun s => { s with active := false }
    return true
  | .foreground => do modify fun s => { s with active := true }; return true
  | .surface present => do
    if !present then suspend
    modify fun s => { s with surface := present }
    return true
  | .resize => do resize (← (← get).io.screen); return true
  | .deepLink url => do
    modify fun s => { s with pendingLinks := s.pendingLinks ++ [url] }
    return true
  | .tap r x y => do onScreenTap r x.toNat y.toNat false; return true
  | .long r x y => do onScreenTap r x.toNat y.toNat true; return true
  | .text => do
    let (t, sel) ← (← get).io.text
    modify fun s => { textInto s t sel with native := t }
    return true
  | .send => do
    if !Occlusion.active (← get).sheet.isSome .page then return true
    if (← get).page == .create || (← get).page == .createName || (← get).page == .paste || (← get).page == .name then
      onPageAct .continue_
      return true
    sendNow
    return true
  | .ime h => do modify fun s => { s with imeH := h.toNat, chromeKey := "", pageKey := none }; return true
  | .scrolling _ => return true
  | .drag ph x y => do
    if ph == 3 then
      modify fun s => { s with sheet := s.sheet.map fun sh => { sh with drag := none, vel := 0 } }
    else onSheetDrag ph.toNat (x.toNat - (Safe.content (← get).window).x) y.toNat
    return true

def loadSrcs : IO (Array Image.Src) := do
  let mut out := #[]
  for i in [0:6] do
    if let .ok bytes ← (IO.FS.readBinFile s!"assets/{i}.qoi").toBaseIO then
      if let some src := Image.decode bytes then out := out.push src
  return out

def stats (s : St) : String :=
  let ts := s.times
  let n := max ts.size 1
  let avg := ts.foldl (· + ·) 0 / n
  let sorted := ts.qsort (· < ·)
  let p95 := sorted[sorted.size * 95 / 100]?.getD 0
  let mx := sorted.back?.getD 0
  s!"frames {s.frames} lean_us avg {avg} p95 {p95} max {mx} paints {s.paints} reads {s.live.reads} rows {s.rows.size} imgs {s.imgs.size}"

/-- One control command; false if it must wait (and the rest behind it). -/
def command (line : String) : M Bool := do
  let s ← get
  let ws := line.splitOn " "
  let rest := String.intercalate " " (ws.drop 1)
  match ws.headD "" with
  | "ping" => s.io.ctlReply "pong"
  | "state" =>
    s.io.ctlReply s!"b {s.b} total {s.total} loaded {s.ids.size} people {s.people} mounted {s.rows.size} ime {s.imeH} text {repr s.text} outbox {s.out.size} busy {← s.wr.busy.get} viewH {viewH s}"
  | "stats" => s.io.ctlReply (stats s)
  | "work" => s.io.ctlReply s!"{repr (← s.raster.stats)} owned_queries {(← s.sh.wants).size} picture_queries {s.pictureNeeds.size}"
  | "input" => s.io.ctlReply s!"page {repr s.page} serial {s.input.serial} retained {s.input.frames.map (·.1)} press {s.input.press.isSome} lastTap {s.input.lastTap} generation {s.life.generation}"
  | "reader" =>
    let ws ← s.sh.wants
    let board ← s.sh.board.get
    let window := match board.get? (.window s.me.c s.anchor half half) with
      | some (.window ids _, _) => s!"ids={ids.size}"
      | _ => "missing"
    s.io.ctlReply s!"threaded {s.threaded} active {s.active} surface {s.surface} reader {s.reader.isSome} stopping {s.readerStop.isSome} rst {s.rst.isSome} wants {ws.size} generation {← s.sh.generation} window {window} anchor {s.anchor.isSome} restore {s.restoreAnchor} netStop {s.netStop.isSome}"

  | "invite" => s.io.ctlReply ((s.invite.map (·.text)).getD "")
  | "scans" => s.io.ctlReply s!"{s.scans} frames decoded, camera {if s.camOn then "on" else "off"}, preview {s.camView.isSome}"
  | "hints" =>
    -- the dial hints an invite issued now would carry (writes nothing)
    let r ← (try (do let as ← Std.Net.interfaceAddresses; pure (Except.ok as)) catch e => pure (Except.error (toString e)))
    match r with
    | .error e => s.io.ctlReply s!"error {e}"
    | .ok as =>
      let hs ← listenHints
      s.io.ctlReply s!"{as.size} interfaces; hints {hs.map fun h => (String.fromUTF8? h).getD "?"}"
  | "chaos" =>
    let n := (ws[1]? >>= String.toNat?).getD 500
    let srcs ← match s.srcs with
      | some t => pure t
      | none => IO.asTask loadSrcs >>= fun t => pure (t.map fun r => match r with | .ok a => a | .error _ => #[])
    modify fun s => { s with srcs := some srcs, seed := s.seed + 1 }
    let me := s.me
    let (k?, _) ← readView (Community.currentKey me.c) #[]
    let k := k?.getD .empty
    let seed := s.seed
    let (top, _) ← readView (Community.topCount me.c) #[]
    let now ← nowMin
    -- made off the app's thread; written by `chaosStep` as user actions
    -- are (writeAll: judged, shown pending, through the node)
    let t ← IO.asTask (prio := .dedicated) (pure (Chaos.make me k srcs.get seed n top now))
    s.wr.busy.modify (· + 1)  -- so `wait` waits for the making too
    modify fun s => { s with chaos := some (t.map fun r => match r with | .ok j => j | .error _ => #[]) }
    s.io.ctlReply s!"chaos {n} started"
  | "wait" =>
    if (← s.wr.busy.get) > 0 && !(← s.wr.paused.get) || !(← s.wr.jobs.get).isEmpty && !(← s.wr.paused.get) then
      return false
    s.io.ctlReply s!"idle total {s.total}"
  | "send" =>
    let ok ← sendText rest
    s.io.ctlReply (if ok then "sent" else "refused")
  | "react" =>
    let i := (ws[1]? >>= String.toNat?).getD 0
    match s.ids[i]? with
    | some (_, m) =>
      let ok ← reactTo m (ws[2]?.getD "👍")
      s.io.ctlReply (if ok then "reacted" else "refused")
    | none => s.io.ctlReply "no such message"
  | "tray" =>
    let i := (ws[1]? >>= String.toNat?).getD 0
    match s.ids[i]? with
    | some (_, m) => modify fun s => { s with selected := some m, sheet := some {} }; s.io.ctlReply "sheet open"
    | none => s.io.ctlReply "no such message"
  | "untray" => closeSheet; s.io.ctlReply "sheet closed"
  | "browse" =>
    match s.sheet with
    | some sh => modify fun s => { s with sheet := some { sh with catalog := true } }; s.io.ctlReply "catalogue"
    | none => s.io.ctlReply "no sheet"
  | "sheet" =>
    -- sheet tap X Y | sheet drag PHASE X Y: as the twin would send them
    match ws[1]?, (ws[2]? >>= String.toNat?), (ws[3]? >>= String.toNat?), (ws[4]? >>= String.toNat?) with
    | some "tap", some x, some y, _ => onTap .composer x y false; s.io.ctlReply "tapped"
    | some "drag", some ph, some x, some y => onSheetDrag ph x y; s.io.ctlReply "dragged"
    | _, _, _, _ => s.io.ctlReply "sheet tap X Y | sheet drag PHASE X Y"
  | "found" =>
    -- found COMMUNITY[|MYNAME]
    let (n, me) := match rest.splitOn "|" with
      | [n, me] => (n, me)
      | _ => (rest, "Me")
    found n me
    s.io.ctlReply s!"founded {n}"
  | "switch" =>
    match ws[1]? >>= String.toNat? with
    | some i => switchTo i
    | none =>
      -- by name, for scripts: refused when two entries share it
      match (← get).comms.filter (·.name == rest) with
      | #[m] => switchToAcc m.acc
      | ms => s.io.ctlReply s!"switch: {ms.size} communities named {rest}; use an index"
    s.io.ctlReply s!"current {(← get).me.name}"
  | "theme" =>
    match rest with
    | "system" | "light" | "dark" => setTheme (Theme.decode rest)
    | _ => pure ()
    let t := (← get).theme
    s.io.ctlReply s!"theme {Theme.encode t.setting} effective {repr (Theme.effective t)}"
  | "open" =>
    let p : Option PageId := match ws[1]? with
      | some "you" => some .you | some "appearance" => some .appearance
      | some "getStarted" => some .getStarted | some "create" => some .create | some "join" => some .joinChoice
      | some "openInvite" => some .openInvite | some "paste" => some .paste | some "scan" => some .scan
      | some "agree" => some .agree | some "waiting" => some .waiting | some "requests" => some .requests
      | some "invite" => some .invite | some "switcher" => some .switcher | some "chat" => some .chat
      | _ => none
    match p with
    | some .chat => back; s.io.ctlReply "chat"
    | some p => openPage p; s.io.ctlReply s!"page {repr p}"
    | none => s.io.ctlReply "open getStarted|create|join|openInvite|paste|scan|agree|waiting|requests|invite|switcher|chat"
  | "back" => back; s.io.ctlReply s!"page {repr (← get).page}"
  | "channel" => onPageAct (.openChannel 0); s.io.ctlReply s!"page {repr (← get).page}"
  | "page" =>
    -- page X ROW: a tap at row ROW of the page's content, as a finger would land
    let x := (ws[1]? >>= String.toNat?).getD 0
    let row := (ws[2]? >>= String.toNat?).getD 0
    let vh := viewH (← get)
    onTap .list x (vh - 1 - row) false
    s.io.ctlReply s!"page {repr (← get).page}"
  | "comms" =>
    let st ← get
    s.io.ctlReply (String.intercalate " | " (st.comms.toList.map fun m => s!"{m.name}{if m.c == st.me.c then "*" else ""}"))
  | "asking" => s.io.ctlReply s!"asking {(← get).asking.size}"
  | "pause" => s.wr.paused.set true; s.io.ctlReply "writer paused"
  | "resume" => s.wr.paused.set false; s.io.ctlReply "writer resumed"
  | "bottom" => s.io.scrollTo 0; s.io.ctlReply "ok"
  | "scroll" =>
    s.io.scrollTo ((ws[1]? >>= String.toNat?).getD 0).toFloat; s.io.ctlReply "ok"
  | "top" =>
    let (_, ch) := bottoms s
    s.io.scrollTo ch.toFloat; s.io.ctlReply "ok"
  -- For driving a demo on phones over ctl, as a person would: the link
  -- Add members shows, a page's field typed (on a page whose keyboard is
  -- open, the keyboard's own text replaces it: type there instead), a
  -- button the page shows, Add photos, and the composer sent with its
  -- text and photos.
  | "link" =>
    s.io.ctlReply (((s.links.find? (·.1 == s.me.acc)).map (·.2)).getD "")
  | "field" =>
    modify fun s => { s with field := rest, refusal := none, pageKey := none }
    s.io.ctlReply s!"field {rest.length}"
  | "act" =>
    let a : Option Pages.Act := match ws[1]?, (ws[2]? >>= String.toNat?) with
      | some "continue", _ => some .continue_
      | some "agree", _ => some .agree
      | some "approve", some i => some (.approve i)
      | _, _ => none
    -- only a button the page shows, as a tap could press only that
    let shown := match a, s.pageNow with
      | some a, some pg => pg.taps.any (·.2 == a)
      | _, _ => false
    match a with
    | some a =>
      if shown then onPageAct a; s.io.ctlReply s!"page {repr (← get).page}"
      else s.io.ctlReply s!"no such button on page {repr s.page}"
    | none => s.io.ctlReply "act continue|agree|approve I"
  | "photo" =>
    attachPhoto
    s.io.ctlReply s!"photos {(← get).chips.size}"
  | "post" =>
    modify fun s => { s with text := rest }
    sendNow
    s.io.ctlReply s!"posted, composer {(← get).chips.size} photos"
  | "pics" =>
    -- the mounted rows with pictures: text, and each picture's chunks here
    let out := s.rows.toList.filterMap fun (_, r) =>
      if r.data.pics.isEmpty then none else
      some s!"{r.data.name}: {String.ofList (r.data.text.toList.take 30)} [{", ".intercalate (r.data.pics.map fun p => s!"{p.got}/{p.total}{if p.complete then " complete" else ""}")}]"
    s.io.ctlReply (if out.isEmpty then "no pictures mounted" else " | ".intercalate out)
  | "visible" =>
    let (bots, _) := bottoms s
    let vh := viewH s
    let mut out := #[]
    for i in [0:s.ids.size] do
      let x := s.ids[i]!.2
      let h := heightOf s x
      if bots[i]! + h > s.b && bots[i]! < s.b + vh then
        if let some r := s.rows[x]? then
          out := out.push s!"{r.data.name}: {String.ofList (r.data.text.toList.take 40)}{if r.data.pending then " (pending)" else ""}"
    s.io.ctlReply (String.intercalate " | " out.toList)
  | _ => s.io.ctlReply s!"unknown: {line}"
  return true

/-! ## The loop -/

/-- The sheet's pixels: quick, or the catalogue composed from its header,
its grid's rows scrolled (painted once per row and kept) and its bar
(SheetGeom.compose: compose_row is about this). -/
def sheetBitmap (sh : SheetSt) (mine : List String) : M Bitmap := do
  let s ← get
  let backdrop := Paint.mixC (Palette.color s.dim.theme .bg) (Palette.color s.dim.theme .scrim) 154
  if !sh.catalog then return Sheet.paintQuick s.font s.dim s.W backdrop mine
  let items := sheetItems s sh
  let c := catOf s sh
  let gk := s!"{sh.cat}|{sh.tone}|{sh.query}|{mine}|{s.W}"
  if gk != s.gridKey then modify fun s => { s with gridKey := gk, gridRows := {} }
  let g := c.grid
  let r0 := sh.scroll / g.key
  let r1 := (sh.scroll + g.vh) / g.key
  for r in [r0:r1 + 1] do
    if !(← get).gridRows.contains r then
      let row := Sheet.gridRow s.font s.dim s.W c s.catalog items sh.tone mine r
      modify fun s => { s with gridRows := s.gridRows.insert r row }
  let rows := (← get).gridRows
  let blank := solid (Palette.color s.dim.theme .panel) s.W
  let line (k : Nat) : ByteArray :=
    let (r, li) := g.lineOf k
    match rows[r]? with
    | some b => b.rows[li]?.getD blank
    | none => blank
  let top := Sheet.catTop s.font s.dim s.W c backdrop sh.query sh.searching sh.tone sh.cat
  let bot := Sheet.catBot s.font s.dim s.W c sh.cat sh.searching
  return { w := s.W, rows := SheetGeom.compose top.rows line g.vh sh.scroll bot.rows }

/-- Protect a page's input too: it is inside the list frame, unlike the
channel's composer. Protecting an unfocused field is harmless. -/
def focusBox (s : St) : Safe.Rect :=
  if s.page == .chat then ⟨0, (geom s).composerTop, s.W, botH s⟩
  else match s.pageNow.bind (fun p => p.taps.find? (·.2 == .field)) with
    | some (b, _) => ⟨b.x, topH s + b.y, b.w, b.h⟩
    | none => ⟨0, 0, 0, 0⟩

/-- The one transient Toast layer, in the current visible viewport. The
frame row accounts for the existing seam's keyboard lift on a channel. -/
def withToast (s : St) (fr : Array ByteArray) (_vh : Nat) : Array ByteArray := Id.run do
  let some t := Toast.showing s.nowMs s.noticeClock <|> Toast.showing s.nowMs s.toast
    | return fr
  let tb := Pages.toast s.font s.dim s.W t
  let g := geom s
  let view : Safe.Rect := ⟨0, g.top, s.W, g.viewNow⟩
  let focused := focusBox s
  let input : Safe.Input := ⟨s.W, s.Hs, ⟨0, s.insetTop, 0, s.insetBot⟩, {}, ⟨0, 0, 0, s.imeH⟩⟩
  let some placed := Toast.layout input view focused tb.w tb.h (SafeFrame.targetPx s.dim.dpi) | return fr
  let r0 := over + (placed.rect.y - g.top) + (if s.page == .chat then g.shift else 0)
  let mut fr := fr
  for k in [0:tb.h] do
    if r0 + k < fr.size then
      fr := fr.set! (r0 + k) (Overlay.toastRow s.dim.theme fr[r0 + k]! tb.rows[k]! placed.rect.x k tb.w tb.h (s.dim.px 16) (max 2 (s.dim.px 2)))
  return fr

/-- The same placement and raw-input boundary on every phone and twin. -/
def present (fr : Array ByteArray) (b : Nat) (pin : Bool) : M (List Event) := do
  let work ← get
  work.raster.reconcile work.rasterNeeds.toList
  work.raster.pause false
  modify fun s => { s with imgs := s.imgs.filter (fun _ h =>
    work.rasterNeeds.any (fun n => n.key == h.ticket.key)) }
  let s ← get
  let screen := if s.sheet.isSome then SafeFrame.Screen.sheet else if s.page == .chat then .channel
    else if s.page == .home then .home else .page
  let colours := SafeFrame.colours s.dim.theme
  let top := (SafeFrame.band s.window screen colours .top).colour
  let bottom := (SafeFrame.band s.window screen colours .bottom).colour
  s.io.bars top bottom (SafeFrame.lightIcons top) (SafeFrame.lightIcons bottom)
  let display : Session.Show := fun list b over top bot pin words hold =>
    s.io.frame (SafeFrame.extend s.window list) b over (SafeFrame.extend s.window top)
      (SafeFrame.extend s.window bot) pin words (SafeFrame.extend s.window hold)
  let result ← Session.present display s.io.motion (geom s) s.dim.dpi
    ((bottoms s).2 - (geom s).viewNow) s.input fr b over s.topBmp.rows s.botBmp.rows pin
    (Hold.plane ⟨s.bgRow, s.dim, s.W⟩ (geom s).viewNow)
  modify fun s => { s with input := result.state }
  return result.events

/-- Lifecycle polling uses the same raw decoder, even with no surface. -/
def pollInput : M (List Event) := do
  let s ← get
  let context : Input.Context := ⟨Surface.make (geom s) (s.page != .chat) over s.b s.b 0,
    s.dim.dpi, (bottoms s).2 - (geom s).viewNow⟩
  let result ← Session.receive s.io.motion context s.input (← s.io.poll)
  modify fun s => { s with input := result.state }
  return result.events

/-- Root facts read for the mounted page, after any conversation rows. -/
def pageWants (s : St) : Array Reader.Want :=
  #[Reader.Want.comms] ++ (if s.me.c.isEmpty then #[] else
    #[Reader.Want.people s.me.c, Reader.Want.asking s.me.c] ++
      (if s.page == .home || s.page == .profile || s.page == .removeConfirm then
        #[Reader.Want.members s.me.c s.me.user] else #[]))

/-- Read and paint only the mounted conversation. -/
def chatFrame : M (Nat × Array Nat × UInt64 × UInt64 × UInt64) := do
  -- 3. the list's ids and counts
  let s ← get
  -- the conversation: the messages this device can read (Community.readable,
  -- a union of message.byKey over the keys it holds); one it cannot read
  -- is not in it, and appears when its key's wrap opens (the key's list is
  -- one the view reads)
  -- (read by the reader: Reader.Want.window; the last window stays until
  -- the board has the wanted one, which is applied below, once the row at
  -- the viewport is known)
  -- (the counts beside it are a want of their own, read after the rows:
  -- the placeholders are the counts less the window's rows on each side)
  let idsW := Reader.Want.window s.me.c s.anchor half half
  let countW := Reader.Want.count s.me.c s.anchor
  -- (the wants as last set, unless the anchor moved: a steady frame
  -- moves no generation, Reader.Want.withView_ofFrame)
  let previous ← s.sh.wants
  let requested := Reader.Want.withView previous idsW countW
  if requested != previous then s.sh.setWants requested
  readerPass
  let bd ← takeBoard
  let fresh := match bd.get? idsW with
    | some (.window ids nr, _) =>
      -- until this anchor's counts are read, the last placeholders stay
      let (newer, older, total) := match bd.get? countW with
        | some (.count cn co, _) => (cn - min cn nr, co - min co (ids.size - nr), cn + co)
        | _ => (s.newer, s.older, s.total)
      if ids != s.ids || newer != s.newer || older != s.older || total != s.total || s.restoreAnchor then some (ids, newer, older, total)
      else none
    | _ => none
  let s ← get
  -- people: the present members (admitted, not removed), each once
  if let some (.people n all, _) := (← s.sh.board.get).get? (.people s.me.c) then
    modify fun s => { s with people := n, peopleAll := all }
  let tIds ← (← get).io.nowUs
  -- 4. the offset, and the rows the frame and the fetch distance need
  let s ← get
  let (_, ch0) := bottoms s
  let sample ← s.io.scroll ch0.toUInt32 (geom s).viewNow.toUInt32
  let input := Input.sampleOffset (ch0 - (geom s).viewNow) s.input sample.toInt64.toInt
  modify fun s => { s with input }
  let b := input.offset
  -- the anchor: the row at the viewport's bottom edge, and how far into it
  let mut anchor := if s.restoreAnchor then s.mark else captureAnchor { s with b }
  -- a new window: in place now; the viewport, in its offsets, is where
  -- the anchor row went (`bv`; the native offset `b` follows in 5)
  let mut b := b
  let mut bv := b
  if let some (ids, newer, older, total) := fresh then
    modify fun s => { s with ids, newer, older, total }
    let s ← get
    if let some (x, off) := anchor then
      if let some i := s.ids.findIdx? (·.2 == x) then
        bv := Lifecycle.offset ((bottoms s).1[i]! + heightOf s x) off
      else if s.restoreAnchor then
        anchor := none
        b := 0
        bv := 0
        s.io.scrollTo 0
        modify fun s => { s with mark := none, anchor := none, restoreAnchor := false }
  let s ← get
  let (bots0, _) := bottoms s
  let vh := viewH s
  let fetch := vh
  let lo := if bv ≥ over + fetch then bv - over - fetch else 0
  let hi := bv + vh + over + fetch
  -- the rows the fetch distance needs: the reader's wants, the ids first
  let mut win := #[]
  for i in [0:s.ids.size] do
    let bot := bots0[i]!
    if bot > hi then break
    if bot + heightOf s s.ids[i]!.2 ≥ lo then win := win.push s.ids[i]!.2
  let rowNeeds := win.map fun x =>
    { (Reader.Want.row s.me.c s.me.adm x).need with
      visible := Raster.near ((s.ids.findIdx? (·.2 == x)).map (fun i => bots0[i]!) |>.getD 0)
        (heightOf s x) bv vh 0 }
  let lists := pageWants s
  let needs := #[idsW.need] ++ rowNeeds ++ s.pictureNeeds ++ #[countW.need] ++ lists.map Reader.Want.need
  s.sh.setNeeds needs
  modify fun s => { s with pictureNeeds := #[], b := bv }
  readerPass
  let bd ← takeBoard
  for x in win do mount bd x
  -- the window follows the viewport: once its edge with messages beyond
  -- comes within the fetch distance, it is read again about the row at
  -- the viewport (or its nearest end); pinned to the newest, it is the
  -- newest, and away from it always about a row, so arrivals cannot push
  -- the row being read out of it (Lifecycle.follow_away)
  let s ← get
  let (bots, _) := bottoms s
  if fresh.isSome || ((← takeBoard).get? idsW).isSome then
    let winLo := bots[0]?.getD (bottomPad + s.newer * est)
    let winHi := match s.ids.back? with
      | some (_, x) => bots.back!.add (heightOf s x)
      | none => winLo
    let near := (s.newer > 0 && lo < winLo) || (s.older > 0 && hi > winHi)
    let next := Lifecycle.follow s.anchor s.newer (bv ≤ 4) near
      ((rowAt s bv).bind fun (x, _) => s.ids.find? (·.2 == x))
      (if bv < winLo then s.ids[0]? else s.ids.back?)
    if next != s.anchor then modify fun s => { s with anchor := next }
  let tMount ← (← get).io.nowUs
  -- 5. keep the anchor still (unless pinned to the newest)
  if b > 4 || s.restoreAnchor then
    if let some (x, off) := anchor then
      if let some i := s.ids.findIdx? (·.2 == x) then
        let b' := Lifecycle.offset (bots[i]! + heightOf s x) off
        if b' != b then
          -- the content's new range first (a new window, its placeholders):
          -- a shell clamps a shift to the range it was last told
          let cur ← s.io.scroll (bottoms s).2.toUInt32 vh.toUInt32
          s.io.scrollBy (b'.toFloat - cur)
          b := b'
  -- 6. paint what the frame shows
  let flo := if b ≥ over then b - over else 0
  let fhi := b + vh + over
  for i in [0:s.ids.size] do
    let bot := bots[i]!
    if bot > fhi then break
    if bot + heightOf s s.ids[i]!.2 ≥ flo then paintRow s.ids[i]!.2 bot b vh
  let current ← get
  current.sh.setNeeds (#[idsW.need] ++ rowNeeds ++ current.pictureNeeds ++ #[countW.need] ++ lists.map Reader.Want.need)
  let tPaint ← (← get).io.nowUs
  -- Retire paints when their row leaves the retained window.
  let s ← get
  let mut rows := s.rows
  for (x, r) in s.rows.toList do
    if !win.contains x then
      retireRow r
      rows := rows.erase x
  modify fun s => { s with
    rows, b, mark := anchor,
    restoreAnchor := s.restoreAnchor && !(s.ids.any fun p => some p.2 == anchor.map (·.1)) }
  modify fun s => { s with mark := if s.restoreAnchor then s.mark else captureAnchor s }
  return (b, bots, tIds, tMount, tPaint)

/-- One frame; the twin's events for the next one, or none when the
window closes. -/
def frame (evs : List Event) (lease : Lifecycle.Lease) (inputPage : PageId × Id) : M (Option (List Event)) := do
  let t0 ← (← get).io.nowUs
  modify fun s => { s with life := s.life.forget .empty }
  -- 1. notices
  let s ← get
  let (fs, vs) ← takeChanges
  if !fs.isEmpty || !vs.isEmpty then
    -- an op whose verdict the store recorded leaves the outbox (the store
    -- answers for it, same id)
    let judged : Std.HashSet Id := vs.foldl (fun a (x, _) => a.insert x) {}
    let decided := s.out.filter fun p => judged.contains p.op.id
    -- the store changed: an image waiting for its chunk ops tries again now
    modify fun s => { s with
      live := s.live.notice fs (vs.map (·.1))
      out := s.out.filter fun p => !judged.contains p.op.id }
    if !decided.isEmpty then noticeLocal decided.toList
  flushNode
  -- the reader's acts: their writes go to the node (or the writer)
  let _ ← takeDone
  chaosStep
  let tNotices ← (← get).io.nowUs
  -- 2. events and commands
  for e in evs do
    match e with
    | .ime h =>
      let s ← get
      if s.active && s.surface && s.life.mounted && inputPage == (s.page, s.cur) then
        discard <| onEvent (.ime h)
    | _ =>
      if let some false ← owned lease (onEvent e) then return none
  let cmds ← (← get).io.ctlPoll
  modify fun s => { s with ctl := s.ctl ++ cmds }
  let mut queue := (← get).ctl
  while !queue.isEmpty do
    if ← command queue[0]! then queue := queue.extract 1 queue.size else break
  modify fun s => { s with ctl := queue }
  -- the native field holds the string it now edits (a page or sheet
  -- change chose another)
  syncText
  let tCommands ← (← get).io.nowUs
  mountPage
  let (b, bots, tIds, tMount, tPaint) ← if (← get).page == .chat then chatFrame else do
    let s ← get
    s.sh.setWants (pageWants s)
    readerPass
    let t ← (← get).io.nowUs
    pure (0, #[], t, t, t)
  -- the sheet's fling: its velocity carries the grid, decaying
  let s ← get
  if let some sh := s.sheet then
    if sh.catalog && sh.drag.isNone && (sh.vel > 0.05 || sh.vel < -0.05) then
      let c := catOf s sh
      let next := (Int.ofNat sh.scroll + (sh.vel * 16.0).toInt64.toInt).toNat
      let sh' := { sh with scroll := c.grid.clamp next, vel := sh.vel * 0.95 }
      modify fun s => { s with sheet := some sh' }
  -- join requests for the current community, and admissions they complete
  refreshComms
  refreshAsking
  refreshMembers
  refreshHomeCount
  netStep
  scanStep
  -- admitted in a community I joined: my first profile (the name I chose),
  -- in every community this device is admitted to, not only the current
  -- one (a join approved while another is on screen still introduces
  -- itself). introduce is a view run through the live cache, so it is
  -- re-evaluated only when a list it read changes, and writes nothing once
  -- a profile is filed or in the outbox
  let s ← get
  for m in s.comms do
    if m.waiting then continue
    let (w, _) ← readView (Community.introduce m.c m.dev (← nowMin)) #[]
    if !w.ops.isEmpty then let _ ← writeAll w
    -- and the community's keys wrapped to this device, opened into local
    -- key ops (a live view too: re-run when a wrap arrives)
    let (w, _) ← readView (Community.unwrap m.c) #[]
    if !w.ops.isEmpty then let _ ← writeAll w
  let tRefresh ← (← get).io.nowUs
  -- a frame over 20 ms says where its time went (logcat / stderr)
  let slow (t1 : UInt64) : IO Unit := do
    if t1 - t0 > 20000 then
      let ms (a b : UInt64) := s!"{(b - a) / 1000}"
      s.io.log s!"slow frame {ms t0 t1} ms: notices {ms t0 tNotices} commands {ms tNotices tCommands} ids {ms tCommands tIds} mount {ms tIds tMount} paint {ms tMount tPaint} refresh {ms tPaint tRefresh} frame {ms tRefresh t1}"
  -- a community this device waits to join shows Waiting in place of its
  -- conversation (read: no admission for my device there)
  let s ← get
  if (s.page == .chat || s.page == .home) && s.me.waiting && !s.me.c.isEmpty then
    modify fun s => { s.withNav (Nav.swap .waiting s.nav) with pageKey := none }
  if s.page == .waiting && !s.me.waiting then
    modify fun s => { s.withNav (Nav.swap .home s.nav) with pageKey := none }
    say "You're in."
  mountPage
  pruneLive
  -- a page instead of the conversation: its bar, its content in the list
  -- layer (which does not scroll on a page), a one-row composer layer
  let s ← get
  if s.page != .chat then
    let key := pageIn s
    if some key != s.pageKey then
      let (pg, top) := drawPage s.font s.bgRow s.camView key
      let bot := Bitmap.blank s.W 1 s.bgRow
      modify fun s => { s with pageNow := some pg, pageKey := some key }
      modify fun s => { s with topBmp := top, botBmp := bot, chromeKey := "" }
    let s ← get
    let vh := viewH s
    let pb ← s.io.scroll vh.toUInt32 vh.toUInt32
    let _ := pb
    let mut fr := Array.replicate (vh + 2 * over) s.bgRow
    if let some pg := s.pageNow then
      for k in [0:min vh pg.bmp.h] do fr := fr.set! (over + k) pg.bmp.rows[k]!
    let shown := withToast s fr vh
    let t1 ← s.io.nowUs
    slow t1
    modify fun s => { s with b := 0, frames := s.frames + 1, times := s.times.push (t1 - t0).toNat }
    return some (← present shown 0 true)
  -- 7. chrome and the frame
  let s ← get
  let sheetKey := match s.sheet, s.selected with
    | some sh, some m => s!"{sh.catalog}|{sh.cat}|{sh.tone}|{sh.query}|{sh.searching}|{sh.scroll}|{mineOn s m}"
    | _, _ => ""
  let key := s!"{s.W}|{s.insetTop}|{s.total}|{s.people}|{s.peopleAll}|{s.text}|{s.sel}|{sheetKey}|{s.me.name}|{s.asking.size}|{s.chips.size}"
  if key != s.chromeKey then
    let bot ← match s.sheet, s.selected with
      | some sh, some m => sheetBitmap sh (mineOn s m)
      | _, _ => pure (composer s)
    modify fun s => { s with topBmp := header s, botBmp := bot, chromeKey := key }
  let s ← get
  let input := Input.sampleOffset ((bottoms s).2 - (geom s).viewNow) s.input b
  modify fun s => { s with input }
  let b := input.offset
  let fr := withToast s (listFrame s b bots) (viewH s)
  let t1 ← s.io.nowUs
  slow t1
  let times := (if s.times.size ≥ 600 then s.times.extract 300 s.times.size else s.times).push (t1 - t0).toNat
  modify fun s => { s with b := b, frames := s.frames + 1, times := times }
  return some (← present fr b false)

/-- One frame, in one read transaction: every read it makes, and the
notices it takes (`takeChanges`, its first read), are of one moment of the
store, so no part of the screen is newer than another. -/
def stepCore (evs : List Event) : M (Option (List Event)) := do
  let io := (← get).io
  let incoming := evs ++ (← pollInput) ++ (← io.links).toList.map Event.deepLink
  let lease := (← get).life.lease
  let inputPage := ((← get).page, (← get).cur)
  let mut input := []
  for e in incoming do
    match e with
    | .background | .foreground | .surface _ | .resize | .deepLink _ | .close =>
      if !(← onEvent e) then return none
    | _ => input := input ++ [e]
  reap
  let s ← get
  if !s.active || !s.surface || s.netStop.isSome then
    IO.sleep 16
    return some []
  let sc ← io.screen
  systemTheme (Theme.ofWord (sc[5]?.getD 0))
  resize sc
  modify fun s =>
    if s.notices.head? != s.noticeClock.map (·.1) then
      { s with noticeClock := s.notices.head?.map fun t => (t, s.nowMs + Toast.life) }
    else if s.noticeClock.isSome && (Toast.showing s.nowMs s.noticeClock).isNone then
      { s with notices := s.notices.drop 1, noticeClock := none }
    else s
  -- A complete snapshot outranks keyboard events queued for an older frame.
  if sc.size ≥ 9 then input := input.filter fun e => match e with | .ime _ => false | _ => true
  mountPage
  let links := (← get).pendingLinks
  modify fun s => { s with pendingLinks := [] }
  for url in links do
    match Community.Invite.parse url with
    | some i => takeInvite i
    | none => say "That isn't a Quiet invite link."
  let rd := (← get).rd
  rd.exec "BEGIN"
  let r ← try
    let r ← frame input lease inputPage
    rd.exec "COMMIT"
    pure r
  catch e =>
    rd.exec "ROLLBACK"
    throw e
  let mut queued := []
  for bytes in (← get).queuedWrites do
    if let some op := Op.decode bytes then
      if (← (Q.op op.id).run rd #[]) == .bytes none then queued := queued ++ [bytes]
  modify fun s => { s with queuedWrites := queued }
  saveCheckpoint
  return r

/-- Foreground assembly suspends admission; the pool can run while the
native shell presents. Finally also releases it on suspend or errors. -/
def step (evs : List Event) : M (Option (List Event)) := do
  let pool := (← get).raster
  pool.pause true
  modify fun s => { s with rasterNeeds := #[], imgWaiting := {} }
  try stepCore evs finally pool.pause false

partial def loop (evs : List Event) : M Unit := do
  match ← step evs with
  | none => pure ()
  | some evs => loop evs

/-- The app's state at start: the window's size, the font, both
connections, this node's identity (the community founded on first run). -/
def start (io : Io) (screen : Array UInt32) (dbPath : String) (net : Option (Nat × Bool) := none) :
    IO St := do
  let window := SafeFrame.report screen
  let safe := Safe.content { window with ime := {} }
  let W := safe.w
  let Hs := window.h
  let font ← Font.load (density := (screen[4]?.getD 420).toNat)
  let rd ← openDb dbPath
  Lifecycle.init rd
  let saved ← Lifecycle.load rd
  if let some (_, _, _, _, _, bs) := saved then
    let queued := (Codec.decode (bs[10]?.getD .empty) : Option (List ByteArray)).getD []
    let ops := queued.filterMap Op.decode
    if !ops.isEmpty then (receive fam (intake fam true ops)).run rd
  let setting ← Theme.load rd
  let wr ← Writer.start dbPath commitCheckpoint
  let theme : Theme.State := ⟨setting, Theme.ofWord (screen[5]?.getD 0)⟩
  io.appearance (Theme.effective theme == .dark) (Palette.color (Theme.effective theme) .bg)
  -- the communities are this device's accepted facts: read them once
  -- here to choose the first page
  let sh ← Reader.Shared.new wr.count
  let raster ← Work.Pool.new
  let probe : St := { io := io, W := W, Hs := Hs, insetTop := 0, insetBot := 0, font := font, bgRow := .empty, rd := rd, wr := wr, me := default, sh := sh, raster }
  let ((all, _), _) ← (Kinds.Accepted.read : M _).run probe
  let comms := Kinds.Accepted.listed all
  let me := comms[0]?.getD default
  let catalog ← match ← (Sheet.loadCatalog).toBaseIO with
    | .ok c => pure c
    | .error e => do IO.eprintln s!"no emoji catalogue: {e}"; pure #[]
  let initial : St := {
           io := io, theme := theme, W := W, Hs := Hs, insetTop := safe.y, window, imeH := window.ime.bottom, catalog := catalog,
           dim := ⟨(screen[4]?.getD 420).toNat, font.cell, Theme.effective theme⟩,
           insetBot := Hs - safe.bottom, font := font, bgRow := solid (Palette.color (Theme.effective theme) .bg) W, rd := rd,
           wr := wr, me := me, comms := comms, cur := me.acc, page := if comms.isEmpty then .getStarted else .home,
           -- a removal already in the store at launch is not announced
           goneSeen := (all.toList.filter (·.removed)).map (·.acc),
           dbPath := dbPath, netCfg := net, sh := sh, raster, rst := some { rd := ← openDb dbPath } }
  let mut initial := initial
  if let some cp := saved then
    let (version, _, acc, _, _, _) := cp
    if version == 1 then
      if acc.isEmpty && comms.isEmpty then initial := applyCheckpoint initial cp
      else if (Kinds.Accepted.select comms acc).isSome then
        initial := (← (switchToAcc acc).run initial).2
        initial := applyCheckpoint initial cp
  initial.io.setText (if fieldPage initial.page then initial.field else initial.text)
  return initial

/-- On a device: the reader's passes on a thread of their own (never the
shared task pool), so the frame only takes the board. -/
def spawnReader (s : St) : IO St := do
  return (← resumeReader.run { s with threaded := true }).2

end App
