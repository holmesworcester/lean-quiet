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
import engine.renderer.Data
import ops.app.Chaos
import engine.renderer.Row
import engine.renderer.Geometry
import engine.renderer.Cover
import engine.renderer.Sheet
import ops.app.Pages
import ops.app.Composer
import ops.community.link.View
import engine.renderer.Camera
import ops.app.Remove
import ops.community.message.View
import ops.community.membership.RequestView
import Std.Data.HashMap

namespace App
open Engine Community Data Paint Font Row

/-- The platform, as the app uses it. -/
structure Io where
  screen : IO (Array UInt32)
  scroll : UInt32 → UInt32 → IO UInt32
  scrollBy : Float → IO Unit
  scrollTo : Float → IO Unit
  frame : Array ByteArray → UInt32 → UInt32 → Array ByteArray → Array ByteArray → Bool → IO (Array UInt32)
  text : IO (String × Array UInt32)
  ime : Bool → IO Unit
  textClear : IO Unit
  copy : String → IO Unit
  ctlPoll : IO (Array String)
  ctlReply : String → IO Unit
  nowUs : IO UInt64
  /-- Wall-clock minutes since the Unix epoch, and the local timezone's
  offset from UTC in minutes. -/
  wall : IO (Nat × Int) := do
    return ((← Std.Time.Timestamp.now).toSecondsSinceUnixEpoch.val.toNat / 60, 0)
  scan : Bool → IO Unit
  luma : IO (Array UInt32 × ByteArray)
  /-- A line for the platform's log (logcat, the device console, stderr). -/
  log : String → IO Unit := IO.eprintln

/-- How far beyond each end of the viewport the list frame is drawn. -/
def over : Nat := 1024
/-- A row's height before it is measured. -/
def est : Nat := 150
def bottomPad : Nat := 16

structure RowSt where
  data : RowData
  lay : Layout
  deps : Array Q
  /-- What the current paint was made from: data version and which
  pictures were ready. -/
  painted : Nat × List Bool
  task : Option (Task Bitmap)
  shown : Option Bitmap
  ver : Nat
  /-- The shown paint darkened, for behind the reaction tray, and the
  version it was made from. -/
  dimmed : Option (Task Bitmap) := none
  dimVer : Nat := 0
  dimShown : Option Bitmap := none

abbrev ImgKey := ByteArray × Nat × Nat

/-- Which page is up: a conversation, or one of libquiet's other screens. -/
inductive PageId where
  | home | chat | getStarted | create | createName | joinChoice | openInvite | paste | scan | name | agree | waiting
  | requests | invite | switcher | profile | removeConfirm | duplicate
  deriving BEq, Repr, Inhabited

/-- The reaction sheet's state: quick or the catalogue, its category,
tone, search, and the grid's scroll (with a drag or fling in progress). -/
structure SheetSt where
  catalog : Bool := false
  cat : Nat := 0
  tone : Nat := 0
  query : String := ""
  searching : Bool := false
  scroll : Nat := 0
  drag : Option (Nat × Nat) := none
  lastY : Nat := 0
  lastT : Nat := 0
  vel : Float := 0
  deriving Inhabited

/-- Everything a page and its bar are drawn from, besides the font, the
background row and the camera's frame: the page cache's key. Communities
appear by their keys (acceptance op id, community id, name, …), so two
entries that share a name are still two keys. -/
structure PageIn where
  page : PageId
  W : Nat
  h : Nat
  insetTop : Nat
  dim : Dim
  field : String
  refusal : Option String
  me : Kinds.Accepted.Key
  comms : Array Kinds.Accepted.Key
  /-- The join requests shown (not hidden), and how many there are in all. -/
  asking : Array Pages.Asking
  askingAll : Nat
  link : Option String
  members : Array (String × Bool)
  online : Array Bool
  backEmpty : Bool
  /-- Which camera frame is shown (a new frame, a new key). -/
  camFrame : Nat
  /-- The open profile: name, whether it is me, whether removed, and
  whether Remove is offered (Remove.offered); and the removal's stage
  (1, 2: asked once, twice; 3: sending; 4: refused) and refusal. -/
  profile : String × Bool × Bool × Bool := ("", false, false, false)
  removeStage : Nat := 0
  removeWhy : String := ""
  deriving BEq, Inhabited

structure St where
  io : Io
  W : Nat
  Hs : Nat
  insetTop : Nat
  insetBot : Nat
  font : Font
  bgRow : ByteArray
  rd : Db
  wr : Writer
  dbPath : String := ""
  /-- The network, if this app runs one: the port its node listens on,
  and whether it is reached on loopback (two apps on one machine, in
  tests) instead of its LAN addresses. -/
  netCfg : Option (Nat × Bool) := none
  /-- The node's runner (Engine.Sync.Runner): it owns the writes once it
  runs. And the ids it stored since the frame last took them. -/
  net : Option Engine.Sync.Runner := none
  /-- The journal's newest row this app has taken notice of. -/
  seen : Nat := 0
  me : Chaos.Me
  live : Live := {}
  out : Array Pending := #[]
  limit : Nat := 64
  ids : Array Pos := #[]
  /-- How many rows the list read returned (hidden ones too): what paging
  compares with its limit. -/
  fetched : Nat := 0
  total : Nat := 0
  people : Nat := 0
  heights : Std.HashMap Id Nat := {}
  rows : Std.HashMap Id RowSt := {}
  imgs : Std.HashMap ImgKey (Task Bitmap) := {}
  /-- When an image whose chunks were not all readable may be tried again
  (a frame number). -/
  imgRetry : Std.HashMap ImgKey Nat := {}
  selected : Option Id := none
  b : Nat := 0
  imeH : Nat := 0
  text : String := ""
  sel : Array UInt32 := #[0, 0, 0, 0]
  topBmp : Bitmap := default
  botBmp : Bitmap := default
  chromeKey : String := ""
  srcs : Option (Task (Array Image.Src)) := none
  /-- Chaos's writes, being made (ctl `chaos`). -/
  chaos : Option (Task (Array Job)) := none
  ctl : Array String := #[]
  frames : Nat := 0
  times : Array Nat := #[]
  paints : Nat := 0
  seed : Nat := 1
  dim : Dim := default
  /-- The reaction sheet, open on the message in `selected`. -/
  sheet : Option SheetSt := none
  catalog : Array Sheet.Item := #[]
  gridKey : String := ""
  gridRows : Std.HashMap Nat Bitmap := {}
  /-- Every community this device is in; `me` is the current one. -/
  comms : Array Chaos.Me := #[]
  /-- The current community: memory, not state. -/
  cur : Id := .empty  -- the current entry's acceptance (Kinds.Accepted.Me.acc)
  /-- The link pasted or scanned, while Agree & join is asked. -/
  invite : Option Community.Invite := none
  /-- This session's invite link per entry (acceptance; Add members). -/
  links : List (Id × String) := []
  /-- Photos attached in the composer: QOI bytes, size, and the chip. -/
  chips : Array (ByteArray × Nat × Nat × Composer.Chip) := #[]
  photoNext : Nat := 0
  /-- The name chosen for joining (Choose a name). -/
  joinName : String := ""
  /-- The community being created, while its founder names themself. -/
  newCommunity : String := ""
  /-- The people of the current community (Direct messages on home):
names, and whether it is me. -/
  members : Array (String × Bool) := #[]
  /-- Each member's user (as `members`). -/
  memberIds : Array Id := #[]
  /-- Whether this device's user is an admin of the current community. -/
  amAdmin : Bool := false
  /-- The member whose profile is open: user, name, whether it is me. -/
  profileOf : Option (Id × String × Bool) := none
  /-- Entries already removed when told (or when the app started): their
removal is not announced again. -/
  goneSeen : List Id := []
  /-- Standing notices (libquiet's: no timeout; a tap puts the first
  away), e.g. "You've been removed from …". -/
  notices : List String := []
  /-- The removal flow (Remove.step). -/
  removal : Remove.Step := .idle
  /-- Whether each member (as `members`) has a device this node holds a
  session with now. -/
  online : Array Bool := #[]
  /-- The peers this node holds sessions with (their device keys), read
  every half second. -/
  peers : List ByteArray := []
  /-- A toast and the frame it goes at (libquiet's: centred, about 3 s). -/
  toast : Option (String × Nat) := none
  page : PageId := .chat
  backStack : List PageId := []
  /-- A page's one-line field (the keyboard's text while a page shows one). -/
  field : String := ""
  refusal : Option String := none
  hidden : List Id := []
  /-- The key of the page drawn (`drawPage`): it is redrawn when the key changes. -/
  pageKey : Option PageIn := none
  pageNow : Option Pages.Page := none
  /-- Requests to join the current community no admission answers yet:
  the request's id, its fact, and its approvals' ids. -/
  asking : Array Kinds.Request.Data := #[]
  /-- Whether the camera is on (as last asked of the twin), and its newest
  frame as drawn on Join with QR code. -/
  camOn : Bool := false
  camView : Option Bitmap := none
  camFrame : Nat := 0
  /-- A camera frame being decoded, off the app's thread. -/
  decoding : Option (Task (Option String)) := none
  /-- Camera frames decoded so far (ctl `scans`). -/
  scans : Nat := 0

instance : Inhabited Io := ⟨⟨pure #[1080, 2400, 0, 0, 420], fun _ _ => pure 0, fun _ => pure (), fun _ => pure (), fun _ _ _ _ _ _ => pure #[],
  pure ("", #[]), fun _ => pure (), pure (), fun _ => pure (), pure #[], fun _ => pure (), pure 0, pure (0, 0), fun _ => pure (), pure (#[], .empty), IO.eprintln⟩⟩

abbrev M := StateT St IO

def c (s : St) : Id := s.me.c

/-! ## Reading through live answers -/

def read (q : Q) : M Ans := do
  let s ← get
  if let some a := s.live.answer q then return a
  let a ← q.run s.rd s.out
  modify fun s => { s with live := s.live.store q a }
  return a

def fresh (q : Q) : M Bool := do return (← get).live.fresh q


instance : Reads M := ⟨read⟩

/-- Message m's row: its view (Kinds.Message.read: the claimed time, in
UTC minutes), shown at the local time (the platform's timezone). -/
def readRow (m : Id) : M (Option (RowData × Array Q)) := do
  let s ← get
  let tz := (← s.io.wall).2
  return (← Kinds.Message.read s.me.c s.me.adm m).map fun (d, qs) =>
    ({ d with time := (d.time + tz).toNat }, qs)

/-! ## Writing -/

/-- Notices made by this node itself: a change to the outbox. -/
def noticeLocal (keys : List ByteArray) : M Unit :=
  modify fun s => { s with live := s.live.notice keys.toArray }

/-- The one way into the store: through the node while it runs (it owns
the store's writes, and offers peers only what it knows), else the local
writer. A write behind the node's back is stored but never synced. -/
def submit (s : St) (j : Job) : IO Unit :=
  match s.net with
  | some r => r.write j.ops
  | none => s.wr.submit j

/-- A user action's write (an intent's ops): each op is
judged in order against what is decided and the ops before it in the
same write. Valid ops show at once, pending. An op whose requirements are
not all here yet (a join's request cites the community's ops, which come
by sync) shows nothing and waits in the store, as the engine waits for
any op. An Invalid op refuses the whole write. Otherwise the ops go in as one job
of this node's own (`submit`). -/
def writeAll (w : Community.Write) : M Bool := do
  let s ← get
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
  noticeLocal (pend.toList.flatMap (·.keys))
  submit s ⟨w.ops, true⟩
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

/-- The newest message's counter (its sort key's first 8 bytes; 0 for none). -/
def newestCounter (s : St) : Nat :=
  match s.ids[0]? with
  | some (sk, _) => (sk.extract 0 8).foldl (fun n b => n * 256 + b.toNat) 0
  | none => 0

/-- Wall-clock minutes since the Unix epoch: the time a write claims. -/
def nowMin : M Nat := do return (← (← get).io.wall).1

def sendText (text : String) : M Bool := do
  let s ← get
  let t := text.trimAscii.toString
  if t.isEmpty then return false
  -- sealed under the community's current key, as the composer's send is
  let (k?, _) ← readView (Community.currentKey s.me.c) #[]
  let some k := k? | return false
  let (w, _) ← readView (Community.send s.me.c s.me.adm s.me.dev k (← Engine.Crypto.randomBytes 24) t.toUTF8
    (← nowMin)) #[]
  writeAll w

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

/-- The loaded rows' bottoms (bottom-anchored), newest first, and the
content's height. -/
def bottoms (s : St) : Array Nat × Nat := Id.run do
  let mut out := Array.mkEmpty s.ids.size
  let mut y := bottomPad
  for (_, x) in s.ids do
    out := out.push y
    y := y + heightOf s x
  let unloaded := s.total - min s.total s.ids.size
  return (out, y + unloaded * est + 16)

/-! ## Mounting, measuring, painting -/

def decodeTask (bytes : ByteArray) (w h : Nat) (sq : Bool) : Task Bitmap :=
  Task.spawn fun _ =>
    match Image.decode bytes with
    | some src => if sq then Image.square src w Row.bg else Image.scaled src w h Row.bg
    | none => Bitmap.blank w h (solid Row.placeholder w)

/-- An attachment's slices, read from its chunk ops in order (a chunk this
device sends may still be in the outbox); none while one is not here. -/
def slicesOf (p : Row.Pic) : M (Option (List ByteArray)) := do
  -- the chunk ops' bytes, as stored or in the outbox: nothing is decoded
  -- here (a 64 KiB chunk is slow to decode; the frame must not wait)
  let s ← get
  let mut raw := #[]
  for x in p.chunks do
    match s.out.find? (·.op.id == x) with
    | some pd => raw := raw.push pd.op.bytes
    | none =>
      let rows ← s.rd.query "SELECT bytes FROM ops WHERE id = ?" #[x]
      let some b := rows[0]? >>= (·[0]?) | return none
      raw := raw.push b
  return some raw.toList

/-- Chunk ops' bytes to their slices, in order (off the app's thread). -/
def slicesFromOps (raw : List ByteArray) : Option (List ByteArray) :=
  raw.mapM fun b => do
    let o ← Engine.Op.decode b
    match (Codec.decode o.body : Option Community.Body) with
    | some (.chunk _ _ _ slice _) => some slice
    | _ => none

/-- A decode of `k` started (or finished): its bitmap once done. `start`
is a thunk, run only when `k` has no decode yet: an argument is evaluated
at the call, so a task built there would be spawned every frame. -/
def decoded (k : ImgKey) (start : Unit → M (Option (Task Bitmap))) : M (Option Bitmap) := do
  match (← get).imgs[k]? with
  | some t => if ← IO.hasFinished t then return some t.get else return none
  | none =>
    if let some t ← start () then modify fun s => { s with imgs := s.imgs.insert k t }
    return none

/-- An attachment drawn at its size, if ready, and whether it is the file
(not its preview), as `Row.Pic.shown` chooses: the preview (softened,
Arrival.soften) until every chunk is here and the file is decoded, then
the file (its slices assembled and opened with the file's key, off the
app's thread). -/
def image (p : Row.Pic) (w h : Nat) : M (Option Bitmap × Bool) := do
  let pre ← decoded (p.hash.push 0, w, h) fun _ => do
    pure (if p.preview.isEmpty then none
      else some ((decodeTask p.preview w h false).map (Arrival.soften Row.bg)))
  let full ← if !p.complete then pure none else decoded (p.hash.push 1, w, h) fun _ => do
    -- not every chunk op is readable yet: try again when the store next
    -- changes (step clears imgRetry on notices), or in two seconds
    let k := (p.hash.push 1, w, h)
    if let some t := (← get).imgRetry[k]? then
      if (← get).frames < t then return none
    let some raw ← slicesOf p
      | modify fun s => { s with imgRetry := s.imgRetry.insert k (s.frames + 120) }; pure none
    let (key, nonce) := (p.key, p.nonce)
    pure <| some <| Task.spawn fun _ =>
      match ((slicesFromOps raw).bind fun slices => Community.openFile slices key nonce).bind Image.decode with
      | some src => Image.scaled src w h Row.bg
      | none => Bitmap.blank w h (solid Row.placeholder w)
  return p.shown pre full

/-- Mount (read, lay out) row x if any of its answers are stale. -/
def mount (x : Id) : M Unit := do
  let s ← get
  let need ← match s.rows[x]? with
    | none => pure true
    | some r => do
      let mut stale := false
      for q in r.deps do
        if !(← fresh q) then stale := true
      pure stale
  if !need then return
  match ← readRow x with
  | none => pure ()
  | some (d, deps) =>
    let s ← get
    match s.rows[x]? with
    | some r =>
      if r.data == d then
        modify fun s => { s with rows := s.rows.insert x { r with deps } }
      else
        let lay := Row.layout s.font s.dim s.W d
        modify fun s => { s with rows := s.rows.insert x { r with data := d, lay, deps, ver := r.ver + 1 },
                                  heights := s.heights.insert x lay.h }
    | none =>
      let lay := Row.layout s.font s.dim s.W d
      modify fun s => { s with rows := s.rows.insert x ⟨d, lay, deps, (0, []), none, none, 1, none, 0, none⟩,
                                heights := s.heights.insert x lay.h }

/-- Start a paint of row x if what it shows changed; collect a finished one. -/
def paintRow (x : Id) : M Unit := do
  let s ← get
  let some r := s.rows[x]? | return
  let av : Option Bitmap := none  -- profiles carry no avatar: Row draws the initial
  let mut imgs := #[]
  -- what is painted: each picture's presence and stage (preview, file)
  let mut ready := [av.isSome]
  for i in [0:r.lay.pics.size] do
    let bx := r.lay.pics[i]!
    match r.data.pics[i]? with
    | some p =>
      let (b, isFile) ← image p bx.w bx.h
      imgs := imgs.push b
      ready := ready ++ [b.isSome, isFile]
    | none => imgs := imgs.push none
  let s ← get
  let some r := s.rows[x]? | return
  -- a finished paint is shown
  let mut r := r
  if let some t := r.task then
    if ← IO.hasFinished t then r := { r with shown := some t.get, task := none }
  -- behind an open tray, every other row is shown darkened
  if s.selected.isSome && s.selected != some x then
    if let some bmp := r.shown then
      if r.dimmed.isNone || r.dimVer != r.painted.1 then
        r := { r with dimmed := some (Task.spawn fun _ => Row.Bitmap.dim bmp), dimVer := r.painted.1 }
    if let some t := r.dimmed then
      if ← IO.hasFinished t then r := { r with dimShown := some t.get }
  else if r.dimmed.isSome then
    r := { r with dimmed := none, dimShown := none }
  if r.painted != (r.ver, ready) && r.task.isNone then
    let (f, dm, W, bgRow, d, l) := (s.font, s.dim, s.W, s.bgRow, r.data, r.lay)
    let t := Task.spawn fun _ => Row.paint f dm W bgRow d l av imgs
    r := { r with task := some t, painted := (r.ver, ready) }
    modify fun s => { s with paints := s.paints + 1 }
  modify fun s => { s with rows := s.rows.insert x r }

/-! ## The frame -/

/-- A placeholder line: the background with a bar where a row's text
would be, in stripes (a row not painted yet, or older rows not loaded). -/
def holdLine (s : St) (li : Nat) : ByteArray :=
  if li % 48 < 12 || li % 48 ≥ 36 then s.bgRow
  else
    let x0 := s.dim.pad + s.dim.px 48
    let w := max 1 (s.W * 2 / 3 - x0)
    (solid Row.placeholder w).copySlice 0 s.bgRow (4 * x0) (4 * w)

/-- The list frame: row r shows content at b + viewH + over - 1 - r, as
Cover.seen says: a painted row's line, else a placeholder (Cover.covered:
nothing inside the content is left blank, however slow a read or a
decode is). -/
def listFrame (s : St) (b : Nat) (bots : Array Nat) : Array ByteArray := Id.run do
  let vh := viewH s
  let hgt := vh + 2 * over
  let top := b + vh + over     -- content above the frame's first row
  let low := if b ≥ over then b - over else 0
  -- the rows overlapping the frame, from the first one up
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
  let bottom := if i0 < s.ids.size then bots[i0]! else
    match s.ids.back? with
    | some (_, x) => bots.back! + heightOf s x
    | none => bottomPad
  -- older rows to load: nothing past the loaded ones is blank
  let more := s.ids.size < s.total
  let rows := slice.toList
  let mut fr := Array.mkEmpty hgt
  for r in [0:hgt] do
    let p := top - 1 - r
    fr := fr.push (match Cover.seen bottom more rows p with
      | .line j li => ((bmps[j]?).join.map (·.rows[li]!)).getD s.bgRow
      | .hold j => holdLine s (heightOf s (s.ids[i0 + j]?.map (·.2) |>.getD .empty) - 1 - (p - (bots[i0 + j]?.getD 0)))
      | .older => holdLine s (p % 150)
      | .blank => s.bgRow)
  return fr

def header (s : St) : Bitmap := Id.run do
  let h := topH s
  let hb := 0x16181B
  let x := s.dim.pad
  let mut b := Bitmap.blank s.W h (solid hb s.W)
  let y := s.insetTop + s.dim.px 8
  -- back to the community's home on the left; the channel and the
  -- community's name, which opens the switcher
  let iy := y + (2 * s.dim.lineH - s.font.cell) / 2
  b := b.line s.font (Text.oneLine s.font s.font.cell "←") x iy nameInk
  let tx := x + s.dim.px 40
  b := b.line s.font (Text.oneLine s.font (s.W - tx - x) s!"# general · {s.me.name} ▾") tx y nameInk true
  let sub := s!"{s.total} messages · {s.people} people"
  b := b.line s.font (Text.oneLine s.font (s.W - tx - x) sub) tx (y + s.dim.lineH) dim
  b := b.fill 0 (h - max 2 (s.dim.px 1)) s.W h pill
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
def say (t : String) : M Unit := modify fun s => { s with toast := some (t, s.frames + 180) }

/-- Where this device is dialed: its LAN addresses at the node's port
(Link.hints, Wi-Fi first), or loopback in a one-machine test. -/
def listenHints : M (List ByteArray) := do
  let s ← get
  let (port, loop) := s.netCfg.getD (Link.port, false)
  if loop then return [s!"127.0.0.1:{port}".toUTF8]
  let addrs ← try Link.local? catch _ => pure []
  return Link.hints addrs port

/-- Open a page (the current one goes on the back stack). -/
def openPage (p : PageId) : M Unit := do
  let s ← get
  if s.page == p then return
  -- Add members issues this community's link once per session: an
  -- invitation op of mine, and the link that carries its bearer secret
  if p == .invite && !s.me.waiting && !(s.links.any (·.1 == s.me.acc)) then
    let bearer ← Chaos.freshSeed "bearer"
    -- dial hints: this device's private LAN addresses (Link.hints)
    let (w, i) := Community.inviteTo s.me.c s.me.adm s.me.dev (Device.ofSeed bearer) (← listenHints)
    if ← writeAll w then
      modify fun s => { s with links := (s.me.acc, i.text) :: s.links }
  s.io.scrollTo 0
  modify fun s => { s with backStack := s.page :: s.backStack, page := p, refusal := none, pageKey := none }

/-- Back: the page before, or the conversation. -/
def back : M Unit := do
  let s ← get
  s.io.ime false
  s.io.textClear
  s.io.scrollTo 0
  match s.backStack with
  | p :: rest => modify fun s => { s with page := p, backStack := rest, field := "", refusal := none, pageKey := none }
  | [] => modify fun s => { s with page := .chat, field := "", refusal := none, pageKey := none }

/-- What the app holds for an entry no longer listed, forgotten: its
invite link, a pasted link to its community, an open profile, and, if it
was current, the composer's text and photos. -/
def forgetEntry (s : St) (a c : Id) : St :=
  let cur := s.me.acc == a
  { s with links := s.links.filter (·.1 != a),
           invite := if (s.invite.map (·.community == c)).getD false then none else s.invite,
           profileOf := if cur then none else s.profileOf,
           text := if cur then "" else s.text, chips := if cur then #[] else s.chips }

/-- The communities, read by the Community kind: those listed (a removed
entry hidden), the current one kept or, gone, the first (Get started when
none is left). -/
def refreshComms : M Unit := do
  let (all, _) ← Kinds.Accepted.read
  let cs := Kinds.Accepted.listed all
  -- removed since last told: a standing notice each, and forgotten
  for g in Kinds.Accepted.newlyGone (← get).goneSeen all do
    if (← get).me.acc == g.acc then (← get).io.textClear
    modify fun s => { forgetEntry s g.acc g.c with
      goneSeen := g.acc :: s.goneSeen,
      notices := s.notices ++ [s!"You’ve been removed from {if g.name.isEmpty then "a community" else g.name}."] }
  modify fun s =>
    match Kinds.Accepted.landing cs s.cur with
    | some me => { s with comms := cs, me, cur := me.acc }
    | none =>
      -- nothing listed: Get started (unless a join is being made)
      { s with comms := cs, me := default, cur := .empty,
               page := if s.comms.isEmpty then s.page else .getStarted,
               backStack := if s.comms.isEmpty then s.backStack else [] }

/-- Make the entry of acceptance `a` the current one (memory only): the
list starts again from its newest. An entry is its acceptance, never its
community id or name (Switch.select_tapped). -/
def switchToAcc (a : Id) : M Unit := do
  let s ← get
  s.io.scrollTo 0
  modify fun s => { s with cur := a, me := (Kinds.Accepted.select s.comms a).getD s.me, page := PageId.home, backStack := [] }
  modify fun s => { s with ids := #[], total := 0, people := 0, limit := 64 }
  modify fun s => { s with heights := {}, rows := {}, selected := none, sheet := none }
  modify fun s => { s with asking := #[], hidden := [], chromeKey := "", pageKey := none }

def switchTo (i : Nat) : M Unit := do
  if let some m := (← get).comms[i]? then switchToAcc m.acc

/-- A link pasted or scanned: Choose a name, then Agree & join; but a link
to a community this device already holds (a member, or its join pending)
goes to that community instead, and joins nothing (libquiet's rule: a
node holds a community at most once). -/
def takeInvite (i : Community.Invite) : M Unit := do
  let s ← get
  if let some m := s.comms.find? (·.c == i.community) then
    s.io.textClear
    s.io.ime false
    modify fun s => { s with invite := none, field := "", refusal := none }
    switchToAcc m.acc
    say (if m.waiting then "You're already waiting to join this community." else "You're already in this community.")
    return
  s.io.textClear
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
  let seed ← Chaos.freshSeed n
  let w := Community.found (Device.ofSeed seed) n.toUTF8 myName.toUTF8 (← nowMin)
    (← Engine.Crypto.randomBytes 32) (← Engine.Crypto.randomBytes 32)
  if ← writeAll w then
    if let some a := acceptOf w then
      refreshComms
      switchToAcc a

/-- The node: started at launch, once (it speaks for every device whose
secret this store holds: Connection.hooks reads them all, and picks the
device for each community from its acceptance). Its first frame waits
for the local writer to be idle, so it boots from everything written. -/
def netStep : M Unit := do
  let s ← get
  let some (port, _) := s.netCfg | return
  if s.net.isSome then return
  if (← s.wr.busy.get) > 0 then return
  let listen := ((← listenHints).head?).getD s!"127.0.0.1:{port}".toUTF8
  let x : Engine.Sync.Sync SF (SqlM SF) :=
    { fam, cfg := { every := 30000, patience := 20000 },
      hooks := Connection.hooks fam Connection.sodium listen }
  try
    let db ← Db.openAt s.dbPath
    let r ← Engine.Sync.Runner.start x db 0 port.toUInt16
    (← get).io.log s!"node: listening on {r.port}, dialed as {(String.fromUTF8? listen).getD "?"}"
    modify fun s => { s with net := some r }
  catch e =>
    (← get).io.log s!"node: cannot start: {e}"
    modify fun s => { s with netCfg := none }

/-- The keys every commit since the last call filed (the writer's and the
node's alike), from the store's journal: read inside the frame's read
transaction, they are exactly the commits this frame's reads see. -/
def takeChanges : M (Array ByteArray) := do
  let s ← get
  let (ks, top) ← s.rd.changesSince s.seen
  modify fun s => { s with seen := top }
  s.wr.read.set top  -- taken: the writer may delete them
  return ks

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

/-- The people of the current community, for home's Direct messages:
its members (the Profile kind's), me first. -/
def refreshMembers : M Unit := do
  let s ← get
  if s.me.c.isEmpty || (s.page != .home && s.page != .profile && s.page != .removeConfirm) then return
  let (ms, _) ← Kinds.Profile.members s.me.c
  let out := ms.map fun (u, ds, p) => ((p.name, u == s.me.user), ds.any (s.peers.contains ·), u)
  let sorted := out.filter (·.1.2) ++ out.filter (!·.1.2)
  -- an admin: the founder's user (the community's id), or one granted admin
  let (ad, _, _) ← readList (Community.admin.byUser.query [s.me.c, s.me.user] (limit := some 0)) #[]
  modify fun s => { s with members := sorted.map (·.1), online := sorted.map (·.2.1),
                           memberIds := sorted.map (·.2.2),
                           amAdmin := !s.me.user.isEmpty && (s.me.user == s.me.c || ad.total > 0) }
  -- a removal being sent is done once its target is no longer present
  if let .sending u := (← get).removal then
    if !(← get).memberIds.contains u then
      let name := ((← get).profileOf.map (·.2.1)).getD "They"
      modify fun s => { s with removal := (Remove.step s.removal .done).1, profileOf := none,
                               page := .home, backStack := [] }
      say s!"Removed {name} from the community."

/-- The node's sessions now (Connection.sessions' kept ones): their
peers' device keys, every 30 frames. -/
def refreshPeers : M Unit := do
  let s ← get
  if s.net.isNone || s.frames % 30 != 0 then return
  let all ← ((Connection.allSessions : SqlM SF _)).run s.rd
  let k := Connection.kept all
  let ps := all.filterMap fun (cid, p, _) => if k.contains cid then some p else none
  if ps != s.peers then modify fun s => { s with peers := ps, pageKey := none }

/-- The requests to join the current community, read by the Request kind. -/
def refreshAsking : M Unit := do
  let s ← get
  if s.me.c.isEmpty then return
  let (out, _) ← Kinds.Request.waiting s.me.c
  modify fun s => { s with asking := out }

/-- My approval of request r (my device in this community signs it). -/
def approveReq (r : Id) : M Unit := do
  -- a fresh ephemeral secret for the wrap of the community's key to the
  -- requester's device
  let esk ← Engine.Crypto.randomBytes 32
  let s ← get
  -- the intent reads the request and its approvals: with mine, is the
  -- tally complete? then the admission goes in the same write
  let w ← ((Community.approveReq s.me.c r s.me.adm s.me.dev esk).liftL.run : SqlM SF _).run s.rd
  let _ ← writeAll w

/-- The current page's picture and taps (kept until what it shows changes). -/
def pageTitle : PageId → String × Bool
  | .getStarted => ("", false) | .create => ("", false) | .joinChoice => ("", false)
  | .openInvite => ("", false) | .paste => ("", false) | .scan => ("Join with QR code", true)
  | .name => ("", false) | .createName => ("", false)
  | .agree => ("Agree & join", false) | .waiting => ("", false) | .requests => ("Waiting to join", true)
  | .invite => ("Add members", true) | .switcher => ("Communities", true) | .chat => ("", false)
  | .profile => ("", true) | .removeConfirm => ("", true) | .duplicate => ("Warning!", true)
  | .home => ("", false)

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
    | .home => Pages.home f dm W h (if me.waiting then 0 else k.askingAll) #["general"] k.members k.online
    | .profile => let (n, isMe, removed, can) := k.profile; Pages.profile f dm W h n isMe removed can
    | .removeConfirm => Pages.removeConfirm f dm W h k.profile.1 k.removeStage k.removeWhy
    | .duplicate => Pages.duplicate f dm W h
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
  { page := s.page, W := s.W, h := viewH s, insetTop := s.insetTop, dim := s.dim, field := s.field,
    refusal := s.refusal, me := s.me.key, comms := s.comms.map (·.key),
    asking := (s.asking.filter fun r => !s.hidden.contains r.id).map (·.row), askingAll := s.asking.size,
    link := (s.links.find? (·.1 == s.me.acc)).map (·.2), members := s.members, online := s.online,
    backEmpty := s.backStack.isEmpty, camFrame := s.camFrame,
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
  | .joinCommunity => openPage .joinChoice
  | .createCommunity =>
    s.io.textClear
    modify fun s => { s with field := "" }
    openPage .create
    s.io.ime true
  | .inviteLink => openPage .openInvite
  | .qrCode => openPage .scan
  | .pasteLink =>
    s.io.textClear
    modify fun s => { s with field := "" }
    openPage .paste
    s.io.ime true
  | .field => s.io.ime true
  | .continue_ =>
    match s.page with
    | .create =>
      let n := s.field.trimAscii.toString
      if !n.isEmpty then
        s.io.textClear
        modify fun s => { s with field := "", newCommunity := n }
        openPage .createName
        s.io.ime true
    | .createName =>
      let me := s.field.trimAscii.toString
      if !me.isEmpty then
        s.io.ime false
        s.io.textClear
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
      let seed ← Chaos.freshSeed "join"
      -- the engine's join: nothing for a held community, the same request
      -- again for a stopped one, else a fresh join
      let (w, _) ← readView (Community.join i i.bearer (Device.ofSeed seed) s.joinName.toUTF8) #[]
      if ← writeAll w then
        s.io.textClear
        modify fun s => { s with invite := none, field := "", backStack := [] }
        refreshComms
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
        refreshComms
        if (← get).comms.isEmpty then
          modify fun s => { s with page := .getStarted, backStack := [], pageKey := none }
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
    modify fun s => { s with backStack := s.page :: s.backStack, page := .chat, pageKey := none, chromeKey := "" }
  | .none => pure ()

def closeSheet : M Unit := do
  let s ← get
  if (s.sheet.map (·.searching)).getD false then
    s.io.ime false
    s.io.textClear
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
                          bytes, key := ← Engine.Crypto.randomBytes 32, nonce := ← Engine.Crypto.randomBytes 24,
                          metaNonce := ← Engine.Crypto.randomBytes 24 } : Community.NewFile)]
  let nonce ← Engine.Crypto.randomBytes 24
  let (w, _) ← readView (Community.send s.me.c s.me.adm s.me.dev k nonce t.toUTF8 (← nowMin) files) #[]
  if ← writeAll w then
    s.io.textClear
    modify fun s => { s with text := "", sel := #[0, 0, 0, 0], chips := #[], chromeKey := "" }

/-- A photo prepared for sending: at most 2048 px a side, as QOI, with its
chip (a 64 dp square crop) and how much smaller than its raw pixels it is. -/
def preparePhoto (dm : Dim) (src : Image.Src) : ByteArray × Nat × Nat × Composer.Chip :=
  let (w, h) := if src.w ≤ 2048 && src.h ≤ 2048 then (src.w, src.h) else Image.fit src 2048 2048
  let px := Chaos.cropPx src 0 0 src.w src.h w h
  let bytes := Image.encode w h px
  let raw := w * h * 4
  let pct := 100 - bytes.size * 100 / max raw 1
  let thumb := Image.square src (dm.px 64) Row.bg
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
      if sh.searching then s.io.ime false; s.io.textClear
      let sh' := { sh with catalog := false, searching := false, query := "" }
      modify fun s => { s with sheet := some sh' }
    | .search =>
      s.io.ime true
      modify fun s => { s with sheet := some { sh with searching := true } }
    | .tone t => modify fun s => { s with sheet := some { sh with tone := t } }
    | .category k =>
      if sh.searching then s.io.ime false; s.io.textClear
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

def onTap (r : Region) (x y : Nat) (long : Bool) : M Unit := do
  let s ← get
  -- a tap puts a standing notice away
  if !s.notices.isEmpty then
    modify fun s => { s with notices := s.notices.drop 1 }
    return
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

def onEvent : Event → M Bool
  | .close => return false
  | .tap r x y => do onTap r x.toNat y.toNat false; return true
  | .long r x y => do onTap r x.toNat y.toNat true; return true
  | .text => do
    let (t, sel) ← (← get).io.text
    if (← get).page == .create || (← get).page == .createName || (← get).page == .paste || (← get).page == .name then
      modify fun s => { s with field := t, refusal := none, pageKey := none }
      return true
    match (← get).sheet with
    | some sh =>
      if sh.searching then modify fun s => { s with sheet := some { sh with query := t, scroll := 0 } }
    | none =>
      modify fun s => { s with text := t, sel := if sel.size == 4 then sel else #[0, 0, 0, 0] }
    return true
  | .send => do
    if (← get).page == .create || (← get).page == .createName || (← get).page == .paste || (← get).page == .name then
      onPageAct .continue_
      return true
    sendNow
    return true
  | .ime h => do modify fun s => { s with imeH := h.toNat }; return true
  | .scrolling _ => return true
  | .drag ph x y => do onSheetDrag ph.toNat x.toNat y.toNat; return true

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
    let top := newestCounter s
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
  | "open" =>
    let p : Option PageId := match ws[1]? with
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
  let backdrop := Paint.mixC Row.bg 0 154
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
  let blank := solid Sheet.panel s.W
  let line (k : Nat) : ByteArray :=
    match rows[k / g.key]? with
    | some b => b.rows[k % g.key]?.getD blank
    | none => blank
  let top := Sheet.catTop s.font s.dim s.W c backdrop sh.query sh.searching sh.tone sh.cat
  let bot := Sheet.catBot s.font s.dim s.W c sh.cat sh.searching
  return ⟨s.W, SheetGeom.compose top.rows line g.vh sh.scroll bot.rows⟩

/-- The toast, if one stands, over the middle of the viewport's rows of a
list frame (new rows: the ones under it are shared and stay). -/
def withToast (s : St) (fr : Array ByteArray) (vh : Nat) : Array ByteArray := Id.run do
  -- a standing notice outranks a passing toast
  let some t := s.notices.head? <|> (s.toast.bind fun (t, upto) => if s.frames > upto then none else some t)
    | return fr
  let tb := Pages.toast s.font s.dim s.W t
  let x := (s.W - tb.w) / 2
  let r0 := over + (vh - tb.h) / 2
  let mut fr := fr
  for k in [0:tb.h] do
    if r0 + k < fr.size then
      fr := fr.set! (r0 + k) (tb.rows[k]!.copySlice 0 fr[r0 + k]! (4 * x) (4 * tb.w))
  return fr

/-- One frame; the twin's events for the next one, or none when the
window closes. -/
def frame (evs : List Event) : M (Option (List Event)) := do
  let t0 ← (← get).io.nowUs
  -- 0. the screen and its insets, as of now (they can arrive after the
  -- first frame, and change with rotation or the navigation mode)
  let sc ← (← get).io.screen
  let hs := (sc[1]?.map (·.toNat)).getD (← get).Hs
  let it := (sc[2]?.map (·.toNat)).getD (← get).insetTop
  let ib := (sc[3]?.map (·.toNat)).getD (← get).insetBot
  modify fun s => { s with Hs := hs, insetTop := it, insetBot := ib }
  -- 1. notices
  let s ← get
  let ns ← takeChanges
  if !ns.isEmpty then
    let decided := s.out.filter fun p => ns.contains (opKey p.op.id)
    -- the store changed: an image waiting for its chunk ops tries again now
    modify fun s => { s with
      live := s.live.notice ns
      out := s.out.filter fun p => !ns.contains (opKey p.op.id)
      imgRetry := {} }
    if !decided.isEmpty then noticeLocal (decided.toList.flatMap fun p => p.keys)
  chaosStep
  let tNotices ← (← get).io.nowUs
  -- 2. events and commands
  for e in evs do
    if !(← onEvent e) then return none
  let cmds ← (← get).io.ctlPoll
  modify fun s => { s with ctl := s.ctl ++ cmds }
  let mut queue := (← get).ctl
  while !queue.isEmpty do
    if ← command queue[0]! then queue := queue.extract 1 queue.size else break
  modify fun s => { s with ctl := queue }
  let tCommands ← (← get).io.nowUs
  -- 3. the list's ids and counts
  let s ← get
  -- the conversation: the messages this device can read (Community.readable,
  -- a union of message.byKey over the keys it holds); one it cannot read
  -- is not in it, and appears when its key's wrap opens (the key's list is
  -- one the view reads)
  let (a, _) ← readView (Community.readable s.me.c (limit := some s.limit)) #[]
  modify fun s => { s with ids := (a.rows.map (·.1)).toArray, fetched := a.rows.length, total := a.total }
  let s ← get
  -- people: the present members (admitted, not removed), each once
  let (ps, _) ← readView (Kinds.Profile.present s.me.c) #[]
  modify fun s => { s with people := ps.length }
  let tIds ← (← get).io.nowUs
  -- 4. the offset, and the rows the frame and the fetch distance need
  let s ← get
  let (bots0, ch0) := bottoms s
  let b ← s.io.scroll ch0.toUInt32 (viewH s).toUInt32
  let b := b.toNat
  -- the anchor: the row at the viewport's bottom edge, and how far into it
  let anchor := (rowAt s b).map fun (x, _) => (x, b - (bots0[s.ids.findIdx? (·.2 == x) |>.getD 0]?.getD 0))
  let vh := viewH s
  let fetch := vh
  let lo := if b ≥ over + fetch then b - over - fetch else 0
  let hi := b + vh + over + fetch
  for i in [0:s.ids.size] do
    let bot := bots0[i]!
    if bot > hi then break
    if bot + heightOf s s.ids[i]!.2 ≥ lo then mount s.ids[i]!.2
  -- more ids, if the loaded ones end below what the fetch distance needs
  let s ← get
  let (bots, _) := bottoms s
  let loadedTop := match s.ids.back? with
    | some (_, x) => bots.back!.add (heightOf s x)
    | none => bottomPad
  if loadedTop < hi + 2 * est && s.ids.size < s.total && s.fetched ≥ s.limit then
    -- enough more ids, at the estimate, to reach past the fetch distance
    let more := (hi + 2 * est - loadedTop) / est + 64
    modify fun s => { s with limit := s.limit + more }
  let tMount ← (← get).io.nowUs
  -- 5. keep the anchor still (unless pinned to the newest)
  let mut b := b
  if b > 4 then
    if let some (x, off) := anchor then
      if let some i := s.ids.findIdx? (·.2 == x) then
        let b' := bots[i]! + off
        if b' != b then
          s.io.scrollBy (b'.toFloat - b.toFloat)
          b := b'
  -- 6. paint what the frame shows
  let flo := if b ≥ over then b - over else 0
  let fhi := b + vh + over
  for i in [0:s.ids.size] do
    let bot := bots[i]!
    if bot > fhi then break
    if bot + heightOf s s.ids[i]!.2 ≥ flo then paintRow s.ids[i]!.2
  let tPaint ← (← get).io.nowUs
  -- forget rows far away (their heights stay)
  let s ← get
  if s.frames % 30 == 0 then
    let keepLo := if b ≥ 4 * vh then b - 4 * vh else 0
    let keepHi := b + 5 * vh
    let mut keep : Std.HashMap Id Unit := {}
    for i in [0:s.ids.size] do
      let bot := bots[i]!
      if bot ≤ keepHi && bot + heightOf s s.ids[i]!.2 ≥ keepLo then keep := keep.insert s.ids[i]!.2 ()
    let rows := s.rows.filter fun x _ => keep.contains x
    let deps := rows.fold (fun acc _ r => r.deps.foldl (fun a q => a.insert q ()) acc) ({} : Std.HashMap Q Unit)
    modify fun s => { s with rows, live := s.live.keep fun q => match q with
      | .list _ => true
      | q => deps.contains q }
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
  refreshPeers
  refreshMembers
  scanStep
  netStep
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
    let (w, _) ← readView (Community.unwrap m.c m.dev) #[]
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
    modify fun s => { s with page := .waiting, pageKey := none }
  if s.page == .waiting && !s.me.waiting then
    modify fun s => { s with page := .home, pageKey := none }
    say "You're in."
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
    let evs ← s.io.frame shown 0 over.toUInt32 s.topBmp.rows s.botBmp.rows true
    return some (Event.decode evs)
  -- 7. chrome and the frame
  let s ← get
  let sheetKey := match s.sheet, s.selected with
    | some sh, some m => s!"{sh.catalog}|{sh.cat}|{sh.tone}|{sh.query}|{sh.searching}|{sh.scroll}|{mineOn s m}"
    | _, _ => ""
  let key := s!"{s.W}|{s.insetTop}|{s.total}|{s.people}|{s.text}|{s.sel}|{sheetKey}|{s.me.name}|{s.asking.size}|{s.chips.size}"
  if key != s.chromeKey then
    let bot ← match s.sheet, s.selected with
      | some sh, some m => sheetBitmap sh (mineOn s m)
      | _, _ => pure (composer s)
    modify fun s => { s with topBmp := header s, botBmp := bot, chromeKey := key }
  let s ← get
  let fr := withToast s (listFrame s b bots) (viewH s)
  let t1 ← s.io.nowUs
  slow t1
  let times := (if s.times.size ≥ 600 then s.times.extract 300 s.times.size else s.times).push (t1 - t0).toNat
  modify fun s => { s with b := b, frames := s.frames + 1, times := times }
  let evs ← s.io.frame fr b.toUInt32 over.toUInt32 s.topBmp.rows s.botBmp.rows false
  return some (Event.decode evs)

/-- One frame, in one read transaction: every read it makes, and the
notices it takes (`takeChanges`, its first read), are of one moment of the
store, so no part of the screen is newer than another. -/
def step (evs : List Event) : M (Option (List Event)) := do
  let rd := (← get).rd
  rd.exec "BEGIN"
  try
    let r ← frame evs
    rd.exec "COMMIT"
    return r
  catch e =>
    rd.exec "ROLLBACK"
    throw e

partial def loop (evs : List Event) : M Unit := do
  match ← step evs with
  | none => pure ()
  | some evs => loop evs

/-- The app's state at start: the window's size, the font, both
connections, this node's identity (the community founded on first run). -/
def start (io : Io) (screen : Array UInt32) (dbPath : String) (net : Option (Nat × Bool) := none) :
    IO St := do
  let W := (screen[0]?.getD 1080).toNat
  let Hs := (screen[1]?.getD 2400).toNat
  let font ← Font.load
  let rd ← openDb dbPath
  let wr ← Writer.start dbPath
  -- the communities are this device's accepted facts: read them once
  -- here to choose the first page
  let probe : St := { io := io, W := W, Hs := Hs, insetTop := 0, insetBot := 0, font := font, bgRow := .empty, rd := rd, wr := wr, me := default }
  let ((all, _), _) ← (Kinds.Accepted.read : M _).run probe
  let comms := Kinds.Accepted.listed all
  let me := comms[0]?.getD default
  let catalog ← match ← (Sheet.loadCatalog).toBaseIO with
    | .ok c => pure c
    | .error e => do IO.eprintln s!"no emoji catalogue: {e}"; pure #[]
  return { io := io, W := W, Hs := Hs, insetTop := (screen[2]?.getD 0).toNat, catalog := catalog,
           dim := ⟨(screen[4]?.getD 420).toNat, font.cell⟩,
           insetBot := (screen[3]?.getD 0).toNat, font := font, bgRow := solid Row.bg W, rd := rd,
           wr := wr, me := me, comms := comms, cur := me.acc, page := if comms.isEmpty then .getStarted else .home,
           -- a removal already in the store at launch is not announced
           goneSeen := (all.toList.filter (·.removed)).map (·.acc),
           dbPath := dbPath, netCfg := net }

end App
