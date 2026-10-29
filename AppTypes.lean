/- App types shared by the root and lifecycle hooks. Existing fields retain their meaning. -/
import engine.renderer.Data
import ops.app.Chaos
import ops.app.ReaderLife
import ops.app.NodeOffer
import engine.renderer.Row
import engine.renderer.Geometry
import engine.renderer.Nav
import engine.renderer.Cover
import engine.renderer.Session
import engine.renderer.Sheet
import engine.renderer.SafeFrame
import engine.renderer.Toast
import engine.renderer.Appearance
import engine.renderer.ThemeStore
import ops.app.Pages
import ops.app.Composer
import ops.community.link.View
import engine.renderer.Camera
import ops.app.Remove
import ops.community.message.View
import ops.community.membership.RequestView
import ops.app.Pics
import Std.Data.HashMap

namespace App
open Engine Community Data Paint Font Row

/-- The platform, as the app uses it. -/
structure Io where
  screen : IO (Array UInt32)
  scroll : UInt32 → UInt32 → IO Float
  scrollBy : Float → IO Unit
  scrollTo : Float → IO Unit
  frame : Session.Show
  text : IO (String × Array UInt32)
  ime : Bool → IO Unit
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
  /-- The native text field's text becomes t (left alone if it is t). -/
  setText : String → IO Unit := fun _ => pure ()
  poll : IO (Array UInt32) := pure #[]
  links : IO (Array String) := pure #[]
  motion : Array UInt32 → IO Unit := fun _ => pure ()
  appearance : Bool → UInt32 → IO Unit := fun _ _ => pure ()
  bars : UInt32 → UInt32 → Bool → Bool → IO Unit := fun _ _ _ _ => pure ()

/-- How far beyond each end of the viewport the list frame is drawn. -/
def over : Nat := 1024
/-- A row's height before it is measured. -/
def est : Nat := 150
/-- A window's rows on each side of its anchor. -/
def half : Nat := 100
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
  /-- The board version its data came from (Reader). -/
  bver : Nat := 0
  /-- The shown paint darkened, for behind the reaction tray, and the
  version it was made from. -/
  dimmed : Option (Task Bitmap) := none
  dimVer : Nat := 0
  dimShown : Option Bitmap := none

abbrev ImgKey := Pics.Key

/-- Which page is up: a conversation, or one of libquiet's other screens. -/
inductive PageId where
  | home | chat | getStarted | create | createName | joinChoice | openInvite | paste | scan | name | agree | waiting
  | requests | invite | switcher | profile | removeConfirm | duplicate | you | appearance | label
  deriving DecidableEq, Repr, Inhabited

/-- Every page (Nav.depth: back reaches a root in fewer steps than this). -/
def PageId.all : List PageId :=
  [.home, .chat, .getStarted, .create, .createName, .joinChoice, .openInvite, .paste, .scan, .name, .agree,
   .waiting, .requests, .invite, .switcher, .profile, .removeConfirm, .duplicate, .you, .appearance, .label]

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
  setting : Theme.Setting := .system
  W : Nat
  h : Nat
  insetTop : Nat
  dim : Dim
  field : String
  /-- The full label shown (Full label), and its page. -/
  labelText : String := ""
  labelPage : Nat := 0
  refusal : Option String
  me : Kinds.Accepted.Key
  comms : Array Kinds.Accepted.Key
  /-- The join requests shown (not hidden), and how many there are in all. -/
  asking : Array Pages.Asking
  askingAll : Nat
  link : Option String
  members : Array (String × Bool)
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
  theme : Theme.State := {}
  window : Safe.Input := ⟨1080, 2400, {}, {}, {}⟩
  nowMs : Nat := 0
  noticeClock : Option (String × Nat) := none
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
  /-- The node starting, off the frame (its connection opened and its
  first reads made on a thread of its own). -/
  netBoot : Option (Task (Except IO.Error Engine.Sync.Runner)) := none
  /-- Writes the node's inbound channel could not take yet, in order. -/
  toNode : Array (List Op) := #[]
  /-- The journal's newest row this app has taken notice of. -/
  seen : Nat := 0
  me : Chaos.Me
  live : Live := {}
  /-- The reads the frame made since it last forgot the others: what it
  keeps watching (Screen.screen_subs). -/
  touched : Std.HashSet Q := {}
  out : Array Pending := #[]
  /-- What the native text field holds, as last set or reported. -/
  native : String := ""
  /-- The reader's board, and the frame's wants of it (Reader): the
  conversation's ids and rows are read there, not on the frame. -/
  sh : Reader.Shared
  /-- The reader's state while the frame runs its passes itself (no
  reader thread: the headless twins); none once a thread runs them. -/
  rst : Option Reader.St := none
  /-- The window of the conversation loaded (Reader.Want.window): its
  anchor (none: the newest), its rows newest first, and how many
  readable messages are newer and older than it, counted, not read: they
  take `est` each, as placeholders, until a window holds them. -/
  anchor : Option Pos := none
  ids : Array Pos := #[]
  newer : Nat := 0
  older : Nat := 0
  total : Nat := 0
  people : Nat := 0
  heights : Std.HashMap Id Nat := {}
  rows : Std.HashMap Id RowSt := {}
  imgs : Std.HashMap ImgKey (Task Bitmap) := {}
  /-- When an image whose chunks were not all on the board may be tried
  again (a frame number; Pics.retryLater). -/
  imgRetry : Std.HashMap ImgKey Nat := {}
  /-- The chunk read of each key waiting in imgRetry: still wanted while
  it waits, so the reader reads it when its chunks land and the wait is
  cleared (`takeBoard`); without it, the want lapses with the frame that
  asked, and the picture waits out its two seconds. -/
  retryWants : Std.HashMap ImgKey Reader.Want := {}
  /-- The chunk read `slicesOf` asked for last: Pics.retryLater files it
  under its key. -/
  lastSlices : Option Reader.Want := none
  /-- The chunk reads this frame's paints asked for (Reader.Want.slices):
  the reader's wants from the next frame. -/
  picWants : Array Reader.Want := #[]
  selected : Option Id := none
  b : Nat := 0
  imeH : Nat := 0
  input : Input.State := {}
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
  /-- A toast and the frame it goes at (libquiet's: centred, about 3 s). -/
  toast : Option (String × Nat) := none
  page : PageId := .chat
  backStack : List PageId := []
  /-- A page's one-line field (the keyboard's text while a page shows one). -/
  field : String := ""
  /-- The full label a long press opened (Full label), and its page. -/
  labelText : String := ""
  labelPage : Nat := 0
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

  life : Lifecycle.Mount := {}
  owner : Id := .empty
  active : Bool := true
  surface : Bool := true
  /-- A message and its top-edge distance above the viewport bottom.
  `anchor` above remains the reader's window position. -/
  mark : Option (Id × Nat) := none
  restoreAnchor : Bool := false
  drafts : List (Id × String × List ByteArray) := []
  saved : Option Lifecycle.Checkpoint := none
  pendingLinks : List String := []
  queuedWrites : List ByteArray := []
  mountedPage : Option (PageId × Id) := none
  reader : Option Reader.Worker := none
  threaded : Bool := false
  /-- Teardown may outlive its deadline; these handles stay owned until
  finished. Foreground never starts another node before netStop finishes. -/
  netStop : Option (Task (Except IO.Error Unit)) := none
  readerStop : Option Reader.Worker := none
  retiredBoard : Option Reader.Shared := none
  paintStop : Array (Task Unit) := #[]

instance : Inhabited Io := ⟨⟨pure #[1080, 2400, 0, 0, 420], fun _ _ => pure 0, fun _ => pure (), fun _ => pure (), fun _ _ _ _ _ _ _ _ => pure #[],
  pure ("", #[]), fun _ => pure (), fun _ => pure (), pure #[], fun _ => pure (), pure 0, pure (0, 0), fun _ => pure (), pure (#[], .empty), IO.eprintln, fun _ => pure (), pure #[], pure #[], fun _ => pure (), fun _ _ => pure (), fun _ _ _ _ => pure ()⟩⟩

abbrev M := StateT St IO

def c (s : St) : Id := s.me.c

/-- The page and the back stack, as Nav has them. -/
def St.nav (s : St) : Nav.Nav PageId := ⟨s.page, s.backStack⟩

/-- The page and the back stack, set to a Nav step's. -/
def St.withNav (s : St) (n : Nav.Nav PageId) : St := { s with page := n.page, backStack := n.stack }


end App
