/-
The OS seam. Lean computes placement (Surface), clamps signed offset
samples, and classifies raw input (Input) through Session.present.
Native code owns pixel copies, OS text editing and scroll physics. It
calls the compiled Slide helpers at each vsync to move the published
list and fill exposed rows with Lean's holdLine tile. Fresh pixels arrive
with the next Lean frame; geometry and input policy remain Lean's.
-/
namespace Platform

/-- Waits for the window; answers `[w, h, insetTop, insetBottom, dpi]` in
pixels, followed by system appearance (0 light, 1 dark): the surface's size, the status bar's and navigation bar's
heights, and the display's density in dots per inch. -/
@[extern "lq_screen"] opaque screen : IO (Array UInt32)

/-- Apply Lean's effective appearance to OS bar icons and the window fill. -/
@[extern "lq_appearance"] opaque appearance (dark : Bool) (background : UInt32) : IO Unit

/-- A signed OS physics sample in physical pixels. `viewH` is the effective
viewport with the keyboard open. Lean clamps before using the sample. -/
@[extern "lq_scroll"] opaque scroll (contentH viewH : UInt32) : IO Float

/-- Moves the offset by d pixels (positive: towards older content), as if
the content above or below the viewport had grown, keeping a fling
going. Used when rows measured late change the content's height below
the viewport's anchor, or a new message arrives while not pinned. -/
@[extern "lq_scroll_by"] opaque scrollBy (d : Float) : IO Unit

/-- Sets the offset, stopping any fling (a jump: to the newest, to a
message). -/
@[extern "lq_scroll_to"] opaque scrollTo (b : Float) : IO Unit

/-- Publish pixel buffers and Surface's rectangles together. The final
placement fields are a frame serial and Lean's last list tap for diagnostics.
The hold buffer repeats the exact tile used by listFrame. Raw touches
carry the displayed serial and translation so Lean
uses the geometry seen at acquisition. Returns eight-word raw records
(Input.decode). `pin` distinguishes pages, whose position is Seam.pinned. -/
@[extern "lq_frame"] opaque frame (list : @& Array ByteArray) (b over : UInt32)
  (top bot : @& Array ByteArray) (pin : Bool) (placement : @& Array UInt32) (hold : @& Array ByteArray) : IO (Array UInt32)

/-- List samples accepted by Lean, encoded as raw eight-word records. -/
@[extern "lq_motion"] opaque motion (samples : @& Array UInt32) : IO Unit

/-- The composer's text as the keyboard left it: the text, and
`[selStart, selEnd, compStart, compEnd]` in characters (code points);
compStart = compEnd when nothing is being composed (an IME's underlined
candidate). -/
@[extern "lq_text"] opaque text : IO (String × Array UInt32)

/-- Opens (true) or closes the keyboard on the composer. -/
@[extern "lq_ime"] opaque ime (show_ : Bool) : IO Unit

/-- The native field's text becomes t (caret at its end); left alone if
it already is t. -/
@[extern "lq_set_text"] opaque setText : @& String → IO Unit

/-- Puts text on the system clipboard. -/
@[extern "lq_copy"] opaque copy (text : @& String) : IO Unit

/-- Control commands received since the last call, one line each (the
Android twin listens on the abstract socket `@leanquiet`; the host twin
reads them from its script). -/
@[extern "lq_ctl_poll"] opaque ctlPoll : IO (Array String)

/-- Answers the oldest unanswered control command: one line, sent back
on the connection it came from. -/
@[extern "lq_ctl_reply"] opaque ctlReply (s : @& String) : IO Unit

/-- Turns the back camera on (its frames start) or off. The first start
asks for the camera permission. The app draws the preview itself
(Camera.preview). -/
@[extern "lq_scan"] opaque scan (on : Bool) : IO Unit

/-- The newest camera frame since the last call, as its luma (Y) plane:
`[w, h, stride, sensor orientation in degrees]` and the bytes, or
`(#[], empty)` when there is none. The app decodes it (lean-qr's
`Qr.decodeLuma`), off its own thread. -/
@[extern "lq_luma"] opaque luma : IO (Array UInt32 × ByteArray)

/-- Microseconds of a monotonic clock (CLOCK_MONOTONIC), shared with the twin's logs. -/
@[extern "lq_now_us"] opaque nowUs : IO UInt64

/-- The local timezone's offset from UTC now, in minutes (localtime_r's
tm_gmtoff), for showing times. -/
@[extern "lq_tz_min"] opaque tzMin : IO Int32

/-- A line for the platform's log: logcat (tag "lean") on Android, the
device console on iOS, stderr on the host. -/
@[extern "lq_log"] opaque log : @& String → IO Unit

/-- Events without submitting a frame; usable while suspended. -/
@[extern "lq_poll"] opaque poll : IO (Array UInt32)
/-- Cold/warm OS URL deliveries, independent of the debug channel. -/
@[extern "lq_links"] opaque links : IO (Array String)

end Platform

namespace App

/-- Where a touch landed. -/
inductive Region where
  | list | header | composer
  deriving BEq, Repr

/-- What a frame's events can be. -/
inductive Event where
  | close
  | background
  | foreground
  | surface (present : Bool)
  | resize
  | deepLink (url : String)
  /-- A tap: a press and release without a drag. In the list, `y` is the
  distance above the content's end (the same coordinate as the list
  frame's rows); in the header or composer, the row within it. -/
  | tap (r : Region) (x y : UInt32)
  /-- A press held 500 ms without a drag, reported while still held (its
  release is then no tap). -/
  | long (r : Region) (x y : UInt32)
  /-- The composer's text or selection changed (read it with
  `Platform.text`). -/
  | text
  /-- The keyboard's send action. -/
  | send
  /-- The keyboard's height changed (0 when closed), in pixels. -/
  | ime (h : UInt32)
  /-- The OS scroll started (a finger down on the list) or settled. -/
  | scrolling (on : Bool)
  /-- A finger that went down on the composer (or the sheet in its place):
  phase 0 down, 1 move, 2 up, 3 cancel; (x, y) within the composer. The app scrolls
  what is there itself. -/
  | drag (phase x y : UInt32)
  deriving BEq, Repr

def Region.ofWord : UInt32 → Region
  | 1 => .header
  | 2 => .composer
  | _ => .list

/-- The twin's events as words, four each (kind, a, b, c): 1 close;
2 tap (region, x, y); 3 long press (region, x, y); 4 text; 5 send;
6 ime (height); 7 scrolling (on); 8 drag (phase, x, y). An unknown kind
is skipped. -/
def Event.decode (ws : Array UInt32) : List Event := Id.run do
  let mut out := #[]
  for i in [0:ws.size / 4] do
    let k := ws[4 * i]!
    let a := ws[4 * i + 1]!
    let b := ws[4 * i + 2]!
    let c := ws[4 * i + 3]!
    if k == 1 then out := out.push .close
    else if k == 2 then out := out.push (.tap (Region.ofWord a) b c)
    else if k == 3 then out := out.push (.long (Region.ofWord a) b c)
    else if k == 4 then out := out.push .text
    else if k == 5 then out := out.push .send
    else if k == 6 then out := out.push (.ime a)
    else if k == 7 then out := out.push (.scrolling (a != 0))
    else if k == 8 then out := out.push (.drag a b c)
    else if k == 9 then out := out.push .background
    else if k == 10 then out := out.push .foreground
    else if k == 11 then out := out.push (.surface (a != 0))
    else if k == 12 then out := out.push .resize
  return out.toList

end App
