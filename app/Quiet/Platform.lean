/-
The seam between the app and the OS, the same on every platform. Each
twin implements these externs: android/twin (NativeActivity plus a small
Java activity for the keyboard and insets) and host/ (headless, for
tests and CI).

The OS owns three things: scrolling (its physics, its overscroll), the
keyboard (its text, its composition, its animation), and the window's
insets. The app owns every pixel, as three frames:

- **the list**, slid by the compositor at every vsync, so motion is even
  whether or not the app finished a frame in time;
- **the header** (`top`), pinned to the screen's top edge;
- **the composer** (`bot`), pinned above the navigation bar, or above the
  keyboard while the keyboard is open, following its animation frame by
  frame.

A frame is an array of pixel rows, 4 bytes a pixel in R G B X order, each
row exactly `w` pixels wide. A row that is the same object as a row of the
last frame of that kind (at the place the offset change moves it to) is
not copied again: rows are immutable, so the twin holds the last frame
while it compares.

**The list is bottom-anchored.** Its offset `b` is the distance in pixels
from the newest content's bottom edge up to the viewport's bottom edge: 0
is pinned to the newest message, and larger values show older content.
Rows measured late (above the viewport) therefore never move what is on
screen. The viewport is the screen between the header and the composer;
`viewH` is its height with the keyboard closed. The list frame is
`viewH + 2 * over` rows high, `over` rows beyond each end: frame row r,
drawn for offset b, shows the content at distance
`b + viewH + over - 1 - r` above the content's end (negative distances
and distances past the content are background). The twin places that
frame for the vsync's offset and shifts it up by the keyboard's height
above the navigation bar, so the newest messages ride up with the
keyboard.
-/
namespace Platform

/-- Waits for the window; answers `[w, h, insetTop, insetBottom, dpi]` in
pixels: the surface's size, the status bar's and navigation bar's
heights, and the display's density in dots per inch. -/
@[extern "lq_screen"] opaque screen : IO (Array UInt32)

/-- The list's offset for the frame about to be drawn (bottom-anchored,
see above): the latest vsync's, predicted on to when the frame will be
shown during a fling. The scroller's range is
`0 .. contentH - viewH'`, where viewH' is viewH less the keyboard's
height above the navigation bar. -/
@[extern "lq_scroll"] opaque scroll (contentH viewH : UInt32) : IO UInt32

/-- Moves the offset by d pixels (positive: towards older content), as if
the content above or below the viewport had grown, keeping a fling
going. Used when rows measured late change the content's height below
the viewport's anchor, or a new message arrives while not pinned. -/
@[extern "lq_scroll_by"] opaque scrollBy (d : Float) : IO Unit

/-- Sets the offset, stopping any fling (a jump: to the newest, to a
message). -/
@[extern "lq_scroll_to"] opaque scrollTo (b : Float) : IO Unit

/-- Shows a frame: the list drawn at offset b (`list.size` must be
`viewH + 2 * over`), the header (its height is `top.size`) and the
composer (`bot.size`). The header is placed at the screen's top; the
composer at `h - bot.size - max(insetBottom, keyboard)`. The viewport is
the rows between them, so `viewH = h - top.size - bot.size - insetBottom`.
Waits for the display's pace. `pin`: the list frame is a page, drawn from
its top at offset 0, and is placed pinned: not slid, not lifted by the
keyboard (Geometry.Seam.pinned; pinned_visible, pinned_tap). Answers the
events since the last frame, four words each (`Event.decode`). -/
@[extern "lq_frame"] opaque frame (list : @& Array ByteArray) (b over : UInt32)
  (top bot : @& Array ByteArray) (pin : Bool) : IO (Array UInt32)

/-- The composer's text as the keyboard left it: the text, and
`[selStart, selEnd, compStart, compEnd]` in characters (code points);
compStart = compEnd when nothing is being composed (an IME's underlined
candidate). -/
@[extern "lq_text"] opaque text : IO (String × Array UInt32)

/-- Opens (true) or closes the keyboard on the composer. -/
@[extern "lq_ime"] opaque ime (show_ : Bool) : IO Unit

/-- Empties the composer's text (after a send). -/
@[extern "lq_text_clear"] opaque textClear : IO Unit

/-- Puts text on the system clipboard. -/
@[extern "lq_copy"] opaque copy (text : @& String) : IO Unit

/-- Control commands received since the last call, one line each (the
Android twin listens on the abstract socket `@leanquiet`; the host twin
reads them from its script). -/
@[extern "lq_ctl_poll"] opaque ctlPoll : IO (Array String)

/-- Answers the oldest unanswered control command: one line, sent back
on the connection it came from. -/
@[extern "lq_ctl_reply"] opaque ctlReply (s : @& String) : IO Unit

/-- Shows the camera's preview in the screen rectangle (x, y, w, h), in
pixels, and starts its frames; w = 0 stops it and takes the preview away.
The first start asks for the camera permission. -/
@[extern "lq_scan"] opaque scan (x y w h : UInt32) : IO Unit

/-- The newest camera frame since the last call, as its luma (Y) plane:
`[w, h, stride]` and the bytes, or `(#[], empty)` when there is none. The
app decodes it (lean-qr's `Qr.decodeLuma`), off its own thread. -/
@[extern "lq_luma"] opaque luma : IO (Array UInt32 × ByteArray)

/-- Microseconds of a monotonic clock (CLOCK_MONOTONIC), shared with the twin's logs. -/
@[extern "lq_now_us"] opaque nowUs : IO UInt64

end Platform

namespace App

/-- Where a touch landed. -/
inductive Region where
  | list | header | composer
  deriving BEq, Repr

/-- What a frame's events can be. -/
inductive Event where
  | close
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
  phase 0 down, 1 move, 2 up; (x, y) within the composer. The app scrolls
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
  return out.toList

end App
