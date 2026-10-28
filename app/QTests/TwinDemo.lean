/-
A demo of the platform seam alone (no engine, no font), for checking a
twin by eye and by control commands:

- the list is 300 bands, 150 px each, the newest at the bottom; each band
  shows its number in block digits; a tap toggles a band white;
- the header (below the status bar) shows the keyboard's height as a bar;
- the composer shows the text's length as a bar and the cursor (selStart)
  as a tick; a tap on it opens the keyboard, a tap on the header closes
  it; the keyboard's send (or the `send` command) appends a band.

Control commands: `ping` (pong), `state` (offset, keyboard, bands, text),
`send <text>` (as the keyboard's send), `ime on|off`, `to <b>`, `by <d>`.
-/
import Quiet.Platform

open App

namespace Demo

def BandH : Nat := 150
def Over : UInt32 := 600

/-- A solid row w pixels wide, R G B X. -/
def solid (w : Nat) (c : UInt32) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity (4 * w)
  for _ in [0:w] do
    b := b.push (c >>> 16).toUInt8 |>.push (c >>> 8).toUInt8 |>.push c.toUInt8 |>.push 255
  return b

/-- A row of colour c with [x0, x1) in colour d. -/
def withBar (w : Nat) (c d : UInt32) (x0 x1 : Nat) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity (4 * w)
  for x in [0:w] do
    let k := if x ≥ x0 && x < x1 then d else c
    b := b.push (k >>> 16).toUInt8 |>.push (k >>> 8).toUInt8 |>.push k.toUInt8 |>.push 255
  return b

/-- 3 x 5 block digits, a row of three bits per line, top line first. -/
def digit : Nat → Array Nat
  | 0 => #[7, 5, 5, 5, 7] | 1 => #[2, 6, 2, 2, 7] | 2 => #[7, 1, 7, 4, 7]
  | 3 => #[7, 1, 7, 1, 7] | 4 => #[5, 5, 7, 1, 1] | 5 => #[7, 4, 7, 1, 7]
  | 6 => #[7, 4, 7, 5, 7] | 7 => #[7, 1, 1, 1, 1] | 8 => #[7, 5, 7, 5, 7]
  | _ => #[7, 5, 7, 1, 7]

def digits (n : Nat) : List Nat := (toString n).toList.map fun c => c.toNat - 48

/-- Line l (0..4) of n's digits: block columns lit, 16 px a block. -/
def digitRow (w : Nat) (n : Nat) (l : Nat) (c ink : UInt32) : ByteArray := Id.run do
  let ds := digits n
  let mut b := ByteArray.emptyWithCapacity (4 * w)
  for x in [0:w] do
    let col := (x - 40) / 16
    let lit := x ≥ 40 && col / 4 < ds.length && col % 4 < 3 &&
      ((digit (ds.getD (col / 4) 0))[l]! >>> (2 - col % 4)) &&& 1 == 1
    let k := if lit then ink else c
    b := b.push (k >>> 16).toUInt8 |>.push (k >>> 8).toUInt8 |>.push k.toUInt8 |>.push 255
  return b

def hue (k : Nat) : UInt32 :=
  let r := (k * 53) % 200 + 40
  let g := (k * 97) % 200 + 40
  let bl := (k * 151) % 200 + 40
  (r.toUInt32 <<< 16) ||| (g.toUInt32 <<< 8) ||| bl.toUInt32

/-- A band's rows: 6 px of separator, then its colour, its number's five
block lines (16 px each) from line 40. Few distinct row objects, so
frames share them and the twin copies little. -/
def bandRows (w : Nat) (k : Nat) (white : Bool) : Array ByteArray := Id.run do
  let c := if white then 0xF0F0F0 else hue k
  let ink : UInt32 := if white then 0x202020 else 0xFFFFFF
  let fill := solid w c
  let sep := solid w 0x101010
  let ds := (Array.range 5).map fun l => digitRow w k l c ink
  let mut out := Array.mkEmpty BandH
  for l in [0:BandH] do
    out := out.push (if l < 6 then sep else if l ≥ 40 && l < 120 then ds[(l - 40) / 16]! else fill)
  return out

structure St where
  w : Nat
  h : Nat
  top : Nat
  bot : Nat
  inset : Nat
  n : Nat
  white : Array Bool
  rows : Array (Array ByteArray)
  ime : Nat
  text : String
  pos : Array UInt32
  bg : ByteArray

def St.viewH (s : St) : Nat := s.h - s.top - s.bot - s.inset

def St.contentH (s : St) : Nat := s.n * BandH

/-- Band k covers distances [(n-1-k)*BandH, (n-k)*BandH) above the end. -/
def St.bandAt (s : St) (d : Nat) : Option Nat :=
  if d < s.contentH then some (s.n - 1 - d / BandH) else none

def St.list (s : St) (b : Nat) : Array ByteArray := Id.run do
  let fh := s.viewH + 2 * Over.toNat
  let mut out := Array.mkEmpty fh
  for r in [0:fh] do
    let d : Int := b + s.viewH + Over.toNat - 1 - r
    if d < 0 then out := out.push s.bg
    else match s.bandAt d.toNat with
      | none => out := out.push s.bg
      | some k =>
        let l := BandH - 1 - d.toNat % BandH
        out := out.push ((s.rows[k]!)[l]!)
  return out

def St.header (s : St) : Array ByteArray :=
  let bar := withBar s.w 0x1C2A4A 0x7FB3FF 40 (40 + s.ime * (s.w - 80) / Max.max s.h 1)
  let plain := solid s.w 0x1C2A4A
  Array.ofFn (n := s.top) fun i => if i.val ≥ s.top - 70 && i.val < s.top - 30 then bar else plain

def St.composer (s : St) : Array ByteArray :=
  let len := s.text.length
  let cur := (s.pos[0]?.getD 0).toNat
  let bar := withBar s.w 0x303030 0xA0E0A0 40 (40 + Min.min (len * 20) (s.w - 80))
  let tick := withBar s.w 0x303030 0xFFFF00 (40 + cur * 20) (44 + cur * 20)
  let plain := solid s.w 0x303030
  Array.ofFn (n := s.bot) fun i =>
    if i.val ≥ 40 && i.val < 80 then bar else if i.val ≥ 85 && i.val < 110 then tick else plain

def St.append (s : St) : St :=
  let k := s.n
  { s with n := k + 1, white := s.white.push false, rows := s.rows.push (bandRows s.w k false) }

def St.toggle (s : St) (k : Nat) : St :=
  let v := !(s.white[k]!)
  { s with white := s.white.set! k v, rows := s.rows.set! k (bandRows s.w k v) }

def reply (s : String) : IO Unit := Platform.ctlReply s

partial def loop (s : St) (lastB : Nat) : IO Unit := do
  let b := (← Platform.scroll s.contentH.toUInt32 s.viewH.toUInt32).toNat
  let evs ← Platform.frame (s.list b) b.toUInt32 Over s.header s.composer
  let mut s := s
  let mut b := b
  for e in Event.decode evs do
    match e with
    | .close => return
    | .tap .list _ y => if let some k := s.bandAt y.toNat then s := s.toggle k
    | .tap .composer _ _ => Platform.ime true
    | .tap .header _ _ => Platform.ime false
    | .text => let (t, p) ← Platform.text; s := { s with text := t, pos := p }
    | .send => s := s.append; Platform.textClear
    | .ime h => s := { s with ime := h.toNat }
    | _ => pure ()
  for c in ← Platform.ctlPoll do
    let ws := c.splitOn " "
    match ws with
    | ["ping"] => reply "pong"
    | ["state"] =>
      reply s!"b={b} ime={s.ime} bands={s.n} contentH={s.contentH} viewH={s.viewH} text={s.text} pos={s.pos.toList}"
    | "send" :: _ => s := s.append; reply s!"ok bands={s.n}"
    | ["ime", "on"] => Platform.ime true; reply "ok"
    | ["ime", "off"] => Platform.ime false; reply "ok"
    | ["to", v] => Platform.scrollTo (v.toNat!.toFloat); reply "ok"
    | ["by", v] => Platform.scrollBy (v.toInt!.toNat.toFloat - (-v.toInt!).toNat.toFloat); reply "ok"
    | _ => reply s!"unknown: {c}"
  loop s b

end Demo

open Demo in
def main : IO Unit := do
  let scr ← Platform.screen
  let w := (scr[0]?.getD 1080).toNat
  let h := (scr[1]?.getD 2400).toNat
  let itop := (scr[2]?.getD 0).toNat
  let ibot := (scr[3]?.getD 0).toNat
  IO.println s!"twin demo: screen {w}x{h}, insets {itop}/{ibot}, dpi {scr[4]?.getD 0}"
  let n := 300
  let s : St := {
    w, h, top := itop + 120, bot := 140, inset := ibot, n
    white := Array.replicate n false
    rows := (Array.range n).map fun k => bandRows w k false
    ime := 0, text := "", pos := #[0, 0, 0, 0], bg := solid w 0x000000 }
  loop s 0
