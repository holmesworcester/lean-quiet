/- The desktop community popover. Geometry is shared by paint and hit testing;
only the visible rows allocate pixels. Community indices keep Pages' proved
current-first ordering, so equal labels cannot change a tap's identity. -/
import App
import engine.renderer.desktop.Layout

namespace Desktop.Switcher
open Paint

inductive Act where
  | close | community (i : Nat) | invite | settings | join | create | linked
  deriving BEq, Repr, Inhabited

structure Model where
  box : Box
  contentH : Nat
  offset : Nat
  rows : List (Nat × Pages.Entry)
  deriving Inhabited

def model (s : App.St) (height offset : Nat) : Model :=
  let px := s.dim.px
  let rows := Pages.switcherOrder (s.comms.map fun m =>
    { name := m.name, id8 := Pages.identity m.c, unread := 0,
      current := m.acc == s.cur, waiting := m.waiting })
  let contentH := px (263 + rows.length * 56 - (if rows.isEmpty then 0 else 4))
  let h := min contentH (height - px 56)
  ⟨⟨px 8, px 48, px 300, h⟩, contentH, min offset (contentH - h), rows⟩

/-- A content-space control clipped to the popover's own viewport. -/
def clipped (m : Model) (b : Box) : Box :=
  let y := b.y - m.offset
  ⟨m.box.x + b.x, m.box.y + y, b.w,
    min (b.y + b.h - m.offset) m.box.h - y⟩

def candidates (s : App.St) (m : Model) : List (Control Act) := Id.run do
  let px := s.dim.px
  let mut out := []
  let add (x y w h : Nat) (a : Act) (label := "") :=
    Control.mk .overlay (clipped m ⟨px x, px y, px w, px h⟩) a label
  out := [add 9 9 40 40 .close "Close"]
  for (j, (i, e)) in m.rows.zipIdx |>.map (fun (r, j) => (j, r)) do
    let y := 65 + j * 56
    if !e.waiting then
      out := out ++ [add 9 y (if e.current then 206 else 282) 52 (.community i) e.name]
      if e.current then
        out := out ++ [add 215 (y + 10) 32 32 .invite "Add members",
          add 251 (y + 10) 32 32 .settings "Community settings"]
  let y := 65 + m.rows.length * 56 - (if m.rows.isEmpty then 0 else 4) + 17
  for (j, (a, label)) in ([(Act.join, "Join a community"), (.create, "Create a community"), (.linked, "Linked devices")].zipIdx.map fun (r, j) => (j, r)) do
    out := out ++ [add 9 (y + j * 56) 282 52 a label]
  return out

/-- Gaussian edge falloff of the CSS 0 8px 24px shadow. The rounded-box
signed distance and a small coverage table bound work by the visible popup,
independent of the number of communities. No screenshot is used at runtime. -/
def shadow (b : Bitmap) (dm : Row.Dim) (box : Box) (blur := 24) (down := 8) (opacity := 0.42) (corner := 16) : Bitmap := Id.run do
  let px := dm.px
  let sigma := max 1 (px blur / 2)
  let reach := px blur * 3 / 2
  let radius := px corner
  let cy0 := box.y + px down
  let coverage := (Array.range (2 * reach + 1)).map fun i =>
    let x := (i.toFloat - reach.toFloat) / sigma.toFloat / 1.41421356237
    let t := 1.0 / (1.0 + 0.3275911 * x.abs)
    let erf := 1.0 - (((((1.061405429 * t - 1.453152027) * t + 1.421413741) * t - 0.284496736) * t + 0.254829592) * t) * (-x*x).exp
    ((0.5 * (1.0 - (if x < 0 then -erf else erf)) * opacity * 255.0).toUInt64.toNat)
  let mut b := b
  for y in [cy0 - reach:min b.h (cy0 + box.h + reach)] do
    b := b.modify y fun row => Id.run do
      let mut row := row
      for x in [box.x - reach:min b.w (box.x + box.w + reach)] do
        -- The opaque interior will be covered; don't blend it twice.
        if cover box.x box.y (box.x + box.w) (box.y + box.h) radius x y == 256 &&
            box.has x y then continue
        let dx : Int := max (Int.ofNat (box.x + radius) - x) (Int.ofNat x - (box.x + box.w - radius))
        let dy : Int := max (Int.ofNat (cy0 + radius) - y) (Int.ofNat y - (cy0 + box.h - radius))
        let distance := Int.ofNat (Nat.sqrt (dx.toNat * dx.toNat + dy.toNat * dy.toNat)) + min 0 (max dx dy) - radius
        let a := coverage[(distance + reach).toNat]?.getD 0
        if a > 0 then row := setPx row x (blendText 0 (getPx row x) a)
      return row
  return b

/-- The visible window into a taller popover. Offscreen entries don't paint,
and clipping is applied after text/icons so partially visible rows stay put. -/
def paint (b : Bitmap) (s : App.St) (m : Model) (hover : Hover.Context) : Bitmap := Id.run do
  let px := s.dim.px
  let color := Palette.color s.dim.theme
  let fg := color .fg
  let panel := color .panel
  let gray := color .selected
  let gray30 := if s.dim.theme == .dark then 0x6f6f6f else 0xb3b3b3
  let accent := if s.dim.theme == .dark then 0xdbbcf0 else 0x9c00ff
  let f := s.font.atSize (px 14)
  -- One row of padding above/below makes a clipped row's local coordinates
  -- nonnegative, without allocating the whole scrollable content.
  let pad := px 64
  let localY (n : Nat) := px n + pad - m.offset
  let visible (y h : Nat) := px (y + h) > m.offset && px y < m.offset + m.box.h
  let hot (x y w h : Nat) := let b := clipped m ⟨px x, px y, px w, px h⟩
    Hover.active hover ⟨b.x, b.y, b.w, b.h⟩
  let mut p := Bitmap.blank m.box.w (m.box.h + 2 * pad) (solid panel m.box.w)
  if visible 1 56 then
    if hot 9 9 40 40 then p := p.round (px 9) (localY 9) (px 49) (localY 49) (px 8) gray
    p := p.icon f "icon-close" (px 19) (localY 19) (px 20) fg
    let titleFont := (s.font.atSize (px 16)).medium
    let line := Text.oneLineFine titleFont (px 202) "Communities"
    p := p.line titleFont line ((m.box.w - Paint.Line.width titleFont line) / 2) (localY 23) fg (exactInk := true)
    p := p.fill (px 9) (localY 56) (px 291) (localY 57) gray
  for (j, (i, e)) in m.rows.zipIdx |>.map (fun (r, j) => (j, r)) do
    let y := 65 + j * 56
    if !visible y 52 then continue
    let hovered := !e.waiting && hot 9 y 282 52
    if hovered then p := p.round (px 9) (localY y) (px 291) (localY (y + 52)) (px 8) gray
    let ground := if hovered then gray else panel
    let ay := y + 8
    if e.current then
      p := p.round (px 14) (localY (ay - 3)) (px 56) (localY (ay + 39)) (px 7) accent
      p := p.round (px 16) (localY (ay - 1)) (px 54) (localY (ay + 37)) (px 5) ground
    p := p.round (px 17) (localY ay) (px 53) (localY (ay + 36)) (px 4) (Palette.avatar e.id8)
    let af := s.font.atSize (px (if e.waiting then 15 else 21))
    let mark := if e.waiting then String.ofList (e.id8.toList.take 2) else String.ofList [(e.name.trimAscii.toString.toList.headD '?').toUpper]
    let line := Text.oneLineFine af (px 36) mark
    p := p.line af line (px 17 + (px 36 - Paint.Line.width af line) / 2) (localY (ay + 9)) 0xffffff (exactInk := true)
    let width := px (if e.current then 142 else 218)
    let name := if e.waiting then s!"<{String.ofList (e.id8.toList.take 8)}>" else e.name
    p := p.line f (Text.oneLineFine f width name) (px 65) (localY (y + (if e.waiting then 10 else 20)))
      (if e.waiting then color .muted else fg) (exactInk := true)
    if e.waiting then
      let small := s.font.atSize (px 12)
      p := p.line small (Text.oneLineFine small (px 218) "Waiting for a member to let you in.") (px 65) (localY (y + 30)) (color .muted) (exactInk := true)
    if e.current && !(s.comms[i]?.any (·.waiting)) then
      for (x, icon) in [(215, "add-person"), (251, "gear")] do
        let toolHot := hot x (y + 10) 32 32
        if toolHot then p := p.round (px x) (localY (y + 10)) (px (x + 32)) (localY (y + 42)) (px 6) (color .line)
        p := p.icon f icon (px (x + 6)) (localY (y + 16)) (px 20) (if toolHot then fg else gray30)
  let edge := 65 + m.rows.length * 56 - (if m.rows.isEmpty then 0 else 4) + 8
  if visible edge 1 then p := p.fill (px 9) (localY edge) (px 291) (localY (edge + 1)) gray
  for (j, (icon, name)) in ([("add-person", "Join a community"), ("add", "Create a community"), ("linked-devices", "Linked devices")].zipIdx.map fun (r, j) => (j, r)) do
    let y := edge + 9 + j * 56
    if !visible y 52 then continue
    if hot 9 y 282 52 then p := p.round (px 9) (localY y) (px 291) (localY (y + 52)) (px 8) gray
    p := p.round (px 17) (localY (y + 8)) (px 53) (localY (y + 44)) (px 4) gray
    p := p.icon f icon (px 27) (localY (y + 18)) (px 16) fg
    p := p.line f (Text.oneLineFine f (px 218) name) (px 65) (localY (y + 20)) fg (exactInk := true)
  let b := shadow b s.dim m.box
  let b := b.round m.box.x m.box.y (m.box.x + m.box.w) (m.box.y + m.box.h) (px 16) gray
  -- CSS border clips all scrolling content, including the header, at radius15.
  let cropped : Bitmap := ⟨m.box.w - px 2,
    (p.rows.extract (pad + px 1) (pad + m.box.h - px 1)).map (·.extract (px 1 * 4) ((m.box.w - px 1) * 4)), #[]⟩
  return b.image cropped (m.box.x + px 1) (m.box.y + px 1) (px 15)

end Desktop.Switcher
