/- Settings share libquiet's drawer geometry on phones and desktop.
Every row has one layout used for both pixels and dispatch. -/
import ops.app.Pages

namespace Appearance
open Paint Pages Row

def gray50 (dm : Dim) : Color := if dm.theme == .dark then 0xa0a0a0 else 0x767676

def choices : Array (Theme.Setting × String) :=
  #[(.system, "System"), (.light, "Light"), (.dark, "Dark")]

def chosen (current choice : Theme.Setting) : Bool := current == choice

structure Item where
  text : String
  action : Act
  icon : String := ""
  detail : String := ""
  sub : String := ""
  selected : Bool := false
  danger : Bool := false
  disabled : Bool := false

/-- Full-width settings row: 14/20 text, 16px inset and a one-pixel rule. -/
def item (f : Font.Font) (dm : Dim) (b : Bitmap) (y : Nat) (a : Item) : Bitmap × (Pages.Box × Act) × Nat := Id.run do
  let px := dm.px
  let font := f.atSize (px 14)
  let small := f.atSize (px 12)
  let left := px (if a.icon.isEmpty then 16 else 48)
  let right := px (if a.selected then 40 else 52)
  let sub := if a.sub.isEmpty then #[] else Text.layoutFine small (b.w - left - right) a.sub
  let h := max (px 48) (px 25 + px 20 + sub.size * px 16)
  let mut b := b
  let ink := if a.disabled then (if dm.theme == .dark then 0x888888 else 0x999999)
    else Palette.color dm.theme (if a.danger then .error else .fg)
  let ty := y + (if a.sub.isEmpty then (h - px 20) / 2 else px 12)
  b := b.line font (Text.oneLineFine font (b.w - left - right) a.text) left (ty + px 4) ink (exactInk := a.disabled)
  for i in [0:sub.size] do
    b := b.line small sub[i]! left (ty + px 20 + i * px 16 + px 1) (gray50 dm)
  if !a.icon.isEmpty then b := b.icon f a.icon (px 16) (y + (h - px 20) / 2) (px 20) (gray50 dm)
  if !a.detail.isEmpty then
    let l := Text.oneLine font (b.w / 2) a.detail
    b := b.line font l (b.w - px 44 - Paint.Line.width font l) (ty + px 4) (gray50 dm)
  b := b.icon f (if a.selected then "icon-check" else "icon-chevron") (b.w - px 32) (y + (h - px 16) / 2) (px 16)
    (if a.selected then Palette.color dm.theme .fg else gray50 dm)
  b := b.fill 0 (y + h - px 1) b.w (y + h) (Palette.color dm.theme .selected)
  return (b, (⟨0, y, b.w, h⟩, a.action), h)

def sectionTitle (f : Font.Font) (dm : Dim) (b : Bitmap) (y : Nat) (title : String) : Bitmap × Nat :=
  let font := f.atSize (dm.px 12)
  let b := b.line font (Text.oneLine font b.w title) (dm.px 16) (y + dm.px 27) (gray50 dm)
  (b.fill 0 (y + dm.px 46) b.w (y + dm.px 47) (Palette.color dm.theme .selected), dm.px 47)

def group (f : Font.Font) (dm : Dim) (pg : Page) (y : Nat) (title : String) (items : Array Item) : Page × Nat := Id.run do
  let (b, h) := sectionTitle f dm pg.bmp y title
  let mut pg := { pg with bmp := b }
  let mut y := y + h
  for a in items do
    let (b, tap, h) := item f dm pg.bmp y a
    pg := { bmp := b, taps := if a.disabled then pg.taps else pg.taps.push tap }
    y := y + h
  return (pg, y)

def header (f : Font.Font) (dm : Dim) (w insetTop : Nat) (title : String) (back := false) : Bitmap :=
  let b := Bitmap.blank w (insetTop + dm.px 60) (solid (Palette.color dm.theme .panel) w)
  let b := b.icon f (if back then "icon-back" else "icon-close") (dm.px 20) (insetTop + dm.px 20) (dm.px 20) (Palette.color dm.theme .fg)
  let font := (f.atSize (dm.px 16)).medium
  let line := Text.oneLineFine font (min ((w - dm.px 16) / 2) (w - dm.px 192)) title
  let b := b.line font line ((w - Paint.Line.width font line) / 2) (insetTop + dm.px 23) (Palette.color dm.theme .fg)
  b.fill 0 (b.h - dm.px 1) w b.h (Palette.color dm.theme .selected)

def page (f : Font.Font) (dm : Dim) (w h : Nat) (current : Theme.Setting) : Page := Id.run do
  let mut pg : Page := ⟨Bitmap.blank w h (solid (Palette.color dm.theme .panel) w), #[]⟩
  let small := f.atSize (dm.px 11)
  pg := { pg with bmp := pg.bmp.line small (Text.oneLine small w "THEME") (dm.px 16) (dm.px 18) (gray50 dm) }
  let mut y := dm.px 40
  for (choice, name) in choices do
    let (b, tap, rh) := item f dm pg.bmp y { text := name, action := .theme choice, selected := chosen current choice }
    -- A non-selected theme has no navigation chevron.
    let b := if chosen current choice then b else b.fill (w - dm.px 36) (y + dm.px 8) (w - dm.px 12) (y + rh - dm.px 8) (Palette.color dm.theme .panel)
    pg := { bmp := b, taps := pg.taps.push tap }
    y := y + rh
  return pg

/-- The profile hero shared by You and Community settings. -/
def hero (f : Font.Font) (dm : Dim) (w h : Nat) (name id tally : String) (community : Bool) : Page := Id.run do
  let px := dm.px
  let color := Palette.color dm.theme
  let mut b := Bitmap.blank w h (solid (color .panel) w)
  let ax := (w - px 96) / 2
  let ay := px 24
  b := b.round ax ay (ax + px 96) (ay + px 96) (px 8) (Palette.avatar id)
  let large := f.atSize (px 56)
  let initial := Text.oneLine large (px 96) (String.ofList [(name.toList.headD '?').toUpper])
  b := b.line large initial (ax + (px 96 - Paint.Line.width large initial) / 2) (ay + px 24) 0xffffff
  let ex := ax + px 96 - px 18
  b := b.round ex (ay - px 10) (ex + px 28) (ay + px 18) (px 14) (color .panel)
  b := b.icon f "image-plus" (ex + px 5) (ay - px 5) (px 18) (color .fg)
  b := centred (f.atSize (px 16)) b name (px 135) (color .fg)
  b := centred (f.atSize (px 12)) b tally (px 159) (gray50 dm)
  let bw := (w - px 40) / 2
  let buttonY := px 192
  b := b.round (px 16) buttonY (px 16 + bw) (buttonY + px 44) (px 16) (color .button)
  let right := px 24 + bw
  b := b.round right buttonY (w - px 16) (buttonY + px 44) (px 16) (color .line)
  b := b.round (right + px 1) (buttonY + px 1) (w - px 17) (buttonY + px 43) (px 15) (color .panel)
  let font := f.atSize (px 14)
  for (x, text, icon, ink) in [(px 16, if community then "Add members" else "Link a device", if community then "icon-person-add" else "icon-devices", color .onAccent),
      (right, "Edit profile", "icon-edit", color .fg)] do
    let l := Text.oneLine font bw text
    let tx := x + (bw - Paint.Line.width font l - px 26) / 2
    b := b.icon f icon tx (buttonY + px 13) (px 18) ink
    b := b.line font l (tx + px 26) (buttonY + px 14) ink
  b := b.fill 0 (px 256) w (px 257) (color .selected)
  return ⟨b, #[(⟨ax, ay, px 96, px 96⟩, .stub "Edit profile"),
    (⟨px 16, buttonY, bw, px 44⟩, if community then .addMembers else .stub "Link a device"),
    (⟨right, buttonY, bw, px 44⟩, .stub "Edit profile")]⟩

/-- Text at the reference's line height, retaining fractional font advances. -/
def prose (f : Font.Font) (dm : Dim) (b : Bitmap) (x y w : Nat)
    (text : String) (size line : Nat := 14) (centered := false) (muted := false) : Bitmap × Nat := Id.run do
  let font := f.atSize (dm.px size)
  let font := if size == 18 then font.medium else font
  let ls := Text.layoutFine font w text
  let mut b := b
  for i in [0:ls.size] do
    let tx := x + (if centered then (w - Paint.Line.width font ls[i]!) / 2 else 0)
    b := b.line font ls[i]! tx (y + i * dm.px line + dm.px (if size == 12 then 1 else 4))
      (if muted then gray50 dm else Palette.color dm.theme .fg)
  return (b, y + ls.size * dm.px line)

def outlineButton (f : Font.Font) (dm : Dim) (b : Bitmap) (y : Nat)
    (text icon : String) (danger := false) : Bitmap := Id.run do
  let px := dm.px
  let ink := Palette.color dm.theme (if danger then .error else .fg)
  let mut b := b.round (px 16) y (b.w - px 16) (y + px 44) (px 16)
    (if danger then ink else Palette.color dm.theme .line)
  b := b.round (px 17) (y + px 1) (b.w - px 17) (y + px 43) (px 15) (Palette.color dm.theme .panel)
  let font := f.atSize (px 14)
  let l := Text.oneLineFine font (b.w - px 64) text
  let mark := if icon.isEmpty then 0 else px 26
  let x := (b.w - Paint.Line.width font l - mark) / 2
  if !icon.isEmpty then b := b.icon f icon x (y + px 13) (px 18) ink
  return b.line font l (x + mark) (y + px 14) ink

def leafTitle (title : String) : String :=
  if title == "Message retention" then "Message retention limit"
  else if title == "Storage on this device" then "Storage limits"
  else title


def you (f : Font.Font) (dm : Dim) (w h : Nat) (name id : String) (communities devices : Nat) (setting : Theme.Setting) : Page := Id.run do
  let tally := s!"{communities} {if communities == 1 then "community" else "communities"} · {devices} {if devices == 1 then "device" else "devices"}"
  let pg := hero f dm w (max h (dm.px 1400)) name id tally false
  let (pg, y) := group f dm pg (dm.px 257) "Devices" #[{ text := "Linked devices", action := .stub "Linked devices", icon := "icon-devices", detail := toString devices }]
  let (pg, y) := group f dm pg y "On this device" #[
    { text := "Appearance", action := .appearance, icon := "icon-appearance", detail := match setting with | .system => "System" | .light => "Light" | .dark => "Dark" },
    { text := "Generate link previews", action := .stub "Link previews", icon := "icon-link", sub := "Fetches a link you share so its card shows the page; the site sees your address." }]
  let (pg, y) := group f dm pg y "Connection" #[{ text := "Connecting", action := .stub "Connection", icon := "icon-signal", sub := "disconnected (searching)" }]
  let (pg, y) := group f dm pg y "About" #[{ text := "About Quiet", action := .stub "About Quiet", icon := "icon-info", detail := "Lean" }]
  return { pg with bmp := { pg.bmp with rows := pg.bmp.rows.extract 0 (max h (y + dm.px 64)) } }

def community (f : Font.Font) (dm : Dim) (w h : Nat) (name id : String) (members : Nat) : Page := Id.run do
  let pg := hero f dm w (max h (dm.px 1400)) name id s!"{members} {if members == 1 then "member" else "members"} · 1 channel" true
  let (pg, y) := group f dm pg (dm.px 257) "People" #[{ text := "Members", action := .stub "Members", icon := "icon-people", detail := toString members }]
  let (pg, y) := group f dm pg y "Conversations" #[
    { text := "Notifications", action := .stub "Notifications", icon := "icon-bell", detail := "All messages" },
    { text := "Create channel", action := .stub "Create channel", icon := "hash" },
    { text := "Message retention", action := .stub "Message retention", detail := "Off", sub := "How long messages are kept" }]
  let (pg, y) := group f dm pg y "Connection" #[
    { text := "Network status", action := .stub "Network status", icon := "icon-signal", detail := "Not connected" },
    { text := "Storage on this device", action := .stub "Storage on this device", icon := "icon-storage" }]
  let buttonY := y + dm.px 32
  let pg := { pg with
    bmp := outlineButton f dm pg.bmp buttonY "Leave community" "icon-leave" true
    taps := pg.taps.push (⟨dm.px 16, buttonY, w - dm.px 32, dm.px 44⟩, .stub "Leave community") }
  return { pg with bmp := { pg.bmp with rows := pg.bmp.rows.extract 0 (max h (buttonY + dm.px 108)) } }

def channel (f : Font.Font) (dm : Dim) (w h members : Nat) : Page := Id.run do
  let mut pg : Page := ⟨Bitmap.blank w (max h (dm.px 800)) (solid (Palette.color dm.theme .panel) w), #[]⟩
  let mut y := 0
  let items : Array Item := #[
    { text := "Community settings", action := Act.communitySettings },
    { text := "Members in this channel", action := .stub "Members", detail := toString members },
    { text := "Permissions", action := .stub "Permissions", sub := "Roles and members" },
    { text := "Disappearing messages", action := .stub "Disappearing messages", detail := "Off" },
    { text := "Notifications", action := .stub "Notifications", sub := "All messages" },
    { text := "Delete channel", action := .stub "Delete channel", danger := true },
    { text := "Chaos", action := .stub "Chaos", sub := "Generate test people, messages, and pictures" }]
  for a in items do
    let (b, tap, rh) := item f dm pg.bmp y a
    pg := { bmp := b, taps := pg.taps.push tap }
    y := y + rh
  return { pg with bmp := { pg.bmp with rows := pg.bmp.rows.extract 0 (max h (y + dm.px 64)) } }

/-- Proposed settings keep libquiet's real choices and selected defaults.
They have no dispatch targets until the corresponding ops exist. -/
def staticPage (f : Font.Font) (dm : Dim) (w h : Nat) (title name id : String) : Page := Id.run do
  let px := dm.px
  let color := Palette.color dm.theme
  let mut b := Bitmap.blank w (max h (px 1400)) (solid (color .panel) w)
  let mut y := px 16
  let mut taps := #[]
  if title == "Message retention" || title == "Disappearing messages" then
    let retention := title == "Message retention"
    let text := if retention then "When enabled, all messages older than the chosen retention limit will be deleted."
      else "When enabled, all messages by anyone in this channel will auto-delete after the chosen countdown. (Countdowns start on send, so short countdowns may lead to undelivered messages.)"
    let (pic, endY) := prose f dm b (px 16) y (w - px 32) text 14 20
    b := pic
    y := endY + px 16
    let options := if retention then #["Off", "1 week", "1 month", "3 months", "6 months", "12 months", "18 months", "24 months", "Custom"]
      else #["Off", "1 min", "5 min", "1 day", "1 week", "1 month", "3 months", "6 months", "12 months", "18 months", "24 months", "Custom"]
    for i in [0:options.size] do
      let (pic, _, rh) := item f dm b y { text := options[i]!, action := .back, selected := i == 0, disabled := true }
      b := if i == 0 then pic else pic.fill (w - px 36) (y + px 8) (w - px 12) (y + rh - px 8) (color .panel)
      y := y + rh
    let foot := if retention then "All messages older than the limit will be deleted. Anyone can set shorter times for particular channels or DMs, but only select roles can choose longer times."
      else "All new messages initiated by anyone in the channel will follow this setting."
    let (pic, endY) := prose f dm b (px 16) (y + px 16) (w - px 32) foot 12 16 false true
    b := pic
    y := endY + px 16
  else if title == "Storage on this device" then
    let (pic, endY) := prose f dm b (px 16) y (w - px 32)
      "Customize your device storage limits for images and files posted by you and others." 14 20
    b := pic
    y := endY + px 16
    for (label, sub) in [("Your files and images", "No limit"), ("Others' files and images", "2 GB")] do
      let (pic, _, rh) := item f dm b y { text := label, action := .back, sub, disabled := true }
      b := pic.fill (w - px 36) (y + px 8) (w - px 12) (y + rh - px 8) (color .panel)
      b := b.icon f "icon-down" (w - px 32) (y + (rh - px 16) / 2) (px 16) (gray50 dm)
      y := y + rh
  else if title == "About Quiet" then
    for text in ["Version: 0.1 (Lean Quiet)", "Copyright © A Quiet LLC"] do
      let (pic, endY) := prose f dm b (px 16) y (w - px 32) text 14 20
      b := pic
      y := endY + px 4
  else if title == "Leave community" then
    let ax := (w - px 96) / 2
    let ay := px 40
    b := b.round ax ay (ax + px 96) (ay + px 96) (px 8) (Palette.avatar id)
    let font := f.atSize (px 56)
    let initial := Text.oneLineFine font (px 96) (String.ofList [(name.toList.headD '?').toUpper])
    b := b.line font initial (ax + (px 96 - Paint.Line.width font initial) / 2) (ay + px 24) 0xffffff
    let bx := ax + px 74
    let badgeY := ay + px 74
    b := b.round (bx - px 3) (badgeY - px 3) (bx + px 35) (badgeY + px 35) (px 19) (color .panel)
    b := b.round bx badgeY (bx + px 32) (badgeY + px 32) (px 16) (color .error)
    b := b.icon f "icon-leave" (bx + px 7) (badgeY + px 7) (px 18) 0xffffff
    let (pic, endY) := prose f dm b (px 16) (px 160) (w - px 32) s!"Leave {name}?" 18 26 true
    let bw := min (px 300) (w - px 32)
    let (pic, endY) := prose f dm pic ((w - bw) / 2) (endY + px 12) bw
      "You'll lose access to its channels and messages on this device. To come back, someone will need to invite you again." 14 20 true true
    y := endY + px 24
    let costs := #[("1 channel and their history leave this device", "icon-chats"),
      ("Members will still see messages you sent", "icon-people")]
    let costHeight := px 3 + costs.foldl (fun total (label, _) => total + px 24 +
      (Text.layoutFine (f.atSize (px 14)) (w - px 98) label).size * px 20) 0
    b := pic.round (px 16) y (w - px 16) (y + costHeight) (px 16) (color .line)
    b := b.round (px 17) (y + px 1) (w - px 17) (y + costHeight - px 1) (px 15) (color .panel)
    let startY := y
    y := y + px 1
    for i in [0:costs.size] do
      let (label, icon) := costs[i]!
      let rh := px 24 + (Text.layoutFine (f.atSize (px 14)) (w - px 98) label).size * px 20
      let (pic, _) := prose f dm b (px 65) (y + px 12) (w - px 98) label 14 20
      b := pic.icon f icon (px 33) (y + (rh - px 20) / 2) (px 20) (gray50 dm)
      y := y + rh
      if i + 1 < costs.size then
        b := b.fill (px 17) y (w - px 17) (y + px 1) (color .selected)
        y := y + px 1
    y := startY + costHeight + px 32
    b := b.round (px 16) y (w - px 16) (y + px 44) (px 16) (mixC (color .panel) (color .error) 154)
    let font := (f.atSize (px 14)).medium
    let line := Text.oneLineFine font (w - px 64) "Leave community"
    b := b.line font line ((w - Paint.Line.width font line) / 2) (y + px 14)
      (mixC (color .panel) 0xffffff 154) (exactInk := true)
    y := y + px 52
    b := outlineButton f dm b y "Stay" ""
    taps := taps.push (⟨px 16, y, w - px 32, px 44⟩, .back)
    y := y + px 68
  else
    let (pic, endY) := prose f dm b (px 16) (px 24) (w - px 32)
      s!"{title} is not available in this build yet." 14 20 false true
    b := pic
    y := endY
  return ⟨{ b with rows := b.rows.extract 0 (max h (y + px 64)) }, taps⟩

def stub (f : Font.Font) (dm : Dim) (w h : Nat) (title : String) (name id : String := "") : Page :=
  staticPage f dm w h title name id

theorem selected_check (s : Theme.Setting) : chosen s s = true := by cases s <;> rfl

end Appearance
