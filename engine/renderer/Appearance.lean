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

/-- Full-width settings row: 14/20 text, 16px inset and a one-pixel rule. -/
def item (f : Font.Font) (dm : Dim) (b : Bitmap) (y : Nat) (a : Item) : Bitmap × (Pages.Box × Act) × Nat := Id.run do
  let px := dm.px
  let font := f.atSize (px 14)
  let small := f.atSize (px 12)
  let left := px (if a.icon.isEmpty then 16 else 48)
  let right := px (if a.selected then 40 else 52)
  let sub := if a.sub.isEmpty then #[] else Text.layout small (b.w - left - right) a.sub
  let h := max (px 48) (px 24 + px 20 + sub.size * px 16)
  let mut b := b
  let ink := Palette.color dm.theme (if a.danger then .error else .fg)
  let ty := y + (if a.sub.isEmpty then (h - px 20) / 2 else px 12)
  b := b.line font (Text.oneLine font (b.w - left - right) a.text) left (ty + px 4) ink
  for i in [0:sub.size] do
    b := b.line small sub[i]! left (ty + px 20 + i * px 16 + px 1) (gray50 dm)
  if !a.icon.isEmpty then b := b.icon f a.icon (px 16) (y + (h - px 20) / 2) (px 20) (gray50 dm)
  if !a.detail.isEmpty then
    let l := Text.oneLine font (b.w / 2) a.detail
    b := b.line font l (b.w - px 44 - Paint.Line.width font l) (ty + px 4) (gray50 dm)
  b := b.icon f (if a.selected then "icon-check" else "icon-chevron") (b.w - px 32) (y + (h - px 16) / 2) (px 16)
    (if a.selected then ink else gray50 dm)
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
    pg := { bmp := b, taps := pg.taps.push tap }
    y := y + h
  return (pg, y)

def header (f : Font.Font) (dm : Dim) (w insetTop : Nat) (title : String) (back := false) : Bitmap :=
  let b := Bitmap.blank w (insetTop + dm.px 60) (solid (Palette.color dm.theme .panel) w)
  let b := b.icon f (if back then "icon-back" else "icon-close") (dm.px 20) (insetTop + dm.px 20) (dm.px 20) (Palette.color dm.theme .fg)
  let font := f.atSize (dm.px 16)
  let b := centred font b title (insetTop + dm.px 24) (Palette.color dm.theme .fg)
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
  return { pg with bmp := { pg.bmp with rows := pg.bmp.rows.extract 0 (max h (y + dm.px 64)) } }

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

def stub (f : Font.Font) (dm : Dim) (w h : Nat) (title : String) : Page :=
  let b := Bitmap.blank w h (solid (Palette.color dm.theme .panel) w)
  let (b, _) := para (f.atSize (dm.px 14)) dm b s!"{title} is not available in this build yet." (dm.px 16) (dm.px 24) (w - dm.px 32) (gray50 dm)
  ⟨b, #[]⟩

theorem selected_check (s : Theme.Setting) : chosen s s = true := by cases s <;> rfl

end Appearance
