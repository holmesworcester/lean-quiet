/-
The reaction sheet, libquiet's on a phone: a long press on a message opens
it from the bottom over the dimmed list.

- **Quick:** a grip; the six quick reactions and Browse, spread across
  the sheet, each a 44 dp key (the touch floor), the ones the user holds
  ringed; then Copy text, a full-width row.
- **Catalogue** (Browse): a back key and the search field; the six skin
  tones; the category's name; its emoji in a grid that scrolls; and the
  category bar along the bottom. The list is libquiet's own
  (assets/picker.txt, tools/picker.py).

Every key is placed by a `SheetGeom.Grid`, and taps go through the same
grid's `hit`, so SheetGeom's theorems (hit_iff, keys_disjoint,
reachable, compose_row) are about this sheet.
-/
import engine.renderer.SheetGeom
import engine.renderer.Row

namespace Sheet
open Paint Text Font Row SheetGeom

structure Item where
  e : String
  skins : Array String
  label : String
  tags : String
  group : Nat
  deriving Inhabited

def loadCatalog (path : String := "assets/picker.txt") : IO (Array Item) := do
  let txt ← IO.FS.readFile path
  let mut out := #[]
  for line in txt.splitOn "\n" do
    match line.splitOn "\t" with
    | [g, e, sk, label, tags] =>
      let skins := if sk.isEmpty then #[] else (sk.splitOn " ").toArray
      out := out.push ⟨e, skins, label, tags, g.toNat?.getD 0⟩
    | _ => pure ()
  return out

/-- libquiet's categories, in its bar's order, and the emoji marking each. -/
def categories : Array (String × String × List Nat) := #[
  ("Smileys & People", "😀", [0, 1]), ("Animals & Nature", "🐻", [3]), ("Food & Drink", "🍔", [4]),
  ("Activity", "⚽", [6]), ("Travel & Places", "🚗", [5]), ("Objects", "💡", [7]),
  ("Symbols", "🔣", [8]), ("Flags", "🏁", [9])]

def toneEmoji : Array String := #["✋", "✋🏻", "✋🏼", "✋🏽", "✋🏾", "✋🏿"]

/-- An item at a skin tone (0 is the default). -/
def Item.toned (it : Item) (tone : Nat) : String :=
  if tone > 0 && it.skins.size == 5 then it.skins[tone - 1]! else it.e

/-- The items a catalogue shows: a category's, or a search's across all. -/
def shown (cat : Array Item) (c : Nat) (query : String) : Array Nat := Id.run do
  let q := query.trimAscii.toString.toLower
  let mut out := #[]
  for i in [0:cat.size] do
    let it := cat[i]!
    if q.isEmpty then
      if (categories[c]?.map (·.2.2.contains it.group)).getD false then out := out.push i
    else if (it.label.toLower.splitOn q).length > 1 || (it.tags.splitOn q).length > 1 then
      out := out.push i
  return out

def panel : Color := 0x222529
def line : Color := 0x3A3D41

/-! ## Quick -/

structure Quick where
  h : Nat
  keys : Grid
  copyY : Nat
  copyH : Nat

def _root_.Row.Dim.key44 (d : Dim) : Nat := d.px 44

def quick (dm : Dim) (W : Nat) : Quick :=
  let k := dm.key44
  let pad := dm.px 16
  let n := Row.quick.size + 1
  -- spread across the sheet: the space left shared between the gaps
  let pitch := k + (W - 2 * pad - n * k) / (n - 1)
  let ky := dm.px 20 + dm.px 12
  let copyY := ky + k + dm.px 12
  let copyH := dm.px 49
  ⟨copyY + copyH + dm.px 16, ⟨pad, ky, pitch, k, n, k, n⟩, copyY, copyH⟩

/-- A key's emoji centred in its box. -/
def key (f : Font) (b : Bitmap) (e : String) (x y k : Nat) : Bitmap :=
  let l := oneLine f (4 * f.cell) e
  let w := Paint.Line.width f l
  b.line f l (x + (k - min k w) / 2) (y + (k - f.cell) / 2) ink

def ring (dm : Dim) (b : Bitmap) (x y k : Nat) : Bitmap :=
  let e := max 2 (dm.px 1)
  (b.round x y (x + k) (y + k) (k / 2) accent).round (x + e) (y + e) (x + k - e) (y + k - e) (k / 2 - e) pillMine

/-- The sheet's ground: its top corners rounded over the dimmed list. -/
def ground (dm : Dim) (W h : Nat) (backdrop : Color) : Bitmap :=
  let r := dm.px 16
  (Bitmap.blank W h (solid backdrop W)).round 0 0 W (h + r) r panel

def paintQuick (f : Font) (dm : Dim) (W : Nat) (backdrop : Color) (mine : List String) : Bitmap := Id.run do
  let q := quick dm W
  let mut b := ground dm W q.h backdrop
  -- the grip
  let gw := dm.px 36
  b := b.round ((W - gw) / 2) (dm.px 8) ((W + gw) / 2) (dm.px 12) (dm.px 2) line
  let g := q.keys
  for i in [0:g.n] do
    let x := g.left i
    if i < Row.quick.size then
      let e := Row.quick[i]!
      if mine.contains e then b := ring dm b x g.y0 g.key
      b := key f b e x g.y0 g.key
    else
      -- Browse: a face with a plus
      b := b.line f (oneLine f f.cell "☺") (x + (g.key - f.cell / 2) / 2) (g.y0 + (g.key - f.cell) / 2) ink
      b := b.line f (oneLine f f.cell "+") (x + g.key - f.cell / 2) g.y0 ink
  -- Copy text
  b := b.fill 0 q.copyY W (q.copyY + max 1 (dm.px 1) / 2 + 1) line
  let ty := q.copyY + (q.copyH - f.cell) / 2
  b := b.line f (oneLine f f.cell "⧉") (dm.px 16) ty ink
  b := b.line f (oneLine f (W / 2) "Copy text") (dm.px 16 + f.cell / 2 + dm.px 16) ty ink
  return b

inductive QuickHit where
  | react (e : String)
  | browse
  | copy
  | none
  deriving BEq

def hitQuick (dm : Dim) (W x y : Nat) : QuickHit :=
  let q := quick dm W
  match q.keys.hit 0 x y with
  | some i => if h : i < Row.quick.size then .react Row.quick[i] else .browse
  | none => if q.copyY ≤ y && y < q.copyY + q.copyH then .copy else .none

/-! ## Catalogue -/

structure Cat where
  h : Nat
  back : Grid
  search : Nat × Nat × Nat × Nat
  tones : Grid
  headY : Nat
  grid : Grid
  bar : Grid

def cat (dm : Dim) (f : Font) (W Hs insetTop n : Nat) : Cat :=
  let k := dm.key44
  let pad := dm.px 16
  let h := min (dm.px 480) (Hs - insetTop - dm.px 48)
  let sy := pad
  let back : Grid := ⟨pad, sy, k, k, 1, k, 1⟩
  let sx := pad + k + dm.px 8
  let ty := sy + k + dm.px 8
  let tones : Grid := ⟨pad, ty, k + dm.px 4, k, 6, k, 6⟩
  let headY := ty + k + dm.px 8
  let gy := headY + f.cell + dm.px 8
  let barH := k
  let bottom := dm.px 16
  let cols := max 1 ((W - 2 * pad) / k)
  let gx := pad + (W - 2 * pad - cols * k) / 2
  let vh := h - gy - barH - dm.px 8 - bottom
  let grid : Grid := ⟨gx, gy, k, k, cols, vh, n⟩
  let bp := (W - 2 * pad) / categories.size
  let bar : Grid := ⟨pad + (bp - min bp k) / 2, h - bottom - barH, bp, min bp k, categories.size, barH, categories.size⟩
  ⟨h, back, (sx, sy, W - pad, sy + k), tones, headY, grid, bar⟩

/-- The rows above the grid: back, search, tones, heading. -/
def catTop (f : Font) (dm : Dim) (W : Nat) (c : Cat) (backdrop : Color) (query : String) (searching : Bool)
    (tone category : Nat) : Bitmap := Id.run do
  let mut b := ground dm W c.grid.y0 backdrop
  b := key f b "‹" (c.back.left 0) c.back.y0 c.back.key
  let (x0, y0, x1, y1) := c.search
  b := b.round x0 y0 x1 y1 ((y1 - y0) / 2) line
  let e := max 2 (dm.px 1)
  b := b.round (x0 + e) (y0 + e) (x1 - e) (y1 - e) ((y1 - y0) / 2 - e) (if searching then selBg else panel)
  let ty := y0 + (y1 - y0 - f.cell) / 2
  b := b.line f (oneLine f (x1 - x0 - dm.px 32) (if query.isEmpty then "Search emoji" else query))
    (x0 + dm.px 16) ty (if query.isEmpty then dim else ink)
  for i in [0:6] do
    let x := c.tones.left i
    if i == tone then b := ring dm b x c.tones.y0 c.tones.key
    b := key f b toneEmoji[i]! x c.tones.y0 c.tones.key
  let head := if query.isEmpty then (categories[category]?.map (·.1)).getD "" else "Search results"
  b := b.line f (oneLine f (W - 2 * dm.px 16) head) (dm.px 16) c.headY dim
  return b

/-- Grid row r's pixels: its items' emoji, each in its key's box
(`Grid.left`, the box `hit` answers for). -/
def gridRow (f : Font) (dm : Dim) (W : Nat) (c : Cat) (cat : Array Item) (items : Array Nat)
    (tone : Nat) (mine : List String) (r : Nat) : Bitmap := Id.run do
  let g := c.grid
  let mut b := Bitmap.blank W g.key (solid panel W)
  for j in [0:g.cols] do
    let i := r * g.cols + j
    if i < items.size then
      let e := (cat[items[i]!]!).toned tone
      if mine.contains e then b := ring dm b (g.left i) 0 g.key
      b := key f b e (g.left i) 0 g.key
  return b

/-- The rows below the grid: the category bar. -/
def catBot (f : Font) (dm : Dim) (W : Nat) (c : Cat) (category : Nat) (searching : Bool) : Bitmap := Id.run do
  let h := c.h - c.grid.y0 - c.grid.vh
  let mut b := Bitmap.blank W h (solid panel W)
  b := b.fill 0 0 W (max 1 (dm.px 1) / 2 + 1) line
  let by0 := c.bar.y0 - c.grid.y0 - c.grid.vh
  for i in [0:categories.size] do
    let x := c.bar.left i
    if i == category && !searching then
      b := b.round x by0 (x + c.bar.key) (by0 + c.bar.key) (c.bar.key / 2) line
    b := key f b categories[i]!.2.1 x by0 c.bar.key
  return b

inductive CatHit where
  | back
  | search
  | tone (t : Nat)
  | pick (i : Nat)
  | category (c : Nat)
  | none
  deriving BEq

def hitCat (c : Cat) (s x y : Nat) : CatHit :=
  let (x0, y0, x1, y1) := c.search
  match c.back.hit 0 x y, c.tones.hit 0 x y, c.grid.hit s x y, c.bar.hit 0 x y with
  | some _, _, _, _ => .back
  | _, some t, _, _ => .tone t
  | _, _, some i, _ => .pick i
  | _, _, _, some k => .category k
  | _, _, _, _ => if x0 ≤ x && x < x1 && y0 ≤ y && y < y1 then .search else .none

end Sheet
