/-
The composer's tray: the attached pictures' thumbnails in a row, as Lean
draws it. `layout` places them (laws in Pic/Laws.lean: every slot is inside
the tray, slots keep their order with `gap` between them so none overlap,
and each thumbnail is its picture fitted into the tray's box); `render`
paints the tray as opaque RGBA (`render_opaque`) for the native side to
show as it is.
-/
import Pic.Fit
import Pic.Thumb

namespace Pic

/-- Where a thumbnail goes, in tray pixels. -/
structure Slot where
  x : Nat
  y : Nat
  w : Nat
  h : Nat
  deriving Repr, DecidableEq

/-- Tray geometry: its height, the padding around the row and the gap
between thumbnails. A thumbnail fits a square box of `height - 2 * pad`. -/
structure Geom where
  height : Nat
  pad : Nat
  gap : Nat

def Geom.box (g : Geom) : Nat := g.height - 2 * g.pad

/-- Slots for pictures of sizes `ss` from `x` on, left to right. -/
def place (g : Geom) (x : Nat) : List (Nat × Nat) → List Slot
  | [] => []
  | (w, h) :: rest =>
    let f := fit w h g.box
    { x, y := g.pad + (g.box - f.2) / 2, w := f.1, h := f.2 } :: place g (x + f.1 + g.gap) rest

/-- The tray's width for `ss`: padding, thumbnails and gaps. -/
def width (g : Geom) (ss : List (Nat × Nat)) : Nat :=
  match (place g g.pad ss).getLast? with
  | some s => s.x + s.w + g.pad
  | none => 2 * g.pad

/-- The slots and the tray's width. -/
def layout (g : Geom) (ss : List (Nat × Nat)) : List Slot × Nat :=
  (place g g.pad ss, width g ss)

/-- The tray's ground. -/
def ground : UInt8 := 236

/-- Byte `k` of the tray (`w` pixels wide): channel `k % 4` of the pixel
it belongs to, which shows the thumbnail whose slot holds that pixel,
blended over the ground by its alpha, or else the ground. Alpha is always
255: the tray is opaque (`render_opaque`), whatever the pictures' alpha. -/
def trayByte (w : Nat) (ts : List (Slot × Rgba)) (k : Nat) : UInt8 :=
  let c := k % 4
  let x := k / 4 % w.max 1
  let y := k / 4 / w.max 1
  if c = 3 then 255
  else
    match ts.find? (fun (s, _) => s.x ≤ x && x < s.x + s.w && s.y ≤ y && y < s.y + s.h) with
    | none => ground
    | some (s, t) =>
      let i := 4 * ((y - s.y) * t.w + (x - s.x))
      let a := (get8 t.px (i + 3)).toNat
      (((get8 t.px (i + c)).toNat * a + ground.toNat * (255 - a)) / 255).toUInt8

/-- The tray painted: the ground, and each picture scaled into its slot. -/
def render (g : Geom) (pics : List Rgba) : Rgba :=
  let (slots, w) := layout g (pics.map fun p => (p.w, p.h))
  let ts := (slots.zip pics).map fun (s, p) => (s, scale p s.w s.h)
  { w, h := g.height, px := ⟨Array.ofFn (n := 4 * w * g.height) fun i => trayByte w ts i.val⟩ }

end Pic
