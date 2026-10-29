/- Op-type components use the generic Work pool. A picture's QOI decode
is one native/pure unit; scaling yields every eight output rows. The
measured largest unit is reported separately from the scheduler's laws. -/
import ops.community.attachment.Image
import engine.renderer.Work
import engine.core.WindowIndex

namespace Raster
open Engine Paint

inductive Key where
  | row (generation : Nat) (message : Id) (version : Nat) (ready : List Bool) (theme : Theme.Value)
  | dim (generation : Nat) (message : Id) (version : Nat) (ready : List Bool) (theme : Theme.Value)
  | image (key : FileImage.Key) (theme : Theme.Value)
  deriving BEq

private theorem lawfulTheme : LawfulBEq Theme.Value where
  eq_of_beq {a b} h := by cases a <;> cases b <;> cases h <;> rfl
  rfl {a} := by cases a <;> rfl
attribute [local instance] Engine.lawfulBEqByteArray lawfulTheme
deriving instance ReflBEq, LawfulBEq for Key
/-- Scheduler key equality is equality of every render input named by Key. -/
theorem key_eq (a b : Key) : (a == b) = true ↔ a = b := beq_iff_eq

def messageOwner (community message : Id) : Demand.Owner :=
  ["community".toUTF8, community, "message".toUTF8, message]

def pictureOwner (community message attachment : Id) : Demand.Owner :=
  messageOwner community message ++ ["attachment".toUTF8, attachment]

/-- Bottom-origin content bounds, shared by component mounting and work
priority. A margin is explicit; it does not silently retain whole rows. -/
def near (bottom height offset viewport margin : Nat) : Bool :=
  bottom ≤ offset + viewport + margin && offset - margin ≤ bottom + height

/-- Exactly the sample box used by Image.scaled for target row y. -/
def scaledRow (src : Image.Src) (w h y : Nat) (bg : Color) : ByteArray :=
  let y0 := y * src.h / max h 1
  let y1 := max (y0 + 1) ((y + 1) * src.h / max h 1)
  (Image.scaleCrop src 0 y0 src.w (y1 - y0) w 1 bg).rows[0]!

def image (source : Unit → Option Image.Src) (w h : Nat) (theme : Theme.Value)
    (preview : Bool) : IO (Work.Action Bitmap) := do
  let state ← IO.mkRef ((none : Option Image.Src), (#[] : Array ByteArray))
  return fun _ => do
    let (src, rows) ← state.get
    let bg := Palette.color theme .bg
    match src with
    | none =>
      match source () with
      | none => return some (Bitmap.blank w h (solid (Palette.color theme .selected) w))
      | some src => state.set (some src, #[]); return none
    | some src =>
      let mut rows := rows
      for y in [rows.size:min (max h 1) (rows.size + 8)] do
        let row := scaledRow src (max w 1) (max h 1) y bg
        let row := if preview then (Arrival.soften bg { w := max w 1, rows := #[row] }).rows[0]! else row
        rows := rows.push row
      if rows.size == max h 1 then return some { w := max w 1, rows }
      state.set (some src, rows)
      return none

def fileSource (p : Row.Pic) (raw : List ByteArray) : Option Image.Src :=
  FileImage.source p raw

end Raster
