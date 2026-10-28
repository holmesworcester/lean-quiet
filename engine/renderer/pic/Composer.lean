/-
The composer's pictures, for native callers (the Android harness's
image tools, android/app/jni/pic_jni.c).

The native side launches the platform's photo picker or camera, decodes
what comes back (EXIF orientation applied), downsamples it to the size
`fit` gives (`lean_pic_fit`), and hands over RGBA. Everything after that is
here: the picture is checked, encoded as QOI for storage, and drawn into
the tray. The state is a Lean value the native side holds and passes back.
-/
import engine.renderer.pic.Tray

namespace Pic

/-- An attached picture. -/
structure Attachment where
  /-- what is stored -/
  qoi : ByteArray
  w : Nat
  h : Nat
  /-- the size the picture had before the native side downsampled it -/
  ow : Nat
  oh : Nat
  /-- its thumbnail (fitted into a 512-pixel box), drawn from the stored QOI -/
  thumb : Rgba

abbrev Composer := Array Attachment

/-- How a picture is described to the reader: "2 · 1536×2048 (from
3024×4032) · QOI 2.9 MB". -/
def describe (n : Nat) (a : Attachment) : String :=
  let kb := (a.qoi.size + 512) / 1024
  let size := if kb ≥ 1024 then s!"{kb / 1024}.{kb % 1024 * 10 / 1024} MB" else s!"{kb} KB"
  s!"{n} · {a.w}×{a.h} (from {a.ow}×{a.oh}) · QOI {size}"

/-- Takes a picture from the native side: `w × h` RGBA, downsampled from
an `ow × oh` original. Refused unless the bytes are exactly `w × h` pixels
and the size is what `fit` gives the original (so at most 2048 a side),
and unless the QOI stored for it decodes back to exactly these pixels
(`add_stored`); the thumbnail is drawn from that decoded copy, so the tray
shows what was stored. -/
def add (c : Composer) (ow oh w h : Nat) (px : ByteArray) : Composer × String :=
  let pic : Rgba := { w, h, px }
  if w < 1 || h < 1 || !pic.wellFormed then (c, s!"refused: {px.size} bytes are not {w}×{h} RGBA")
  else if fit ow oh attachEdge != (w, h) then
    (c, s!"refused: {w}×{h} is not {ow}×{oh} fitted within {attachEdge}")
  else
    let qoi := encode pic
    match decode qoi with
    | some back =>
      if back.w = w ∧ back.h = h ∧ back.px = px then
        let (tw, th) := fit w h 512
        let a : Attachment := { qoi, w, h, ow, oh, thumb := scale back tw th }
        let c' := Array.push c a
        (c', describe c'.size a)
      else (c, "refused: the QOI does not decode to the picture")
    | none => (c, "refused: the QOI does not decode")

def trayGeom (height : Nat) : Geom := { height, pad := height / 12, gap := height / 12 }

/-- The tray, `height` pixels high. -/
def tray (c : Composer) (height : Nat) : Rgba :=
  render (trayGeom height) (c.toList.map (·.thumb))

/-! ## For the native side -/

@[export lean_pic_empty] def empty (_ : Unit) : Composer := #[]

/-- The `fit` size within `edge`, packed as `w * 2^32 + h`. -/
@[export lean_pic_fit] def fitPacked (w h edge : UInt32) : UInt64 :=
  let (a, b) := fit w.toNat h.toNat edge.toNat
  (a * 4294967296 + b).toUInt64

@[export lean_pic_add]
def addExport (c : Composer) (ow oh w h : UInt32) (px : ByteArray) : Composer × String :=
  add c ow.toNat oh.toNat w.toNat h.toNat px

@[export lean_pic_count] def count (c : Composer) : UInt32 := c.size.toUInt32

/-- The tray's RGBA, `height` rows (its width is the size / 4 / height). -/
@[export lean_pic_tray] def trayExport (c : Composer) (height : UInt32) : ByteArray :=
  (tray c height.toNat).px

/-- The stored QOI of attachment `i` (empty if there is none). -/
@[export lean_pic_blob] def blob (c : Composer) (i : UInt32) : ByteArray :=
  (c[i.toNat]?.map (·.qoi)).getD .empty

end Pic
