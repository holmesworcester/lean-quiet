import engine.renderer.pic.Laws
import engine.renderer.ImageLaws
import engine.renderer.Ttf.Laws
import engine.renderer.Ttf.Memo

set_option maxRecDepth 10000
set_option maxHeartbeats 800000
namespace Vacuity.RendererImages

-- Two RGBA pixels: opaque red and half-transparent green.
def picture : Pic.Rgba := ⟨2, 1, ByteArray.mk #[255, 0, 0, 255, 0, 255, 0, 128]⟩
def encoded : ByteArray := ByteArray.mk #[113, 111, 105, 102, 0, 0, 0, 2, 0, 0, 0, 1, 4, 0,
  255, 255, 0, 0, 255, 255, 0, 255, 0, 128, 0, 0, 0, 0, 0, 0, 0, 1]
def decodedPicture : Pic.Rgba := (Pic.decode encoded).getD picture
private theorem decoded : Pic.decode encoded = some decodedPicture := by
  have hs : (Pic.decode encoded).isSome = true := by decide
  cases h : Pic.decode encoded with
  | none => simp [h] at hs
  | some p => simp [decodedPicture, h]

theorem pictureSized : 1 ≤ decodedPicture.w ∧ decodedPicture.w ≤ Pic.maxSide ∧
    1 ≤ decodedPicture.h ∧ decodedPicture.h ≤ Pic.maxSide ∧ decodedPicture.wellFormed = true :=
  Pic.decode_sized decoded

theorem imageSized :
    let s := Image.Src.ofRgba decodedPicture
    1 ≤ s.w ∧ s.w ≤ Pic.maxSide ∧ 1 ≤ s.h ∧ s.h ≤ Pic.maxSide ∧ s.px.size = s.w * s.h :=
  Image.decode_sized (b := encoded) (s := Image.Src.ofRgba decodedPicture) (by
    unfold Image.decode; rw [decoded]; rfl)
example : decodedPicture.w = 2 ∧ decodedPicture.h = 1 ∧ decodedPicture.px.size = 8 := by decide
example : Pic.decode "not a picture".toUTF8 = none := by rfl
example : Image.decode "not a picture".toUTF8 = none := by rfl

def tray : Pic.Geom := ⟨12, 2, 3⟩
def sizes : List (Nat × Nat) := [(4032, 3024), (3024, 4032), (2, 1)]
theorem layoutSizes : (Pic.layout tray sizes).1.map (fun s => (s.w, s.h)) =
    sizes.map (fun p => Pic.fit p.1 p.2 tray.box) :=
  Pic.layout_sizes tray sizes

theorem separated : (Pic.layout tray sizes).1.Pairwise (fun a b => a.x + a.w + tray.gap ≤ b.x) :=
  Pic.layout_apart tray (by decide) sizes

theorem inside : ∀ s ∈ (Pic.layout tray sizes).1,
    tray.pad ≤ s.x ∧ s.x + s.w + tray.pad ≤ (Pic.layout tray sizes).2 ∧
    tray.pad ≤ s.y ∧ s.y + s.h + tray.pad ≤ tray.height :=
  Pic.layout_inside tray (by decide) sizes
example : (Pic.layout tray sizes).1.map (fun s => (s.w, s.h)) = [(8, 6), (6, 8), (2, 1)] := by decide

theorem renderSized : (Pic.render tray [picture]).wellFormed = true :=
  Pic.render_wellFormed tray [picture]
theorem opacity : (Pic.render tray [picture]).px[4 * 0 + 3]? = some 255 :=
  Pic.render_opaque tray [picture] 0 (by decide)
theorem scaled : (Pic.scale picture 1 1).wellFormed = true := Pic.scale_wellFormed picture 1 1

-- Checked font byte/character-map and cache primitives, no native font file.
def fontBytes := ByteArray.mk #[0, 127, 255, 42]
theorem byteBound : ∃ hi : 2 < fontBytes.size, fontBytes[2].toNat = 255 :=
  Ttf.byte_in_bounds fontBytes 2 255 (by rfl)
example : Ttf.u8 fontBytes 4 = none := rfl

def cmap : Ttf.Cmap := [⟨65, 90, .sequential 3⟩, ⟨97, 122, .sequential 29⟩]
theorem character : ∃ e ∈ cmap, e.contains 66 = true ∧ e.glyph 66 = 4 :=
  Ttf.cmap_entry cmap 66 4 (by rfl)
example : Ttf.lookup cmap 63 = none := rfl

theorem saturated : (Ttf.coverage 128).toNat = min 255 (128 * 255 / 64) :=
  Ttf.coverage_value 128
example : Ttf.coverage 128 = 255 ∧ Ttf.coverage 0 = 0 := by decide

def glyph : Ttf.Bitmap := ⟨-1, -1, 2, 2, 1, 1, 1, 0, 1, 0, ByteArray.mk #[0, 127, 255, 0]⟩
def squares : Ttf.Memo.Table (fun k => k * k) := Ttf.Memo.Table.new _ fun _ => 200

/-- A key on the table's third page, past its first page boundary. -/
theorem tableAnswers : squares.get 130 = 130 * 130 := Ttf.Memo.Table.get_eq squares 130
/-- A key past the table falls back to the function. -/
theorem tablePast : squares.get 9000 = 9000 * 9000 := Ttf.Memo.Table.get_eq squares 9000

def face : Ttf.Memo.Source := Ttf.Memo.source ByteArray.empty 20 20
theorem memoRaster : face.bitmap 4 = face.bitmapFast 4 :=
  congrFun (congrFun Ttf.Memo.bitmap_eq_fast face) 4
theorem compactSame : Ttf.Memo.compact glyph = glyph := Ttf.Memo.compact_eq glyph
example : glyph.Valid := by decide
example : ¬ ({ glyph with pixels := ByteArray.mk #[0] } : Ttf.Bitmap).Valid := by decide

end Vacuity.RendererImages
