import engine.renderer.TextLaws
import engine.renderer.WrapLaws

/-! Synthetic mixed-script chat text with explicit bidi controls, combining
marks, European digits and Arabic-Indic digits. The font is a layout-only
fallback fixture; these checks do not establish native font-file fidelity. -/
namespace Vacuity.RendererText

def font : Font.Font := { bytes := .empty, cell := 20, emoji := default }
def mixed : Array UInt32 := #[0x41, 0x20, 0x5D0, 0x31, 0x32, 0x20, 0x627, 0x661, 0x200F]

theorem permutation : (Text.visual mixed).1.toList.Perm mixed.toList :=
  Text.visual_perm mixed

theorem visibleGlyphs : (Text.place font mixed).1.toList.map (·.c) =
    mixed.toList.filter (fun c => !Text.isInvisible c) :=
  Text.place_shows font mixed

theorem starts :
    ((Text.placeL font [0x41, 0x301, 0x42, 0x200F, 0x43] 12 0).1.filter
      (fun g => !Text.isMark g.c)).map (·.x) =
      Text.starts 12 (([0x41, 0x301, 0x42, 0x200F, 0x43].filter
        fun c => !Text.isInvisible c && !Text.isMark c).map (Text.adv font)) :=
  Text.place_starts font [0x41, 0x301, 0x42, 0x200F, 0x43] 12 0

def euro : List UInt32 := [0x5D0, 0x24, 0x31, 0x32, 0x3A, 0x33, 0x30, 0x25, 0x5D1]
def euroRun : List UInt32 := [0x24, 0x31, 0x32, 0x3A, 0x33, 0x30, 0x25]
theorem europeanOrder : euroRun <:+: Text.visualIn true euro :=
  Text.numbers_keep_order true euro euroRun (by decide)

def arabic : List UInt32 := [0x627, 0x661, 0x2C, 0x662, 0x628]
def arabicRun : List UInt32 := [0x661, 0x2C, 0x662]
theorem arabicOrder : arabicRun <:+: Text.visualIn true arabic :=
  Text.arabic_numbers_keep_order true arabic arabicRun (by decide)
example : ¬ [0x662, 0x2C, 0x661] ∈ Text.numberRuns .an true arabic := by decide
example : ¬ [0x32, 0x31] ∈ Text.numberRuns .en true euro := by decide

theorem controls : Text.bidiControls.all (fun c => Text.dirOf c == .on) = true :=
  Text.controls_neutral

theorem invisibles : Text.isInvisible 0x200E = true ∧ Text.isInvisible 0x200F = true :=
  Text.marks_invisible
example : Text.isInvisible 0x41 = false := by decide

-- A long name with a Hebrew suffix: cut to a logical prefix if needed.
theorem ellipsis :
    let cs := Text.shape (font.emoji.emojify ("A long name אב".toList.toArray.map (·.val)))
    (Text.shown (Text.oneLine font 40 "A long name אב")).Perm
        (cs.toList.filter (fun c => !Text.isInvisible c)) ∨
    ∃ k, (Text.shown (Text.oneLine font 40 "A long name אב")).Perm
      (((cs.toList.take k) ++ [0x2026]).filter (fun c => !Text.isInvisible c)) :=
  Text.oneLine_prefix font 40 "A long name אב"

def words : List UInt32 := [0x41, 0x42, 0x20, 0x43, 0x44, 0x20, 0x45, 0x46]
theorem wrapping : (Text.wrapL font 30 words).flatten.filter Text.ns = words.filter Text.ns ∧
    (Text.wrapL font 30 words).flatten.Sublist words :=
  Text.wrap_keeps font 30 words

private theorem characterFits : ∀ c ∈ words, Text.adv font c ≤ 30 := by
  intro c hc
  simp only [words, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Text.adv, font, Font.Font.glyph, Font.Font.glyph?, Font.Font.bitmapGlyph?,
      Font.Font.u32, Font.Font.adv] <;> decide

theorem wrappedWidth : ∀ l ∈ Text.wrapL font 30 words, Text.lineW font l ≤ 30 :=
  Text.wrap_fits font 30 words characterFits

end Vacuity.RendererText
