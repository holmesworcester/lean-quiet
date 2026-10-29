/- Raster twin of the compositor: copy a translated painted row or the
published holdLine plane. The selector is the same exported Lean function
that host.c executes; SlideLaws transfers TranslateLaws and its Cover contract. -/
import engine.renderer.Translate
namespace Translate

def compose (words : Array UInt32) (sample : Int32) (height : Nat) (bg : ByteArray)
    (list top bot hold : Array ByteArray) : Array ByteArray := Id.run do
  let mut out := Surface.compose words height bg list top bot
  for y in [words[7]!.toNat:words[10]!.toNat] do
    let r := Slide.pick (words[22]! != 0) words[15]! words[20]!.toInt32 words[21]! sample y.toUInt32
    let pixel := if r.toInt ≥ 0 then list[r.toInt.toNat]!
      else hold[(Slide.fillRow (words[22]! != 0) words[15]! words[7]! words[10]! sample y.toUInt32).toNat]!
    out := out.set! y pixel
  return out
end Translate
