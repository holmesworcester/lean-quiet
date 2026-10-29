/- Integer geometry and composition contract for per-vsync translation.
Slide supplies the fixed-width native exports; SlideLaws proves them equal
to these functions for every ABI input. No app state or frame work is
needed to translate the last publication. -/
import engine.renderer.Slide
import engine.renderer.Surface
import engine.renderer.Cover
namespace Translate
open Geometry

def position (pin : Bool) (base origin sample : Int) : Int :=
  origin + if pin then 0 else sample - base

def row (f : Surface.Frame) (sample : Int) (r : Nat) : Int :=
  position f.pin f.b f.origin sample + r

def rect (pin : Bool) (base origin sample : Int) (height top bottom : Nat) : Surface.Rect :=
  Surface.crop (position pin base origin sample) height top bottom

def source (pin : Bool) (base origin sample : Int) (height : Nat) (y : Int) : Option Nat :=
  let r := y - position pin base origin sample
  if 0 ≤ r ∧ r < height then some r.toNat else none

/-- The content position at screen y; bottom-anchored as Geometry.home. -/
def content (sample : Int) (bottom : Nat) (y : Int) : Int := sample + bottom - 1 - y

/-- A periodic fill plane covers the viewport, with the tile moving with
content even when the painted buffer is wholly outside the viewport. -/
def fillOrigin (pin : Bool) (base sample : Int) (top bottom : Nat) : Int :=
  (top : Int) - 48 + (((if pin then base else sample) + bottom - top) % 48)

def fillRect (pin : Bool) (base sample : Int) (top bottom : Nat) : Surface.Rect :=
  Surface.crop (fillOrigin pin base sample top bottom) (bottom - top + 48) top bottom

/-- Composition's content-level contract. The frame holds Cover.seen at
high - 1 - r. Outside that buffer the compositor supplies the hold tile. -/
def seen (f : Surface.Frame) (height : Nat) (high : Int) (pad bottom : Nat)
    (more : Bool) (rows : List (Nat × Option Nat)) (sample y : Int) : Cover.Px :=
  match source f.pin f.b f.origin sample height y with
  | some r => Cover.seen pad bottom more rows (high - 1 - r).toNat
  | none => .unloaded

/-- Integer specification of the ABI rectangles. Slide.edge implements
it with fixed-width arithmetic; SlideLaws proves equality for every input. -/
def edge (fill : Bool) (which : UInt8) (pin : Bool) (base : UInt32)
    (origin : Int32) (height top bottom : UInt32) (sample : Int32) : UInt32 :=
  let r := if fill then fillRect pin base.toNat sample.toInt top.toNat bottom.toNat
    else rect pin base.toNat origin.toInt sample.toInt height.toNat top.toNat bottom.toNat
  (if which == 0 then r.src0 else if which == 1 then r.src1
    else if which == 2 then r.dst0 else r.dst1).toUInt32

/-- Raw touch records carry the translation, so taps use the image seen
at acquisition even while the last Lean frame is moving. -/
def delta (pin : Bool) (base : UInt32) (sample : Int32) : Int32 :=
  (if pin then 0 else sample.toInt - base.toNat).toInt32

/-- Integer specification of the painted-row selector implemented by Slide.pick. -/
def pick (pin : Bool) (base : UInt32) (origin : Int32) (height : UInt32)
    (sample : Int32) (y : UInt32) : Int64 :=
  match source pin base.toNat origin.toInt sample.toInt height.toNat y.toNat with
  | some r => (r : Int).toInt64
  | none => -1

/-- The row in the already-published fill plane. -/
def fillRow (pin : Bool) (base : UInt32) (top bottom : UInt32)
    (sample : Int32) (y : UInt32) : UInt32 :=
  ((y.toNat : Int) - fillOrigin pin base.toNat sample.toInt top.toNat bottom.toNat).toNat.toUInt32

end Translate
