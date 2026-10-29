/- Fixed-width compositor arithmetic. Coordinates carry a 3*2^32 bias,
so all intermediate values fit UInt64 even at either Int32 endpoint.
SlideLaws connects these exports to Translate's integer geometry. -/
namespace Slide

@[inline] def lift (x : Int32) : UInt64 :=
  x.toUInt32.toUInt64 + if x.toUInt32 < 2147483648 then 12884901888 else 8589934592

@[inline] def sub (a b : UInt64) : UInt64 := if a < b then 0 else a - b
@[inline] def sub32 (a b : UInt64) : UInt32 := if a < b then 0 else (a - b).toUInt32
@[inline] def low (a b : UInt64) : UInt64 := if a < b then a else b
@[inline] def high (a b : UInt64) : UInt64 := if a < b then b else a

@[inline] def position (pin : Bool) (base : UInt32) (origin sample : Int32) : UInt64 :=
  if pin then lift origin else sub (sub (lift origin + lift sample) 12884901888) base.toUInt64

@[inline] def fillOrigin (pin : Bool) (base top bottom : UInt32) (sample : Int32) : UInt64 :=
  let offset := if pin then 12884901888 + base.toUInt64 else lift sample
  sub (12884901888 + top.toUInt64) 48 + (sub (offset + bottom.toUInt64) top.toUInt64 % 48)

@[inline] def crop (which : UInt8) (p h top bottom : UInt64) : UInt32 :=
  let a := low h (sub (12884901888 + top) p)
  let z := high a (low h (sub (12884901888 + bottom) p))
  if which == 0 then a.toUInt32 else if which == 1 then z.toUInt32
    else if which == 2 then sub32 (p + a) 12884901888 else sub32 (p + z) 12884901888

@[export lq_slide_edge]
def edge (fill : Bool) (which : UInt8) (pin : Bool) (base : UInt32)
    (origin : Int32) (height top bottom : UInt32) (sample : Int32) : UInt32 :=
  let p := if fill then fillOrigin pin base top bottom sample else position pin base origin sample
  let h := if fill then sub bottom.toUInt64 top.toUInt64 + 48 else height.toUInt64
  crop which p h top.toUInt64 bottom.toUInt64

@[export lq_slide_delta]
def delta (pin : Bool) (base : UInt32) (sample : Int32) : Int32 :=
  (if pin then (0 : UInt32) else sample.toUInt32 - base).toInt32

@[export lq_slide_source]
def pick (pin : Bool) (base : UInt32) (origin : Int32) (height : UInt32)
    (sample : Int32) (y : UInt32) : Int64 :=
  let p := position pin base origin sample
  let q := 12884901888 + y.toUInt64
  (if p ≤ q && q - p < height.toUInt64 then q - p else 18446744073709551615).toInt64

@[export lq_slide_fill_row]
def fillRow (pin : Bool) (base top bottom : UInt32) (sample : Int32) (y : UInt32) : UInt32 :=
  sub32 (12884901888 + y.toUInt64) (fillOrigin pin base top bottom sample)

end Slide
