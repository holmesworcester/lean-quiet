/-
The decoder for native callers (the Android harness's JNI glue):
`lean_qr_decode_luma` takes a luma frame and gives back the payload and a
one-line description, or `none`.
-/
import engine.renderer.qr.Decode

namespace Qr

/-- Version, level, mask, corrected codewords, and whether the frame was a
mirror image: "v10 M mask 4 fixed 3 mirrored no". -/
def Decoded.describe (d : Decoded) : String :=
  s!"v{d.version} {d.ecc.name} mask {d.mask} fixed {d.corrected} mirrored {if d.mirrored then "yes" else "no"}"

@[export lean_qr_decode_luma]
def decodeLuma (w h stride : UInt32) (px : ByteArray) : Option (ByteArray × String) :=
  (decodeImage { w := w.toNat, h := h.toNat, stride := stride.toNat, px }).map fun d =>
    (d.payload, d.describe)

end Qr
