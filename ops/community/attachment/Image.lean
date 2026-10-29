/- Image preparation owned by an attachment op component. Query results
contain encoded chunk ops; opening and decoding run on the Work worker. -/
import engine.renderer.Row
import engine.renderer.Image
import ops.community.Compose

namespace FileImage
open Engine

abbrev Key := ByteArray × Nat × Nat

def slices (raw : List ByteArray) : Option (List ByteArray) :=
  raw.mapM fun b => do
    let o ← Op.decode b
    match (Codec.decode o.body : Option Community.Body) with
    | some (.chunk _ _ _ slice _) => some slice
    | _ => none

def source (p : Row.Pic) (raw : List ByteArray) : Option Image.Src :=
  ((slices raw).bind fun chunks => Community.openFile chunks p.key p.nonce).bind Image.decode

end FileImage
