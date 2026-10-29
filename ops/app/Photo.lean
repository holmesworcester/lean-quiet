/- A photo selection belongs to one composer request. OS presentation may
suspend the app; navigating or switching communities revokes the request. -/
import engine.renderer.Image
import engine.core.Core

namespace Photo

structure Request where
  token : UInt32
  owner : Engine.Id
  deriving Inhabited, BEq

def Request.accepts (r : Request) (token : UInt32) (owner : Engine.Id) (composer : Bool) : Bool :=
  r.token != 0 && r.token == token && r.owner == owner && composer

/-- The native seam supplies straight sRGB RGBA, already oriented and bounded.
Validate before constructing the pixel array or allocating an encoded image. -/
def pixels (header : Array UInt32) (rgba : ByteArray) : Option Image.Src := do
  if header.size != 4 || header[1]! != 1 then none else do
    let w := header[2]!.toNat
    let h := header[3]!.toNat
    if w == 0 || h == 0 || w > 2048 || h > 2048 || rgba.size != w * h * 4 then none
    else some (Image.Src.ofRgba ⟨w, h, rgba⟩)

theorem inactive_rejects (r : Request) (token : UInt32) (owner : Engine.Id) :
    r.accepts token owner false = false := by simp [Request.accepts]

theorem stale_rejects (r : Request) (token : UInt32) (owner : Engine.Id)
    (h : (r.token == token) = false) : r.accepts token owner true = false := by
  simp [Request.accepts, h]

theorem other_owner_rejects (r : Request) (token : UInt32) (owner : Engine.Id)
    (h : (r.owner == owner) = false) : r.accepts token owner true = false := by
  simp [Request.accepts, h]

end Photo
