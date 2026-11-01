import ops.Commands
import engine.renderer.Image
import engine.renderer.Row
import ops.community.Proofs

/-!
`community.channel.message.attachment.chunk`: its component, which reads its own facts, and the component's laws.
-/
namespace Kinds.File
open _root_.Engine _root_.Community _root_.Data
variable {m : Type → Type} [Monad m] [Reads m]

/-- One attachment's picture, its info opened: how many of its file's
chunks are here, of how many (`Community.progress`), and once all are,
their op ids in index order. -/
def pic (c att root : Id) (len : Nat) (info : FileMeta) (fk fn : ByteArray) (deps : Array Q) :
    m (Row.Pic × Array Q) := do
  let ((got, total), deps) ← readView (progress c att len) deps
  let p : Row.Pic := { hash := root, w := info.w, h := info.h, len, preview := info.preview,
                       got, total, key := fk, nonce := fn, attachment := att }
  if !p.complete then return (p, deps)
  let (ch, _, deps) ← readList (chunk.byAttachment.query [c, att] (desc := false)) deps
  return ({ p with chunks := ch.rows.map (·.1.2) }, deps)
end Kinds.File
namespace FileImage
open _root_.Engine

def slices (raw : List ByteArray) : Option (List ByteArray) :=
  raw.mapM fun b => do
    let o ← Op.decode b
    match (Codec.decode o.body : Option Community.Body) with
    | some (.chunk _ _ _ slice _) => some slice
    | _ => none

def source (p : Row.Pic) (raw : List ByteArray) : Option Image.Src :=
  ((slices raw).bind fun chunks => Community.openFile chunks p.key p.nonce).bind Image.decode

end FileImage
