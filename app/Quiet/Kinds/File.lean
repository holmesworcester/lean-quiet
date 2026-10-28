/-
A message's attachments (libquiet's op graph: each attachment is a child
of its message, and its chunks are its file's), as the message's
pictures.

Reads: `attachment.byMessage [c, msg]` (the first four: the render
bound); per attachment, its content key (`key.byId [kid]`, local), which
opens its sealed info (name, size, preview, the file's key); and
`chunk.byFile [c, root, len]` in index order, whose count is the download's
progress (Merkle.nChunks len chunks make the file). An attachment whose key
this device lacks shows nothing yet.
-/
import Quiet.Row
import Quiet.Data

namespace Kinds.File
open Engine Community Data

/-- The most attachments a message shows (libquiet's). -/
def maxShown : Nat := 4

variable {m : Type → Type} [Monad m] [Reads m]

def read (c msg : Id) (deps : Array Q) : m (Array Row.Pic × Array Q) := do
  let (as, _, deps) ← readList (attachment.byMessage.query [c, msg] (limit := some maxShown) (desc := false)) deps
  let mut deps := deps
  let mut out := #[]
  for (_, f) in as.rows do
    let .attachment _ _ _ root len kid sealed := f | continue
    let (ks, _, d1) ← readList (key.byId.query [kid] (limit := some 1)) deps
    deps := d1
    let some k := ks.rows.head?.bind fun (_, g) => match g with | .key _ _ k => some k | _ => none
      | continue
    let some (info, fk, fn) := openInfo c kid sealed k | continue
    let (ch, _, d2) ← readList (chunk.byFile.query [c, root, Codec.encode len] (desc := false)) deps
    deps := d2
    out := out.push { hash := root, w := info.w, h := info.h, preview := info.preview,
                      got := ch.rows.length, total := Merkle.nChunks len,
                      chunks := ch.rows.map (·.1.2), key := fk, nonce := fn }
  return (out, deps)

end Kinds.File
