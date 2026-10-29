/-
A message's attachments (libquiet's op graph: each attachment is a child
of its message, and its chunks are its file's), as the message's
pictures.

Reads: `attachment.byMessage [c, msg]` (the first four: the render
bound); per attachment, its content key (`key.byId [kid]`, local), which
opens its sealed info (name, size, preview, the file's key); and the
attachment's chunk list (`chunk.byAttachment [c, att]`):
its count is the download's progress (`Community.progress`, read as is),
and once every chunk is here the list itself, in index order, is what
assembles the file. An attachment whose key this device lacks shows
nothing yet.
-/
import engine.renderer.Row
import engine.renderer.Data

namespace Kinds.File
open Engine Community Data

/-- The most attachments a message shows (libquiet's). -/
def maxShown : Nat := 4

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

def read (c msg : Id) (deps : Array Q) (withProgress : Bool := true) : m (Array Row.Pic × Array Q) := do
  let (as, _, deps) ← readList (attachment.byMessage.query [c, msg] (limit := some maxShown) (desc := false)) deps
  let mut deps := deps
  let mut out := #[]
  for ((_, att), f) in as.rows do
    let .attachment _ _ _ root len kid sealed := f | continue
    let (ks, _, d1) ← readList (key.byId.query [kid] (limit := some 1)) deps
    deps := d1
    let some k := ks.rows.head?.bind fun (_, g) => match g with | .key _ _ k => some k | _ => none
      | continue
    let some (info, fk, fn) := openInfo c kid sealed k | continue
    -- The parent's layout manifest needs immutable dimensions/preview,
    -- never the offscreen child's changing chunk/progress subscriptions.
    let (p, d2) ← if withProgress then pic c att root len info fk fn deps else
      pure ({
        hash := root, w := info.w, h := info.h, len, preview := info.preview,
        key := fk, nonce := fn, attachment := att : Row.Pic }, deps)
    deps := d2
    out := out.push p
  return (out, deps)

/-- The attachment component's own view. Its live subscriptions end when
its last visible/prefetch owner leaves, independently of its message. -/
def readOne (c att : Id) (withProgress : Bool := true) : m (Option Row.Pic × Array Q) := do
  let (fact, _, deps) ← readFact att #[]
  let some (.attachment _ _ _ root len kid sealed) := fact | return (none, deps)
  let (ks, _, deps) ← readList (key.byId.query [kid] (limit := some 1)) deps
  let some key := ks.rows.head?.bind fun (_, f) => match f with | .key _ _ k => some k | _ => none
    | return (none, deps)
  let some (info, fk, fn) := openInfo c kid sealed key | return (none, deps)
  if !withProgress then
    return (some { hash := root, w := info.w, h := info.h, len, preview := info.preview,
                   key := fk, nonce := fn, attachment := att }, deps)
  let (p, deps) ← pic c att root len info fk fn deps
  return (some p, deps)

/-- The collection discovers attachment op identities. Each attachment
opens its own metadata, including dimensions, through readOne. -/
def ids (c msg : Id) : m (List Id × Array Q) := do
  let (a, _, deps) ← readList (attachment.byMessage.query [c, msg]
    (limit := some maxShown) (desc := false)) #[]
  return (a.rows.map (·.1.2), deps)

end Kinds.File
