/-
A message: its fact, its text opened with the content key it names, its
author (Profile), its attachments (File) and its reactions (React), each
read by that kind; the row's data is theirs put together. The row's
layout and pixels are Row's.

Reads: the message's own fact; its key (`key.byId [kid]`, local); then its
children's reads. A parent (the list) passes only the message's id. A
message whose key this device lacks is not shown until the key's wrap
opens.
-/
import ops.community.profile.View
import ops.community.reaction.View
import ops.community.attachment.View

namespace Kinds.Message
open Engine Community Data

variable {m : Type → Type} [Monad m] [Reads m]

def read (c me msg : Id) (attachmentProgress : Bool := true) : m (Option (Row.RowData × Array Q)) := do
  let (f, pending, deps) ← readFact msg #[]
  let some (.message _ u _ kid sealed _ tm) := f | return none
  let (ks, _, deps) ← readList (key.byId.query [kid] (limit := some 1)) deps
  -- no key here yet, or a body it does not open: not shown (the list
  -- leaves such messages out; this is the row's own check)
  let some text := (match ks.rows.head? with
    | some (_, .key _ _ k) => (openSealed cryptoSeal c kid sealed k).map Profile.bytesStr
    | _ => none) | return none
  let (who, deps) ← Profile.read c u deps
  let (twin, deps) ← Profile.namesake c u who.name deps
  let (pics, deps) ← File.read c msg deps attachmentProgress
  let (tallies, deps) ← React.read c msg me deps
  return some (⟨who.name, none, text, tm, pics.toList, tallies, pending, false, twin⟩, deps)

end Kinds.Message
