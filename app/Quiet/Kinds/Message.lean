/-
A message: its fact, its text opened with the content key it names, its
author (Profile), its attachments (File) and its reactions (React), each
read by that kind; the row's data is theirs put together. The row's
layout and pixels are Row's.

Reads: the message's own fact; its key (`key.byId [kid]`, local); then its
children's reads. A parent (the list) passes only the message's id. A
message whose key this device lacks says so, until the key's wrap opens.
-/
import Quiet.Kinds.Profile
import Quiet.Kinds.React
import Quiet.Kinds.File

namespace Kinds.Message
open Engine Community Data

/-- What a message this device cannot open yet says. -/
def cantRead : String := "🔒 Can't read this yet: the key is on its way."

variable {m : Type → Type} [Monad m] [Reads m]

def read (c me msg : Id) : m (Option (Row.RowData × Array Q)) := do
  let (f, pending, deps) ← readFact msg #[]
  let some (.message _ u _ kid sealed tm) := f | return none
  let (ks, _, deps) ← readList (key.byId.query [kid] (limit := some 1)) deps
  let text := match ks.rows.head? with
    | some (_, .key _ _ k) => (openSealed cryptoSeal c kid sealed k).map Profile.bytesStr
    | _ => none
  let (who, deps) ← Profile.read c u deps
  let (pics, deps) ← File.read c msg deps
  let (tallies, deps) ← React.read c msg me deps
  return some (⟨who.name, none, text.getD cantRead, tm, pics.toList, tallies, pending, false⟩, deps)

end Kinds.Message
