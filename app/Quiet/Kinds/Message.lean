/-
A message: its fact, its author (Profile), its pictures (Blob) and its
reactions (React), each read by that kind; the row's data is theirs put
together. The row's layout and pixels are Row's.

Reads: the message's own fact; then its children's reads. A parent (the
list) passes only the message's id.
-/
import Quiet.Kinds.Profile
import Quiet.Kinds.React

namespace Kinds.Message
open Engine Community Data

variable {m : Type → Type} [Monad m] [Reads m]

def read (c me msg : Id) : m (Option (Row.RowData × Array Q)) := do
  let (f, pending, deps) ← readFact msg #[]
  let some (.message _ u _ _ text tm atts) := f | return none
  let (who, deps0) ← Profile.read c u deps
  let mut pics := #[]
  let mut acc := deps0
  for b in atts do
    let (p, d) ← Blob.read b acc
    acc := d
    if let some p := p then pics := pics.push p
  let (tallies, deps1) ← React.read c msg me acc
  return some (⟨who.name, who.avatar, Profile.bytesStr text, tm, pics.toList, tallies, pending, false⟩, deps1)

end Kinds.Message
