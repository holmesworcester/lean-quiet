/-
A person, by their newest profile: its name, and its avatar's blob.

Reads: `profile.byUser [c, u]` (newest first, one row), then the avatar's
blob (Blob.read). Drawn by Message's view (the avatar and the name).

Every name read starts from a member (an admission, or a message's
author), never from `profile.all`: a requester's profile is filed before
anyone admits it, and is not a member's.
-/
import Quiet.Kinds.Blob

namespace Kinds.Profile
open Engine Community Data

structure Data where
  name : String
  avatar : Option ByteArray
  deriving BEq, Inhabited

def bytesStr (b : ByteArray) : String := (String.fromUTF8? b).getD "?"

variable {m : Type → Type} [Monad m] [Reads m]

def read (c u : Id) (deps : Array Q) : m (Data × Array Q) := do
  let (a, _, deps) ← readList (profile.byUser.query [c, u] (limit := some 1)) deps
  match a.rows.head? with
  | some (_, .profile _ _ n _ av) =>
    match av.head? with
    | some bid =>
      let (pic, deps) ← Blob.read bid deps
      return (⟨bytesStr n, pic.map (·.hash)⟩, deps)
    | none => return (⟨bytesStr n, none⟩, deps)
  | _ => return (⟨"…", none⟩, deps)

/-- The members of c, by admission (each user once, in admission order),
with their profiles. -/
def members (c : Id) : m (Array (Id × Data) × Array Q) := do
  let (a, _, deps) ← readList (admission.all.query [c] (limit := some 200)) #[]
  let mut deps := deps
  let mut seen : List Id := []
  let mut out := #[]
  for (_, f) in a.rows do
    if let .admission _ u _ _ := f then
      if seen.contains u then continue
      seen := u :: seen
      let (p, d) ← read c u deps
      deps := d
      out := out.push (u, p)
  return (out, deps)

end Kinds.Profile
