/-
A person, by their newest profile: its name, and its avatar's blob.

Reads: `profile.byUser [c, u]` (newest first, one row), then the avatar's
blob (Blob.read). Drawn by Message's view (the avatar and the name).
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

end Kinds.Profile
