/-
A person, by their newest profile: its name.

Reads: `profile.byUser [c, u]` (newest first, one row). Drawn by
Message's view (the name, and the avatar's initial).

Every name read starts from a member (an admission, or a message's
author), never from `profile.all`: a requester's profile is filed before
anyone admits it, and is not a member's.
-/
import Quiet.Data

namespace Kinds.Profile
open Engine Community Data

structure Data where
  name : String
  deriving BEq, Inhabited

def bytesStr (b : ByteArray) : String := (String.fromUTF8? b).getD "?"

variable {m : Type → Type} [Monad m] [Reads m]

def read (c u : Id) (deps : Array Q) : m (Data × Array Q) := do
  let (a, _, deps) ← readList (profile.byUser.query [c, u] (limit := some 1)) deps
  match a.rows.head? with
  | some (_, .profile _ _ n _) => return (⟨bytesStr n⟩, deps)
  | _ => return (⟨"…"⟩, deps)

/-- The members of c, by admission (each user once, in admission order),
with their devices and profiles. -/
def members (c : Id) : m (Array (Id × List Key × Data) × Array Q) := do
  let (a, _, deps) ← readList (admission.all.query [c] (limit := some 200)) #[]
  let mut deps := deps
  let mut out : Array (Id × List Key × Data) := #[]
  for (_, f) in a.rows do
    if let .admission _ u dev _ := f then
      match out.findIdx? (·.1 == u) with
      | some i => out := out.modify i fun (u, ds, p) => (u, dev :: ds, p)
      | none =>
        let (p, d) ← read c u deps
        deps := d
        out := out.push (u, [dev], p)
  return (out, deps)

end Kinds.Profile
