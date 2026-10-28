/-
A person, by their newest profile: its name.

Reads: `profile.byUser [c, u]` (newest first, one row). Drawn by
Message's view (the name, and the avatar's initial).

Every name read starts from a member (an admission, or a message's
author), never from `profile.all`: a requester's profile is filed before
anyone admits it, and is not a member's.
-/
import engine.renderer.Data
import ops.community.reaction.View

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

/-- The users of these live admissions, each once (in admission order),
with their devices. -/
def byUser (ls : List (Id × Key × Key)) : List (Id × List Key) :=
  (React.uniq (ls.map (·.1))).map fun u => (u, (ls.filter fun l => decide (l.1 = u)).map (·.2.1))

/-- The community's present members: users with a live device (the
engine's `live`: admitted, and none of the device's users removed), with
those devices. Laws (PeopleLaws): `present_iff`, `present_not_removed`. -/
def present (c : Id) : View Fact (List (Id × List Key)) := do
  let a ← admission.all.read [c]
  let ls ← live c a.rows
  pure (byUser ls)

/-- The present members of c with their profiles, for the people list
and its count. A removed member is not among them (their messages keep
their names: Message reads the profile by author). -/
def members (c : Id) : m (Array (Id × List Key × Data) × Array Q) := do
  let (ps, deps) ← readView (present c) #[]
  let mut deps := deps
  let mut out : Array (Id × List Key × Data) := #[]
  for (u, ds) in ps do
    let (p, d) ← read c u deps
    deps := d
    out := out.push (u, ds, p)
  return (out, deps)

end Kinds.Profile
