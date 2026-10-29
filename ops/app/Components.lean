/- Components receive identities and constraints, and observe their own
queries. Lists/sets discover identities; an op component interprets its
own data. The app supplies one interpreter backed by the shared Reader. -/
import ops.app.Reader
import ops.app.Raster

namespace Component
open Engine

structure Scope where
  owner : Demand.Owner
  visible : Bool := true

def Scope.child (s : Scope) (kind : String) (id : Id) : Scope :=
  { s with owner := s.owner ++ [kind.toUTF8, id] }

def Scope.need (s : Scope) (key : Reader.Want) : Demand.Need Reader.Want :=
  ⟨s.owner, key, s.visible⟩

class Queries (m : Type → Type) where
  query : Scope → Reader.Want → m (Option Reader.Val)

export Queries (query)

variable {m : Type → Type} [Monad m] [Queries m]

def author (scope : Scope) (c user : Id) (old : String × Bool) : m (String × Bool) := do
  match ← query scope (.author c user) with
  | some (.author name twin) => return (name, twin)
  | _ => return old

def attachments (scope : Scope) (c msg : Id) (old : List Id) : m (List Id) := do
  match ← query scope (.attachments c msg) with
  | some (.ids ids) => return ids
  | _ => return old

/-- Once opened, an attachment's dimensions/key/preview are immutable.
Retain that measured result without retaining a metadata subscription. -/
def attachment (scope : Scope) (c id : Id) (old : Option Row.Pic) : m (Option Row.Pic) := do
  if old.isSome then return old
  match ← query scope (.attachment c id) with
  | some (.picture p) => return p
  | _ => return none

def picture (scope : Scope) (c id : Id) (old : Row.Pic) : m Row.Pic := do
  match ← query scope (.picture c id) with
  | some (.picture (some p)) => return p
  | _ => return old

def emojis (scope : Scope) (c msg : Id) (old : List String) : m (List String) := do
  match ← query scope (.emojis c msg) with
  | some (.emojis es) => return es
  | _ => return old

def reaction (scope : Scope) (c msg me : Id) (emoji : String) (old : Row.Tally) : m Row.Tally := do
  match ← query scope (.reaction c msg me emoji) with
  | some (.reaction t) => return t
  | _ => return old

/-- Initial measurement composes child answers, without waiting for image
pixels. Pending metadata is distinct from an answered, unavailable file.
Once mounted, each child refreshes only inside its own visibility bounds. -/
def measure (scope : Scope) (c msg : Id) : m (Option (List Row.Pic × List Row.Tally)) := do
  let some (.ids ids) ← query (scope.child "attachments" msg) (.attachments c msg)
    | return none
  let mut pics := []
  for id in ids do
    let some (.picture p) ← query (scope.child "attachment" id) (.attachment c id)
      | return none
    if let some p := p then pics := pics ++ [p]
  let some (.emojis es) ← query (scope.child "reactions" msg) (.emojis c msg)
    | return none
  return some (pics, es.map fun e => ⟨e, 0, false⟩)

end Component
