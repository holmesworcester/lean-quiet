/-
A picture: a blob's hash and size.

Reads: the blob op's own fact. Its bytes are outside the engine (the
blob store, by hash) and are decoded where they are drawn.
-/
import Quiet.Row
import Quiet.Data

namespace Kinds.Blob
open Engine Community Data

variable {m : Type → Type} [Monad m] [Reads m]

def read (b : Id) (deps : Array Q) : m (Option Row.Pic × Array Q) := do
  let (f, _, deps) ← readFact b deps
  match f with
  | some (.blob _ hh w h) => return (some ⟨hh, w, h⟩, deps)
  | _ => return (none, deps)

end Kinds.Blob
