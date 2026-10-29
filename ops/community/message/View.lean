/-
A message's running readOwn view reads its own fact and content key.
The composed read below is retained for the older view model and its
laws; shipping components observe author, attachment and reaction views
independently. The list supplies identity; Row owns layout and pixels.
-/
import ops.community.profile.View
import ops.community.reaction.View
import ops.community.attachment.View

namespace Kinds.Message
open Engine Community Data

variable {m : Type → Type} [Monad m] [Reads m]

/-- The message op alone. Child collections and op components own all
profile, attachment and reaction reads; this view never subscribes to them. -/
def readOwn (msg : Id) : m (Option (Row.RowData × Array Q)) := do
  let (f, pending, deps) ← readFact msg #[]
  let some (.message c u _ kid sealed _ tm clump) := f | return none
  let (ks, _, deps) ← readList (key.byId.query [kid] (limit := some 1)) deps
  let some text := (match ks.rows.head? with
    | some (_, .key _ _ k) => (openSealed cryptoSeal c kid sealed k).map Profile.bytesStr
    | _ => none) | return none
  return some ({ name := "…", avatar := none, text, time := tm, pics := [], tallies := [],
                 pending, selected := false, author := u, clump }, deps)

def read (c me msg : Id) (attachmentProgress : Bool := true) : m (Option (Row.RowData × Array Q)) := do
  let (f, pending, deps) ← readFact msg #[]
  let some (.message _ u _ kid sealed _ tm clump) := f | return none
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
  return some (⟨who.name, none, text, tm, pics.toList, tallies, pending, false, twin, u, clump⟩, deps)

end Kinds.Message
