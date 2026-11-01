import app.community.channel.message.draft.Proofs

/-
Draft's laws, witnessed on the app's ephemeral log as it starts: empty.
Writing a draft there rebuilds the log from that one op; an empty
composer rebuilds it from none.
-/

namespace Vacuity.Draft
open Engine Engine.Sync Data

def acc : ByteArray := "entry: design team".toUTF8
def text : ByteArray := "half a thought".toUTF8

theorem distinct_one (o : Op) : Distinct [o] := by
  intro a ha b hb _
  rw [List.mem_singleton] at ha hb
  rw [ha, hb]

theorem drafted_empty : drafted {} acc 1 text [] = [Community.Draft.write acc 1 text []] := rfl

/-- The first draft, "half a thought" for one entry, on the empty log: the
log's newest draft for the entry is exactly it. -/
theorem first : draftOf (draftIn {} acc 1 text []) acc =
    some ((Community.Draft.write acc 1 text []).id, ⟨acc, 1, text, []⟩) :=
  draftIn_newest {} acc 1 text [] (by decide) (by rw [drafted_empty]; exact distinct_one _)

/-- An empty composer on the empty log leaves no draft. -/
theorem drafted_none : drafted {} acc 1 .empty [] = [] := rfl

theorem none_left : draftOf (draftIn {} acc 1 .empty []) acc = none :=
  draftIn_empty {} acc 1 .empty [] (by decide) (by rw [drafted_none]; intro a ha; cases ha)

/-- The stash-and-return law's premise holds whenever the ops the log is
rebuilt from have distinct ids (SHA-256 collision-free on them). -/
theorem back (s : App.St) (hacc : s.me.acc.isEmpty = false)
    (hne : (s.text.toUTF8.isEmpty && (s.chips.toList.map (·.1)).isEmpty) = false)
    (hc : CollisionFree (drafted s.eph s.me.acc (s.draftGen + 1) s.text.toUTF8 (s.chips.toList.map (·.1)))) :
    (App.useDraft (App.stashDraft s)).text = s.text :=
  App.stash_use s hacc hne (distinct_of_collisionFree hc)

/-- A draft is ephemeral, and Valid, in Community's family. -/
theorem ephemeral : (Community.family Data.C).scope (Community.Draft.write acc 1 text []) = .ephemeral :=
  Community.Draft.write_ephemeral Data.C acc 1 text []

theorem valid : (Community.family Data.C).validate (Community.Draft.write acc 1 text []) [] =
    some (.ofDraft ⟨acc, 1, text, []⟩) :=
  Community.Draft.write_valid Data.C acc 1 text []

end Vacuity.Draft
