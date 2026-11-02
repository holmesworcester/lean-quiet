import app.community.Family

/-
Draft's intent: leaving a conversation with text or photos in the
composer writes one op, a generation past the newest, for the entry it
was typed in. An honest draft is Valid (`write_valid`) and ephemeral
(`write_ephemeral`).
-/

namespace Community
open Engine Codec

namespace Draft

/-- The op holding `text` and `pics` as entry `acc`'s draft, at generation `gen`. -/
def write (acc : Id) (gen : Nat) (text : ByteArray) (pics : List ByteArray) : Op :=
  mkOp [] (.ofDraft ⟨acc, gen, text, pics⟩)

/-- An op's draft body, if it is a draft. -/
def of (o : Op) : Option Body :=
  match (decode o.body : Option Community.Body) with
  | some (.ofDraft b) => some b
  | _ => none

/-- Whether an op is entry `acc`'s draft. -/
def isFor (acc : Id) (o : Op) : Bool := ((of o).map (·.acc == acc)).getD false

/-- **An honest draft is Valid,** with its fields. -/
theorem write_valid (C : Crypto) (acc : Id) (gen : Nat) (text : ByteArray) (pics : List ByteArray) :
    (family C).validate (write acc gen text pics) [] = some (.ofDraft ⟨acc, gen, text, pics⟩) := by
  simp [family, validate, write, mkOp, Codec.decode_encode, Body.tag, Community.check, Draft.check]

/-- **A draft lives in memory only.** -/
theorem write_ephemeral (C : Crypto) (acc : Id) (gen : Nat) (text : ByteArray) (pics : List ByteArray) :
    (family C).scope (write acc gen text pics) = .ephemeral := by
  simp [family, scopeOf, write, body_mkOp, Body.isEphemeral]

theorem of_write (acc : Id) (gen : Nat) (text : ByteArray) (pics : List ByteArray) :
    of (write acc gen text pics) = some ⟨acc, gen, text, pics⟩ := by
  simp [of, write, body_mkOp]

end Draft

end Community
