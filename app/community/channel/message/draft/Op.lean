import app.community.Op

/-
`draft` (ephemeral): unsent text for one conversation, with its photos
(the composer's chips, as their bytes), for the community entry it was
typed in. Each carries a generation, one past the newest this app
holds, and its list (by entry) sorts by generation, so the draft is the
newest. It cites nothing, and lives only in the app's in-memory log:
never stored, never offered, never taken (`Community.scopeOf`,
`Engine.Scope.ephemeral`). The app writes one when it leaves a
conversation with text in it (`App.stashDraft`), and its log keeps only
the newest per entry.

This op type's body and fact, their bytes, and the list its fact is
filed in. Its validator is Validate.lean; the registry is
app/community/Family.lean; its component, the composer, is View.lean.
-/

namespace Community
open Engine Codec

namespace Draft

/-- What its author writes: the entry, the generation, the text and the
photos' bytes. -/
structure Body where
  acc : B
  gen : Nat
  text : B
  pics : List B
  deriving DecidableEq, Inhabited

instance : Codec Body := Codec.tagged 25 (fun x => (x.acc, x.gen, x.text, x.pics))
  (fun (p : B × Nat × B × List B) => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩) (fun _ => rfl)

@[simp] theorem Body.enc_tag (x : Body) : Codec.enc x = 25 :: Codec.enc (x.acc, x.gen, x.text, x.pics) := rfl

/-- Nothing to blank: the body is unsigned. -/
def Body.unsigned (b : Body) : Body := b

/-- Its fact, `draft`: the same fields. -/
structure Fact where
  acc : B
  gen : Nat
  text : B
  pics : List B
  deriving DecidableEq, Inhabited

instance : Codec Fact := Codec.tagged 25 (fun x => (x.acc, x.gen, x.text, x.pics))
  (fun (p : B × Nat × B × List B) => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩) (fun _ => rfl)

@[simp] theorem Fact.enc_tag (x : Fact) : Codec.enc x = 25 :: Codec.enc (x.acc, x.gen, x.text, x.pics) := rfl

/-- Where it sorts under its entry: by generation. -/
def sortKey (f : Fact) : B := be64 f.gen

/-! ## The list its fact is filed in (`draft.byAcc`) -/
def byAcc : Rel Fact := ⟨"draft", "byAcc", fun f => some [f.acc]⟩
@[simp] theorem byAcc_args (f : Fact) : byAcc.args f = (some [f.acc]) := rfl

end Draft

end Community
