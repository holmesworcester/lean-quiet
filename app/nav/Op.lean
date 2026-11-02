import engine.core.Engine
import engine.core.Merkle

/-
`nav` (ephemeral): where this window is, the page shown and the pages
under it (ROUTE03), as the app's page numbers (`App.PageId.code`). Each
carries a generation, one past the newest this window holds, and its list
sorts by generation, so the window's place is the newest: the list's
first row, newest first (`Nav.current`, View.lean). It cites nothing,
and lives only in the app's in-memory log: never stored, never offered,
never taken (`Nav.scopeOf`, `Engine.Scope.ephemeral`). The app writes one
for each change of page, through `App.St.withNav`, and its log keeps only
the newest (`App.St.eph`).

This op type's body and fact, their bytes, and the list its fact is filed
in. Its validator is Validate.lean; the registry is app/nav/Family.lean.
-/

namespace Nav
open Engine Codec

/-- What its author writes: the generation, the page shown, and the
pages under it, nearest first. -/
structure Body where
  gen : Nat
  page : Nat
  stack : List Nat
  deriving BEq

instance : Codec Body := Codec.tagged 48 (fun x => (x.gen, x.page, x.stack))
  (fun (p : Nat × Nat × List Nat) => ⟨p.1, p.2.1, p.2.2⟩) (fun _ => rfl)

/-- Its fact, `nav`: the same fields. -/
structure Fact where
  gen : Nat
  page : Nat
  stack : List Nat
  deriving Inhabited, BEq

instance : Codec Fact := Codec.tagged 0 (fun x => (x.gen, x.page, x.stack))
  (fun (p : Nat × Nat × List Nat) => ⟨p.1, p.2.1, p.2.2⟩) (fun _ => rfl)

/-- Where it sorts: by generation. -/
def sortKey (f : Fact) : ByteArray := Merkle.be64 f.gen

/-! ## The list its fact is filed in (`nav.all`) -/
def all : Rel Fact := ⟨"nav", "all", fun _ => some []⟩
@[simp] theorem all_args (f : Fact) : all.args f = (some []) := rfl

end Nav
