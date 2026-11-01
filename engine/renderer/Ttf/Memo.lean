/-
The glyph memo beneath pure Paint, in plain Lean. A Source's `bitmap` is
its raster (`uncached`); the compiler runs `bitmapFast` instead, which
reads the Source's own table of thunks, and `bitmap_eq_fast` (`@[csimp]`)
proves the two equal. Lean's runtime evaluates a thunk once and keeps
the value, so each glyph is rastered at most once per Source. No global
state, no `unsafe`, no `implemented_by`.

A table is lazy: a Source that is never painted costs a few objects,
and a glyph's page of thunks is made when one of its glyphs is first
read. What a table keeps it keeps for the Source's life; the app drops
its Sources, and so their glyphs, when it rebuilds its font
(`Font.Font.fresh`, on suspend; `Font.load`, on a density change).
-/
import engine.renderer.Ttf.Raster

namespace Ttf.Memo

/-- Keys on one page of a table. -/
abbrev page : Nat := 64

/-- The values of `f`, each kept once read: pages of thunks, made when a
key on them is first read. `exact` says entry `j` of page `i` is `f` at
key `i * page + j`. -/
structure Table {α : Type} (f : Nat → α) where
  pages : Thunk (Array (Thunk (Array (Thunk α))))
  exact : ∀ i (hi : i < pages.get.size) j (hj : j < (pages.get[i]'hi).get.size),
    ((pages.get[i]'hi).get[j]'hj).get = f (i * page + j)

/-- A table for the keys below `count ()`; nothing is made until it is read. -/
def Table.new {α : Type} (f : Nat → α) (count : Unit → Nat) : Table f where
  pages := Thunk.mk fun _ => Array.ofFn (n := (count () + page - 1) / page) fun i =>
    Thunk.mk fun _ => Array.ofFn (n := page) fun j => Thunk.mk fun _ => f (i.1 * page + j.1)
  exact := by
    intro i hi j hj
    simp [Thunk.get, Array.getElem_ofFn]

/-- `f` at `k`: the kept value, or `f k` for a key past the table. -/
@[inline] def Table.get {α : Type} {f : Nat → α} (t : Table f) (k : Nat) : α :=
  if hi : k / page < t.pages.get.size then
    if hj : k % page < (t.pages.get[k / page]'hi).get.size then
      ((t.pages.get[k / page]'hi).get[k % page]'hj).get
    else f k
  else f k

/-- **A table answers as its function.** -/
theorem Table.get_eq {α : Type} {f : Nat → α} (t : Table f) (k : Nat) : t.get k = f k := by
  unfold Table.get
  split
  · split
    · rw [t.exact]
      exact congrArg f (Nat.div_add_mod' k page)
    · rfl
  · rfl

/-- A copy of a bitmap's coverage at its exact size: `copySlice` into an
empty array allocates exactly the length, so a kept bitmap holds none of
the raster builder's spare capacity. -/
def compact (b : Bitmap) : Bitmap := { b with pixels := b.pixels.extract 0 b.pixels.size }

theorem compact_eq (b : Bitmap) : compact b = b := by
  simp [compact, ByteArray.extract_zero_size]

/-- A face at one size: its parsed font (shared by its sizes), the size
and cell it rasters at, and its table of glyphs. -/
structure Source where
  private mk ::
  private font : Thunk (Option Face)
  private size : Nat
  private cell : Nat
  private glyphs : Table fun glyph => (font.get >>= fun face => raster face glyph size cell).map compact

/-- One table key per glyph the face has (its `loca` offsets); none for a
font that does not parse. -/
private def glyphCount (font : Thunk (Option Face)) : Nat :=
  match font.get with
  | some face => face.offsets.size
  | none => 0

private def make (font : Thunk (Option Face)) (size cell : Nat) : Source :=
  ⟨font, size, cell, Table.new _ fun _ => glyphCount font⟩

/-- Parsing is pure and deferred until a glyph is actually painted. readHeader
checks tables/metrics; raster checks each requested outline, including cycles. -/
def source (bytes : ByteArray) (size cell : Nat) : Source :=
  make (Thunk.mk fun _ => readHeader bytes) size cell

instance : Inhabited Source := ⟨source .empty 1 1⟩

def Source.uncached (f : Source) (glyph : Nat) : Option Bitmap :=
  f.font.get >>= fun font => raster font glyph f.size f.cell

/-- Sizes share the immutable font bytes and parsing; each size has its
own table. -/
def Source.sized (f : Source) (size cell : Nat) : Source :=
  make f.font size cell

/-- The same face and size with an empty table. -/
def Source.fresh (f : Source) : Source :=
  make f.font f.size f.cell

/-- A glyph's bitmap: its raster. What runs is `bitmapFast`. -/
def Source.bitmap (f : Source) (glyph : Nat) : Option Bitmap :=
  f.uncached glyph

/-- A glyph's bitmap, from the Source's table. -/
def Source.bitmapFast (f : Source) (glyph : Nat) : Option Bitmap :=
  f.glyphs.get glyph

/-- **The memo is the raster.** The compiler runs `bitmapFast` for
`bitmap`: every field and byte is the raster's, whatever was read before. -/
@[csimp] theorem bitmap_eq_fast : @Source.bitmap = @Source.bitmapFast := by
  funext f glyph
  have : compact = id := funext compact_eq
  simp only [Source.bitmap, Source.bitmapFast, Table.get_eq, Source.uncached, this, Option.map_id,
    id]

/-! ## Negative control -/

/-- Control: a table one key off, page `i` holding `id` at `i * page + j + 1`;
never run. -/
def shifted : Thunk (Array (Thunk (Array (Thunk Nat)))) :=
  Thunk.mk fun _ => #[Thunk.mk fun _ => Array.ofFn (n := page) fun j => Thunk.mk fun _ => j.1 + 1]

/-- The table's law rejects it: no `Table id` has these pages. -/
theorem shifted_not_exact : ¬ ∀ i (hi : i < shifted.get.size) j (hj : j < (shifted.get[i]'hi).get.size),
    ((shifted.get[i]'hi).get[j]'hj).get = id (i * page + j) := by
  intro h
  have := h 0 (by simp [shifted, Thunk.get]) 0 (by simp [shifted, Thunk.get])
  simp [shifted, Thunk.get] at this

example : (Table.new (fun k => k * k) fun _ => 200).get 130 = 16900 := Table.get_eq _ _

end Ttf.Memo
