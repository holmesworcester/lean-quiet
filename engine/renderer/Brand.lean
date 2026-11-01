/-
The Quiet lockup (the mark and "Quiet"), as libquiet's `Wordmark.svelte`
draws it: `ui/brand/quiet-lockup.svg` holds the unmodified paths and
viewBox of libquiet's `app/src/brand/quiet.json` (see ui/brand/SOURCE.txt),
read at compile time. The mark is filled even-odd, the letters nonzero,
as the component fills them. It is rasterized at the size it is drawn
(Vector.fill), never scaled from another size.
-/
import engine.renderer.Vector

namespace Brand

/-- The pinned lockup source. -/
def source : String := include_str "../../ui/brand/quiet-lockup.svg"

/-- The lockup's viewBox: 285 × 82. -/
def viewW : Nat := 285
def viewH : Nat := 82

/-- Each `<path>`'s fill rule and data, in document order. -/
def paths (svg : String) : Array (Vector.Rule × String) := Id.run do
  let mut out := #[]
  for part in (svg.splitOn "<path ").drop 1 do
    let rule := if (part.splitOn "fill-rule=\"evenodd\"").length > 1 then Vector.Rule.evenOdd else .nonzero
    match (part.splitOn "d=\"")[1]? with
    | some rest => out := out.push (rule, (rest.splitOn "\"")[0]!)
    | none => pure ()
  return out

/-- The lockup's outlines, parsed once (none if the source is unreadable). -/
def outline : Option (Array (Vector.Rule × Array Vector.Contour)) :=
  (paths source).mapM fun (rule, d) => (Vector.parse d).map (rule, ·)

/-- The lockup `width` device pixels wide (its height follows the
viewBox), with its viewBox origin at (x, y). -/
def lockup (width : Float) (x y : Float) : Vector.Mask :=
  match outline with
  | none => default
  | some ps =>
    let place : Vector.Place := ⟨width / viewW.toFloat, x, y⟩
    Vector.fill (ps.map fun (rule, cs) => (rule, Vector.edges place cs))

end Brand
