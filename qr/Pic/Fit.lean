/-
Sizes: what size a picture is stored or drawn at.

`fit w h edge` is the rule the native side downsamples to (an attachment's
longer side at most 2048) and the tray draws thumbnails by: a picture that
fits is kept as it is; a larger one gets its longer side at exactly `edge`
and its other side scaled to the nearest pixel, never below 1. The laws
are in Pic/Laws.lean.
-/
namespace Pic

/-- The size of a `w × h` picture fitted within `edge` on its longer side. -/
def fit (w h edge : Nat) : Nat × Nat :=
  let l := max w h
  if l ≤ edge then (w, h)
  else (max 1 ((2 * (w * edge) + l) / (2 * l)), max 1 ((2 * (h * edge) + l) / (2 * l)))

/-- The longer side a stored attachment may have. -/
def attachEdge : Nat := 2048

end Pic
