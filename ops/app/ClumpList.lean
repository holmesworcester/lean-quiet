/- A collection owns its window and counts, independently of the op rows
within it. Geometry keeps an unloaded range as one spacer; drawing still
mounts individual messages, attachments, authors and reaction pills. -/
import ops.app.Components

namespace ClumpList
open Engine

structure Window where
  anchor : Option Pos := none
  ids : Array Pos := #[]
  newer : Nat := 0
  older : Nat := 0
  ready : Bool := false
  deriving Inhabited

def observe {m : Type → Type} [Monad m] [Component.Queries m]
    (scope : Component.Scope) (c root : Id) (old : Window) (half : Nat) : m Window := do
  let rows ← Component.query (scope.child "messages" root) (.clumps c (some root) old.anchor half half)
  let counts ← Component.query { scope.child "count" root with visible := false }
    (.clumpCount c (some root) old.anchor)
  match rows, counts with
  | some (.window ids nr), some (.count cn co) =>
    return { old with ids := ids, newer := cn - (min cn nr), older := co - (min co (ids.size - nr)), ready := true }
  | _, _ => return old

/-- Synthetic spacer ids cannot be real SHA-256 op ids: their prefix
already exceeds 32 bytes. They never enter the query or write API. -/
def gap (root : Id) (part : Nat) : Id :=
  "quiet/clump/spacer/not-an-op-identifier/".toUTF8 ++ Codec.encode (root, part)

/-- A flat virtualizer cell: position, measured/estimated height, spacer. -/
abbrev Cell := Pos × Nat × Bool

def cells (root : Pos) (w : Window) (height : Id → Nat) (estimate : Nat) : Array Cell :=
  (if w.newer > 0 then #[((.empty, gap root.2 0), w.newer * estimate, true)] else #[]) ++
  w.ids.map (fun p => (p, height p.2, false)) ++
  (if w.older > 0 then #[((.empty, gap root.2 1), w.older * estimate, true)] else #[]) ++
  #[(root, height root.2, false)]

/-- The collapsed and expanded forms share exactly one geometry function. -/
def extent (root : Pos) (w : Window) (height : Id → Nat) (estimate : Nat) : Nat :=
  (cells root w height estimate).foldl (fun n cell => n + cell.2.1) 0

/-- A million unloaded children still cost at most two spacer cells.
Only the bounded page contributes individual message cells. -/
theorem cells_bounded (root : Pos) (w : Window) (height : Id → Nat) (estimate : Nat) :
    (cells root w height estimate).size ≤ w.ids.size + 3 := by
  simp only [cells, Array.size_append, Array.size_map]
  split <;> split <;> simp_all <;> omega

/-- Collapsing an offscreen collection cannot move its neighbours. -/
theorem extent_cells (root : Pos) (w : Window) (height : Id → Nat) (estimate : Nat) :
    extent root w height estimate = (cells root w height estimate).foldl (fun n cell => n + cell.2.1) 0 := rfl

end ClumpList
