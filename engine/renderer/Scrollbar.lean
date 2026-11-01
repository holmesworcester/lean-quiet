/-
A conversation's scrollbar, by rank: where the thumb is says how far back
in the conversation the screen is, counted in messages (the engine's exact
counts), not in estimated pixels. Row heights are estimates until rows
are measured, so a thumb placed by pixels jumps as they are; one placed
by rank does not. The conversation is bottom-anchored, so offsets are from
the track's bottom.

`n` messages, `k` of them on screen, `r` of them entirely below the screen
(newer), a track `t` pixels tall and a thumb at least `m` tall (a hit
target). Then:

- `fits`: the thumb lies inside the track, and is at least `m` tall.
- `newest_bottom`, `oldest_top`: with nothing newer the thumb is at the
  bottom; with nothing older, at the top.
- `monotone`: further back in the conversation, the thumb is higher.
- `exact`: the thumb's offset is r's share of the track's free length, to
  the pixel: it is meaningful whatever the rows' heights.
- `seek_below`, `seek_mono`: dragging the thumb's bottom to an offset
  seeks a rank whose thumb lands there or below it, never above; dragging
  higher seeks further back.

`Col` is the column the app lays out: `newer` messages not loaded (each
`est` tall), the loaded window's heights, `older` not loaded, above a pad.
`ranks` counts n, k and r from it at a scroll offset `b` and view height,
in the window's size, never the community's. `ranks_fit` says r and k
never exceed n; `ranks_mono` that a higher offset never has fewer newer.
-/
namespace Scrollbar

/-- The thumb's height: k's share of the track, at least m, at most t. -/
def size (t m n k : Nat) : Nat := min t (max m (t * k / n))

/-- A rank's offset along `travel` pixels, `span` ranks in all. -/
def place (travel span r : Nat) : Nat := travel * r / span

/-- The thumb's offset from the track's bottom. -/
def offset (t m n k r : Nat) : Nat := place (t - size t m n k) (n - k) r

/-- The rank a drag to offset y seeks (the thumb's bottom at y). -/
def seek (travel span y : Nat) : Nat := min span (y * span / travel)

theorem size_le (t m n k : Nat) : size t m n k ≤ t := Nat.min_le_left _ _

/-- **The thumb lies inside its track.** -/
theorem inside (t m n k r : Nat) (hr : r ≤ n - k) :
    offset t m n k r + size t m n k ≤ t := by
  have hle : offset t m n k r ≤ t - size t m n k := by
    unfold offset place
    rcases Nat.eq_zero_or_pos (n - k) with h0 | hpos
    · simp [h0]
    · exact Nat.div_le_of_le_mul (Nat.le_trans (Nat.mul_le_mul_left _ hr) (Nat.le_of_eq (Nat.mul_comm _ _)))
  have := size_le t m n k
  omega

/-- **The thumb fits its track, and is a target.** -/
theorem fits (t m n k r : Nat) (hm : m ≤ t) (hr : r ≤ n - k) :
    offset t m n k r + size t m n k ≤ t ∧ m ≤ size t m n k :=
  ⟨inside t m n k r hr, Nat.le_min.2 ⟨hm, Nat.le_max_left _ _⟩⟩

/-- **With nothing newer, the thumb is at the bottom.** -/
theorem newest_bottom (t m n k : Nat) : offset t m n k 0 = 0 := by simp [offset, place]

/-- **With nothing older, the thumb is at the top.** -/
theorem oldest_top (t m n k : Nat) (h : k < n) :
    offset t m n k (n - k) + size t m n k = t := by
  unfold offset place
  rw [Nat.mul_div_cancel _ (by omega)]
  have := size_le t m n k
  omega

/-- **Further back, higher.** -/
theorem monotone (t m n k : Nat) {r r' : Nat} (h : r ≤ r') :
    offset t m n k r ≤ offset t m n k r' :=
  Nat.div_le_div_right (Nat.mul_le_mul_left _ h)

/-- **The offset is the rank's share, to the pixel.** -/
theorem exact (t m n k r : Nat) (h : k < n) :
    offset t m n k r * (n - k) ≤ (t - size t m n k) * r ∧
    (t - size t m n k) * r < (offset t m n k r + 1) * (n - k) := by
  unfold offset place
  have hp : 0 < n - k := by omega
  refine ⟨Nat.div_mul_le_self _ _, ?_⟩
  have := Nat.lt_mul_div_succ ((t - size t m n k) * r) hp
  rwa [Nat.mul_comm (n - k)] at this

/-- **A drag never lands the thumb above the pointer.** -/
theorem seek_below (travel span y : Nat) :
    place travel span (seek travel span y) ≤ y := by
  unfold place seek
  apply Nat.div_le_of_le_mul
  calc travel * min span (y * span / travel)
      ≤ travel * (y * span / travel) := Nat.mul_le_mul_left _ (Nat.min_le_right _ _)
    _ ≤ y * span := Nat.mul_div_le _ _
    _ = span * y := Nat.mul_comm _ _

/-- **Dragging higher seeks further back.** -/
theorem seek_mono (travel span : Nat) {y y' : Nat} (h : y ≤ y') :
    seek travel span y ≤ seek travel span y' := by
  unfold seek
  have := Nat.div_le_div_right (c := travel) (Nat.mul_le_mul_right span h)
  omega

/-! ## Counting the column -/

/-- The loaded window's heights, newest first, beneath `newer` unloaded
messages and above `older`. -/
structure Col where
  pad : Nat
  est : Nat
  newer : Nat
  older : Nat
  hs : Array Nat

def Col.n (c : Col) : Nat := c.newer + c.hs.size + c.older

/-- Where each window message ends, from `a` (its bottom edge). -/
def ends : Nat → List Nat → List Nat
  | _, [] => []
  | a, h :: t => (a + h) :: ends (a + h) t

/-- Where each window message starts, from `a`. -/
def starts : Nat → List Nat → List Nat
  | _, [] => []
  | a, h :: t => a :: starts (a + h) t

def Col.base (c : Col) : Nat := c.pad + c.newer * c.est

/-- The window's top edge. -/
def Col.edge (c : Col) : Nat := c.base + c.hs.foldl (· + ·) 0

/-- Messages entirely below `p`: ended at or before it. -/
def below (c : Col) (p : Nat) : Nat :=
  min c.newer ((p - c.pad) / c.est) + ((ends c.base c.hs.toList).filter (· ≤ p)).length +
    min c.older ((p - c.edge) / c.est)

/-- Messages begun before `p`: all but those entirely above it. -/
def begun (c : Col) (p : Nat) : Nat :=
  min c.newer ((p - c.pad + c.est - 1) / c.est) + ((starts c.base c.hs.toList).filter (· < p)).length +
    min c.older ((p - c.edge + c.est - 1) / c.est)

/-- (n, k, r): the messages, those on screen and those entirely below it,
for a screen `view` tall at scroll offset `b`. -/
def ranks (c : Col) (b view : Nat) : Nat × Nat × Nat :=
  let s := min c.n (begun c (b + view))
  let r := min (below c b) s
  (c.n, s - r, r)

/-- Where scrolling puts the screen's bottom edge for `q` messages to be
entirely below it: at the end of the q-th, counting from the newest. -/
def offsetOf (c : Col) (q : Nat) : Nat :=
  if q = 0 then 0
  else if q ≤ c.newer then c.pad + q * c.est
  else if q ≤ c.newer + c.hs.size then (ends c.base c.hs.toList).getD (q - c.newer - 1) c.edge
  else c.edge + (q - c.newer - c.hs.size) * c.est

theorem ranks_fit (c : Col) (b view : Nat) :
    (ranks c b view).2.2 + (ranks c b view).2.1 ≤ (ranks c b view).1 := by
  unfold ranks
  simp only
  have := Nat.min_le_right c.n (begun c (b + view))
  have := Nat.min_le_left c.n (begun c (b + view))
  have := Nat.min_le_right (below c b) (min c.n (begun c (b + view)))
  omega

private theorem filter_le_mono (l : List Nat) {p p' : Nat} (h : p ≤ p') :
    (l.filter (· ≤ p)).length ≤ (l.filter (· ≤ p')).length := by
  induction l with
  | nil => simp
  | cons x t ih =>
    by_cases hx : x ≤ p
    · have : x ≤ p' := Nat.le_trans hx h
      simp [hx, this, ih]
    · by_cases hx' : x ≤ p'
      · simp [hx, hx']; omega
      · simp [hx, hx', ih]

private theorem filter_lt_mono (l : List Nat) {p p' : Nat} (h : p ≤ p') :
    (l.filter (· < p)).length ≤ (l.filter (· < p')).length := by
  induction l with
  | nil => simp
  | cons x t ih =>
    by_cases hx : x < p
    · have : x < p' := Nat.lt_of_lt_of_le hx h
      simp [hx, this, ih]
    · by_cases hx' : x < p'
      · simp [hx, hx']; omega
      · simp [hx, hx', ih]

theorem below_mono (c : Col) {p p' : Nat} (h : p ≤ p') : below c p ≤ below c p' := by
  unfold below
  have h1 : min c.newer ((p - c.pad) / c.est) ≤ min c.newer ((p' - c.pad) / c.est) := by
    have := Nat.div_le_div_right (c := c.est) (show (p - c.pad) ≤ (p' - c.pad) by omega)
    omega
  have h2 : min c.older ((p - c.edge) / c.est) ≤ min c.older ((p' - c.edge) / c.est) := by
    have := Nat.div_le_div_right (c := c.est) (show (p - c.edge) ≤ (p' - c.edge) by omega)
    omega
  have h3 := filter_le_mono (ends c.base c.hs.toList) h
  omega

theorem begun_mono (c : Col) {p p' : Nat} (h : p ≤ p') : begun c p ≤ begun c p' := by
  unfold begun
  have h1 : min c.newer ((p - c.pad + c.est - 1) / c.est) ≤ min c.newer ((p' - c.pad + c.est - 1) / c.est) := by
    have := Nat.div_le_div_right (c := c.est) (show (p - c.pad + c.est - 1) ≤ (p' - c.pad + c.est - 1) by omega)
    omega
  have h2 : min c.older ((p - c.edge + c.est - 1) / c.est) ≤ min c.older ((p' - c.edge + c.est - 1) / c.est) := by
    have := Nat.div_le_div_right (c := c.est) (show (p - c.edge + c.est - 1) ≤ (p' - c.edge + c.est - 1) by omega)
    omega
  have h3 := filter_lt_mono (starts c.base c.hs.toList) h
  omega

/-- **Scrolling back never has fewer messages newer than the screen.** -/
theorem ranks_mono (c : Col) {b b' : Nat} (view : Nat) (h : b ≤ b') :
    (ranks c b view).2.2 ≤ (ranks c b' view).2.2 := by
  unfold ranks
  simp only
  have := below_mono c h
  have := begun_mono c (p := b + view) (p' := b' + view) (by omega)
  omega

private theorem ends_ge (hs : List Nat) : ∀ (a x : Nat), x ∈ ends a hs → a ≤ x := by
  induction hs with
  | nil => intro a x hx; simp [ends] at hx
  | cons h t ih =>
    intro a x hx
    simp only [ends, List.mem_cons] at hx
    rcases hx with rfl | hx
    · omega
    · have := ih (a + h) x hx
      omega

/-- **At the newest message, nothing is below the screen.** -/
theorem ranks_newest (c : Col) (view : Nat) (hp : 0 < c.pad) :
    (ranks c 0 view).2.2 = 0 := by
  unfold ranks
  simp only
  have h1 : min c.newer ((0 - c.pad) / c.est) = 0 := by simp
  have h2 : ((ends c.base c.hs.toList).filter (· ≤ 0)).length = 0 := by
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro x hx
    have := ends_ge c.hs.toList c.base x hx
    unfold Col.base at this
    simp; omega
  have h3 : min c.older ((0 - c.edge) / c.est) = 0 := by simp
  have : below c 0 = 0 := by unfold below; omega
  omega

end Scrollbar
