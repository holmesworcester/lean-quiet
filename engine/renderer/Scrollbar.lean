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

/-! ## Counting the column

The unit is a root (a clump: one root and the messages that follow it
from the same author), the engine's own count. A position is `unit` per
root, fractional inside the root the screen's edge cuts, by that root's
pixels: `rank c p` is how many roots lie below the pixel `p` (from the
newest end), exact in the window's roots (their heights are the app's)
and by `est` in the `newer` and `older` roots it has not loaded. It is
monotone in `p` and never more than all the roots, which is all the
thumb needs. -/

/-- A position's resolution: this many parts to a root. -/
def unit : Nat := 256

/-- The loaded window's roots' heights, newest first, beneath `newer`
unloaded roots and above `older`, over a bottom pad. -/
structure Col where
  pad : Nat
  est : Nat
  newer : Nat
  older : Nat
  hs : Array Nat

/-- The roots in all. -/
def Col.n (c : Col) : Nat := c.newer + c.hs.size + c.older

/-- How far of `h` pixels (from `e`) the pixel `p` is, in parts of `unit`. -/
def part (e h p : Nat) : Nat := unit * min (p - e) h / h

/-- `m` unloaded roots of `est` pixels each, from `e` up: a root is
`unit` parts, so `unit` per `est` pixels. -/
def blk (e m est p : Nat) : Nat := unit * min (p - e) (m * est) / est

/-- The window's roots below `p`: each root from `e` up, a part of
`unit` for its fraction of its height below. -/
def win : Nat → List Nat → Nat → Nat
  | _, [], _ => 0
  | e, h :: t, p => part e h p + win (e + h) t p

def Col.base (c : Col) : Nat := c.pad + c.newer * c.est

/-- The window's top edge. -/
def Col.edge (c : Col) : Nat := c.base + c.hs.foldl (· + ·) 0

/-- The roots below the pixel `p`, in parts of `unit`. -/
def rank (c : Col) (p : Nat) : Nat :=
  blk c.pad c.newer c.est p + win c.base c.hs.toList p + blk c.edge c.older c.est p

/-- (n, k, r), in parts of `unit`: all the roots, those the screen shows
(`view` tall, its bottom edge at scroll offset `b`) and those below it. -/
def ranks (c : Col) (b view : Nat) : Nat × Nat × Nat :=
  (unit * c.n, rank c (b + view) - rank c b, rank c b)

/-- The pixel at which a root's `i`-th part-of-`unit` fraction `f` is
reached, from `e`: the inverse of `part` within the window. -/
def pixelIn : Nat → List Nat → Nat → Nat
  | e, [], _ => e
  | e, h :: t, q => if q < unit then e + q * h / unit else pixelIn (e + h) t (q - unit)

/-- The scroll offset that puts `q` parts of roots below the screen, when
that falls among the window's roots (none outside: those are not loaded,
so a seek there is read from the engine, `Reader.Want.rankPos`). -/
def pixelAt (c : Col) (q : Nat) : Option Nat :=
  if unit * c.newer ≤ q ∧ q < unit * (c.newer + c.hs.size) then
    some (pixelIn c.base c.hs.toList (q - unit * c.newer))
  else none

theorem part_mono (e h : Nat) {p p' : Nat} (hp : p ≤ p') : part e h p ≤ part e h p' := by
  unfold part
  exact Nat.div_le_div_right (Nat.mul_le_mul_left _
    (Nat.le_min.2 ⟨Nat.le_trans (Nat.min_le_left _ _) (by omega), Nat.min_le_right _ _⟩))

theorem part_le (e h p : Nat) : part e h p ≤ unit := by
  unfold part
  rcases Nat.eq_zero_or_pos h with rfl | hp
  · simp
  · exact Nat.div_le_of_le_mul (Nat.le_trans (Nat.mul_le_mul_left _ (Nat.min_le_right _ _))
      (Nat.le_of_eq (Nat.mul_comm _ _)))

theorem part_zero (e h : Nat) : part e h 0 = 0 := by simp [part]

theorem blk_mono (e m est : Nat) {p p' : Nat} (hp : p ≤ p') : blk e m est p ≤ blk e m est p' := by
  unfold blk
  exact Nat.div_le_div_right (Nat.mul_le_mul_left _
    (Nat.le_min.2 ⟨Nat.le_trans (Nat.min_le_left _ _) (by omega), Nat.min_le_right _ _⟩))

theorem blk_le (e m est p : Nat) : blk e m est p ≤ unit * m := by
  unfold blk
  rcases Nat.eq_zero_or_pos est with rfl | hp
  · simp
  · refine Nat.div_le_of_le_mul ?_
    calc unit * min (p - e) (m * est) ≤ unit * (m * est) := Nat.mul_le_mul_left _ (Nat.min_le_right _ _)
      _ = est * (unit * m) := by ac_rfl

theorem blk_zero (e m est : Nat) : blk e m est 0 = 0 := by simp [blk]

theorem win_mono (hs : List Nat) (e : Nat) {p p' : Nat} (hp : p ≤ p') : win e hs p ≤ win e hs p' := by
  induction hs generalizing e with
  | nil => simp [win]
  | cons h t ih => simp only [win]; have := part_mono e h hp; have := ih (e + h); omega

theorem win_le (hs : List Nat) (e p : Nat) : win e hs p ≤ unit * hs.length := by
  induction hs generalizing e with
  | nil => simp [win]
  | cons h t ih =>
    simp only [win, List.length_cons]
    have := part_le e h p
    have := ih (e + h)
    rw [Nat.mul_succ]; omega

theorem win_zero (hs : List Nat) (e : Nat) : win e hs 0 = 0 := by
  induction hs generalizing e with
  | nil => simp [win]
  | cons h t ih => simp [win, part_zero, ih]

theorem rank_mono (c : Col) {p p' : Nat} (h : p ≤ p') : rank c p ≤ rank c p' := by
  unfold rank
  have := blk_mono c.pad c.newer c.est h
  have := blk_mono c.edge c.older c.est h
  have := win_mono c.hs.toList c.base h
  omega

theorem rank_zero (c : Col) : rank c 0 = 0 := by
  simp [rank, blk_zero, win_zero]

theorem rank_le (c : Col) (p : Nat) : rank c p ≤ unit * c.n := by
  unfold rank Col.n
  have := blk_le c.pad c.newer c.est p
  have := blk_le c.edge c.older c.est p
  have := win_le c.hs.toList c.base p
  simp only [Array.length_toList] at this
  rw [Nat.mul_add, Nat.mul_add]
  omega

/-- **The screen's roots fit among all of them.** -/
theorem ranks_fit (c : Col) (b view : Nat) :
    (ranks c b view).2.2 + (ranks c b view).2.1 ≤ (ranks c b view).1 := by
  unfold ranks
  simp only
  have := rank_le c (b + view)
  have := rank_mono c (p := b) (p' := b + view) (by omega)
  omega

/-- **Scrolling back never has fewer roots below the screen.** -/
theorem ranks_mono (c : Col) {b b' : Nat} (view : Nat) (h : b ≤ b') :
    (ranks c b view).2.2 ≤ (ranks c b' view).2.2 := rank_mono c h

/-- **At the newest message, nothing is below the screen.** -/
theorem ranks_newest (c : Col) (view : Nat) : (ranks c 0 view).2.2 = 0 := rank_zero c

end Scrollbar
