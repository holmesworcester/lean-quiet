/-
The reaction sheet's geometry, and the proofs that what a finger hits is
what is drawn under it.

A `Grid` is keys in rows: `cols` to a row, each `key` pixels square, one
every `pitch` pixels across (a gap of `pitch - key` between keys) from
`x0`, rows `key` apart; it shows `vh` pixel rows of its content from `y0`,
scrolled by `s`. The quick keys are a grid of one row (with gaps) and the
catalogue a grid of many (without), so one set of theorems covers both:

- `hit_iff`: a tap at (x, y) hits item i exactly when (x, y) is inside the
  box item i is drawn in (`Grid.box`), within the grid's visible rows.
- `hit_cell`: every point of item i's drawn box that is on screen selects
  item i: the key you see is the key you get.
- `keys_disjoint`: two items' boxes never overlap.
- `reachable`: every item can be scrolled wholly into view by a scroll
  within the grid's range: no emoji is out of reach.
- `clamp_le`: the scroll the app keeps is within that range.
- `compose_row`: the sheet's pixel row at `top.size + k` is the grid's
  content row `s + k`, for every visible k: the header above, the bar below,
  and the grid between them, scrolled exactly by s.

The painter (Quiet/Sheet.lean) draws item i at `Grid.box`, and the app's
taps go through `Grid.hit`, the functions these are about.
-/
namespace SheetGeom

structure Grid where
  x0 : Nat
  y0 : Nat
  pitch : Nat
  key : Nat
  cols : Nat
  vh : Nat
  n : Nat
  deriving Inhabited, Repr

/-- The grid's content rows: one key high each. -/
def Grid.rows (g : Grid) : Nat := (g.n + g.cols - 1) / g.cols

def Grid.contentH (g : Grid) : Nat := g.rows * g.key

/-- How far the grid can scroll. -/
def Grid.maxScroll (g : Grid) : Nat := g.contentH - g.vh

def Grid.clamp (g : Grid) (s : Nat) : Nat := min s g.maxScroll

/-- Item i's column and row. -/
def Grid.col (g : Grid) (i : Nat) : Nat := i % g.cols
def Grid.row (g : Grid) (i : Nat) : Nat := i / g.cols

/-- Item i's box: its left edge on screen, and its top in content rows. -/
def Grid.left (g : Grid) (i : Nat) : Nat := g.x0 + g.col i * g.pitch
def Grid.ctop (g : Grid) (i : Nat) : Nat := g.row i * g.key

/-- Whether screen point (x, y) is in item i's box, at scroll s, and on
the grid's visible rows. -/
def Grid.inBox (g : Grid) (s i x y : Nat) : Prop :=
  g.left i ≤ x ∧ x < g.left i + g.key ∧
  g.y0 ≤ y ∧ y < g.y0 + g.vh ∧
  g.ctop i ≤ y - g.y0 + s ∧ y - g.y0 + s < g.ctop i + g.key

/-- The item a tap at (x, y) hits, at scroll s. -/
def Grid.hit (g : Grid) (s x y : Nat) : Option Nat :=
  if g.x0 ≤ x ∧ g.y0 ≤ y ∧ y < g.y0 + g.vh then
    let dx := x - g.x0
    let j := dx / g.pitch
    if j < g.cols ∧ dx % g.pitch < g.key then
      let i := (y - g.y0 + s) / g.key * g.cols + j
      if i < g.n then some i else none
    else none
  else none

/-- The grid is well formed: keys are at least a pixel, fit their pitch,
and rows have columns. -/
structure Grid.Ok (g : Grid) : Prop where
  key_pos : 0 < g.key
  key_le : g.key ≤ g.pitch
  cols_pos : 0 < g.cols

theorem div_eq {m d k : Nat} (_hd : 0 < d) (lo : k * d ≤ m) (hi : m < k * d + d) : m / d = k := by
  apply Nat.div_eq_of_lt_le
  · exact lo
  · rw [Nat.succ_mul]; exact hi

theorem mod_eq {m d k : Nat} (hd : 0 < d) (lo : k * d ≤ m) (hi : m < k * d + d) :
    m % d = m - k * d := by
  have h := Nat.div_add_mod m d
  rw [div_eq hd lo hi] at h
  rw [Nat.mul_comm] at h
  omega

/-- **What you tap is what is drawn there.** -/
theorem hit_iff (g : Grid) (ok : g.Ok) (s x y i : Nat) :
    g.hit s x y = some i ↔ i < g.n ∧ g.inBox s i x y := by
  have hk := ok.key_pos
  have hp : 0 < g.pitch := Nat.lt_of_lt_of_le hk ok.key_le
  have hc := ok.cols_pos
  unfold Grid.hit Grid.inBox Grid.left Grid.ctop Grid.col Grid.row
  constructor
  · intro h
    split at h
    · rename_i hv
      obtain ⟨hx0, hy0, hy1⟩ := hv
      simp only at h
      split at h
      · rename_i hj
        obtain ⟨hj, hm⟩ := hj
        split at h
        · rename_i hn
          cases h
          -- the column and row of i are j and the row the finger is on
          have hcol : ((y - g.y0 + s) / g.key * g.cols + (x - g.x0) / g.pitch) % g.cols =
              (x - g.x0) / g.pitch := by
            rw [Nat.mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hj
          have hrow : ((y - g.y0 + s) / g.key * g.cols + (x - g.x0) / g.pitch) / g.cols =
              (y - g.y0 + s) / g.key := by
            rw [Nat.mul_comm, Nat.mul_add_div hc, Nat.div_eq_of_lt hj, Nat.add_zero]
          rw [hcol, hrow]
          have d1 := Nat.div_add_mod (x - g.x0) g.pitch
          have d2 := Nat.div_add_mod (y - g.y0 + s) g.key
          have m2 := Nat.mod_lt (y - g.y0 + s) hk
          refine ⟨hn, ?_, ?_, hy0, hy1, ?_, ?_⟩
          · rw [Nat.mul_comm] at d1; omega
          · rw [Nat.mul_comm] at d1; omega
          · rw [Nat.mul_comm] at d2; omega
          · rw [Nat.mul_comm] at d2; omega
        · cases h
      · cases h
    · cases h
  · rintro ⟨hn, hx0, hx1, hy0, hy1, hr0, hr1⟩
    have hkp := ok.key_le
    have hj := Nat.mod_lt i hc
    -- the finger's column is i's
    have hx0' : g.x0 ≤ x := by omega
    have hdx : (x - g.x0) / g.pitch = i % g.cols := div_eq hp (by omega) (by omega)
    have hmx : (x - g.x0) % g.pitch < g.key := by
      rw [mod_eq hp (k := i % g.cols) (by omega) (by omega)]; omega
    have hdy : (y - g.y0 + s) / g.key = i / g.cols := div_eq hk hr0 (by omega)
    have hi : i / g.cols * g.cols + i % g.cols = i := by
      rw [Nat.mul_comm]; exact Nat.div_add_mod i g.cols
    simp only [hx0', hy0, hy1, and_self, ite_true, hdx, hj, hmx, hdy, hi, hn]

/-- **Every point of a drawn key selects it.** -/
theorem hit_cell (g : Grid) (ok : g.Ok) (s i x y : Nat) (hn : i < g.n) (h : g.inBox s i x y) :
    g.hit s x y = some i := (hit_iff g ok s x y i).2 ⟨hn, h⟩

/-- **Keys never overlap.** A point is in at most one item's box. -/
theorem keys_disjoint (g : Grid) (ok : g.Ok) (s i i' x y : Nat) (hn : i < g.n) (hn' : i' < g.n)
    (h : g.inBox s i x y) (h' : g.inBox s i' x y) : i = i' := by
  have a := hit_cell g ok s i x y hn h
  have b := hit_cell g ok s i' x y hn' h'
  rw [a] at b; exact Option.some.inj b

theorem clamp_le (g : Grid) (s : Nat) : g.clamp s ≤ g.maxScroll := Nat.min_le_right _ _

theorem row_lt (g : Grid) (ok : g.Ok) (i : Nat) (hn : i < g.n) : g.row i < g.rows := by
  unfold Grid.row Grid.rows
  have hc := ok.cols_pos
  have h1 : i / g.cols * g.cols ≤ i := Nat.div_mul_le_self i g.cols
  have h2 : (i / g.cols + 1) * g.cols ≤ g.n + g.cols - 1 := by rw [Nat.succ_mul]; omega
  have := (Nat.le_div_iff_mul_le hc).2 h2
  omega

/-- **Every item can be brought wholly into view**, by a scroll in range,
when a key fits the visible rows. -/
theorem reachable (g : Grid) (ok : g.Ok) (fits : g.key ≤ g.vh) (i : Nat) (hn : i < g.n) :
    ∃ s, s ≤ g.maxScroll ∧ s ≤ g.ctop i ∧ g.ctop i + g.key ≤ s + g.vh := by
  have hr := row_lt g ok i hn
  have hc : g.ctop i + g.key ≤ g.contentH := by
    unfold Grid.ctop Grid.contentH
    have := Nat.mul_le_mul_right g.key (Nat.succ_le_of_lt hr)
    rw [Nat.succ_mul] at this; exact this
  refine ⟨min (g.ctop i) g.maxScroll, Nat.min_le_right _ _, Nat.min_le_left _ _, ?_⟩
  unfold Grid.maxScroll at *
  omega

/-! ## The sheet's rows -/

/-- The catalogue sheet's pixel rows: the header, `vh` rows of the grid's
content from scroll s, and the bar. -/
def compose {α} (top : Array α) (line : Nat → α) (vh s : Nat) (bot : Array α) : Array α :=
  top ++ Array.ofFn (n := vh) (fun k => line (s + k)) ++ bot

theorem compose_size {α} (top : Array α) (line : Nat → α) (vh s : Nat) (bot : Array α) :
    (compose top line vh s bot).size = top.size + vh + bot.size := by
  simp [compose]; omega

/-- **The grid shows exactly its content scrolled by s**, between the
header and the bar. -/
theorem compose_row {α} (top : Array α) (line : Nat → α) (vh s : Nat) (bot : Array α)
    (k : Nat) (hk : k < vh) (h : top.size + k < (compose top line vh s bot).size) :
    (compose top line vh s bot)[top.size + k] = line (s + k) := by
  simp only [compose]
  rw [Array.getElem_append_left (by simp; omega)]
  rw [Array.getElem_append_right (by omega)]
  simp

/-- And the header and bar are where they were. -/
theorem compose_top {α} (top : Array α) (line : Nat → α) (vh s : Nat) (bot : Array α)
    (k : Nat) (hk : k < top.size) (h : k < (compose top line vh s bot).size) :
    (compose top line vh s bot)[k] = top[k] := by
  simp only [compose]
  rw [Array.getElem_append_left (by simp; omega), Array.getElem_append_left hk]

end SheetGeom
