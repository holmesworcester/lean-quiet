/-
Navigation: the page shown and the stack of pages under it, and the four
ways they change. The app changes its page and back stack only through
these (App.St.withNav): opening a page, going back, resetting to a root
(a switch, a removal, Get started) and putting a page in place of the
shown one (Waiting in place of a conversation).

- `back_go`: **back goes back.** Back after opening a page that is
  neither shown nor under it gives exactly what was there before.
- `back_root`: back with nothing under the page changes nothing (it never
  opens a page that was not there).
- `go_inv`, `back_inv`, `reset_inv`, `swap_inv`: no page is twice in the
  page and its stack. Opening a page already under the shown one goes
  back to it, so going back never shows a page twice.
- `back_reset`: after a reset, back stays on the new root: a switch never
  backs into the community before it.
- `depth`: with no page twice, the pages under the shown one are fewer
  than the kinds of page there are, so back reaches the root within that
  many steps.

Every law holds for any type of page; the app's is App.PageId.
-/
namespace Nav

structure Nav (P : Type) where
  page : P
  stack : List P := []
  deriving Repr

variable {P : Type} [DecidableEq P]

/-- What is under p in the stack (p's own entry and those above it gone). -/
def under (p : P) (s : List P) : List P := (s.dropWhile (· ≠ p)).tail

/-- Open p. The shown page goes on the stack; a page already under it is
gone back to instead. -/
def go (p : P) (n : Nav P) : Nav P :=
  if p = n.page then n
  else if p ∈ n.stack then ⟨p, under p n.stack⟩
  else ⟨p, n.page :: n.stack⟩

/-- Back: the page under the shown one; nothing, at a root. -/
def back (n : Nav P) : Nav P :=
  match n.stack with
  | p :: rest => ⟨p, rest⟩
  | [] => n

/-- A root: p with nothing under it. -/
def reset (p : P) : Nav P := ⟨p, []⟩

/-- p in place of the shown page, which is not gone back to. -/
def swap (p : P) (n : Nav P) : Nav P :=
  if p ∈ n.stack then ⟨p, under p n.stack⟩ else ⟨p, n.stack⟩

/-- No page twice: the shown page and its stack. -/
def Inv (n : Nav P) : Prop := (n.page :: n.stack).Nodup

theorem dropWhile_mem (p : P) : ∀ s : List P, p ∈ s →
    s.dropWhile (· ≠ p) = p :: under p s
  | [], h => by simp at h
  | x :: t, h => by
    by_cases hx : x = p
    · subst hx; simp [under]
    · have ht : p ∈ t := by
        rcases List.mem_cons.1 h with h | h
        · exact absurd h.symm hx
        · exact h
      have ih := dropWhile_mem p t ht
      simp only [under] at ih ⊢
      rw [List.dropWhile_cons_of_pos (p := fun y => decide (y ≠ p)) (decide_eq_true hx)]
      exact ih

omit [DecidableEq P] in
theorem dropWhile_sublist (f : P → Bool) : ∀ s : List P, (s.dropWhile f).Sublist s
  | [] => by simp
  | x :: t => by
    rw [List.dropWhile_cons]
    split
    · exact (dropWhile_sublist f t).cons x
    · exact List.Sublist.refl _

/-- Going to p under the shown page: p and what is under it, with no
page twice. -/
theorem under_inv {p : P} {s : List P} (hs : s.Nodup) (h : p ∈ s) :
    (p :: under p s).Nodup := by
  rw [← dropWhile_mem p s h]
  exact hs.sublist (dropWhile_sublist _ s)

theorem go_page (p : P) (n : Nav P) : (go p n).page = p := by
  unfold go; split
  · next h => exact h.symm
  · split <;> rfl

/-- **Back goes back.** -/
theorem back_go (p : P) (n : Nav P) (hp : p ≠ n.page) (hs : p ∉ n.stack) :
    back (go p n) = n := by
  simp [go, back, hp, hs]

omit [DecidableEq P] in
/-- **Back at a root changes nothing.** -/
theorem back_root (n : Nav P) (h : n.stack = []) : back n = n := by
  simp [back, h]

omit [DecidableEq P] in
theorem back_reset (p : P) : back (reset p) = reset p := rfl

theorem go_inv (p : P) (n : Nav P) (h : Inv n) : Inv (go p n) := by
  unfold go Inv
  split
  · exact h
  · next hp =>
    split
    · next hs => exact under_inv (List.nodup_cons.1 h).2 hs
    · next hs =>
      refine List.nodup_cons.2 ⟨?_, h⟩
      intro hm
      rcases List.mem_cons.1 hm with hm | hm
      · exact hp hm
      · exact hs hm

omit [DecidableEq P] in
theorem back_inv (n : Nav P) (h : Inv n) : Inv (back n) := by
  unfold back Inv
  split
  · next p rest hst =>
    have := (List.nodup_cons.1 h).2
    rw [hst] at this
    exact this
  · exact h

omit [DecidableEq P] in
theorem reset_inv (p : P) : Inv (reset p) := by
  simp [Inv, reset]

theorem swap_inv (p : P) (n : Nav P) (h : Inv n) : Inv (swap p n) := by
  unfold swap Inv
  split
  · next hs => exact under_inv (List.nodup_cons.1 h).2 hs
  · next hs => exact List.nodup_cons.2 ⟨hs, (List.nodup_cons.1 h).2⟩

omit [DecidableEq P] in
/-- **Back reaches the root.** With no page twice, the pages under the
shown one are fewer than the `all` pages there are. -/
theorem depth (all : List P) (hall : ∀ p, p ∈ all) (n : Nav P) (h : Inv n) :
    n.stack.length < all.length := by
  have := List.Nodup.length_le_of_subset h (fun x _ => hall x)
  simp at this
  omega

end Nav
