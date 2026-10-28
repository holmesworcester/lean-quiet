/-
What the screen subscribes to: exactly what it shows (law 2).

A list on screen is its rows, newest first, stacked up from the list's
bottom (each row's bottom edge and height), the viewport (offset b from
the bottom, height vh) and a margin kept mounted around it. A row is
near when it meets [b − margin, b + vh + margin]. The frame wants
(`Frame.wants`):
- the page's own reads (`chrome`: header, composer, counts);
- the list's windows (`listWins`): per key, the positions from the
  oldest near row to the newest, open above when the newest row of all
  is near (a new message lands on screen);
- each near row's own windows (`deps`: its fact, its author, its
  reactions, its pictures).

`screen_subs`:
- **coverage**: every near row's position is in every list window, and
  its own windows are wanted;
- **minimality**: every wanted window is the page's, a list window, or a
  near row's; a list window's range is the near rows' hull, so no loaded
  row it covers is far (`hull_near`): a row filed inside it lands among
  near rows.

The subscriptions built from the wants (`Subs.ofList`) hold exactly them
(`Subs.has_ofList`).

**What runs today** (App, Reader): the conversation is a window of rows
about an anchor, at most `half` at or older than it and `half` newer
(`Reader.Want.window`), watched by its rows' windows, which hold exactly
its rows (`WindowRead.window_rows`); the counts beside it, which size
the scroll extent, are a want of their own (`Reader.Want.count`), read
after the rows, and are among the page's reads (`chrome`). So (i) and
coverage hold as stated, and minimality holds weakened to
`past_hull_le`: with the anchor near, at most `half` loaded rows lie
past each end of the near rows' hull.

**The plan for the hull** (after the reader's want model settles): the
window becomes a buffer that is read but not watched, and a hull want
reads the near rows' range, watching exactly `listWins`; laws
`buffer_unwatched` (no window of the buffer is registered) and
`near_fresh` (a row comes near only through the hull want, read before
it is shown). The mutant `keep_scrolled_off` (the app's keep
before this: list reads kept for good, rows' reads kept every 30 frames
within 4 screens) wants a far row's windows and a list window covering
a far row.
-/
import engine.core.WindowIndex

namespace Screen
open Engine

/-- A row of a list on screen: its position, where it lies (its bottom
edge above the list's bottom, and its height), and the windows its own
reads subscribe. -/
structure Row where
  pos : Pos
  bot : Nat
  h : Nat
  deps : List Win

/-- A list on screen and the page around it. -/
structure Frame where
  /-- The list's keys (a union reads several). -/
  keys : List ByteArray
  /-- Its loaded rows, newest first. -/
  rows : List Row
  b : Nat
  vh : Nat
  margin : Nat
  /-- The page's own reads. -/
  chrome : List Win

namespace Frame

/-- On screen or within the margin. -/
def near (fr : Frame) (r : Row) : Bool := r.bot ≤ fr.b + fr.vh + fr.margin && fr.b - fr.margin ≤ r.bot + r.h

/-- The near rows, newest first. -/
def shown (fr : Frame) : List Row := fr.rows.filter fr.near

/-- The list's windows: per key, from the oldest near row to the newest,
open above when the newest row of all is near. -/
def listWins (fr : Frame) : List Win :=
  match fr.shown.head?, fr.shown.getLast? with
  | some newest, some oldest =>
    let top := match fr.rows.head? with
      | some r => if fr.near r then none else some (newest.pos, true)
      | none => some (newest.pos, true)
    fr.keys.map fun k => { key := k, lo := some (oldest.pos, true), hi := top }
  | _, _ => []

/-- **What the frame subscribes to.** -/
def wants (fr : Frame) : List Win := fr.chrome ++ fr.listWins ++ fr.shown.flatMap (·.deps)

/-- The frame's geometry: newest first, strictly, and stacked upward
without overlap (each row's bottom at or above the top of every newer
one). -/
structure Good (fr : Frame) : Prop where
  order : fr.rows.Pairwise fun r r' => r'.pos.cmp r.pos = .lt
  stack : fr.rows.Pairwise fun r r' => r.bot + r.h ≤ r'.bot

end Frame

open Frame

theorem mem_shown {fr : Frame} {r : Row} : r ∈ fr.shown ↔ r ∈ fr.rows ∧ fr.near r = true := by
  simp [shown]

/-- Every element of a list ordered by r is the last or ahead of it. -/
theorem mem_last_or' {α : Type} {R : α → α → Prop} {l : List α} (h : l.Pairwise R) {y : α}
    (hy : l.getLast? = some y) {x : α} (hx : x ∈ l) : x = y ∨ R x y := by
  obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.1 hy
  rw [List.pairwise_append] at h
  rcases List.mem_append.1 hx with hx | hx
  · exact Or.inr (h.2.2 x hx y (List.mem_singleton_self _))
  · exact Or.inl (List.mem_singleton.1 hx)

theorem mem_head_or {α : Type} {R : α → α → Prop} {l : List α} (h : l.Pairwise R) {y : α}
    (hy : l.head? = some y) {x : α} (hx : x ∈ l) : x = y ∨ R y x := by
  cases l with
  | nil => cases hy
  | cons a t =>
    simp only [List.head?_cons, Option.some.injEq] at hy
    subst hy
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact Or.inl rfl
    · exact Or.inr (h.1 x hx)

/-- **Law 2, screen_subs.** -/
theorem screen_subs {fr : Frame} (hg : fr.Good) :
    -- what is wanted: the page's, the list's, the near rows'; nothing else
    (∀ w, w ∈ fr.wants ↔ w ∈ fr.chrome ∨ w ∈ fr.listWins ∨ ∃ r ∈ fr.rows, fr.near r = true ∧ w ∈ r.deps) ∧
    -- coverage: every near row is in every list window
    (∀ r ∈ fr.rows, fr.near r = true → ∀ w ∈ fr.listWins, w.inside r.pos = true) ∧
    -- minimality: a list window runs between near rows, or above the newest row of all when it is near
    (∀ w ∈ fr.listWins, ∀ p, w.inside p = true →
      ∃ o ∈ fr.shown, o.pos.cmp p ≠ .gt ∧
        ((∃ n ∈ fr.shown, p.cmp n.pos ≠ .gt) ∨ ∃ r, fr.rows.head? = some r ∧ fr.near r = true)) := by
  have hs : fr.shown.Pairwise fun r r' => r'.pos.cmp r.pos = .lt := hg.order.filter _
  refine ⟨fun w => ?_, ?_, ?_⟩
  · simp only [wants, List.mem_append, List.mem_flatMap, mem_shown, or_assoc]
    constructor
    · rintro (h | h | ⟨r, ⟨hr, hn⟩, hw⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨r, hr, hn, hw⟩)
    · rintro (h | h | ⟨r, hr, hn, hw⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨r, ⟨hr, hn⟩, hw⟩)
  · intro r hr hn w hw
    unfold listWins at hw
    split at hw
    · rename_i newest oldest hnew hold
      obtain ⟨k, _, rfl⟩ := List.mem_map.1 hw
      have hrs : r ∈ fr.shown := mem_shown.2 ⟨hr, hn⟩
      simp only [Win.inside, Bool.and_eq_true]
      constructor
      · simp only [above]
        rcases mem_last_or' hs hold hrs with rfl | h
        · rw [Pos.cmp_self]
        · rw [Pos.lt_swap h]
      · split
        · split
          · rfl
          · rcases mem_head_or hs hnew hrs with rfl | h
            · simp [below, Pos.cmp_self]
            · simp [below, h]
        · rcases mem_head_or hs hnew hrs with rfl | h
          · simp [below, Pos.cmp_self]
          · simp [below, h]
    · cases hw
  · intro w hw p hp
    unfold listWins at hw
    split at hw
    · rename_i newest oldest hnew hold
      obtain ⟨k, _, rfl⟩ := List.mem_map.1 hw
      simp only [Win.inside, Bool.and_eq_true] at hp
      obtain ⟨hlo, hhi⟩ := hp
      refine ⟨oldest, List.mem_of_getLast? hold, ?_, ?_⟩
      · simp only [above] at hlo
        rw [Pos.cmp_swap]
        rcases e : p.cmp oldest.pos with _ | _ | _ <;> rw [e] at hlo <;> simp_all [Ordering.swap]
      · revert hhi
        split
        · rename_i r hr
          split
          · rename_i hn
            intro _
            exact Or.inr ⟨r, hr, hn⟩
          · intro hhi
            refine Or.inl ⟨newest, List.mem_of_mem_head? hnew, ?_⟩
            simp only [below] at hhi
            rcases e : p.cmp newest.pos with _ | _ | _ <;> rw [e] at hhi <;> simp_all
        · intro hhi
          refine Or.inl ⟨newest, List.mem_of_mem_head? hnew, ?_⟩
          simp only [below] at hhi
          rcases e : p.cmp newest.pos with _ | _ | _ <;> rw [e] at hhi <;> simp_all
    · cases hw

/-- Two members of a pairwise-related list: one, or related one way. -/
theorem pairwise_two {α : Type} {R : α → α → Prop} :
    ∀ {l : List α}, l.Pairwise R → ∀ {a c : α}, a ∈ l → c ∈ l → a = c ∨ R a c ∨ R c a
  | [], _, _, _, ha, _ => by cases ha
  | x :: t, h, a, c, ha, hc => by
    rw [List.pairwise_cons] at h
    have ha' := List.mem_cons.1 ha
    have hc' := List.mem_cons.1 hc
    rcases ha' with ea | ha'' <;> rcases hc' with ec | hc''
    · exact Or.inl (ea.trans ec.symm)
    · subst ea; exact Or.inr (Or.inl (h.1 c hc''))
    · subst ec; exact Or.inr (Or.inr (h.1 a ha''))
    · exact pairwise_two h.2 ha'' hc''

/-- **A list window covers no far row.** Every loaded row whose position
a list window holds is near: it lies between two near rows (or below the
newest near row of all, or is it), so on screen or in the margin. -/
theorem hull_near {fr : Frame} (hg : fr.Good) {w : Win} (hw : w ∈ fr.listWins) {r : Row} (hr : r ∈ fr.rows)
    (hin : w.inside r.pos = true) : fr.near r = true := by
  obtain ⟨-, -, hmin⟩ := screen_subs hg
  obtain ⟨o, ho, hop, hn⟩ := hmin w hw r.pos hin
  obtain ⟨hor, hon⟩ := mem_shown.1 ho
  have hb := hg.order.and hg.stack
  -- an older row sits above a newer one
  have above_of : ∀ a ∈ fr.rows, ∀ c ∈ fr.rows, c.pos.cmp a.pos = .lt → a.bot + a.h ≤ c.bot := by
    intro a ha c hc hlt
    rcases pairwise_two hb ha hc with rfl | h | h
    · rw [Pos.cmp_self] at hlt; cases hlt
    · exact h.2
    · have := Pos.cmp_lt_trans hlt h.1; rw [Pos.cmp_self] at this; cases this
  -- rows at one position are one row
  have same : ∀ a ∈ fr.rows, ∀ c ∈ fr.rows, a.pos = c.pos → a = c := by
    intro a ha c hc he
    rcases pairwise_two hb ha hc with e | h | h
    · exact e
    · rw [he, Pos.cmp_self] at h; cases h.1
    · rw [he, Pos.cmp_self] at h; cases h.1
  simp only [Frame.near, Bool.and_eq_true, decide_eq_true_eq] at hon ⊢
  -- r is at or after o, the oldest near row
  rcases e : o.pos.cmp r.pos with _ | _ | _
  · have h1 := above_of r hr o hor e
    refine ⟨by omega, ?_⟩
    rcases hn with ⟨n, hns, hnp⟩ | ⟨r0, h0, hn0⟩
    · obtain ⟨hnr, hnn⟩ := mem_shown.1 hns
      simp only [Frame.near, Bool.and_eq_true, decide_eq_true_eq] at hnn
      rcases e2 : r.pos.cmp n.pos with _ | _ | _
      · have := above_of n hnr r hr e2; omega
      · rw [same r hr n hnr ((Pos.cmp_eq_iff _ _).1 e2)]; exact hnn.2
      · exact absurd e2 hnp
    · simp only [Frame.near, Bool.and_eq_true, decide_eq_true_eq] at hn0
      rcases mem_head_or hg.stack h0 hr with rfl | h
      · exact hn0.2
      · omega
  · rw [← same o hor r hr ((Pos.cmp_eq_iff _ _).1 e)]; exact hon
  · exact absurd e hop

/-- **The subscriptions the frame registers are exactly its wants**,
each under its owner (the read that wants it). -/
theorem screen_index {S : Type} (fr : Frame) (own : Win → S) (x : S) (w : Win) :
    (Subs.ofList (fr.wants.map fun v => (own v, v))).Has x w ↔ w ∈ fr.wants ∧ own w = x := by
  rw [Subs.has_ofList, List.mem_map]
  constructor
  · rintro ⟨v, hv, he⟩
    cases he
    exact ⟨hv, rfl⟩
  · rintro ⟨hw, rfl⟩
    exact ⟨w, hw, rfl⟩

/-- **Minimality as the frame runs it** (weakened (iii)). The loaded rows
are at most `half` newer than an anchor and at most `half` at or older,
and the anchor row is near; then at most `half` loaded rows are newer
than every near row, and at most `half` older than every near row: the
list windows, which hold exactly the loaded rows (`window_rows`), reach
at most `half` rows past each end of the near rows' hull. -/
theorem past_hull_le {fr : Frame} {a : Row} (ha : a ∈ fr.rows) (hn : fr.near a = true) (half : Nat)
    (hnew : (fr.rows.filter fun r => a.pos.cmp r.pos == .lt).length ≤ half)
    (hold : (fr.rows.filter fun r => r.pos.cmp a.pos != .gt).length ≤ half) :
    (fr.rows.filter fun r => fr.shown.all fun n => n.pos.cmp r.pos == .lt).length ≤ half ∧
      (fr.rows.filter fun r => fr.shown.all fun o => r.pos.cmp o.pos == .lt).length ≤ half := by
  have has : a ∈ fr.shown := mem_shown.2 ⟨ha, hn⟩
  constructor
  · refine Nat.le_trans ?_ hnew
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    apply List.countP_mono_left
    intro r _ h
    exact List.all_eq_true.1 h a has
  · refine Nat.le_trans ?_ hold
    rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
    apply List.countP_mono_left
    intro r _ h
    have := List.all_eq_true.1 h a has
    simp only [beq_iff_eq] at this
    simp [this]

/-! ## The mutant: keeping what scrolled off -/

/-- The app's keep before this (App.lean, every 30 frames): every list
read is kept, over all its loaded rows, and every loaded row's reads. -/
def keepAll (fr : Frame) : List Win :=
  fr.chrome ++ (match fr.rows.getLast? with
    | some oldest => fr.keys.map fun k => { key := k, lo := some (oldest.pos, true) }
    | none => []) ++ fr.rows.flatMap (·.deps)

/-- A row on screen and one far above it, with a read of its own. -/
def far : Row := { pos := (⟨#[1]⟩, .empty), bot := 100, h := 10, deps := [Win.all ⟨#[9]⟩] }
def onScreen : Row := { pos := (⟨#[2]⟩, .empty), bot := 0, h := 10, deps := [] }
def frame2 : Frame := { keys := [⟨#[7]⟩], rows := [onScreen, far], b := 0, vh := 20, margin := 0, chrome := [] }

theorem frame2_good : frame2.Good where
  order := by
    show List.Pairwise _ [onScreen, far]
    rw [List.pairwise_pair]
    show Pos.cmp (⟨#[1]⟩, .empty) (⟨#[2]⟩, .empty) = .lt
    simp only [Pos.cmp, bcmp_eq_lexCmp]
    rfl
  stack := by simp [frame2, far, onScreen]

/-- **The mutant violates screen_subs**: it wants the far row's read, which
no near row, no list window and no page read is; and its list window
covers the far row. -/
theorem keep_scrolled_off :
    Win.all ⟨#[9]⟩ ∈ keepAll frame2 ∧ Win.all ⟨#[9]⟩ ∉ frame2.wants ∧
      (∃ w ∈ keepAll frame2, w.inside far.pos = true) ∧ frame2.near far = false := by
  have hfar : frame2.near far = false := by decide
  have hon : frame2.near onScreen = true := by decide
  refine ⟨?_, ?_, ?_, hfar⟩
  · simp [keepAll, frame2, far]
  · intro h
    rcases (screen_subs frame2_good).1 _ |>.1 h with h | h | ⟨r, hr, hn, hd⟩
    · simp [frame2] at h
    · -- the list windows are under the list's key
      unfold Frame.listWins at h
      split at h
      · obtain ⟨k, hk, he⟩ := List.mem_map.1 h
        simp only [frame2, List.mem_singleton] at hk
        subst hk
        have := congrArg Win.key he
        simp [Win.all] at this
      · cases h
    · simp only [frame2, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · simp [onScreen] at hd
      · rw [hfar] at hn; cases hn
  · refine ⟨{ key := ⟨#[7]⟩, lo := some (far.pos, true) }, by simp [keepAll, frame2, far], ?_⟩
    simp [Win.inside, above, below, Pos.cmp_self]

end Screen
