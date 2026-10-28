/-
What the frame may rely on from the board (engine/renderer/Board.lean),
and that the screen settles to the store's values.

The board's laws are about the code the reader and the frame call
(`put`, `take`, `keep`):

- `put_same`, `put_moves`: an equal refill changes nothing; a different
  or new one takes the next version and is moved.
- `ver_ident`: along any run of puts, takes and keeps, one version of a
  want is one value, so a frame that holds a value at version n and
  sees version n again has nothing to do.
- `seen_put`, `seen_take`, `seen_keep`: no change is lost between two
  takes. `Seen`: every value held is moved or is what the frame shows.

The world (a model of the threads around the board, its steps the
board's own operations): the writer's commits, the reader's passes, and
the frame, in any order. The store is abstract (`eval s w`: want w's
value in store s), and one thing is assumed of it, the engine's
`view_stable`: a commit that does not touch w leaves its value
(`Stable`). Then:

- `inv_commit`, `inv_pass`, `inv_frame`, `inv_want`: every step keeps
  `Inv` (every value held is dirty, touched by a commit the reader has
  not taken, or the store's; and `Seen`).
- `settle` (no missed update): a pass that refills every dirty want,
  then one frame: every want shows the store's value. `marked_pass`: a
  pass leaves dirty only what it did not refill, so passes of `refill`
  each settle in ⌈dirty / refill⌉ of them (`settle_passes`).
- `gated_stale`, the mutant control: a frame that works only when it
  took a notice (holmes-1e's TwoNodes failures) shows a stale value for
  ever after its refill lands a frame late, where the frame above shows
  the store's.
-/
import engine.renderer.Board

set_option linter.unusedSectionVars false

namespace Live
open Std

namespace Board
variable {W V : Type} [BEq W] [Hashable W] [LawfulBEq W]

section
variable [BEq V]

theorem put_same {b : Board W V} {w : W} {u v : V} {n : Ver} (h : b.vals[w]? = some (u, n))
    (e : (u == v) = true) : b.put w v = b := by
  simp [put, h, e]

/-- A put leaves the board, or bumps w to v. -/
theorem put_cases (b : Board W V) (w : W) (v : V) :
    (b.put w v = b ∧ ∃ u n, b.vals[w]? = some (u, n) ∧ (u == v) = true) ∨ b.put w v = b.bump w v := by
  unfold put
  split
  · rename_i u n h
    split
    · rename_i e; exact Or.inl ⟨rfl, u, n, h, e⟩
    · exact Or.inr rfl
  · exact Or.inr rfl

theorem bump_vals (b : Board W V) (w x : W) (v : V) :
    (b.bump w v).vals[x]? = if w == x then some (v, b.next) else b.vals[x]? := by
  simp only [bump, HashMap.getElem?_insert]

theorem bump_other (b : Board W V) {w x : W} (v : V) (hx : w ≠ x) :
    (b.bump w v).vals[x]? = b.vals[x]? := by
  rw [bump_vals, ite_eq_right (by simpa using hx)]

theorem bump_moved (b : Board W V) (w x : W) (v : V) :
    (b.bump w v).moved.contains x = (w == x || b.moved.contains x) := by
  simp [bump, HashSet.contains_insert]

/-- **A different or new value takes the next version and is moved.** -/
theorem put_moves {b : Board W V} {w : W} {v : V}
    (h : ∀ u n, b.vals[w]? = some (u, n) → (u == v) = false) :
    (b.put w v).vals[w]? = some (v, b.next) ∧ (b.put w v).moved.contains w = true ∧
      (b.put w v).next = b.next + 1 := by
  unfold put
  cases hw : b.vals[w]? with
  | none => simp [bump]
  | some p =>
    obtain ⟨u, n⟩ := p
    simp [h u n hw, bump]

/-- A put leaves every other want's value. -/
theorem put_other (b : Board W V) {w x : W} (v : V) (hx : w ≠ x) :
    (b.put w v).vals[x]? = b.vals[x]? := by
  unfold put
  split
  · split
    · rfl
    · exact bump_other _ _ hx
  · exact bump_other _ _ hx

/-- After a put, w holds v, or a value v equals. -/
theorem put_self (b : Board W V) (w : W) (v : V) :
    ∃ u n, (b.put w v).vals[w]? = some (u, n) ∧ (u = v ∨ (u == v) = true) := by
  unfold put
  cases hw : b.vals[w]? with
  | none => exact ⟨v, b.next, by simp [bump_vals], Or.inl rfl⟩
  | some p =>
    obtain ⟨u, n⟩ := p
    by_cases e : (u == v) = true
    · exact ⟨u, n, by simp [e, hw], Or.inr e⟩
    · exact ⟨v, b.next, by simp [e, bump_vals], Or.inl rfl⟩

theorem put_next (b : Board W V) (w : W) (v : V) : b.next ≤ (b.put w v).next := by
  unfold put
  split
  · split
    · exact Nat.le_refl _
    · exact Nat.le_succ _
  · exact Nat.le_succ _

/-- A put changes the moved set only by w. -/
theorem put_moved (b : Board W V) (w x : W) (v : V) (hx : b.moved.contains x = true) :
    (b.put w v).moved.contains x = true := by
  unfold put
  split
  · split
    · exact hx
    · simp [bump_moved, hx]
  · simp [bump_moved, hx]

end

theorem keep_vals (b : Board W V) (want : W → Bool) (x : W) :
    (b.keep want).vals[x]? = if want x then b.vals[x]? else none := by
  simp only [keep, HashMap.getElem?_filter']
  cases b.vals[x]? <;> cases want x <;> rfl

/-! ## One version, one value -/

/-- A step of the reader or the frame on the board. -/
inductive Step [BEq V] : Board W V → Board W V → Prop
  | put (b : Board W V) (w : W) (v : V) : Step b (b.put w v)
  | take (b : Board W V) : Step b b.take.2
  | keep (b : Board W V) (want : W → Bool) : Step b (b.keep want)

/-- Steps in a row. -/
inductive Run [BEq V] : Board W V → Board W V → Prop
  | refl (b : Board W V) : Run b b
  | step {a b c : Board W V} : Step a b → Run b c → Run a c

/-- Every version held is below the next. -/
def Fresh (b : Board W V) : Prop := ∀ (w : W) (v : V) (n : Ver), b.vals[w]? = some (v, n) → n < b.next

theorem fresh_empty : Fresh ({} : Board W V) := by
  intro w v n h
  simp at h

variable [BEq V]

theorem Step.next_le {a b : Board W V} : Step a b → a.next ≤ b.next
  | .put _ _ _ => put_next _ _ _
  | .take _ => Nat.le_refl _
  | .keep _ _ => Nat.le_refl _

/-- A version below a's next that b holds, a held, with the same value. -/
theorem Step.old {a b : Board W V} (s : Step a b) {w : W} {v : V} {n : Ver}
    (hb : b.vals[w]? = some (v, n)) (hn : n < a.next) : a.vals[w]? = some (v, n) := by
  cases s with
  | put k u =>
    by_cases hk : k = w
    · subst hk
      rcases put_cases a k u with ⟨e, _⟩ | e
      · rwa [e] at hb
      · rw [e, bump_vals, ite_eq_left (beq_self_eq_true k)] at hb
        cases hb; exact absurd hn (Nat.lt_irrefl _)
    · rwa [put_other _ _ hk] at hb
  | take => exact hb
  | keep want =>
    rw [keep_vals] at hb
    split at hb
    · exact hb
    · cases hb

theorem Step.fresh {a b : Board W V} (s : Step a b) (fa : Fresh a) : Fresh b := by
  intro w v n hb
  cases s with
  | put k u =>
    by_cases hk : k = w
    · subst hk
      rcases put_cases a k u with ⟨e, _⟩ | e
      · rw [e] at hb ⊢; exact fa _ _ _ hb
      · rw [e] at hb ⊢
        rw [bump_vals, ite_eq_left (beq_self_eq_true k)] at hb
        cases hb; exact Nat.lt_succ_self _
    · rw [put_other _ _ hk] at hb
      exact Nat.lt_of_lt_of_le (fa _ _ _ hb) (put_next _ _ _)
  | take => exact fa _ _ _ hb
  | keep want =>
    rw [keep_vals] at hb
    split at hb
    · exact fa _ _ _ hb
    · cases hb

theorem Run.next_le {a b : Board W V} (r : Run a b) : a.next ≤ b.next := by
  induction r with
  | refl => exact Nat.le_refl _
  | step s _ ih => exact Nat.le_trans s.next_le ih

theorem Run.old {a b : Board W V} (r : Run a b) {w : W} {v : V} {n : Ver}
    (hb : b.vals[w]? = some (v, n)) (hn : n < a.next) : a.vals[w]? = some (v, n) := by
  induction r with
  | refl => exact hb
  | step s r ih => exact s.old (ih hb (Nat.lt_of_lt_of_le hn s.next_le)) hn

/-- **One version, one value**: along any run of puts, takes and keeps
from a board whose versions are below its next (as every board is, from
the empty one: `fresh_empty`, `Step.fresh`), a want held at the same
version at both ends holds the same value. -/
theorem ver_ident {a b : Board W V} (r : Run a b) (fa : Fresh a) {w : W} {v₁ v₂ : V} {n : Ver}
    (ha : a.vals[w]? = some (v₁, n)) (hb : b.vals[w]? = some (v₂, n)) : v₁ = v₂ := by
  have := r.old hb (fa _ _ _ ha)
  rw [ha] at this
  cases this
  rfl

/-! ## No change is lost between two takes -/

/-- Every value held is moved, or is what the frame shows. -/
def Seen (shown : W → Option V) (b : Board W V) : Prop :=
  ∀ (x : W) (v : V) (n : Ver), b.vals[x]? = some (v, n) → b.moved.contains x = true ∨ shown x = some v

/-- What the frame shows after it takes b's moved set. -/
def apply (shown : W → Option V) (b : Board W V) : W → Option V := fun x =>
  if b.moved.contains x then (b.vals[x]?.map (·.1)) else shown x

theorem seen_put {shown : W → Option V} {b : Board W V} (h : Seen shown b) (w : W) (v : V) :
    Seen shown (b.put w v) := by
  intro x u n hx
  by_cases hk : w = x
  · subst hk
    rcases put_cases b w v with ⟨e, _⟩ | e
    · rw [e] at hx ⊢; exact h _ _ _ hx
    · rw [e]; left; simp [bump_moved]
  · rw [put_other _ _ hk] at hx
    rcases h _ _ _ hx with m | s
    · exact Or.inl (put_moved _ _ _ _ m)
    · exact Or.inr s

theorem seen_take {shown : W → Option V} {b : Board W V} (h : Seen shown b) :
    Seen (apply shown b) b.take.2 := by
  intro x v n hx
  right
  simp only [take] at hx
  unfold apply
  split
  · simp [hx]
  · rcases h _ _ _ hx with m | s
    · rename_i hm; exact absurd m hm
    · exact s

theorem seen_keep {shown : W → Option V} {b : Board W V} (h : Seen shown b) (want : W → Bool) :
    Seen shown (b.keep want) := by
  intro x v n hx
  rw [keep_vals] at hx
  split at hx
  · exact h _ _ _ hx
  · cases hx

end Board

/-! ## The world: the writer, the reader and the frame -/

/-- The store (σ, changed by commits C), the journal of commits the
reader has not taken, the reader's board and dirty wants, the frame's
wants and what it shows. -/
structure World (σ C W V : Type) [BEq W] [Hashable W] where
  store : σ
  journal : List C := []
  board : Board W V := {}
  dirty : List W := []
  wants : List W := []
  shown : W → Option V := fun _ => none

namespace World
variable {σ C W V : Type} [BEq W] [Hashable W] [LawfulBEq W] [BEq V]
  (apply : C → σ → σ) (touch : C → W → Bool) (eval : σ → W → V)

/-- The writer commits c. -/
def commit (c : C) (w : World σ C W V) : World σ C W V :=
  { w with store := apply c w.store, journal := w.journal ++ [c] }

/-- What a pass finds to refill: the dirty, what the journal's commits
touched, and every want not held; only wants. -/
def marked (w : World σ C W V) : List W :=
  (w.dirty ++ w.wants.filter (fun x => w.journal.any (touch · x)) ++
    w.wants.filter (fun x => !w.board.vals.contains x)).filter (w.wants.contains ·)

/-- A reader pass, in one snapshot (the store as it is): take the
journal, forget what is not wanted, refill `pick` (at most `refill` of
the marked, the reader's choice), and keep the rest dirty. -/
def pass (pick : List W) (w : World σ C W V) : World σ C W V :=
  { w with
    journal := []
    board := pick.foldl (fun b x => b.put x (eval w.store x)) (w.board.keep (w.wants.contains ·))
    dirty := (w.marked touch).filter (!pick.contains ·) }

/-- The frame takes the moved set and shows those values. -/
def frame (w : World σ C W V) : World σ C W V :=
  { w with board := w.board.take.2, shown := Board.apply w.shown w.board }

/-- The frame changes what it wants. -/
def want (ws : List W) (w : World σ C W V) : World σ C W V := { w with wants := ws }

/-- A commit that does not touch w leaves w's value (the engine's
`view_stable`). -/
def Stable : Prop := ∀ c s x, touch c x = false → eval (apply c s) x = eval s x

/-- Every value held is dirty, touched by a commit not yet taken, or the
store's; and the frame has seen it or it is moved. -/
def Inv (w : World σ C W V) : Prop :=
  (∀ (x : W) (v : V) (n : Ver), w.board.vals[x]? = some (v, n) →
    x ∈ w.dirty ∨ (∃ c ∈ w.journal, touch c x = true) ∨ v = eval w.store x) ∧
  Board.Seen w.shown w.board

theorem inv_start (s : σ) (ws : List W) : Inv touch eval ({ store := s, wants := ws } : World σ C W V) := by
  constructor <;> intro x v n h <;> simp at h

theorem inv_commit (hs : Stable apply touch eval) {w : World σ C W V} (h : Inv touch eval w) (c : C) :
    Inv touch eval (w.commit apply c) := by
  refine ⟨fun x v n hx => ?_, h.2⟩
  rcases h.1 x v n hx with d | ⟨c', hc', t⟩ | e
  · exact Or.inl d
  · exact Or.inr (Or.inl ⟨c', by simp [commit, hc'], t⟩)
  · cases ht : touch c x
    · exact Or.inr (Or.inr (by simp only [commit]; rw [hs c _ x ht]; exact e))
    · exact Or.inr (Or.inl ⟨c, by simp [commit], ht⟩)

/-- What the refills of pick leave: each picked want holds its value in
s (or one equal to it), every other what it held. -/
theorem foldl_put (s : W → V) : ∀ (pick : List W) (b : Board W V) (x : W),
    (x ∈ pick → ∃ u n, (pick.foldl (fun b y => b.put y (s y)) b).vals[x]? = some (u, n) ∧
      (u = s x ∨ (u == s x) = true)) ∧
    (x ∉ pick → (pick.foldl (fun b y => b.put y (s y)) b).vals[x]? = b.vals[x]?)
  | [], b, x => ⟨fun h => absurd h (List.not_mem_nil), fun _ => rfl⟩
  | y :: rest, b, x => by
    obtain ⟨ih1, ih2⟩ := foldl_put s rest (b.put y (s y)) x
    simp only [List.foldl_cons, List.mem_cons]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · by_cases hr : x ∈ rest
      · exact ih1 hr
      · rw [ih2 hr]
        have hy : y = x := by rcases h with h | h; exact h.symm; exact absurd h hr
        subst hy
        exact Board.put_self _ _ _
    · have hy : y ≠ x := fun e => h (Or.inl e.symm)
      rw [ih2 (fun m => h (Or.inr m)), Board.put_other _ _ hy]

theorem seen_foldl {shown : W → Option V} (s : W → V) :
    ∀ (pick : List W) (b : Board W V), Board.Seen shown b →
      Board.Seen shown (pick.foldl (fun b y => b.put y (s y)) b)
  | [], _, h => h
  | y :: rest, _, h => seen_foldl s rest _ (Board.seen_put h y (s y))

variable [LawfulBEq V]

theorem inv_pass {w : World σ C W V} (h : Inv touch eval w) (pick : List W) :
    Inv touch eval (w.pass touch eval pick) := by
  refine ⟨fun x v n hx => ?_, seen_foldl _ _ _ (Board.seen_keep h.2 _)⟩
  simp only [pass] at hx ⊢
  by_cases hp : x ∈ pick
  · obtain ⟨u, k, hu, e⟩ := (foldl_put (eval w.store) pick _ x).1 hp
    rw [hu] at hx
    cases hx
    right; right
    rcases e with e | e
    · exact e
    · exact beq_iff_eq.1 e
  · rw [(foldl_put (eval w.store) pick _ x).2 hp, Board.keep_vals] at hx
    split at hx
    · rename_i hwant
      rcases h.1 x v n hx with d | ⟨c, hc, t⟩ | e
      · left
        simp only [marked, List.mem_filter, List.mem_append, hwant, and_true]
        exact ⟨Or.inl (Or.inl d), by simpa using hp⟩
      · left
        simp only [marked, List.mem_filter, List.mem_append, hwant, and_true]
        refine ⟨Or.inl (Or.inr ⟨List.contains_iff_mem.1 hwant, List.any_eq_true.2 ⟨c, hc, t⟩⟩), ?_⟩
        simpa using hp
      · exact Or.inr (Or.inr e)
    · cases hx

theorem inv_frame {w : World σ C W V} (h : Inv touch eval w) : Inv touch eval w.frame :=
  ⟨h.1, Board.seen_take h.2⟩

theorem inv_want {w : World σ C W V} (h : Inv touch eval w) (ws : List W) :
    Inv touch eval (w.want ws) := h

/-- **No missed update**: from any world the steps above reach, a pass
that refills every want it marks, then one frame, shows every want's
value in the store. -/
theorem settle {w : World σ C W V} (h : Inv touch eval w) {pick : List W}
    (hp : ∀ x ∈ w.marked touch, x ∈ pick) {x : W} (hx : x ∈ w.wants) :
    ((w.pass touch eval pick).frame).shown x = some (eval w.store x) := by
  have hw : w.wants.contains x = true := List.contains_iff_mem.2 hx
  -- after the pass, x is held at its value in the store
  have held : ∃ n, (w.pass touch eval pick).board.vals[x]? = some (eval w.store x, n) := by
    simp only [pass]
    by_cases hpk : x ∈ pick
    · obtain ⟨u, k, hu, e⟩ := (foldl_put (eval w.store) pick _ x).1 hpk
      refine ⟨k, ?_⟩
      rw [hu]
      rcases e with e | e
      · rw [e]
      · rw [beq_iff_eq.1 e]
    · rw [(foldl_put (eval w.store) pick _ x).2 hpk, Board.keep_vals, ite_eq_left hw]
      have notMarked : x ∉ w.marked touch := fun m => hpk (hp x m)
      cases hv : w.board.vals[x]? with
      | none =>
        exfalso; apply notMarked
        simp only [marked, List.mem_filter, List.mem_append, hw, and_true]
        right
        exact ⟨hx, by simp [Std.HashMap.contains_eq_isSome_getElem?, hv]⟩
      | some p =>
        obtain ⟨v, n⟩ := p
        refine ⟨n, ?_⟩
        rcases h.1 x v n hv with d | ⟨c, hc, t⟩ | e
        · exfalso; apply notMarked
          simp only [marked, List.mem_filter, List.mem_append, hw, and_true]
          exact Or.inl (Or.inl d)
        · exfalso; apply notMarked
          simp only [marked, List.mem_filter, List.mem_append, hw, and_true]
          exact Or.inl (Or.inr ⟨hx, List.any_eq_true.2 ⟨c, hc, t⟩⟩)
        · rw [e]
  obtain ⟨n, hn⟩ := held
  have hs := (inv_frame touch eval (inv_pass touch eval h pick)).2 x (eval w.store x) n
  simp only [frame, Board.take] at hs
  rcases hs hn with m | s
  · simp at m
  · exact s

/-- A pass leaves dirty only what it marked and did not refill, and
nothing else is marked after it until a commit or a new want. -/
theorem marked_pass {w : World σ C W V} {pick : List W} {x : W}
    (hx : x ∈ (w.pass touch eval pick).marked touch) : x ∈ w.marked touch ∧ x ∉ pick := by
  unfold marked at hx
  rw [List.mem_filter, List.mem_append, List.mem_append] at hx
  obtain ⟨(hd | ht) | hm, hw⟩ := hx
  · simp only [pass, List.mem_filter] at hd
    exact ⟨hd.1, by simpa using hd.2⟩
  · simp [pass] at ht
  · have hw' : w.wants.contains x = true := hw
    simp only [pass, List.mem_filter] at hm
    obtain ⟨hxw, hnot⟩ := hm
    rw [Std.HashMap.contains_eq_isSome_getElem?] at hnot
    by_cases hp : x ∈ pick
    · exfalso
      obtain ⟨u, k, hu, _⟩ := (foldl_put (eval w.store) pick (w.board.keep (w.wants.contains ·)) x).1 hp
      rw [hu] at hnot
      simp at hnot
    · refine ⟨?_, hp⟩
      rw [(foldl_put (eval w.store) pick _ x).2 hp, Board.keep_vals, ite_eq_left hw'] at hnot
      unfold marked
      rw [List.mem_filter, List.mem_append]
      refine ⟨Or.inr (List.mem_filter.2 ⟨hxw, ?_⟩), hw'⟩
      rw [Std.HashMap.contains_eq_isSome_getElem?]
      exact hnot

/-- **Settling in passes**: with no commit and no new want meanwhile,
passes whose refills together cover what the first marks, then one
frame, show every want's value in the store. A pass refills at most
`refill` wants, so ⌈marked / refill⌉ passes suffice. -/
theorem settle_passes : ∀ (ps : List (List W)) (p : List W) {w : World σ C W V}, Inv touch eval w →
    (∀ x ∈ w.marked touch, x ∈ p ∨ ∃ q ∈ ps, x ∈ q) → ∀ x ∈ w.wants,
    (((ps.foldl (fun w q => w.pass touch eval q) w).pass touch eval p).frame).shown x =
      some (eval w.store x)
  | [], p, w, h, hp, x, hx => settle touch eval h (fun y m => by simpa using hp y m) hx
  | q :: rest, p, w, h, hp, x, hx => by
    simp only [List.foldl_cons]
    exact settle_passes rest p (inv_pass touch eval h q) (fun y m => by
      obtain ⟨m0, nq⟩ := marked_pass touch eval m
      rcases hp y m0 with a | ⟨q', hq', b⟩
      · exact Or.inl a
      · simp only [List.mem_cons] at hq'
        rcases hq' with e | e
        · subst e; exact absurd b nq
        · exact Or.inr ⟨q', e, b⟩) x hx

end World

/-! ## The mutant: a frame gated on notices -/

namespace Gated

/-- One want, its value the store's number. -/
abbrev Wd := World Nat Nat Unit Nat

def apply (c : Nat) (_ : Nat) : Nat := c
def touch (_ : Nat) (_ : Unit) : Bool := true
def eval (s : Nat) (_ : Unit) : Nat := s

/-- The frame that works only when it took a notice this frame. -/
def frameGated (notice : Bool) (w : Wd) : Wd := if notice then w.frame else w

/-- The trace: the reader fills the want and the frame shows it (0);
a commit (1); the frame takes its notice before the refill lands; the
refill lands. -/
def w4 : Wd :=
  ((((({ store := 0, wants := [()] } : Wd).pass touch eval [()]).frame).commit apply 1).frame)

def w5 : Wd := w4.pass touch eval [()]

theorem stable : World.Stable apply touch eval := fun _ _ _ h => by simp [touch] at h

/-- k gated frames that take no notice. -/
def quiet : Nat → Wd → Wd
  | 0, w => w
  | k + 1, w => quiet k (frameGated false w)

/-- **The notice-gated frame shows a stale value for ever**: after the
refill lands with no notice, it shows 0 at every later frame, while the
store's value is 1. -/
theorem gated_stale (k : Nat) : (quiet k w5).shown () = some 0 ∧ w5.store = 1 := by
  have h : ∀ k (w : Wd), quiet k w = w := by
    intro k; induction k with
    | zero => intro _; rfl
    | succ k ih => intro w; exact ih _
  refine ⟨?_, rfl⟩
  rw [h]
  -- the pass leaves what the frame shows; the second frame took nothing
  show (w4.shown ()) = some 0
  simp [w4, World.frame, World.commit, World.pass, Board.apply, Board.take, Board.put,
    Board.bump, Board.keep, World.marked, eval]

/-- **The frame above shows the store's value** one frame after the
same refill lands (`settle`). -/
theorem ungated_fresh : (w5.frame).shown () = some 1 := by
  have inv : World.Inv touch eval w4 :=
    World.inv_frame touch eval (World.inv_commit apply touch eval stable
      (World.inv_frame touch eval (World.inv_pass touch eval (World.inv_start touch eval 0 [()]) _)) 1)
  have := World.settle touch eval inv (pick := [()]) (fun x _ => by cases x; simp) (x := ())
    (by simp [w4, World.frame, World.commit, World.pass])
  simpa [w5, w4, World.frame, World.commit, World.pass, eval, Gated.apply] using this

end Gated

end Live
