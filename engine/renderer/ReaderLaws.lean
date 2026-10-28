/-
The reader's pass as it runs (ops/app/Reader.lean, holmes-1e's): its
cache's stale reads, each held want's reads, its dirty wants, and the
board. `RWorld` is the world of engine/renderer/BoardLaws.lean with the
reader's own state in place of an abstract `touch`: a commit stales the
reads it files under (`hits`, Live.notice), a want is marked when one of
its reads is stale or it holds none (`staleW`, Reader.stale), every want
is marked before any is read again (`mark`), and the first `cap` marked
wants in the frame's order are read (`pick`), each value put on the
board (Board.put) and its reads recorded fresh.

`mark` and `pick` are the pass's decisions, pure, for Reader.pass to
call (its marking fold and its `cap` loop compute the same, and the
diff that makes them these functions is in docs/PERF.md). What the
reader reads, through its cache, is its pass's one moment: holmes-1e's
LiveLaws (`Agrees`, `read_one_moment`), so a read here is `eval` of the
store as it is.

Laws, with the store abstract and one assumption, the engine's
`view_stable` per commit as made (`StableAt`: a commit that files under
none of a want's reads leaves its value, and its reads):

- `inv_commit`, `inv_pass`, `inv_frame`: every step keeps `Inv`: each
  value held is dirty, has a read a commit not yet taken hits, has a
  stale read or none, or is the store's with its reads recorded; a want
  is held exactly when its reads are; and `Seen`.
- `settle`: a pass that reads every marked want, then one frame, shows
  every want's value in the store.
- `eager_stale`, the mutant control (holmes-1e's finding): a pass that
  checks staleness while it reads, two wants sharing one read: the first
  read refreshes the shared read, the second then looks clean, and it
  shows the old value for ever, where `pass` shows the new
  (`marked_fresh`).
-/
import engine.renderer.BoardLaws

set_option linter.unusedSectionVars false

namespace Live

/-- The reader's world: the store, the commits the reader has not taken,
the board, the cache's stale reads, each held want's reads, the dirty
wants, the frame's wants (most urgent first), and what the frame shows. -/
structure RWorld (σ C W V Q : Type) [BEq W] [Hashable W] where
  store : σ
  journal : List C := []
  board : Board W V := {}
  staleQ : Q → Bool := fun _ => false
  deps : W → Option (List Q) := fun _ => none
  dirty : Std.HashSet W := {}
  wants : List W := []
  shown : W → Option V := fun _ => none
  /-- The reverse index: each read, the wants that recorded it (the
  reader at rest, engine/renderer/RestLaws.lean). -/
  rev : Q → List W := fun _ => []
  /-- The writers' commit counter, and its value at the reader's last
  pass (RestLaws: at rest the reader reads no journal). -/
  commits : Nat := 0
  seen : Nat := 0

/-! ## The pass's decisions: what they compute, and what they cost -/

section
variable {W : Type} [BEq W] [Hashable W] [LawfulBEq W]

theorem mem_filter' (d : Std.HashSet W) (f : W → Bool) (x : W) : x ∈ d.filter f ↔ x ∈ d ∧ f x = true := by
  rw [Std.HashSet.mem_filter]
  constructor
  · rintro ⟨h, hf⟩; rw [Std.HashSet.get_eq] at hf; exact ⟨h, hf⟩
  · rintro ⟨h, hf⟩; exact ⟨h, by rw [Std.HashSet.get_eq]; exact hf⟩

theorem mem_markM (stale : W → Bool) : ∀ (ws : List W) (d : Std.HashSet W) (x : W),
    x ∈ Id.run (markM stale d ws) ↔ x ∈ d ∨ (x ∈ ws ∧ stale x = true)
  | [], d, x => by simp [markM]
  | w :: ws, d, x => by
    show x ∈ Id.run (markM stale (if stale w then d.insert w else d) ws) ↔ _
    rw [mem_markM stale ws]
    by_cases hs : stale w = true
    · simp only [hs, ite_true, Std.HashSet.mem_insert, beq_iff_eq, List.mem_cons]
      constructor
      · rintro ((rfl | h) | ⟨h1, h2⟩)
        · exact Or.inr ⟨Or.inl rfl, hs⟩
        · exact Or.inl h
        · exact Or.inr ⟨Or.inr h1, h2⟩
      · rintro (h | ⟨rfl | h1, h2⟩)
        · exact Or.inl (Or.inr h)
        · exact Or.inl (Or.inl rfl)
        · exact Or.inr ⟨h1, h2⟩
    · simp only [hs, Bool.false_eq_true, ite_false, List.mem_cons]
      constructor
      · rintro (h | ⟨h1, h2⟩)
        · exact Or.inl h
        · exact Or.inr ⟨Or.inr h1, h2⟩
      · rintro (h | ⟨rfl | h1, h2⟩)
        · exact Or.inl h
        · exact absurd h2 hs
        · exact Or.inr ⟨h1, h2⟩

/-- **What a pass marks**: the dirty, and every want whose reads changed. -/
theorem mem_mark (ws : List W) (stale : W → Bool) (d : Std.HashSet W) (x : W) :
    x ∈ mark ws stale d ↔ x ∈ d ∨ (x ∈ ws ∧ stale x = true) := mem_markM stale ws d x

theorem pickM_eq (d : Std.HashSet W) : ∀ (cap : Nat) (ws : List W),
    Id.run (pickM d cap ws) = (ws.filter (d.contains ·)).take cap
  | 0, ws => by simp [pickM]
  | k + 1, [] => by simp [pickM]
  | k + 1, w :: ws => by
    show Id.run (if d.contains w then (do return w :: (← pickM d k ws)) else pickM d (k + 1) ws) = _
    by_cases h : d.contains w = true
    · simp only [h, ite_true, List.filter_cons_of_pos h, List.take_succ_cons]
      rw [← pickM_eq d k ws]; rfl
    · simp only [h, Bool.false_eq_true, ite_false, List.filter_cons_of_neg h]
      exact pickM_eq d (k + 1) ws

/-- **What a pass reads**: the first `cap` marked, in the frame's order. -/
theorem pick_eq (ws : List W) (d : Std.HashSet W) (cap : Nat) :
    pick ws d cap = (ws.filter (d.contains ·)).take cap := pickM_eq d cap ws

/-- What a pass leaves dirty: the marked it did not read. -/
theorem mem_eraseAll : ∀ (p : List W) (d : Std.HashSet W) (x : W),
    x ∈ p.foldl (·.erase ·) d ↔ x ∈ d ∧ x ∉ p
  | [], d, x => by simp
  | y :: p, d, x => by
    simp only [List.foldl_cons, List.mem_cons, not_or]
    rw [mem_eraseAll p, Std.HashSet.mem_erase, beq_eq_false_iff_ne]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h2, fun e => h1 e.symm, h3⟩
    · rintro ⟨h2, h1, h3⟩; exact ⟨⟨fun e => h1 e.symm, h2⟩, h3⟩

open Engine Engine.Counted in
/-- **Marking costs a step per want.** -/
theorem markM_cost (stale : W → Bool) : ∀ (ws : List W) (d : Std.HashSet W),
    cost (markM (m := Counted) stale d ws) = { work := ws.length }
  | [], d => by simp [markM]; rfl
  | w :: ws, d => by
    simp only [markM, cost_bind, cost_tick, markM_cost stale ws, List.length_cons]
    ext <;> simp; omega

open Engine Engine.Counted in
/-- **Picking costs at most a step per want**: one hash lookup each, so a
pass's decisions are O(wants), however many are dirty. -/
theorem pickM_cost (d : Std.HashSet W) : ∀ (cap : Nat) (ws : List W),
    cost (pickM (m := Counted) d cap ws) ≤ { work := ws.length }
  | 0, ws => by simp [pickM]; meter_le
  | k + 1, [] => by simp [pickM]; meter_le
  | k + 1, w :: ws => by
    simp only [pickM]
    have h1 := pickM_cost d k ws
    have h2 := pickM_cost d (k + 1) ws
    split
    · simp only [cost_bind, cost_tick, cost_map, bind_pure_comp]
      rw [Meter.le_iff] at h1 ⊢
      simp only [Meter.work_add, Meter.reads_add, Meter.lists_add, Meter.writes_add, Meter.hashes_add,
        Meter.hashed_add, Meter.spawns_add, Meter.copied_add, Meter.seeks_add, Meter.rows_add,
        List.length_cons] at *
      omega
    · simp only [cost_bind, cost_tick]
      rw [Meter.le_iff] at h2 ⊢
      simp only [Meter.work_add, Meter.reads_add, Meter.lists_add, Meter.writes_add, Meter.hashes_add,
        Meter.hashed_add, Meter.spawns_add, Meter.copied_add, Meter.seeks_add, Meter.rows_add,
        List.length_cons] at *
      omega

/-- The mutant: the marked set as a list, each lookup a pass over it. -/
def pickListM {m : Type → Type} [Monad m] [Engine.Tick m] (dirty : List W) : Nat → List W → m (List W)
  | 0, _ => pure []
  | _, [] => pure []
  | k + 1, w :: ws => do
    Engine.tick { work := dirty.length }
    if dirty.contains w then return w :: (← pickListM dirty k ws) else pickListM dirty (k + 1) ws

end

namespace RWorld
variable {σ C W V Q : Type} [BEq W] [Hashable W] [LawfulBEq W] [BEq V] [LawfulBEq V] [BEq Q] [LawfulBEq Q]
  (apply : C → σ → σ) (hits : C → Q → Bool) (eval : σ → W → V) (reads : σ → W → List Q)

def commit (c : C) (w : RWorld σ C W V Q) : RWorld σ C W V Q :=
  { w with store := apply c w.store, journal := w.journal ++ [c], commits := w.commits + 1 }

/-- The cache after the journal's notices. -/
def noticed (w : RWorld σ C W V Q) : Q → Bool := fun q => w.staleQ q || w.journal.any (hits · q)

/-- Each want's reads, the unwanted forgotten. -/
def kept (w : RWorld σ C W V Q) : W → Option (List Q) := fun x => if w.wants.contains x then w.deps x else none

/-- What a pass marks. -/
def marked (w : RWorld σ C W V Q) : Std.HashSet W :=
  mark w.wants (staleW (w.noticed hits) w.kept) (w.dirty.filter (w.wants.contains ·))

/-- One read: x's value in s on the board, its reads recorded, fresh. -/
def read1 (s : σ) (st : Board W V × (Q → Bool) × (W → Option (List Q))) (x : W) :
    Board W V × (Q → Bool) × (W → Option (List Q)) :=
  (st.1.put x (eval s x), fun q => st.2.1 q && !(reads s x).contains q,
    fun y => if y == x then some (reads s x) else st.2.2 y)

/-- **A pass** (Reader.pass): take the journal's notices, forget the
unwanted, mark, read the first `cap` marked in the frame's order. -/
def passWith (M : Std.HashSet W) (cap : Nat) (w : RWorld σ C W V Q) : RWorld σ C W V Q :=
  let p := pick w.wants M cap
  let r := p.foldl (read1 eval reads w.store) (w.board.keep (w.wants.contains ·), w.noticed hits, w.kept)
  { w with journal := [], board := r.1, staleQ := r.2.1, deps := r.2.2, seen := w.commits,
           dirty := p.foldl (·.erase ·) M,
           rev := fun q => w.rev q ++ p.filter fun x => (reads w.store x).contains q }

def pass (cap : Nat) (w : RWorld σ C W V Q) : RWorld σ C W V Q := w.passWith hits eval reads (w.marked hits) cap

def frame (w : RWorld σ C W V Q) : RWorld σ C W V Q :=
  { w with board := w.board.take.2, shown := Board.apply w.shown w.board }

def want (ws : List W) (w : RWorld σ C W V Q) : RWorld σ C W V Q := { w with wants := ws }

/-- The cache forgets the reads `held` does not keep (Reader.pass, every
256th): forgotten reads count as stale, so the wants reading them are
read again. -/
def evict (held : Q → Bool) (w : RWorld σ C W V Q) : RWorld σ C W V Q :=
  { w with staleQ := fun q => w.staleQ q || !held q }

/-- Commit c, as made on s, leaves every want none of whose reads it
hits: its value and its reads (view_stable). -/
def StableAt (c : C) (s : σ) : Prop :=
  ∀ x, (∀ q ∈ reads s x, hits c q = false) → eval (apply c s) x = eval s x ∧ reads (apply c s) x = reads s x

/-- Each value held is dirty, has a read a commit not taken hits, has a
stale read or none, or is the store's with its reads; a want is held
exactly when its reads are; and the frame has seen each or it is moved. -/
def Inv (w : RWorld σ C W V Q) : Prop :=
  (∀ (x : W) (v : V) (n : Ver), w.board.vals[x]? = some (v, n) →
    x ∈ w.dirty ∨ (∃ c ∈ w.journal, ∃ qs, w.deps x = some qs ∧ ∃ q ∈ qs, hits c q = true) ∨
      staleW w.staleQ w.deps x = true ∨ (v = eval w.store x ∧ w.deps x = some (reads w.store x))) ∧
  (∀ x, (w.board.vals[x]?).isSome = (w.deps x).isSome) ∧
  Board.Seen w.shown w.board

theorem inv_start (s : σ) (ws : List W) : Inv hits eval reads ({ store := s, wants := ws } : RWorld σ C W V Q) := by
  refine ⟨fun x v n h => by simp at h, fun x => by simp, fun x v n h => by simp at h⟩

theorem inv_commit {w : RWorld σ C W V Q} (h : Inv hits eval reads w) (c : C)
    (hs : StableAt apply hits eval reads c w.store) : Inv hits eval reads (w.commit apply c) := by
  obtain ⟨hj, hh, hseen⟩ := h
  refine ⟨fun x v n hx => ?_, hh, hseen⟩
  rcases hj x v n hx with d | ⟨c', hc', qs, hd, q, hq, t⟩ | st | ⟨e, hd⟩
  · exact Or.inl d
  · exact Or.inr (Or.inl ⟨c', by simp [commit, hc'], qs, hd, q, hq, t⟩)
  · exact Or.inr (Or.inr (Or.inl st))
  · by_cases hit : ∃ q ∈ reads w.store x, hits c q = true
    · obtain ⟨q, hq, t⟩ := hit
      exact Or.inr (Or.inl ⟨c, by simp [commit], _, hd, q, hq, t⟩)
    · have none : ∀ q ∈ reads w.store x, hits c q = false := fun q hq => by
        cases ht : hits c q
        · rfl
        · exact absurd ⟨q, hq, ht⟩ hit
      obtain ⟨he, hr⟩ := hs x none
      exact Or.inr (Or.inr (Or.inr ⟨by simp only [commit]; rw [he]; exact e,
        by simp only [commit]; rw [hr]; exact hd⟩))

theorem inv_frame {w : RWorld σ C W V Q} (h : Inv hits eval reads w) : Inv hits eval reads (w.frame) :=
  ⟨h.1, h.2.1, Board.seen_take h.2.2⟩

theorem inv_evict {w : RWorld σ C W V Q} (h : Inv hits eval reads w) (held : Q → Bool) :
    Inv hits eval reads (w.evict held) := by
  refine ⟨fun x v n hx => ?_, h.2.1, h.2.2⟩
  rcases h.1 x v n hx with d | hit | st | e
  · exact Or.inl d
  · exact Or.inr (Or.inl hit)
  · refine Or.inr (Or.inr (Or.inl ?_))
    revert st
    simp only [staleW, evict]
    split
    · simp
    · simp only [Bool.or_eq_true, List.any_eq_true]
      intro st
      rcases st with st | ⟨q, hq, t⟩
      · exact Or.inl st
      · exact Or.inr ⟨q, hq, by simp [t]⟩
  · exact Or.inr (Or.inr (Or.inr e))

theorem inv_want {w : RWorld σ C W V Q} (h : Inv hits eval reads w) (ws : List W) :
    Inv hits eval reads (w.want ws) := by
  refine ⟨fun x v n hx => ?_, h.2.1, h.2.2⟩
  exact h.1 x v n hx

/-- What the reads of p leave: each read want holds its value in s (or
one equal) with its reads, every other what it held; no read goes stale. -/
theorem foldl_read (s : σ) : ∀ (p : List W) (st : Board W V × (Q → Bool) × (W → Option (List Q))) (x : W),
    (x ∈ p → ∃ u n, (p.foldl (read1 eval reads s) st).1.vals[x]? = some (u, n) ∧ u = eval s x ∧
      (p.foldl (read1 eval reads s) st).2.2 x = some (reads s x)) ∧
    (x ∉ p → (p.foldl (read1 eval reads s) st).1.vals[x]? = st.1.vals[x]? ∧
      (p.foldl (read1 eval reads s) st).2.2 x = st.2.2 x) ∧
    (∀ q, (p.foldl (read1 eval reads s) st).2.1 q = true → st.2.1 q = true)
  | [], st, x => ⟨fun h => absurd h (List.not_mem_nil), fun _ => ⟨rfl, rfl⟩, fun _ h => h⟩
  | y :: rest, st, x => by
    obtain ⟨ih1, ih2, ih3⟩ := foldl_read s rest (read1 eval reads s st y) x
    simp only [List.foldl_cons, List.mem_cons]
    refine ⟨fun h => ?_, fun h => ?_, fun q hq => ?_⟩
    · by_cases hr : x ∈ rest
      · exact ih1 hr
      · obtain ⟨a, b⟩ := ih2 hr
        rw [a, b]
        have hy : y = x := by rcases h with h | h; exact h.symm; exact absurd h hr
        subst hy
        obtain ⟨u, n, hu, e⟩ := Board.put_self st.1 y (eval s y)
        refine ⟨u, n, hu, ?_, by simp [read1]⟩
        rcases e with e | e
        · exact e
        · exact beq_iff_eq.1 e
    · have hy : y ≠ x := fun e => h (Or.inl e.symm)
      obtain ⟨a, b⟩ := ih2 (fun m => h (Or.inr m))
      refine ⟨by rw [a]; exact Board.put_other _ _ hy, by rw [b]; simp [read1, Ne.symm hy]⟩
    · have := ih3 q hq
      simp only [read1, Bool.and_eq_true] at this
      exact this.1

theorem seen_reads {shown : W → Option V} (s : σ) : ∀ (p : List W) (st : Board W V × (Q → Bool) × (W → Option (List Q))),
    Board.Seen shown st.1 → Board.Seen shown (p.foldl (read1 eval reads s) st).1
  | [], _, h => h
  | y :: rest, st, h => seen_reads s rest _ (Board.seen_put h y (eval s y))

theorem kept_vals {w : RWorld σ C W V Q} (x : W) :
    (w.board.keep (w.wants.contains ·)).vals[x]? = if w.wants.contains x then w.board.vals[x]? else none :=
  Board.keep_vals _ _ _

theorem kept_of {w : RWorld σ C W V Q} {x : W} (hw : w.wants.contains x = true) : w.kept x = w.deps x := by
  show (if w.wants.contains x then w.deps x else none) = w.deps x
  rw [ite_eq_left hw]

/-! ### A pass, field by field -/

section
variable {w : RWorld σ C W V Q} {cap : Nat} {M : Std.HashSet W}

theorem pass_picked {x : W} (hx : x ∈ pick w.wants M cap) :
    ∃ u n, (w.passWith hits eval reads M cap).board.vals[x]? = some (u, n) ∧ u = eval w.store x ∧
      (w.passWith hits eval reads M cap).deps x = some (reads w.store x) :=
  (foldl_read eval reads w.store _ _ x).1 hx

theorem pass_other {x : W} (hx : x ∉ pick w.wants M cap) :
    (w.passWith hits eval reads M cap).board.vals[x]? = (if w.wants.contains x then w.board.vals[x]? else none) ∧
      (w.passWith hits eval reads M cap).deps x = w.kept x := by
  obtain ⟨a, b⟩ := (foldl_read eval reads w.store _ (w.board.keep (w.wants.contains ·), w.noticed hits, w.kept) x).2.1 hx
  exact ⟨a.trans (kept_vals x), b⟩

theorem pass_dirty : (w.passWith hits eval reads M cap).dirty =
    (pick w.wants M cap).foldl (·.erase ·) M := rfl

theorem pass_store : (w.passWith hits eval reads M cap).store = w.store := rfl

theorem marked_of {x : W} (hw : w.wants.contains x = true)
    (m : x ∈ w.dirty ∨ staleW (w.noticed hits) w.kept x = true) : x ∈ w.marked hits := by
  rw [marked, mem_mark, mem_filter']
  rcases m with m | m
  · exact Or.inl ⟨m, hw⟩
  · exact Or.inr ⟨List.contains_iff_mem.1 hw, m⟩

/-- A held want with a read a commit not taken hits, or a stale read or
none, is stale after the notices. -/
theorem stale_of {x : W} (hw : w.wants.contains x = true)
    (h : (∃ c ∈ w.journal, ∃ qs, w.deps x = some qs ∧ ∃ q ∈ qs, hits c q = true) ∨
      staleW w.staleQ w.deps x = true) : staleW (w.noticed hits) w.kept x = true := by
  rw [show staleW (w.noticed hits) w.kept x = staleW (w.noticed hits) w.deps x by
    simp only [staleW, kept_of hw]]
  rcases h with ⟨c, hc, qs, hd, q, hq, t⟩ | st
  · simp only [staleW, hd, Bool.or_eq_true, List.any_eq_true]
    exact Or.inr ⟨q, hq, by simp only [noticed, Bool.or_eq_true, List.any_eq_true]; exact Or.inr ⟨c, hc, t⟩⟩
  · revert st
    unfold staleW
    split
    · intro _; rfl
    · simp only [Bool.or_eq_true, List.any_eq_true]
      intro st
      rcases st with st | ⟨q, hq, t⟩
      · exact Or.inl st
      · exact Or.inr ⟨q, hq, by simp [noticed, t]⟩

end

/-- **Every step keeps the invariant: a pass.** -/
theorem inv_passWith {w : RWorld σ C W V Q} (h : Inv hits eval reads w) (cap : Nat) {M : Std.HashSet W}
    (hM : ∀ x, x ∈ w.marked hits → x ∈ M) : Inv hits eval reads (w.passWith hits eval reads M cap) := by
  obtain ⟨hj, hh, hseen⟩ := h
  refine ⟨fun x v n hx => ?_, fun x => ?_, seen_reads eval reads _ _ _ (Board.seen_keep hseen _)⟩
  · by_cases hp : x ∈ pick w.wants M cap
    · obtain ⟨u, k, hu, e, hd⟩ := pass_picked hits eval reads hp
      rw [hu] at hx
      cases hx
      exact Or.inr (Or.inr (Or.inr ⟨e, hd⟩))
    · obtain ⟨a, b⟩ := pass_other hits eval reads hp
      rw [a] at hx
      split at hx
      · rename_i hw
        have toDirty : x ∈ w.marked hits → x ∈ (w.passWith hits eval reads M cap).dirty := fun m => by
          rw [pass_dirty, mem_eraseAll]
          exact ⟨hM x m, hp⟩
        rcases hj x v n hx with d | hit | st | ⟨e, hd⟩
        · exact Or.inl (toDirty (marked_of hits hw (Or.inl d)))
        · exact Or.inl (toDirty (marked_of hits hw (Or.inr (stale_of hits hw (Or.inl hit)))))
        · exact Or.inl (toDirty (marked_of hits hw (Or.inr (stale_of hits hw (Or.inr st)))))
        · refine Or.inr (Or.inr (Or.inr ⟨e, ?_⟩))
          rw [b, kept_of hw]; exact hd
      · cases hx
  · by_cases hp : x ∈ pick w.wants M cap
    · obtain ⟨u, k, hu, _, hd⟩ := pass_picked hits eval reads hp
      rw [hu, hd]; rfl
    · obtain ⟨a, b⟩ := pass_other hits eval reads hp
      rw [a, b]
      show _ = (if w.wants.contains x then w.deps x else none).isSome
      split
      · exact hh x
      · rfl

theorem inv_pass {w : RWorld σ C W V Q} (h : Inv hits eval reads w) (cap : Nat) :
    Inv hits eval reads (w.pass hits eval reads cap) := inv_passWith hits eval reads h cap fun _ m => m

/-- **No missed update, as the reader runs**: a pass that reads every
want it marks (or any set holding them), then one frame, shows every
want's value in the store. -/
theorem settleWith {w : RWorld σ C W V Q} (h : Inv hits eval reads w) {cap : Nat} {M : Std.HashSet W}
    (hM : ∀ x, x ∈ w.marked hits → x ∈ M)
    (hcap : (w.wants.filter (M.contains ·)).length ≤ cap) {x : W} (hx : x ∈ w.wants) :
    ((w.passWith hits eval reads M cap).frame).shown x = some (eval w.store x) := by
  obtain ⟨hj, hh, hseen⟩ := h
  have hw : w.wants.contains x = true := List.contains_iff_mem.2 hx
  have hpick : pick w.wants M cap = w.wants.filter (M.contains ·) := by
    rw [pick_eq]; exact List.take_of_length_le hcap
  have held : ∃ n, (w.passWith hits eval reads M cap).board.vals[x]? = some (eval w.store x, n) := by
    by_cases hp : x ∈ pick w.wants M cap
    · obtain ⟨u, k, hu, e, _⟩ := pass_picked hits eval reads hp
      exact ⟨k, by rw [hu, e]⟩
    · obtain ⟨a, _⟩ := pass_other hits eval reads hp
      rw [a, ite_eq_left hw]
      have notMarked : x ∉ w.marked hits := fun m => hp (by
        rw [hpick]; exact List.mem_filter.2 ⟨hx, Std.HashSet.contains_iff_mem.2 (hM x m)⟩)
      cases hv : w.board.vals[x]? with
      | none =>
        exfalso
        have hd : w.deps x = none := by
          have := hh x; rw [hv] at this
          cases hd : w.deps x
          · rfl
          · rw [hd] at this; cases this
        apply notMarked
        refine marked_of hits hw (Or.inr ?_)
        simp only [staleW, kept_of hw, hd]
      | some p =>
        obtain ⟨v, n⟩ := p
        refine ⟨n, ?_⟩
        rcases hj x v n hv with d | hit | st | ⟨e, _⟩
        · exact absurd (marked_of hits hw (Or.inl d)) notMarked
        · exact absurd (marked_of hits hw (Or.inr (stale_of hits hw (Or.inl hit)))) notMarked
        · exact absurd (marked_of hits hw (Or.inr (stale_of hits hw (Or.inr st)))) notMarked
        · rw [e]
  obtain ⟨n, hn⟩ := held
  have hs := (inv_frame hits eval reads (inv_passWith hits eval reads ⟨hj, hh, hseen⟩ cap hM)).2.2 x (eval w.store x) n
  simp only [frame, Board.take] at hs
  rcases hs hn with m | s
  · simp at m
  · exact s

theorem settle {w : RWorld σ C W V Q} (h : Inv hits eval reads w) {cap : Nat}
    (hcap : (w.wants.filter ((w.marked hits).contains ·)).length ≤ cap) {x : W} (hx : x ∈ w.wants) :
    ((w.pass hits eval reads cap).frame).shown x = some (eval w.store x) :=
  settleWith hits eval reads h (fun _ m => m) hcap hx

/-! ## The mutant: checking staleness while reading -/

/-- The pass as first written: each want, in order, read if its reads
look stale now, after the reads before it in the same pass. -/
def passEager (w : RWorld σ C W V Q) : RWorld σ C W V Q :=
  let r := w.wants.foldl (fun st x => if staleW st.2.1 st.2.2 x then read1 eval reads w.store st x else st)
    (w.board.keep (w.wants.contains ·), w.noticed hits, w.kept)
  { w with journal := [], board := r.1, staleQ := r.2.1, deps := r.2.2, dirty := {} }

end RWorld

namespace Eager

/-- Two wants (false, true) reading one list (()), their value the
store's number; every commit hits the list. -/
abbrev Rw := RWorld Nat Nat Bool Nat Unit

def apply (c : Nat) (_ : Nat) : Nat := c
def hits (_ : Nat) (_ : Unit) : Bool := true
def eval (s : Nat) (_ : Bool) : Nat := s
def reads (_ : Nat) (_ : Bool) : List Unit := [()]

/-- A put moves no other want. -/
theorem put_moved_other {W V : Type} [BEq W] [Hashable W] [LawfulBEq W] [BEq V] (b : Board W V) {w x : W}
    (v : V) (h : w ≠ x) : (b.put w v).moved.contains x = b.moved.contains x := by
  rcases Board.put_cases b w v with ⟨e, _⟩ | e
  · rw [e]
  · rw [e, Board.bump_moved]; simp [h]

/-- Both wants read (0, at versions 1 and 2) and shown, both reading the
one list; then a commit (1) that hits it, not yet taken. (A state the
invariant holds of: `w1_inv`.) -/
def b1 : Board Bool Nat := ((({} : Board Bool Nat).put false 0).put true 0).take.2

def w1 : Rw :=
  { store := 1, journal := [1], board := b1, staleQ := fun _ => false, deps := fun _ => some [()],
    wants := [false, true], shown := fun _ => some 0 }

theorem b1_vals (x : Bool) : ∃ n, b1.vals[x]? = some (0, n) := by
  have e0 : (({} : Board Bool Nat).put false 0).vals[false]? = some (0, 1) :=
    (Board.put_moves (fun u n h => by simp at h)).1
  have n0 : (({} : Board Bool Nat).put false 0).vals[true]? = none := by
    rw [Board.put_other _ _ (by decide)]; simp
  cases x
  · exact ⟨1, by
      show ((({} : Board Bool Nat).put false 0).put true 0).vals[false]? = _
      rw [Board.put_other _ _ (by decide), e0]⟩
  · exact ⟨_, (Board.put_moves (fun u n h => by rw [n0] at h; cases h)).1⟩

theorem b1_moved (x : Bool) : b1.moved.contains x = false := by simp [b1, Board.take]

theorem w1_inv : RWorld.Inv hits eval reads w1 := by
  refine ⟨fun x v n hx => ?_, fun x => ?_, fun x v n hx => ?_⟩
  · exact Or.inr (Or.inl ⟨1, by simp [w1], [()], rfl, (), by simp, rfl⟩)
  · obtain ⟨n, h⟩ := b1_vals x
    show (b1.vals[x]?).isSome = (some [()]).isSome
    rw [h]; rfl
  · right
    obtain ⟨n', h⟩ := b1_vals x
    show some 0 = some v
    have : b1.vals[x]? = some (v, n) := hx
    rw [h] at this; cases this; rfl

/-- k eager passes, each with a frame. -/
def eager : Nat → Rw → Rw
  | 0, w => w
  | k + 1, w => eager k ((w.passEager hits eval reads).frame)

/-- Where the eager pass is stuck: nothing to take, the shared read
clean, both wants' reads recorded, the second want's value and what the
frame shows the old one, and it is not moved. -/
def Stuck (w : Rw) : Prop :=
  w.journal = [] ∧ w.staleQ () = false ∧ w.deps false = some [()] ∧ w.deps true = some [()] ∧
    w.wants = [false, true] ∧ (∀ v n, w.board.vals[true]? = some (v, n) → v = 0) ∧
    w.shown true = some 0 ∧ w.board.moved.contains true = false ∧ w.store = 1

theorem stuck_step {w : Rw} (h : Stuck w) : Stuck ((w.passEager hits eval reads).frame) := by
  obtain ⟨hj, hq, hd0, hd1, hw, hv, hs, hm, hst⟩ := h
  have sq : RWorld.noticed hits w = fun _ => false := by
    funext q; cases q; simp [RWorld.noticed, hj, hq]
  have kd : RWorld.kept w = w.deps := by
    funext x; cases x <;> simp [RWorld.kept, hw]
  have fold : w.wants.foldl (fun st x => if staleW st.2.1 st.2.2 x then RWorld.read1 eval reads w.store st x else st)
      (w.board.keep (w.wants.contains ·), RWorld.noticed hits w, RWorld.kept w) =
      (w.board.keep (w.wants.contains ·), fun _ => false, w.deps) := by
    rw [sq, kd, hw]; simp [staleW, hd0, hd1]
  have e : (w.passEager hits eval reads).board = w.board.keep (w.wants.contains ·) ∧
      (w.passEager hits eval reads).staleQ = (fun _ => false) ∧
      (w.passEager hits eval reads).deps = w.deps := by
    simp only [RWorld.passEager]; rw [fold]; exact ⟨rfl, rfl, rfl⟩
  obtain ⟨eb, es, ed⟩ := e
  refine ⟨rfl, ?_, ?_, ?_, hw, ?_, ?_, ?_, hst⟩
  · show (w.passEager hits eval reads).staleQ () = false
    rw [es]
  · show (w.passEager hits eval reads).deps false = _
    rw [ed, hd0]
  · show (w.passEager hits eval reads).deps true = _
    rw [ed, hd1]
  · intro v n hx
    have hx' : (w.passEager hits eval reads).board.vals[true]? = some (v, n) := hx
    rw [eb, Board.keep_vals, hw] at hx'
    simp at hx'
    exact hv v n hx'
  · show Board.apply w.shown (w.passEager hits eval reads).board true = some 0
    rw [eb]
    simp only [Board.apply, Board.keep, hm, Bool.false_eq_true, ite_false]; exact hs
  · simp [RWorld.frame, Board.take]

/-- The first eager pass from w1 reads the first want, which refreshes
the shared list, and leaves the second at 0. -/
theorem w2_stuck : Stuck ((w1.passEager hits eval reads).frame) := by
  have sq : RWorld.noticed hits w1 = fun _ => true := by funext q; simp [RWorld.noticed, w1, hits]
  have kd : RWorld.kept w1 = fun _ => some [()] := by funext x; cases x <;> rfl
  have fold : w1.wants.foldl (fun st x => if staleW st.2.1 st.2.2 x then RWorld.read1 eval reads w1.store st x else st)
      (w1.board.keep (w1.wants.contains ·), RWorld.noticed hits w1, RWorld.kept w1) =
      RWorld.read1 eval reads w1.store (w1.board.keep (w1.wants.contains ·), fun _ => true, fun _ => some [()]) false := by
    rw [sq, kd]
    show List.foldl _ _ [false, true] = _
    simp [staleW, RWorld.read1, reads]
  have eb : (w1.passEager hits eval reads).board = (w1.board.keep (w1.wants.contains ·)).put false 1 := by
    simp only [RWorld.passEager]; rw [fold]; rfl
  have es : (w1.passEager hits eval reads).staleQ () = false := by
    simp only [RWorld.passEager]; rw [fold]; simp [RWorld.read1, reads]
  have ed : (w1.passEager hits eval reads).deps = fun y => if y == false then some [()] else some [()] := by
    simp only [RWorld.passEager]; rw [fold]; rfl
  refine ⟨rfl, es, ?_, ?_, rfl, ?_, ?_, ?_, rfl⟩
  · show (w1.passEager hits eval reads).deps false = _; rw [ed]; rfl
  · show (w1.passEager hits eval reads).deps true = _; rw [ed]; rfl
  · intro v n hx
    have hx' : (w1.passEager hits eval reads).board.vals[true]? = some (v, n) := hx
    rw [eb, Board.put_other _ _ (by decide), Board.keep_vals] at hx'
    have : w1.wants.contains true = true := rfl
    rw [ite_eq_left this] at hx'
    obtain ⟨m, hm⟩ := b1_vals true
    have : b1.vals[true]? = some (v, n) := hx'
    rw [hm] at this; cases this; rfl
  · show Board.apply w1.shown (w1.passEager hits eval reads).board true = some 0
    rw [eb]
    have hm : ((w1.board.keep (w1.wants.contains ·)).put false 1).moved.contains true = false := by
      rw [put_moved_other _ _ (by decide)]
      exact b1_moved true
    simp only [Board.apply, hm, Bool.false_eq_true, ite_false]
    rfl
  · simp [RWorld.frame, Board.take]

theorem eager_stuck : ∀ k, Stuck (eager k ((w1.passEager hits eval reads).frame))
  | 0 => w2_stuck
  | k + 1 => by
    show Stuck (eager k (((w1.passEager hits eval reads).frame.passEager hits eval reads).frame))
    exact (eager_stuck_from _ (stuck_step w2_stuck)) k
where
  eager_stuck_from : ∀ (w : Rw), Stuck w → ∀ k, Stuck (eager k w)
    | _, h, 0 => h
    | _, h, k + 1 => eager_stuck_from _ (stuck_step h) k

/-- **Checking staleness while reading shows a stale value for ever**:
after the commit, every eager pass and frame shows the second want at 0
while the store holds 1. -/
theorem eager_stale (k : Nat) :
    (eager k ((w1.passEager hits eval reads).frame)).shown true = some 0 ∧
      eval (eager k ((w1.passEager hits eval reads).frame)).store true = 1 := by
  obtain ⟨_, _, _, _, _, _, hs, _, hst⟩ := eager_stuck k
  exact ⟨hs, by simp [eval, hst]⟩

theorem stable : ∀ c s, RWorld.StableAt apply hits eval reads c s := fun c s x h => by
  simp [reads, hits] at h

/-- **Marking first shows the new value** one pass and one frame after
the same commit (`settle`). -/
theorem marked_fresh : ((w1.pass hits eval reads 2).frame).shown true = some 1 := by
  have := RWorld.settle hits eval reads w1_inv (cap := 2) (x := true) (by
      refine Nat.le_trans (List.length_filter_le _ _) ?_
      simp [w1]) (by simp [w1])
  simpa [w1, eval] using this

end Eager

end Live
