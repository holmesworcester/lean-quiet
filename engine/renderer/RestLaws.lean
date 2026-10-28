/-
The reader at rest (docs/PERF.md: battery and CPU when nothing changes).

Reader.pass marked by checking every want's reads every pass
(`staleW` over each want's recorded reads: O(wants × reads) at rest),
and a row with no reads recorded was read again every pass. Here the
reader keeps two things more:

- **the dirty set holds every wanted want whose reads went stale, or
  that holds none** (`IdxOk`, first half): a want the frame starts
  wanting is marked when it does (`wantIdx`);
- **a reverse index**, each read to the wants that recorded it (`rev`,
  complete: `IdxOk`, second half), kept as each read is recorded.

Then a pass marks the dirty set and the wants its notices hit, through
the index (`markHit`, `markIdx`): a step per key noticed and per want
it names (`markHitM_cost`), nothing per want held. A pass with no
notice and nothing dirty does nothing at all (`passIdx`, `rest_idle`).

- `marked_sub_idx`: under `IdxOk`, every want the old pass marked, this
  one marks too; so `inv_passWith` and `settleWith` carry the reader's
  laws over (`inv_passIdx`, `settle_idx`), and the refinement with them.
- `idxok_commit`, `idxok_frame`, `idxok_want`, `idxok_passIdx`: every step
  keeps `IdxOk`, given that every want's view reads at least one list
  (`reads s x ≠ []`; holmes-1e's rows not shown yet must record the
  reads they made, not none) and that the reads a commit hits are the
  ones its keys name (`hitQs`, exact).
- The mutant: the scan (`scanM`) costs a step per want and per read it
  recorded, every pass, at rest too (`scanM_cost`).
- `passCostM_cost`: a pass costs a step per key noticed and per want it
  names, a step per want picked from, and, when the wants moved, the
  cache's keep over its entries (bounded by the window and its margin).
- **No journal poll**: the writers keep a commit counter, and a pass
  reads the journal only when it moved, a note came, the wants moved or
  a want is dirty, or once a second for commits no counter sees, the
  node's purges (`mustRead`, `startM`); the sessions list is read only
  in a pass that opened the store, at most every half second. `CountOk` (every commit not
  taken is journaled) is kept by every step, so an unmoved counter means
  an empty journal (`counter_idle`), and at rest a pass's start costs
  nothing (`start_rest`); the poll queries every pass (`poll_queries`).
- `nextGen_same`: the frame re-setting the same wants leaves the
  generation, so the reader rests; the mutant moves it on every set
  (`always_moves`).
- `Want.count` reads one or two count lists, so it too reads a list: the
  premise of `idxok_passIdx`.

With window-subs' exact notices (engine/core/Window*.lean, `notify`),
the index is by window rather than by key, and the hit wants are those
whose windows changed: the same law, fewer marks.
-/
import engine.renderer.ReaderLaws

set_option linter.unusedSectionVars false

namespace Live

section
variable {W K : Type} [BEq W] [Hashable W] [LawfulBEq W]

theorem mem_foldl_insert : ∀ (l : List W) (d : Std.HashSet W) (x : W),
    x ∈ l.foldl (·.insert ·) d ↔ x ∈ d ∨ x ∈ l
  | [], d, x => by simp
  | y :: l, d, x => by
    simp only [List.foldl_cons, List.mem_cons]
    rw [mem_foldl_insert l, Std.HashSet.mem_insert, beq_iff_eq]
    constructor
    · rintro ((rfl | h) | h)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rintro (h | rfl | h)
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr h

theorem mem_markHitM (rev : K → List W) : ∀ (ks : List K) (d : Std.HashSet W) (x : W),
    x ∈ Id.run (markHitM rev d ks) ↔ x ∈ d ∨ ∃ k ∈ ks, x ∈ rev k
  | [], d, x => by simp [markHitM]
  | k :: ks, d, x => by
    show x ∈ Id.run (markHitM rev ((rev k).foldl (·.insert ·) d) ks) ↔ _
    rw [mem_markHitM rev ks, mem_foldl_insert]
    constructor
    · rintro ((h | h) | ⟨k', hk, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨k, List.mem_cons_self .., h⟩
      · exact Or.inr ⟨k', List.mem_cons_of_mem _ hk, h⟩
    · rintro (h | ⟨k', hk, h⟩)
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.1 hk with rfl | hk
        · exact Or.inl (Or.inr h)
        · exact Or.inr ⟨k', hk, h⟩

/-- **What a pass at rest marks**: the dirty, and the wants the index
names for the keys noticed. -/
theorem mem_markHit (rev : K → List W) (d : Std.HashSet W) (ks : List K) (x : W) :
    x ∈ markHit rev d ks ↔ x ∈ d ∨ ∃ k ∈ ks, x ∈ rev k := mem_markHitM rev ks d x

open Engine Engine.Counted in
/-- **Marking at rest costs a step per key noticed and per want it
names**; with no notice, nothing. -/
theorem markHitM_cost (rev : K → List W) : ∀ (ks : List K) (d : Std.HashSet W),
    cost (markHitM (m := Counted) rev d ks) = { work := (ks.map fun k => 1 + (rev k).length).sum }
  | [], d => by simp [markHitM]; rfl
  | k :: ks, d => by
    simp only [markHitM, cost_bind, cost_tick, markHitM_cost rev ks, List.map_cons, List.sum_cons]
    ext <;> simp

/-- The mutant: each want's reads checked, every pass. -/
def scanM {Q : Type} {m : Type → Type} [Monad m] [Engine.Tick m] (deps : W → Option (List Q))
    (stale : W → Bool) : Std.HashSet W → List W → m (Std.HashSet W)
  | d, [] => pure d
  | d, x :: xs => do
    Engine.tick { work := 1 + ((deps x).getD []).length }
    scanM deps stale (if stale x then d.insert x else d) xs

open Engine Engine.Counted in
/-- **The scan costs a step per want and per read recorded, every pass**,
at rest too. -/
theorem scanM_cost {Q : Type} (deps : W → Option (List Q)) (stale : W → Bool) : ∀ (ws : List W) (d : Std.HashSet W),
    cost (scanM (m := Counted) deps stale d ws) = { work := (ws.map fun x => 1 + ((deps x).getD []).length).sum }
  | [], d => by simp [scanM]; rfl
  | x :: xs, d => by
    simp only [scanM, cost_bind, cost_tick, scanM_cost deps stale xs, List.map_cons, List.sum_cons]
    ext <;> simp

end

section
variable {W K : Type} [BEq W] [Hashable W] [LawfulBEq W] {m : Type → Type} [Monad m] [Engine.Tick m]

/-- **A pass's start**: the writers' counter (a load, no query) says
whether anything was committed since the last pass; only if it was, or
a note came, or the wants moved, or a want is dirty, does the pass read
the journal (one query). -/
def startM (c seen : Nat) (notes moved : Bool) (dirty : Std.HashSet W) (late : Bool) (journal : m (List K)) :
    m (Option (List K)) :=
  if !mustRead c seen notes moved dirty late then pure none
  else do Engine.tick { lists := 1 }; some <$> journal

/-- The mutant: the journal polled every pass. -/
def startPollM (journal : m (List K)) : m (Option (List K)) := do
  Engine.tick { lists := 1 }; some <$> journal

/-- **A pass's decisions, counted**: when the wants moved, the cache's
keep over its entries (`cached`, at most the window and its margin);
then the mark (a step per key noticed and per want it names) and the
pick (a step per want looked at). -/
def passCostM {Q : Type} (rev : Q → List W) (dirty : Std.HashSet W) (keys : List Q) (wants : List W)
    (cap : Nat) (moved : Bool) (cached : Nat) : m (List W) := do
  if moved then Engine.tick { work := cached }
  let marked ← markHitM rev dirty keys
  pickM marked cap wants

end

/-- The frame re-setting the same wants does not move the generation. -/
theorem nextGen_same {W : Type} [BEq W] [LawfulBEq W] (ws : Array W) (g : Nat) : nextGen ws ws g = g := by
  simp [nextGen]

theorem nextGen_moves {W : Type} [BEq W] [LawfulBEq W] {old new : Array W} (h : old ≠ new) (g : Nat) :
    nextGen old new g = g + 1 := by
  simp [nextGen, h]

/-- The mutant: a generation moved on every set; re-setting the same
wants moves it, and the reader never rests. -/
def nextGenAlways {W : Type} (_ _ : Array W) (g : Nat) : Nat := g + 1

theorem always_moves {W : Type} (ws : Array W) (g : Nat) : nextGenAlways ws ws g ≠ g := by
  simp [nextGenAlways]

section
variable {W K : Type} [BEq W] [Hashable W] [LawfulBEq W]
open Engine Engine.Counted

/-- **At rest, a pass reads nothing**: no commit since the last pass, no
note, the same wants and nothing dirty, and within a second of the last
time the store was opened, its start costs nothing, not a query. So at
rest the store (the journal, and the sessions read with it) is opened
at most once a second, however often the reader passes. -/
theorem start_rest (c readAt now : Nat) (hn : now < readAt + 1000) (dirty : Std.HashSet W)
    (hd : dirty.isEmpty = true) (journal : Counted (List K)) :
    cost (startM (m := Counted) c c false false dirty (Decidable.decide (now ≥ readAt + 1000)) journal) = 0 := by
  have : ¬ now ≥ readAt + 1000 := by omega
  simp [startM, mustRead, hd, this]

/-- **The poll reads the journal every pass**, at rest too. -/
theorem poll_queries (journal : Counted (List K)) :
    1 ≤ (cost (startPollM (m := Counted) journal)).lists := by
  simp [startPollM]

/-- **A pass costs O(keys noticed + wants named + wants + [wants moved] ·
cached entries).** -/
theorem passCostM_cost {Q : Type} (rev : Q → List W) (dirty : Std.HashSet W) (keys : List Q) (wants : List W)
    (cap : Nat) (moved : Bool) (cached : Nat) :
    (cost (passCostM (m := Counted) rev dirty keys wants cap moved cached)).work ≤
      (keys.map fun k => 1 + (rev k).length).sum + wants.length + (if moved then cached else 0) := by
  have hm := markHitM_cost rev keys dirty
  have hp := pickM_cost (val (markHitM (m := Counted) rev dirty keys)) cap wants
  rw [Meter.le_iff] at hp
  unfold passCostM
  cases moved <;> simp only [cost_bind, cost_tick, Meter.work_add, hm, Bool.false_eq_true, ite_true, ite_false,
    cost_pure, Meter.work_zero] <;> simp at hp ⊢ <;> omega

end

namespace RWorld
variable {σ C W V Q : Type} [BEq W] [Hashable W] [LawfulBEq W] [BEq V] [LawfulBEq V] [BEq Q] [LawfulBEq Q]
  (apply : C → σ → σ) (hits : C → Q → Bool) (eval : σ → W → V) (reads : σ → W → List Q)
  (hitQs : C → List Q)

/-- What an indexed pass marks: the dirty, and the wants the index
names for the reads the journal's commits hit; only those wanted. -/
def markIdx (w : RWorld σ C W V Q) : Std.HashSet W :=
  (markHit w.rev w.dirty (w.journal.flatMap hitQs)).filter (w.wants.contains ·)

/-- **The reader at rest**: with no notice and nothing dirty it does
nothing; else a pass over what it marks. -/
def passIdx (cap : Nat) (w : RWorld σ C W V Q) : RWorld σ C W V Q :=
  if idle (w.journal.flatMap hitQs) w.dirty then { w with journal := [], seen := w.commits }
  else w.passWith hits eval reads (w.markIdx hitQs) cap

/-- The frame changes what it wants: a want it starts wanting is marked
now; one it stops wanting leaves the dirty set. -/
def wantIdx (ws : List W) (w : RWorld σ C W V Q) : RWorld σ C W V Q :=
  { w with wants := ws,
           dirty := (ws.filter fun x => !w.wants.contains x).foldl (·.insert ·) (w.dirty.filter (ws.contains ·)) }

/-- Every wanted want whose reads went stale, or that holds none, is
dirty; the index names, for each read, every want that recorded it. -/
def IdxOk (w : RWorld σ C W V Q) : Prop :=
  (∀ x ∈ w.wants, staleW w.staleQ w.deps x = true → x ∈ w.dirty) ∧
  (∀ x qs q, w.deps x = some qs → q ∈ qs → x ∈ w.rev q)

/-- The reads a commit hits are the ones its keys name. -/
def Exact : Prop := ∀ c q, hits c q = true ↔ q ∈ hitQs c

theorem idxok_start (s : σ) : IdxOk ({ store := s } : RWorld σ C W V Q) :=
  ⟨fun x hx => by simp at hx, fun x qs q h => by simp at h⟩

/-- **Every want the old pass marks, the pass at rest marks too.** -/
theorem marked_sub_idx (hex : Exact hits hitQs) {w : RWorld σ C W V Q} (ok : IdxOk w) :
    ∀ x, x ∈ w.marked hits → x ∈ w.markIdx hitQs := by
  intro x hx
  rw [markIdx, mem_filter', mem_markHit]
  rw [marked, mem_mark, mem_filter'] at hx
  rcases hx with ⟨hd, hwd⟩ | ⟨hw, hs⟩
  · exact ⟨Or.inl hd, hwd⟩
  · have hwc : w.wants.contains x = true := List.contains_iff_mem.2 hw
    refine ⟨?_, hwc⟩
    rw [show staleW (w.noticed hits) w.kept x = staleW (w.noticed hits) w.deps x by
      simp only [staleW, kept_of hwc]] at hs
    cases hd : w.deps x with
    | none => exact Or.inl (ok.1 x hw (by simp [staleW, hd]))
    | some qs =>
      rw [staleW, hd] at hs
      simp only [Bool.or_eq_true, List.any_eq_true] at hs
      rcases hs with he | ⟨q, hq, hn⟩
      · exact Or.inl (ok.1 x hw (by simp [staleW, hd, he]))
      · simp only [noticed, Bool.or_eq_true, List.any_eq_true] at hn
        rcases hn with st | ⟨c, hc, hit⟩
        · exact Or.inl (ok.1 x hw (by simp only [staleW, hd, Bool.or_eq_true, List.any_eq_true]; exact Or.inr ⟨q, hq, st⟩))
        · exact Or.inr ⟨q, List.mem_flatMap.2 ⟨c, hc, (hex c q).1 hit⟩, ok.2 x qs q hd hq⟩

/-- **At rest the reader does nothing**: no notice and nothing dirty, the
pass leaves the world as it was. -/
theorem rest_idle {w : RWorld σ C W V Q} (hj : w.journal = []) (hd : w.dirty.isEmpty = true)
    (hs : w.seen = w.commits) (cap : Nat) :
    w.passIdx hits eval reads hitQs cap = w := by
  unfold passIdx
  rw [if_pos (by simp [idle, hj, hd])]
  cases w; simp_all

/-- Every commit the reader has not taken is in the journal: the
counter is the commits taken plus those still journaled. -/
def CountOk (w : RWorld σ C W V Q) : Prop := w.seen + w.journal.length = w.commits

theorem countok_start (s : σ) : CountOk ({ store := s } : RWorld σ C W V Q) := rfl

theorem countok_commit {w : RWorld σ C W V Q} (h : CountOk w) (c : C) : CountOk (w.commit apply c) := by
  unfold CountOk at *; simp only [commit, List.length_append, List.length_singleton]; omega

theorem countok_passIdx {w : RWorld σ C W V Q} (h : CountOk w) (cap : Nat) :
    CountOk (w.passIdx hits eval reads hitQs cap) := by
  unfold CountOk passIdx
  split <;> simp [passWith]

theorem countok_frame {w : RWorld σ C W V Q} (h : CountOk w) : CountOk w.frame := h

/-- **The counter tells the journal is empty**: with no commit since the
last pass, there is nothing to take, so a pass need not read the journal
(`mustRead`); with nothing dirty and the same wants, it does nothing. -/
theorem counter_idle {w : RWorld σ C W V Q} (h : CountOk w) (hc : w.commits = w.seen) : w.journal = [] := by
  unfold CountOk at h
  exact List.eq_nil_of_length_eq_zero (by omega)

theorem inv_idle_drop (hex : Exact hits hitQs) {w : RWorld σ C W V Q} (h : Inv hits eval reads w)
    (hk : w.journal.flatMap hitQs = []) : Inv hits eval reads { w with journal := [] } := by
  refine ⟨fun x v n hx => ?_, h.2.1, h.2.2⟩
  rcases h.1 x v n hx with d | ⟨c, hc, qs, hd, q, hq, t⟩ | st | e
  · exact Or.inl d
  · exfalso
    have : q ∈ w.journal.flatMap hitQs := List.mem_flatMap.2 ⟨c, hc, (hex c q).1 t⟩
    rw [hk] at this; cases this
  · exact Or.inr (Or.inr (Or.inl st))
  · exact Or.inr (Or.inr (Or.inr e))

/-- **The reader's invariant holds of the pass at rest.** -/
theorem inv_passIdx (hex : Exact hits hitQs) {w : RWorld σ C W V Q} (h : Inv hits eval reads w)
    (ok : IdxOk w) (cap : Nat) : Inv hits eval reads (w.passIdx hits eval reads hitQs cap) := by
  unfold passIdx
  split
  · rename_i hi
    simp only [idle, Bool.and_eq_true, List.isEmpty_iff] at hi
    exact inv_idle_drop hits eval reads hitQs hex h hi.1
  · exact inv_passWith hits eval reads h cap (marked_sub_idx hits hitQs hex ok)

/-- **No missed update, at rest too**: a pass at rest that reads every
want it marks, then one frame, shows every wanted value in the store. -/
theorem settle_idx (hex : Exact hits hitQs) {w : RWorld σ C W V Q} (h : Inv hits eval reads w)
    (ok : IdxOk w) {cap : Nat} (hcap : (w.wants.filter ((w.markIdx hitQs).contains ·)).length ≤ cap)
    {x : W} (hx : x ∈ w.wants) :
    ((w.passIdx hits eval reads hitQs cap).frame).shown x = some (eval w.store x) := by
  have full := settleWith hits eval reads h (marked_sub_idx hits hitQs hex ok) hcap hx
  unfold passIdx
  split
  · rename_i hi
    simp only [idle, Bool.and_eq_true, List.isEmpty_iff] at hi
    -- nothing marked: the pass over the empty mark reads nothing, and
    -- shows what the board shows
    have hf : w.wants.filter ((w.markIdx hitQs).contains ·) = [] := by
      rw [List.filter_eq_nil_iff]
      intro y _ hy
      have hm : y ∈ w.markIdx hitQs := Std.HashSet.contains_iff_mem.1 (by simpa using hy)
      rw [markIdx, mem_filter', mem_markHit, hi.1] at hm
      rcases hm.1 with hm | ⟨_, hk, _⟩
      · rw [Std.HashSet.isEmpty_iff_forall_not_mem] at hi; exact hi.2 y hm
      · cases hk
    have hp : pick w.wants (w.markIdx hitQs) cap = [] := by rw [pick_eq, hf, List.take_nil]
    have hw : w.wants.contains x = true := List.contains_iff_mem.2 hx
    rw [← full]
    show Board.apply w.shown w.board x = Board.apply w.shown (w.passWith hits eval reads (w.markIdx hitQs) cap).board x
    have hb : (w.passWith hits eval reads (w.markIdx hitQs) cap).board = w.board.keep (w.wants.contains ·) := by
      show (List.foldl (read1 eval reads w.store) (w.board.keep (w.wants.contains ·), w.noticed hits, w.kept)
        (pick w.wants (w.markIdx hitQs) cap)).1 = _
      rw [hp]; rfl
    rw [hb]
    unfold Board.apply
    have hm : (w.board.keep (w.wants.contains ·)).moved = w.board.moved := rfl
    rw [hm, Board.keep_vals, ite_eq_left hw]
  · exact full

/-! ### Every step keeps the index right -/

theorem idxok_commit {w : RWorld σ C W V Q} (ok : IdxOk w) (c : C) : IdxOk (w.commit apply c) := ok

theorem idxok_frame {w : RWorld σ C W V Q} (ok : IdxOk w) : IdxOk w.frame := ok

theorem idxok_want {w : RWorld σ C W V Q} (ok : IdxOk w) (ws : List W) : IdxOk (w.wantIdx ws) := by
  refine ⟨fun x hx hs => ?_, ok.2⟩
  simp only [wantIdx] at hx hs ⊢
  rw [mem_foldl_insert, mem_filter']
  by_cases ho : x ∈ w.wants
  · exact Or.inl ⟨ok.1 x ho hs, List.contains_iff_mem.2 hx⟩
  · exact Or.inr (List.mem_filter.2 ⟨hx, by simpa [List.contains_iff_mem] using ho⟩)

/-- A read want's reads are clean after the pass, the others no staler
than the notices made them. -/
theorem foldl_read_clean (s : σ) : ∀ (p : List W) (st : Board W V × (Q → Bool) × (W → Option (List Q))) (x : W),
    x ∈ p → ∀ q ∈ reads s x, (p.foldl (read1 eval reads s) st).2.1 q = false
  | [], _, _, h => absurd h List.not_mem_nil
  | y :: rest, st, x, h => by
    intro q hq
    simp only [List.foldl_cons]
    by_cases hr : x ∈ rest
    · exact foldl_read_clean s rest _ x hr q hq
    · have hy : y = x := by
        rcases List.mem_cons.1 h with h | h
        · exact h.symm
        · exact absurd h hr
      subst hy
      cases hf : (rest.foldl (read1 eval reads s) (read1 eval reads s st y)).2.1 q
      · rfl
      · have := (foldl_read eval reads s rest (read1 eval reads s st y) y).2.2 q hf
        simp only [read1, Bool.and_eq_true, Bool.not_eq_true'] at this
        rw [List.contains_iff_mem.2 hq] at this
        cases this.2

/-- **A pass keeps the index right**, when every want's view reads a
list and the reads a commit hits are the ones its keys name. -/
theorem idxok_passIdx (hex : Exact hits hitQs) (hne : ∀ s x, reads s x ≠ []) {w : RWorld σ C W V Q}
    (ok : IdxOk w) (cap : Nat) : IdxOk (w.passIdx hits eval reads hitQs cap) := by
  unfold passIdx
  split
  · exact ok
  · have fr := foldl_read eval reads w.store (pick w.wants (w.markIdx hitQs) cap)
      (w.board.keep (w.wants.contains ·), w.noticed hits, w.kept)
    refine ⟨fun x hx hs => ?_, fun x qs q hd hq => ?_⟩
    · show x ∈ (pick w.wants (w.markIdx hitQs) cap).foldl (·.erase ·) (w.markIdx hitQs)
      rw [mem_eraseAll]
      by_cases hp : x ∈ pick w.wants (w.markIdx hitQs) cap
      · exfalso
        have hd' := ((fr x).1 hp).choose_spec.choose_spec.2.2
        change (w.passWith hits eval reads (w.markIdx hitQs) cap).deps x = _ at hd'
        have hclean := foldl_read_clean eval reads w.store (pick w.wants (w.markIdx hitQs) cap)
          (w.board.keep (w.wants.contains ·), w.noticed hits, w.kept) x hp
        change staleW (w.passWith hits eval reads (w.markIdx hitQs) cap).staleQ (w.passWith hits eval reads (w.markIdx hitQs) cap).deps x = true at hs
        rw [staleW, hd'] at hs
        simp only [Bool.or_eq_true, List.any_eq_true, List.isEmpty_iff] at hs
        rcases hs with he | ⟨q, hq, t⟩
        · exact hne _ _ he
        · have := hclean q hq
          change (w.passWith hits eval reads (w.markIdx hitQs) cap).staleQ q = false at this
          rw [this] at t; cases t
      · refine ⟨marked_sub_idx hits hitQs hex ok x ?_, hp⟩
        have hwc : w.wants.contains x = true := List.contains_iff_mem.2 hx
        rw [marked, mem_mark]
        right
        refine ⟨hx, ?_⟩
        have hd' : (w.passWith hits eval reads (w.markIdx hitQs) cap).deps x = w.kept x := ((fr x).2.1 hp).2
        change staleW (w.passWith hits eval reads (w.markIdx hitQs) cap).staleQ (w.passWith hits eval reads (w.markIdx hitQs) cap).deps x = true at hs
        rw [staleW, hd'] at hs
        rw [staleW]
        split at hs
        · rfl
        · simp only [Bool.or_eq_true, List.any_eq_true] at hs ⊢
          rcases hs with he | ⟨q, hq, t⟩
          · exact Or.inl he
          · exact Or.inr ⟨q, hq, (fr x).2.2 q t⟩
    · show x ∈ w.rev q ++ (pick w.wants (w.markIdx hitQs) cap).filter fun y => (reads w.store y).contains q
      by_cases hp : x ∈ pick w.wants (w.markIdx hitQs) cap
      · have hd' := ((fr x).1 hp).choose_spec.choose_spec.2.2
        change (w.passWith hits eval reads (w.markIdx hitQs) cap).deps x = _ at hd'
        change (w.passWith hits eval reads (w.markIdx hitQs) cap).deps x = some qs at hd
        rw [hd'] at hd; cases hd
        exact List.mem_append_right _ (List.mem_filter.2 ⟨hp, List.contains_iff_mem.2 hq⟩)
      · have hd' : (w.passWith hits eval reads (w.markIdx hitQs) cap).deps x = w.kept x := ((fr x).2.1 hp).2
        change (w.passWith hits eval reads (w.markIdx hitQs) cap).deps x = some qs at hd
        rw [hd'] at hd
        simp only [kept] at hd
        split at hd
        · exact List.mem_append_left _ (ok.2 x qs q hd hq)
        · cases hd

end RWorld

end Live
