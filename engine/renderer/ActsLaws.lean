/-
The reader's pass with acts (Reader.pass): the user's writes run first,
in the pass's transaction, and commit (to the outbox, their rows this
pass's notices) before the marks; the wants they touch are read this
pass, ahead of any backlog (`Live.pickActs`). The model is RestLaws'
indexed pass with the acts committed first (`RWorld.passActs`); its
decisions are the running pass's own (`mustReadActs`, `markHit`,
`pickActs`).

- `passActs_nil`: with no act it is the pass at rest's (`passIdx`), so
  RestLaws' laws are its no-act case.
- `inv_passActs`, `idxok_passActs`: the invariants hold.
- `acts_shown`: every wanted want an act touches (one of its recorded
  reads among the keys the act files) shows the store's value after the
  acts, one pass and one frame later, however long the backlog.
- `AWorld`: the composer is the frame's alone; the pass neither changes
  it nor depends on it (`passActs_comp`, `passActs_indep`), and typing
  changes nothing else (`type_only`).
- `acts_force`: acts queued open the store, at rest too.
- The mutants: the acts after the marks (`passLate`) show a stale value
  after the pass and the frame where the pass with acts shows the new
  one (`late_stale`, `acts_fresh`); a start that ignores the acts rests
  with acts queued (`rest_ignores_acts`).
-/
import engine.renderer.RestLaws

namespace Live

/-- **Acts queued open the store**, whatever else. -/
theorem acts_force {W : Type} [BEq W] [Hashable W] (c seen : Nat) (notes moved : Bool) (dirty : Std.HashSet W)
    (late : Bool) : mustReadActs true c seen notes moved dirty late = true := by
  simp [mustReadActs]

/-- The mutant: a start that ignores the acts (`mustRead`) opens nothing
at rest, acts queued or not, so they wait for the next commit. -/
theorem rest_ignores_acts {W : Type} [BEq W] [Hashable W] (c : Nat) :
    mustRead c c false false ({} : Std.HashSet W) false = false := by
  simp [mustRead]

section
variable {W : Type} [BEq W] [Hashable W] [LawfulBEq W]

theorem mem_actsFirst (ws : List W) (t : Std.HashSet W) (x : W) : x ∈ actsFirst ws t ↔ x ∈ ws := by
  simp only [actsFirst, List.mem_append, List.mem_filter]
  cases t.contains x <;> simp

theorem contains_actsFirst (ws : List W) (t : Std.HashSet W) (x : W) :
    (actsFirst ws t).contains x = ws.contains x := by
  rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem]; exact mem_actsFirst ws t x

/-- **A touched want is read**: when every touched want is marked, each
is among `pickActs`' picks, whatever the cap. -/
theorem mem_pickActs {ws : List W} {t m : Std.HashSet W} (cap : Nat)
    (htm : ∀ y ∈ ws, t.contains y = true → m.contains y = true) {x : W} (hx : x ∈ ws) (ht : t.contains x = true) :
    x ∈ pickActs ws t m cap := by
  rw [pickActs, pick_eq, actsFirst, List.filter_append]
  have ha : (ws.filter (t.contains ·)).filter (m.contains ·) = ws.filter (t.contains ·) := by
    rw [List.filter_eq_self]
    intro y hy
    obtain ⟨hy, hty⟩ := List.mem_filter.1 hy
    exact htm y hy hty
  rw [ha, List.take_length_add_append]
  exact List.mem_append_left _ (List.mem_filter.2 ⟨hx, ht⟩)

end

namespace RWorld
variable {σ C W V Q : Type} [BEq W] [Hashable W] [LawfulBEq W] [BEq V] [LawfulBEq V] [BEq Q] [LawfulBEq Q]
  (apply : C → σ → σ) (hits : C → Q → Bool) (eval : σ → W → V) (reads : σ → W → List Q)
  (hitQs : C → List Q)

/-- The acts, committed in order. -/
def commitAll (acts : List C) (w : RWorld σ C W V Q) : RWorld σ C W V Q :=
  acts.foldl (fun w c => w.commit apply c) w

/-- The wants the acts touched: through the index, each whose recorded
reads one of the acts' keys names. -/
def touched (acts : List C) (w : RWorld σ C W V Q) : Std.HashSet W :=
  markHit w.rev {} (acts.flatMap hitQs)

/-- The world after the acts, its wants put touched first: what the
pass with acts passes over. -/
def actsWorld (acts : List C) (w : RWorld σ C W V Q) : RWorld σ C W V Q :=
  let w1 := w.commitAll apply acts
  { w1 with wants := actsFirst w1.wants (w1.touched hitQs acts) }

/-- How many wanted wants the acts touched: the cap's allowance for them. -/
def nTouched (acts : List C) (w : RWorld σ C W V Q) : Nat :=
  ((w.commitAll apply acts).wants.filter (((w.commitAll apply acts).touched hitQs acts).contains ·)).length

/-- **A pass with acts** (Reader.pass): the acts commit first, then the
indexed pass reads the touched wants and the first `cap` other marked
(what `pickActs` picks: `passActs_picks`). -/
def passActs (acts : List C) (cap : Nat) (w : RWorld σ C W V Q) : RWorld σ C W V Q :=
  { (w.actsWorld apply hitQs acts).passIdx hits eval reads hitQs (w.nTouched apply hitQs acts + cap) with
    wants := w.wants }

/-- What the pass with acts reads, when it reads, is `pickActs`' pick. -/
theorem passActs_picks (acts : List C) (cap : Nat) (w : RWorld σ C W V Q) :
    pick (w.actsWorld apply hitQs acts).wants ((w.actsWorld apply hitQs acts).markIdx hitQs)
        (w.nTouched apply hitQs acts + cap) =
      pickActs (w.commitAll apply acts).wants ((w.commitAll apply acts).touched hitQs acts)
        ((w.actsWorld apply hitQs acts).markIdx hitQs) cap := rfl

/-- The acts' steps run in the store each acts on, in order. -/
def ActsStable : σ → List C → Prop
  | _, [] => True
  | s, c :: cs => StableAt apply hits eval reads c s ∧ ActsStable (apply c s) cs

theorem commitAll_fields : ∀ (acts : List C) (w : RWorld σ C W V Q),
    (w.commitAll apply acts).store = acts.foldl (fun s c => apply c s) w.store ∧
    (w.commitAll apply acts).journal = w.journal ++ acts ∧
    (w.commitAll apply acts).wants = w.wants ∧ (w.commitAll apply acts).deps = w.deps ∧
    (w.commitAll apply acts).rev = w.rev ∧ (w.commitAll apply acts).dirty = w.dirty ∧
    (w.commitAll apply acts).commits = w.commits + acts.length
  | [], w => by simp [commitAll]
  | c :: cs, w => by
    have := commitAll_fields cs (w.commit apply c)
    simp only [commitAll, List.foldl_cons] at this ⊢
    obtain ⟨a, b, c', d, e, f, g⟩ := this
    refine ⟨a, ?_, c', d, e, f, ?_⟩
    · rw [b]; simp [commit]
    · rw [g]; simp [commit]; omega

theorem inv_commitAll : ∀ (acts : List C) {w : RWorld σ C W V Q}, Inv hits eval reads w →
    ActsStable apply hits eval reads w.store acts → Inv hits eval reads (w.commitAll apply acts)
  | [], _, h, _ => h
  | c :: cs, w, h, hs => by
    show Inv hits eval reads ((w.commit apply c).commitAll apply cs)
    exact inv_commitAll cs (inv_commit apply hits eval reads h c hs.1) hs.2

theorem idxok_commitAll : ∀ (acts : List C) {w : RWorld σ C W V Q}, IdxOk w → IdxOk (w.commitAll apply acts)
  | [], _, ok => ok
  | c :: cs, w, ok => by
    show IdxOk ((w.commit apply c).commitAll apply cs)
    exact idxok_commitAll cs (idxok_commit apply ok c)

theorem passIdx_wants (cap : Nat) (w : RWorld σ C W V Q) : (w.passIdx hits eval reads hitQs cap).wants = w.wants := by
  unfold passIdx; split <;> rfl

/-- With no act, the pass with acts is the pass at rest's. -/
theorem passActs_nil (cap : Nat) (w : RWorld σ C W V Q) :
    w.passActs apply hits eval reads hitQs [] cap = w.passIdx hits eval reads hitQs cap := by
  have ha : w.actsWorld apply hitQs [] = w := by
    have : actsFirst w.wants ({} : Std.HashSet W) = w.wants := by
      simp only [actsFirst, Std.HashSet.contains_empty, Bool.not_false]
      rw [List.filter_eq_nil_iff.2 (fun _ _ => by simp), List.filter_eq_self.2 (fun _ _ => rfl)]; rfl
    simp only [actsWorld, commitAll, List.foldl_nil, touched, List.flatMap_nil]
    show { w with wants := actsFirst w.wants (markHit w.rev {} []) } = w
    rw [show markHit w.rev ({} : Std.HashSet W) ([] : List Q) = {} from rfl, this]
  have hn : w.nTouched apply hitQs [] = 0 := by
    simp only [nTouched, commitAll, List.foldl_nil, touched, List.flatMap_nil]
    rw [show markHit w.rev ({} : Std.HashSet W) ([] : List Q) = {} from rfl]
    simp
  simp only [passActs, ha, hn, Nat.zero_add]
  rw [← passIdx_wants hits eval reads hitQs cap w]

section
variable {apply hits eval reads hitQs}

/-- A world with its wants put in another order: the same world but for
what a pass reads first. -/
theorem inv_wants {w : RWorld σ C W V Q} (h : Inv hits eval reads w) (ws : List W) :
    Inv hits eval reads { w with wants := ws } := h

theorem idxok_wants {w : RWorld σ C W V Q} (ok : IdxOk w) {ws : List W} (hw : ∀ x, x ∈ ws → x ∈ w.wants) :
    IdxOk { w with wants := ws } :=
  ⟨fun x hx hs => ok.1 x (hw x hx) hs, ok.2⟩

end

theorem actsWorld_fields (acts : List C) (w : RWorld σ C W V Q) :
    (∀ x, x ∈ (w.actsWorld apply hitQs acts).wants ↔ x ∈ w.wants) ∧
    (w.actsWorld apply hitQs acts).store = acts.foldl (fun s c => apply c s) w.store ∧
    (w.actsWorld apply hitQs acts).journal = w.journal ++ acts ∧
    (w.actsWorld apply hitQs acts).deps = w.deps ∧ (w.actsWorld apply hitQs acts).rev = w.rev := by
  obtain ⟨fs, fj, fw, fd, fr, _, _⟩ := commitAll_fields apply acts w
  refine ⟨fun x => ?_, fs, fj, fd, fr⟩
  show x ∈ actsFirst _ _ ↔ _
  rw [mem_actsFirst, fw]

theorem inv_actsWorld {w : RWorld σ C W V Q} (h : Inv hits eval reads w) {acts : List C}
    (hs : ActsStable apply hits eval reads w.store acts) : Inv hits eval reads (w.actsWorld apply hitQs acts) :=
  inv_wants (inv_commitAll apply hits eval reads acts h hs) _

theorem idxok_actsWorld {w : RWorld σ C W V Q} (ok : IdxOk w) (acts : List C) :
    IdxOk (w.actsWorld apply hitQs acts) :=
  idxok_wants (idxok_commitAll apply acts ok) (fun y hy => by
    rw [(commitAll_fields apply acts w).2.2.1]
    exact ((actsWorld_fields apply hitQs acts w).1 y).1 hy)

/-- **Every step keeps the invariants: a pass with acts.** -/
theorem inv_passActs (hex : Exact hits hitQs) {w : RWorld σ C W V Q} (h : Inv hits eval reads w) (ok : IdxOk w)
    {acts : List C} (hs : ActsStable apply hits eval reads w.store acts) (cap : Nat) :
    Inv hits eval reads (w.passActs apply hits eval reads hitQs acts cap) :=
  inv_wants (inv_passIdx hits eval reads hitQs hex (inv_actsWorld apply hits eval reads hitQs h hs)
    (idxok_actsWorld apply hitQs ok acts) _) _

/-- **The index stays complete** after a pass with acts, as after the
pass at rest (`idxok_passIdx`). -/
theorem idxok_passActs (hex : Exact hits hitQs) (hne : ∀ s x, reads s x ≠ []) {w : RWorld σ C W V Q}
    (ok : IdxOk w) (acts : List C) (cap : Nat) :
    IdxOk (w.passActs apply hits eval reads hitQs acts cap) :=
  idxok_wants (idxok_passIdx hits eval reads hitQs hex hne (idxok_actsWorld apply hitQs ok acts) _)
    (fun y hy => by
      rw [passIdx_wants]
      exact ((actsWorld_fields apply hitQs acts w).1 y).2 hy)

/-- **No missed update, the user's own first**: every wanted want one of
whose recorded reads an act's keys name shows the store's value after
the acts, one pass and one frame later, whatever the cap and however
long the backlog of other marked wants. -/
theorem acts_shown (hex : Exact hits hitQs) {w : RWorld σ C W V Q} (h : Inv hits eval reads w) (ok : IdxOk w)
    {acts : List C} (hs : ActsStable apply hits eval reads w.store acts) (cap : Nat)
    {x : W} (hx : x ∈ w.wants) {q : Q} (hq : q ∈ acts.flatMap hitQs) {qs : List Q} (hd : w.deps x = some qs)
    (hqs : q ∈ qs) :
    ((w.passActs apply hits eval reads hitQs acts cap).frame).shown x =
      some (eval (acts.foldl (fun s c => apply c s) w.store) x) := by
  obtain ⟨fw, fs, fj, fd, fr⟩ := actsWorld_fields apply hitQs acts w
  have h2 := inv_actsWorld apply hits eval reads hitQs h hs
  have ok2 := idxok_actsWorld apply hitQs ok acts
  generalize hw2 : w.actsWorld apply hitQs acts = w2 at *
  -- the acts' keys are in the journal: the pass is not idle
  have hj : q ∈ w2.journal.flatMap hitQs := by
    rw [fj, List.flatMap_append]; exact List.mem_append_right _ hq
  have hni : idle (w2.journal.flatMap hitQs) w2.dirty = false := by
    simp only [idle, Bool.and_eq_false_iff]
    left
    cases e : w2.journal.flatMap hitQs with
    | nil => rw [e] at hj; cases hj
    | cons _ _ => rfl
  -- x is read this pass: the touched come first, and each is marked
  have hp : x ∈ pick w2.wants (w2.markIdx hitQs) (w.nTouched apply hitQs acts + cap) := by
    have e := passActs_picks apply hitQs acts cap w
    rw [hw2] at e
    rw [e]
    obtain ⟨_, _, cw, _, cr, _, _⟩ := commitAll_fields apply acts w
    refine mem_pickActs cap (fun y hy ht => ?_) (by rw [cw]; exact hx) ?_
    · rw [Std.HashSet.contains_iff_mem, touched, mem_markHit] at ht
      rcases ht with e | ⟨k, hk, hr⟩
      · simp at e
      · rw [Std.HashSet.contains_iff_mem, markIdx, mem_filter', mem_markHit]
        refine ⟨Or.inr ⟨k, ?_, by rw [fr]; rw [cr] at hr; exact hr⟩, ?_⟩
        · rw [fj, List.flatMap_append]; exact List.mem_append_right _ hk
        · rw [cw] at hy; exact List.contains_iff_mem.2 ((fw y).2 hy)
    · rw [Std.HashSet.contains_iff_mem, touched, mem_markHit, cr]
      exact Or.inr ⟨q, hq, ok.2 x qs q hd hqs⟩
  -- read, so shown after the frame
  simp only [passActs, hw2]
  unfold passIdx
  rw [hni]
  simp only [Bool.false_eq_true, ite_false]
  obtain ⟨u, n, hu, e, _⟩ := pass_picked hits eval reads hp
  have hI := inv_frame hits eval reads (inv_passWith hits eval reads h2 (w.nTouched apply hitQs acts + cap)
    (marked_sub_idx hits hitQs hex ok2))
  have hseen := hI.2.2 x u n
  simp only [frame, Board.take] at hseen
  rcases hseen hu with m | s
  · simp at m
  · show Board.apply (w2.passWith hits eval reads (w2.markIdx hitQs) (w.nTouched apply hitQs acts + cap)).shown
      (w2.passWith hits eval reads (w2.markIdx hitQs) (w.nTouched apply hitQs acts + cap)).board x = _
    rw [← fs, ← e]
    exact s

/-! ## The composer: the frame's alone -/

end RWorld

/-- The reader's world with the frame's queue of acts and its composer
(text, IME, selection). -/
structure AWorld (σ C W V Q K : Type) [BEq W] [Hashable W] where
  r : RWorld σ C W V Q
  acts : List C := []
  comp : Option K := none

namespace AWorld
variable {σ C W V Q K : Type} [BEq W] [Hashable W] [LawfulBEq W] [BEq V] [LawfulBEq V] [BEq Q] [LawfulBEq Q]
  (apply : C → σ → σ) (hits : C → Q → Bool) (eval : σ → W → V) (reads : σ → W → List Q)
  (hitQs : C → List Q)

/-- The frame queues an act. -/
def queue (c : C) (a : AWorld σ C W V Q K) : AWorld σ C W V Q K := { a with acts := a.acts ++ [c] }

/-- The frame edits its composer, and nothing else. -/
def type (f : Option K → Option K) (a : AWorld σ C W V Q K) : AWorld σ C W V Q K := { a with comp := f a.comp }

/-- A pass takes the queued acts. -/
def pass (cap : Nat) (a : AWorld σ C W V Q K) : AWorld σ C W V Q K :=
  { a with r := a.r.passActs apply hits eval reads hitQs a.acts cap, acts := [] }

/-- **The pass leaves the composer.** -/
theorem passActs_comp (cap : Nat) (a : AWorld σ C W V Q K) :
    (a.pass apply hits eval reads hitQs cap).comp = a.comp := rfl

/-- **And does not depend on it**: a pass from any composer is the same
pass, the composer aside. -/
theorem passActs_indep (cap : Nat) (a : AWorld σ C W V Q K) (k : Option K) :
    ({ a with comp := k } : AWorld σ C W V Q K).pass apply hits eval reads hitQs cap =
      { a.pass apply hits eval reads hitQs cap with comp := k } := rfl

/-- A pass takes every queued act. -/
theorem passActs_acts (cap : Nat) (a : AWorld σ C W V Q K) : (a.pass apply hits eval reads hitQs cap).acts = [] := rfl

/-- **Typing changes the composer and nothing else.** -/
theorem type_only (f : Option K → Option K) (a : AWorld σ C W V Q K) : { a.type f with comp := a.comp } = a := rfl

end AWorld

/-! ## The mutant: the acts after the marks -/

namespace RWorld
variable {σ C W V Q : Type} [BEq W] [Hashable W] [LawfulBEq W] [BEq V] [LawfulBEq V] [BEq Q] [LawfulBEq Q]
  (apply : C → σ → σ) (hits : C → Q → Bool) (eval : σ → W → V) (reads : σ → W → List Q)
  (hitQs : C → List Q)

/-- The pass, then the acts: they commit after the marks, so this pass
reads nothing they touched. -/
def passLate (acts : List C) (cap : Nat) (w : RWorld σ C W V Q) : RWorld σ C W V Q :=
  (w.passIdx hits eval reads hitQs cap).commitAll apply acts

end RWorld

namespace Eager

def hitQs (_ : Nat) : List Unit := [()]

/-- Both wants read (0) and shown, at rest: nothing journaled, nothing
dirty, the index naming both under the one list. -/
def w0 : Rw :=
  { store := 0, board := b1, staleQ := fun _ => false, deps := fun _ => some [()],
    wants := [false, true], shown := fun _ => some 0, rev := fun _ => [false, true] }

theorem w0_inv : RWorld.Inv hits eval reads w0 := by
  refine ⟨fun x v n hx => ?_, fun x => ?_, fun x v n hx => ?_⟩
  · obtain ⟨m, h⟩ := b1_vals x
    have : b1.vals[x]? = some (v, n) := hx
    rw [h] at this; cases this
    exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
  · obtain ⟨n, h⟩ := b1_vals x
    show (b1.vals[x]?).isSome = (some [()]).isSome
    rw [h]; rfl
  · right
    obtain ⟨n', h⟩ := b1_vals x
    show some 0 = some v
    have : b1.vals[x]? = some (v, n) := hx
    rw [h] at this; cases this; rfl

theorem w0_idx : RWorld.IdxOk w0 :=
  ⟨fun x _ hs => by simp [staleW, w0] at hs, fun x qs q h _ => by cases x <;> simp [w0]⟩

theorem exact : RWorld.Exact hits hitQs := fun _ q => by simp [hits, hitQs]

/-- **The acts after the marks show a stale value**: the user's write
(1) commits after a pass at rest, and the frame still shows 0. -/
theorem late_stale :
    ((w0.passLate apply hits eval reads hitQs [1] 2).frame).shown true = some 0 ∧
      eval (apply 1 w0.store) true = 1 := by
  refine ⟨?_, rfl⟩
  have hi : (w0.passIdx hits eval reads hitQs 2) = { w0 with journal := [], seen := w0.commits } := by
    unfold RWorld.passIdx
    rw [if_pos (by simp [idle, w0])]
  show Board.apply _ _ true = _
  simp only [RWorld.passLate, hi, RWorld.commitAll, List.foldl, RWorld.commit]
  simp only [Board.apply, w0, b1_moved, Bool.false_eq_true, ite_false]

/-- **The acts before the marks show the new value** on the same world,
one pass and one frame later (`acts_shown`). -/
theorem acts_fresh : ((w0.passActs apply hits eval reads hitQs [1] 2).frame).shown true = some 1 :=
  RWorld.acts_shown apply hits eval reads hitQs exact w0_inv w0_idx (by simp only [RWorld.ActsStable]; exact ⟨stable 1 0, trivial⟩) 2
    (x := true) (by simp [w0]) (q := ()) (by simp [hitQs]) (qs := [()]) rfl (by simp)

end Eager

end Live
