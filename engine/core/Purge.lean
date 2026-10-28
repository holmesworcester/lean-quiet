/-
Purge: forgetting ops. Forward secrecy needs it. A session's
ephemeral secrets and keys are local ops, and once the session closes
nothing on disk may open its traffic (tiny's "close is a death key, and
forward secrecy is its verdict"). A shipped courier is forgotten the
same way.

`purge ids` deletes the conn and local ops among `ids` and among every
stored op that requires one of them, transitively (`closeUp`): their
bytes, verdicts, filings and waits. Shared ops are never deleted; they
leave only by removal semantics. A shared op among the dependents is
kept, but it loses its verdict and filings and goes back on the queue,
so the next drain judges it again over what remains. It then waits on
the op that is gone, or is Invalid if another requirement is. That is
its verdict over the remaining ops, and it is what every other node
already holds, since conn and local ops never travel. So no peer can
pin a session's secrets by sending a shared op that cites them: the
purge still deletes them.

Purge is an engine operation, not an op. A family's hook names what to
purge: the connection family names a closed session's ops, and the node
names a courier once it is handed out. Nothing records the purge,
because what was purged was this node's transient state. A purged
local op never returns from the wire (`intake_local`). A purged conn op
may return: a replayed request is admitted, opened and either answered
afresh (a new ephemeral, a session nobody but the dialer can use) or
left to time out. A purged op written again is stored and judged anew.

The SQLite instance (`purgeSql`, Engine/Sqlite.lean) walks dependents
through its `reqs` table, deletes in one transaction and drains, with
`secure_delete` on, so the cells it frees are zeroed. That is not
enough: a page that a b-tree split rebuilt keeps copies of cells it
gave away, and Tests/Purge.lean finds a purged secret there. So a purge
then runs `VACUUM`, which rewrites the file from its live rows, and
checkpoints the WAL with TRUNCATE, so no old frame keeps a byte. The
test reads the database's files raw and finds none of the secret's
bytes; without `secure_delete`, without the checkpoint, or without
`VACUUM`, it finds them.

Laws (proven):
- `purge_gone`: no purged op is stored, or filed under any key.
- `purge_named`: every conn or local op named is purged, whatever cites
  it, so a closed session's ops are gone (`close_forgets`).
- `purge_shared`: no shared op is deleted.
- `purge_undecides`: but a shared dependent is not left as it was: its
  verdict and filings go and it is queued, to be judged again over the
  remaining ops (Engine/Proofs.lean).
- `mem_purgeSet`: the purged ops are exactly the conn and local ops among
  `ids` and their stored dependents (Engine/Proofs.lean).
- `purge_inv`: a purge keeps the invariant, from any state that has it,
  at rest or not (Engine/Proofs.lean). The remaining verdicts are the
  spec's over the remaining ops (`Engine.Sync.spec_local`: no remaining
  decided op requires a purged one).
- `Reach` has a purge step, so every law over reachable states (order
  freedom, termination, the drain budget) holds with purges anywhere
  among arrivals and steps; `purge_settles` (Engine/Budget.lean): after a
  purge, draining with the budget empties the queue and every verdict is
  the spec's over the remaining ops.
-/
import engine.core.Run
import engine.core.Locality

namespace Engine
variable {F : Type} {fam : Family F}

theorem has_append (S T : List Id) (x : Id) : has (S ++ T) x = (has S x || has T x) := by
  apply Bool.eq_iff_iff.2
  simp only [has_iff, Bool.or_eq_true, List.mem_append]

/-! ## Dependents -/

/-- Whether y is a stored op that requires one of S. -/
def requiresIn (s : DB F) (S : List Id) (y : Id) : Bool :=
  match s.ops y with
  | some o => o.reqs.any (has S)
  | none => false

/-- The stored ops outside S that require one of S. -/
def moreOf (s : DB F) (S : List Id) : List Id :=
  s.stored.filter fun y => !has S y && requiresIn s S y

theorem moreOf_lt (s : DB F) (S : List Id) (h : moreOf s S ≠ []) :
    (s.stored.filter fun y => !has (S ++ moreOf s S) y).length <
      (s.stored.filter fun y => !has S y).length := by
  have e : (s.stored.filter fun y => !has (S ++ moreOf s S) y) =
      (s.stored.filter fun y => !has S y).filter fun y => !has (moreOf s S) y := by
    rw [List.filter_filter]
    congr 1; funext y; rw [has_append]; cases has S y <;> cases has (moreOf s S) y <;> rfl
  rw [e, List.length_filter_lt_length_iff_exists]
  obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ h
  have hy' := hy
  simp only [moreOf, List.mem_filter, Bool.and_eq_true] at hy'
  exact ⟨y, List.mem_filter.2 ⟨hy'.1, hy'.2.1⟩, by simp [(has_iff _ _).2 hy]⟩

/-- S grown by every stored op that requires one of it, until no stored
op outside it does: S and its dependents. -/
def closeUp (s : DB F) (S : List Id) : List Id :=
  if moreOf s S = [] then S else closeUp s (S ++ moreOf s S)
termination_by (s.stored.filter fun y => !has S y).length
decreasing_by exact moreOf_lt s S ‹_›

theorem closeUp_sub (s : DB F) (S : List Id) {x : Id} (hx : x ∈ S) : x ∈ closeUp s S := by
  induction S using closeUp.induct s with
  | case1 S h => rw [closeUp, ite_eq_left h]; exact hx
  | case2 S h ih => rw [closeUp, ite_eq_right h]; exact ih (List.mem_append_left _ hx)

/-- Every stored op requiring one of the closure is in it. -/
theorem closeUp_closed (s : DB F) (S : List Id) {y r : Id} {o : Op} (hs : y ∈ s.stored)
    (hy : s.ops y = some o) (hr : r ∈ o.reqs) (hc : r ∈ closeUp s S) : y ∈ closeUp s S := by
  induction S using closeUp.induct s with
  | case1 S h =>
    rw [closeUp, ite_eq_left h] at hc ⊢
    apply Classical.byContradiction; intro hn
    have : y ∈ moreOf s S := by
      simp only [moreOf, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true']
      refine ⟨hs, (has_false _ _).2 hn, ?_⟩
      simp only [requiresIn, hy, List.any_eq_true]
      exact ⟨r, hr, (has_iff _ _).2 hc⟩
    rw [h] at this; cases this
  | case2 S h ih => rw [closeUp, ite_eq_right h] at hc ⊢; exact ih hc

/-- Everything in the closure is one of S or requires one, transitively. -/
theorem closeUp_sound (s : DB F) (S : List Id) {x : Id} (hx : x ∈ closeUp s S) :
    ∃ y ∈ S, Sync.Reach s.ops x y := by
  induction S using closeUp.induct s with
  | case1 S h => rw [closeUp, ite_eq_left h] at hx; exact ⟨x, hx, .refl⟩
  | case2 S h ih =>
    rw [closeUp, ite_eq_right h] at hx
    obtain ⟨y, hy, hxy⟩ := ih hx
    rcases List.mem_append.1 hy with hy | hy
    · exact ⟨y, hy, hxy⟩
    · simp only [moreOf, List.mem_filter, Bool.and_eq_true] at hy
      have hreq := hy.2.2
      unfold requiresIn at hreq
      split at hreq
      · rename_i o ho
        obtain ⟨r, hr, hrS⟩ := List.any_eq_true.1 hreq
        exact ⟨r, (has_iff _ _).1 hrS, Sync.Reach.trans hxy (.step .refl ho hr)⟩
      · cases hreq

/-- A set closed under dependents holds everything that requires one of
its members, transitively. -/
theorem reach_closed {ops : Id → Option Op} {C : Id → Prop}
    (hC : ∀ y o r, ops y = some o → r ∈ o.reqs → C r → C y) {x y : Id}
    (h : Sync.Reach ops x y) (hy : C y) : C x := by
  induction h with
  | refl => exact hy
  | step _ ho hr ih => exact ih (hC _ _ _ ho hr hy)

/-! ## The purge -/

/-- Whether x is a stored conn or local op. -/
def purgeable (fam : Family F) (s : DB F) (x : Id) : Bool :=
  match s.ops x with
  | some o => (fam.room o).isNone
  | none => false

/-- The ops purge deletes: the conn and local ops among `ids` and their
stored dependents. -/
def purgeSet (fam : Family F) (s : DB F) (ids : List Id) : List Id :=
  (closeUp s ids).filter (purgeable fam s)

/-- The shared ops among them: kept, and judged again. -/
def rejudgeSet (fam : Family F) (s : DB F) (ids : List Id) : List Id :=
  (closeUp s ids).filter fun x => match s.ops x with
    | some o => (fam.room o).isSome
    | none => false

/-- The state with those ops forgotten: the purged ops leave every
table; every op of the closure loses its verdict, filings and queue
entries; the shared ones are queued again, in byte order. -/
def purgeS (fam : Family F) (ids : List Id) (s : DB F) : DB F :=
  let C := closeUp s ids
  let P := purgeSet fam s ids
  { ops := fun x => if has P x then none else s.ops x
    stored := s.stored.filter fun x => !has P x
    status := fun x => if has C x then none else s.status x
    waits := fun r => if has P r then [] else (s.waits r).filter fun y => !has P y
    queue := s.queue.filter (fun x => !has C x) ++ sortIds (rejudgeSet fam s ids)
    idx := fun k => (s.idx k).filter fun x => !has C x }

theorem mem_purgeSet_iff {s : DB F} {ids : List Id} {x : Id} :
    x ∈ purgeSet fam s ids ↔ x ∈ closeUp s ids ∧ ∃ o, s.ops x = some o ∧ fam.room o = none := by
  simp only [purgeSet, List.mem_filter, purgeable]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    split at h2
    · rename_i o ho; exact ⟨o, ho, Option.isNone_iff_eq_none.1 h2⟩
    · cases h2
  · rintro ⟨h1, o, ho, hr⟩
    refine ⟨h1, ?_⟩
    rw [ho]; simp [hr]

theorem mem_rejudgeSet_iff {s : DB F} {ids : List Id} {x : Id} :
    x ∈ rejudgeSet fam s ids ↔ x ∈ closeUp s ids ∧ ∃ o, s.ops x = some o ∧ (fam.room o).isSome := by
  simp only [rejudgeSet, List.mem_filter]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    split at h2
    · rename_i o ho; exact ⟨o, ho, h2⟩
    · cases h2
  · rintro ⟨h1, o, ho, hr⟩
    refine ⟨h1, ?_⟩
    rw [ho]; exact hr

theorem purgeSet_closeUp {s : DB F} {ids : List Id} {x : Id} (h : x ∈ purgeSet fam s ids) :
    x ∈ closeUp s ids := (mem_purgeSet_iff.1 h).1

/-! ## What a purge does to the tables -/

theorem purgeS_ops_mem (s : DB F) (ids : List Id) {x : Id} (h : x ∈ purgeSet fam s ids) :
    (purgeS fam ids s).ops x = none := by
  show (if has _ x then none else s.ops x) = _
  rw [ite_eq_left ((has_iff _ _).2 h)]

theorem purgeS_ops_not (s : DB F) (ids : List Id) {x : Id} (h : x ∉ purgeSet fam s ids) :
    (purgeS fam ids s).ops x = s.ops x := by
  show (if has _ x then none else s.ops x) = _
  rw [ite_eq_right (by rw [has_iff]; exact h)]

theorem purgeS_status_mem (s : DB F) (ids : List Id) {x : Id} (h : x ∈ closeUp s ids) :
    (purgeS fam ids s).status x = none := by
  show (if has _ x then none else s.status x) = _
  rw [ite_eq_left ((has_iff _ _).2 h)]

theorem purgeS_status_not (s : DB F) (ids : List Id) {x : Id} (h : x ∉ closeUp s ids) :
    (purgeS fam ids s).status x = s.status x := by
  show (if has _ x then none else s.status x) = _
  rw [ite_eq_right (by rw [has_iff]; exact h)]

theorem mem_purgeS_stored (s : DB F) (ids : List Id) (x : Id) :
    x ∈ (purgeS fam ids s).stored ↔ x ∈ s.stored ∧ x ∉ purgeSet fam s ids := by
  show x ∈ s.stored.filter _ ↔ _
  simp only [List.mem_filter, Bool.not_eq_true', has_false]

theorem mem_purgeS_waits (s : DB F) (ids : List Id) (r y : Id) :
    y ∈ (purgeS fam ids s).waits r ↔
      r ∉ purgeSet fam s ids ∧ y ∈ s.waits r ∧ y ∉ purgeSet fam s ids := by
  show y ∈ (if has _ r then [] else (s.waits r).filter _) ↔ _
  by_cases h : r ∈ purgeSet fam s ids
  · rw [ite_eq_left ((has_iff _ _).2 h)]; simp [h]
  · rw [ite_eq_right (by rw [has_iff]; exact h)]
    simp only [List.mem_filter, Bool.not_eq_true', has_false]
    exact ⟨fun ⟨a, b⟩ => ⟨h, a, b⟩, fun ⟨_, a, b⟩ => ⟨a, b⟩⟩

theorem mem_purgeS_queue (s : DB F) (ids : List Id) (x : Id) :
    x ∈ (purgeS fam ids s).queue ↔
      (x ∈ s.queue ∧ x ∉ closeUp s ids) ∨ x ∈ rejudgeSet fam s ids := by
  show x ∈ s.queue.filter _ ++ sortIds _ ↔ _
  simp only [List.mem_append, List.mem_filter, Bool.not_eq_true', has_false, mem_sortIds]

theorem mem_purgeS_idx (s : DB F) (ids : List Id) (k : ByteArray) (x : Id) :
    x ∈ (purgeS fam ids s).idx k ↔ x ∈ s.idx k ∧ x ∉ closeUp s ids := by
  show x ∈ (s.idx k).filter _ ↔ _
  simp only [List.mem_filter, Bool.not_eq_true', has_false]

/-! ## Laws -/

/-- **A purged op is gone:** not stored, and filed under no key. -/
theorem purge_gone (s : DB F) (ids : List Id) {x : Id} (hx : x ∈ purgeSet fam s ids) :
    (purgeS fam ids s).ops x = none ∧ ∀ k, x ∉ (purgeS fam ids s).idx k := by
  refine ⟨purgeS_ops_mem s ids hx, fun k h => ?_⟩
  exact ((mem_purgeS_idx s ids k x).1 h).2 (purgeSet_closeUp hx)

/-- **A conn or local op named is gone**, whatever cites it: no shared
op that requires it keeps it. -/
theorem purge_named (s : DB F) {ids : List Id} {x : Id} (hx : x ∈ ids) {o : Op}
    (ho : s.ops x = some o) (hl : fam.room o = none) :
    (purgeS fam ids s).ops x = none ∧ ∀ k, x ∉ (purgeS fam ids s).idx k :=
  purge_gone s ids (mem_purgeSet_iff.2 ⟨closeUp_sub s ids hx, o, ho, hl⟩)

/-- **A purge deletes no shared op.** -/
theorem purge_shared (s : DB F) (ids : List Id) {x : Id} {o : Op} (ho : s.ops x = some o)
    (hs : (fam.room o).isSome) : (purgeS fam ids s).ops x = some o := by
  rw [purgeS_ops_not, ho]
  intro h
  obtain ⟨_, p, hp, hr⟩ := mem_purgeSet_iff.1 h
  rw [ho] at hp; cases hp
  rw [hr] at hs; cases hs

end Engine
