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

The purge is one code over the store, `purge` (Engine/Core.lean): it
walks from `ids` to every stored op that requires one (`dependents`,
SQLite's `reqs` rows), un-decides each op it found, deletes the conn and
local ones and queues the shared ones. On the model's tables it is
`purgeS`, deleting `purgeSet` (`run_purge`), so the laws below are of the
purge SQLite runs, as far as SQLite answers as the model does
(tests/engine/Purge.lean checks that, table by table).

SQLite (`purgeSql`, Engine/Sqlite.lean) runs it in one transaction and
drains, with `secure_delete` on, so the cells it frees are zeroed. That
is not enough: a page that a b-tree split rebuilt keeps copies of cells
it gave away, and Tests/Purge.lean finds a purged secret there. So a
purge then runs `VACUUM`, which rewrites the file from its live rows,
and checkpoints the WAL with TRUNCATE, so no old frame keeps a byte
(`scrubSql`, which changes no row). The test reads the database's files
raw and finds none of the secret's bytes; without `secure_delete`,
without the checkpoint, or without `VACUUM`, it finds them.

Laws (proven):
- `run_purge`: the running `purge`, on the model's tables, is `purgeS`,
  and returns `purgeSet`.
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

/-! ## The walk, on the tables -/

/-- `ByteArray`'s `==` is equality, so the walk's set of seen ids holds
exactly what was put in it. Local, as in engine/wire/WorldLaws.lean. -/
private theorem byteArray_beq : LawfulBEq ByteArray where
  eq_of_beq {a b} h := ByteArray.ext (eq_of_beq (show a.data == b.data from h))
  rfl {a} := show a.data == a.data from beq_self_eq_true a.data

attribute [local instance] byteArray_beq

theorem mem_dependents {s : DB F} {x y : Id} :
    y ∈ s.dependents x ↔ y ∈ s.stored ∧ ∃ o, s.ops y = some o ∧ x ∈ o.reqs := by
  simp only [DB.dependents, mem_sortIds, List.mem_filter]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    split at h2
    · rename_i o ho; exact ⟨o, ho, (has_iff _ _).1 h2⟩
    · cases h2
  · rintro ⟨h1, o, ho, hr⟩
    refine ⟨h1, ?_⟩
    rw [ho]; exact (has_iff _ _).2 hr

/-- What `pushNew` pushes: the ids of ys not seen, each once. -/
theorem pushNew_spec (ys todo : List Id) (seen : Std.HashSet Id) :
    ∃ new, (pushNew ys todo seen).1 = new ++ todo ∧ new.Nodup ∧
      (∀ z ∈ new, z ∈ ys ∧ seen.contains z = false) ∧
      (∀ z, (pushNew ys todo seen).2.contains z = true ↔ seen.contains z = true ∨ z ∈ new) ∧
      (∀ z ∈ ys, seen.contains z = true ∨ z ∈ new) := by
  induction ys generalizing todo seen with
  | nil => exact ⟨[], rfl, List.nodup_nil, by simp, by simp [pushNew], by simp⟩
  | cons y ys ih =>
    by_cases hy : seen.contains y = true
    · have e : pushNew (y :: ys) todo seen = pushNew ys todo seen := by
        simp only [pushNew, List.foldl_cons, hy, ite_true]
      obtain ⟨new, h1, h2, h3, h4, h5⟩ := ih todo seen
      refine ⟨new, e ▸ h1, h2, fun z hz => ⟨List.mem_cons_of_mem _ (h3 z hz).1, (h3 z hz).2⟩,
        e ▸ h4, fun z hz => ?_⟩
      rcases List.mem_cons.1 hz with rfl | hz
      · exact Or.inl hy
      · exact h5 z hz
    · have e : pushNew (y :: ys) todo seen = pushNew ys (y :: todo) (seen.insert y) := by
        simp only [pushNew, List.foldl_cons, hy, Bool.false_eq_true, ite_false]
      have hc : ∀ z, (seen.insert y).contains z = true ↔ y = z ∨ seen.contains z = true := by
        intro z; rw [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq]
      obtain ⟨new, h1, h2, h3, h4, h5⟩ := ih (y :: todo) (seen.insert y)
      have hyn : y ∉ new := fun hm => by
        have := (h3 y hm).2
        rw [Bool.eq_false_iff] at this
        exact this ((hc y).2 (Or.inl rfl))
      refine ⟨new ++ [y], by rw [e, h1, List.append_assoc]; rfl, ?_, ?_, ?_, ?_⟩
      · rw [List.nodup_append]
        refine ⟨h2, List.nodup_cons.2 ⟨by simp, List.nodup_nil⟩, fun a ha b hb => ?_⟩
        rw [List.mem_singleton] at hb; subst hb
        intro e'; subst e'; exact hyn ha
      · intro z hz
        rcases List.mem_append.1 hz with hz | hz
        · refine ⟨List.mem_cons_of_mem _ (h3 z hz).1, ?_⟩
          have := (h3 z hz).2
          rw [Bool.eq_false_iff] at this ⊢
          exact fun h' => this ((hc z).2 (Or.inr h'))
        · rw [List.mem_singleton] at hz; subst hz
          exact ⟨List.mem_cons_self .., Bool.eq_false_iff.2 hy⟩
      · intro z
        rw [e, h4, hc, List.mem_append, List.mem_singleton]
        constructor
        · rintro ((rfl | h) | h)
          · exact Or.inr (Or.inr rfl)
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        · rintro (h | h | rfl)
          · exact Or.inl (Or.inr h)
          · exact Or.inr h
          · exact Or.inl (Or.inl rfl)
      · intro z hz
        rcases List.mem_cons.1 hz with rfl | hz
        · exact Or.inr (List.mem_append_right _ (List.mem_singleton.2 rfl))
        · rcases h5 z hz with h | h
          · rcases (hc z).1 h with rfl | h
            · exact Or.inr (List.mem_append_right _ (List.mem_singleton.2 rfl))
            · exact Or.inl h
          · exact Or.inr (List.mem_append_left _ h)

/-- `walkDeps` on the tables. -/
def walkS (s : DB F) : Nat → List Id → List Id → Std.HashSet Id → Option (List Id)
  | _, [], found, _ => some found
  | 0, _ :: _, _, _ => none
  | n + 1, x :: todo, found, seen =>
    let r := pushNew (s.dependents x) todo seen
    walkS s n r.1 (x :: found) r.2

theorem run_walkDeps (n : Nat) (todo found : List Id) (seen : Std.HashSet Id) (s : DB F) :
    (walkDeps n todo found seen : Model F _).run s = (walkS s n todo found seen, s) := by
  induction n generalizing todo found seen with
  | zero => cases todo <;> rfl
  | succ n ih =>
    cases todo with
    | nil => rfl
    | cons x todo => simp only [walkDeps, walkS, Model.run_bind, run_dependents, ih]

/-- What the walk keeps true, of what it found and has to do: seen is
those, each once; each is named or stored, and requires a named id,
transitively; every op requiring a found one is found or to do; and
every named id is one of them. -/
structure WalkInv (s : DB F) (ids todo found : List Id) (seen : Std.HashSet Id) : Prop where
  mem : ∀ z, seen.contains z = true ↔ z ∈ found ∨ z ∈ todo
  nodup : (found ++ todo).Nodup
  within : ∀ z, z ∈ found ∨ z ∈ todo → z ∈ ids ∨ z ∈ s.stored
  sound : ∀ z, z ∈ found ∨ z ∈ todo → ∃ y ∈ ids, Sync.Reach s.ops z y
  closed : ∀ x ∈ found, ∀ y ∈ s.dependents x, y ∈ found ∨ y ∈ todo
  named : ∀ z ∈ ids, z ∈ found ∨ z ∈ todo

/-- What was found and is to do, each once, are among the named and
stored ids: the walk's bound. -/
theorem WalkInv.length {s : DB F} {ids todo found : List Id} {seen : Std.HashSet Id}
    (h : WalkInv s ids todo found seen) : found.length + todo.length ≤ ids.length + s.stored.length := by
  have := h.nodup.length_le_of_subset (l₂ := ids ++ s.stored) fun z hz =>
    List.mem_append.2 (h.within z (List.mem_append.1 hz))
  simpa using this

theorem WalkInv.step {s : DB F} {ids todo found : List Id} {seen : Std.HashSet Id} {x : Id}
    (h : WalkInv s ids (x :: todo) found seen) :
    WalkInv s ids (pushNew (s.dependents x) todo seen).1 (x :: found)
      (pushNew (s.dependents x) todo seen).2 := by
  obtain ⟨new, e, hnd, hnew, hc, hcov⟩ := pushNew_spec (s.dependents x) todo seen
  rw [e]
  have unseen : ∀ z ∈ new, z ∉ found ∧ z ∉ x :: todo := fun z hz => by
    have := (hnew z hz).2
    rw [Bool.eq_false_iff] at this
    exact ⟨fun h' => this ((h.mem z).2 (Or.inl h')), fun h' => this ((h.mem z).2 (Or.inr h'))⟩
  -- the new ones are x's dependents, so stored, and reach a named id through x
  have dep : ∀ z ∈ new, z ∈ s.stored ∧ ∃ y ∈ ids, Sync.Reach s.ops z y := fun z hz => by
    obtain ⟨hs, o, ho, hr⟩ := mem_dependents.1 (hnew z hz).1
    obtain ⟨y, hy, hxy⟩ := h.sound x (Or.inr (List.mem_cons_self ..))
    exact ⟨hs, y, hy, Sync.Reach.trans (.step .refl ho hr) hxy⟩
  -- found, x :: todo and new, all at once
  have split : ∀ z, (z ∈ x :: found ∨ z ∈ new ++ todo) ↔ ((z ∈ found ∨ z ∈ x :: todo) ∨ z ∈ new) := by
    intro z
    simp only [List.mem_cons, List.mem_append]
    constructor
    · rintro ((rfl | h) | h | h)
      · exact Or.inl (Or.inr (Or.inl rfl))
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
      · exact Or.inl (Or.inr (Or.inr h))
    · rintro ((h | rfl | h) | h)
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inl h)
  have hnd0 := h.nodup
  rw [List.nodup_append] at hnd0
  obtain ⟨hf, hxt, hft⟩ := hnd0
  obtain ⟨hx, ht⟩ := List.nodup_cons.1 hxt
  refine ⟨fun z => ?_, ?_, fun z hz => ?_, fun z hz => ?_, fun y hy z hz => ?_, fun z hz => ?_⟩
  · rw [hc, h.mem, split]
  · rw [List.cons_append, List.nodup_cons, List.mem_append, List.mem_append]
    refine ⟨fun hm => ?_, ?_⟩
    · rcases hm with hm | hm | hm
      · exact hft x hm x (List.mem_cons_self ..) rfl
      · exact (unseen x hm).2 (List.mem_cons_self ..)
      · exact hx hm
    · rw [List.nodup_append, List.nodup_append]
      refine ⟨hf, ⟨hnd, ht, fun a ha b hb e' => ?_⟩, fun a ha b hb e' => ?_⟩
      · subst e'; exact (unseen a ha).2 (List.mem_cons_of_mem _ hb)
      · subst e'
        rcases List.mem_append.1 hb with hb | hb
        · exact (unseen a hb).1 ha
        · exact hft a ha a (List.mem_cons_of_mem _ hb) rfl
  · rcases (split z).1 hz with hz | hz
    · exact h.within z hz
    · exact Or.inr (dep z hz).1
  · rcases (split z).1 hz with hz | hz
    · exact h.sound z hz
    · exact (dep z hz).2
  · rcases List.mem_cons.1 hy with rfl | hy
    · exact (split z).2 ((hcov z hz).imp_left (h.mem z).1)
    · exact (split z).2 (Or.inl (h.closed y hy z hz))
  · exact (split z).2 (Or.inl (h.named z hz))

/-- **The walk ends within its bound,** having found every named id and
every stored op that requires a found one. -/
theorem walkS_ends (s : DB F) (ids : List Id) :
    ∀ n todo found seen, WalkInv s ids todo found seen →
      ids.length + s.stored.length ≤ n + found.length →
      ∃ c seen', walkS s n todo found seen = some c ∧ WalkInv s ids [] c seen' := by
  intro n
  induction n with
  | zero =>
    intro todo found seen h hn
    cases todo with
    | nil => exact ⟨found, seen, rfl, h⟩
    | cons x todo => have := h.length; simp only [List.length_cons] at this; omega
  | succ n ih =>
    intro todo found seen h hn
    cases todo with
    | nil => exact ⟨found, seen, rfl, h⟩
    | cons x todo =>
      obtain ⟨c, seen', hw, hi⟩ := ih _ _ _ h.step (by simp only [List.length_cons]; omega)
      exact ⟨c, seen', hw, hi⟩

/-- `ids` and every stored op that requires one of them, transitively:
what the walk finds, given a step for each id named and op stored
(`closeUp_walk`: enough). -/
def closeUp (s : DB F) (ids : List Id) : List Id :=
  (walkS s (ids.length + s.stored.length) (pushNew ids [] {}).1 [] (pushNew ids [] {}).2).getD []

theorem closeUp_walk (s : DB F) (ids : List Id) :
    walkS s (ids.length + s.stored.length) (pushNew ids [] {}).1 [] (pushNew ids [] {}).2 =
        some (closeUp s ids) ∧ ∃ seen, WalkInv s ids [] (closeUp s ids) seen := by
  obtain ⟨new, e, hnd, hnew, hc, hcov⟩ := pushNew_spec ids [] {}
  have h0 : WalkInv s ids (pushNew ids [] {}).1 [] (pushNew ids [] {}).2 := by
    rw [e, List.append_nil]
    refine ⟨fun z => ?_, by simpa using hnd, fun z hz => ?_, fun z hz => ?_, by simp, fun z hz => ?_⟩
    · rw [hc]; simp
    · simp only [List.not_mem_nil, false_or] at hz; exact Or.inl (hnew z hz).1
    · simp only [List.not_mem_nil, false_or] at hz; exact ⟨z, (hnew z hz).1, .refl⟩
    · rcases hcov z hz with h | h
      · simp at h
      · exact Or.inr h
  obtain ⟨c, seen', hw, hi⟩ :=
    walkS_ends s ids (ids.length + s.stored.length) _ _ _ h0 (Nat.le_add_right _ _)
  have : closeUp s ids = c := by unfold closeUp; rw [hw]; rfl
  rw [this]
  exact ⟨hw, seen', hi⟩

theorem closeUp_sub (s : DB F) (S : List Id) {x : Id} (hx : x ∈ S) : x ∈ closeUp s S := by
  obtain ⟨_, _, h⟩ := closeUp_walk s S
  simpa using h.named x hx

/-- Every stored op requiring one of the closure is in it. -/
theorem closeUp_closed (s : DB F) (S : List Id) {y r : Id} {o : Op} (hs : y ∈ s.stored)
    (hy : s.ops y = some o) (hr : r ∈ o.reqs) (hc : r ∈ closeUp s S) : y ∈ closeUp s S := by
  obtain ⟨_, _, h⟩ := closeUp_walk s S
  simpa using h.closed r hc y (mem_dependents.2 ⟨hs, o, hy, hr⟩)

/-- Everything in the closure is one of S or requires one, transitively. -/
theorem closeUp_sound (s : DB F) (S : List Id) {x : Id} (hx : x ∈ closeUp s S) :
    ∃ y ∈ S, Sync.Reach s.ops x y := by
  obtain ⟨_, _, h⟩ := closeUp_walk s S
  exact h.sound x (Or.inl hx)

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

/-- Whether x is a stored shared op. -/
def rejudgeable (fam : Family F) (s : DB F) (x : Id) : Bool :=
  match s.ops x with
  | some o => (fam.room o).isSome
  | none => false

/-- The shared ops among them: kept, and judged again. -/
def rejudgeSet (fam : Family F) (s : DB F) (ids : List Id) : List Id :=
  (closeUp s ids).filter (rejudgeable fam s)

/-- The state with those ops forgotten: the purged ops leave every
table; every op of the closure loses its verdict, filings and queue
entries; the shared ones are queued again, in the walk's order. -/
def purgeS (fam : Family F) (ids : List Id) (s : DB F) : DB F :=
  let C := closeUp s ids
  let P := purgeSet fam s ids
  { ops := fun x => if has P x then none else s.ops x
    stored := s.stored.filter fun x => !has P x
    status := fun x => if has C x then none else s.status x
    waits := fun r => if has P r then [] else (s.waits r).filter fun y => !has P y
    queue := s.queue.filter (fun x => !has C x) ++ rejudgeSet fam s ids
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
  simp only [rejudgeSet, List.mem_filter, rejudgeable]
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
  show x ∈ s.queue.filter _ ++ _ ↔ _
  simp only [List.mem_append, List.mem_filter, Bool.not_eq_true', has_false]

theorem mem_purgeS_idx (s : DB F) (ids : List Id) (k : ByteArray) (x : Id) :
    x ∈ (purgeS fam ids s).idx k ↔ x ∈ s.idx k ∧ x ∉ closeUp s ids := by
  show x ∈ (s.idx k).filter _ ↔ _
  simp only [List.mem_filter, Bool.not_eq_true', has_false]

/-! ## The running purge is `purgeS`

`purge` (engine/core/Core.lean) is the code SQLite runs. On the tables
it walks as `closeUp` does, un-decides the closure one op at a time,
deletes the purged ops one at a time and queues the rest: `purgeS`
(`run_purge`). -/

/-- The un-deciding of `unsettle`, on the tables. -/
def undecideAllS (xs : List Id) (s : DB F) : DB F := xs.foldl (fun s x => s.undecide x) s

/-- `deleteAll` on the tables. -/
def deleteAllS (xs : List Id) (s : DB F) : DB F := xs.foldl (fun s x => s.deleteOp x) s

theorem run_unsettle (fam : Family F) (xs gone again : List Id) (s : DB F) :
    (unsettle fam xs gone again : Model F _).run s =
      ((gone.reverse ++ xs.filter (purgeable fam s), again.reverse ++ xs.filter (rejudgeable fam s)),
        undecideAllS xs s) := by
  induction xs generalizing gone again s with
  | nil => simp only [unsettle, Model.run_pure, List.filter_nil, List.append_nil]; rfl
  | cons x xs ih =>
    have e : (s.undecide x).ops x = s.ops x := rfl
    simp only [unsettle, Model.run_bind, run_undecide, run_getOp, e]
    have hp : purgeable fam (s.undecide x) = purgeable fam s := rfl
    have hr : rejudgeable fam (s.undecide x) = rejudgeable fam s := rfl
    have hu : undecideAllS xs (s.undecide x) = undecideAllS (x :: xs) s := rfl
    cases ho : s.ops x with
    | none =>
      have h1 : purgeable fam s x = false := by simp [purgeable, ho]
      have h2 : rejudgeable fam s x = false := by simp [rejudgeable, ho]
      simp only [ih, hp, hr, hu, List.filter_cons, h1, h2, Bool.false_eq_true, ite_false]
    | some o =>
      cases hs : (fam.room o).isSome with
      | true =>
        have h1 : purgeable fam s x = false := by
          have : (fam.room o).isNone = false := by
            cases hr : fam.room o with
            | none => rw [hr] at hs; cases hs
            | some _ => rfl
          simp only [purgeable, ho, this]
        have h2 : rejudgeable fam s x = true := by simp [rejudgeable, ho, hs]
        simp only [hs, ite_true, ih, hp, hr, hu, List.filter_cons, h1, h2, Bool.false_eq_true,
          ite_false, List.reverse_cons, List.append_assoc, List.singleton_append]
      | false =>
        have h1 : purgeable fam s x = true := by
          have : (fam.room o).isNone = true := by
            cases hr : fam.room o with
            | none => rfl
            | some _ => rw [hr] at hs; cases hs
          simp only [purgeable, ho, this]
        have h2 : rejudgeable fam s x = false := by simp [rejudgeable, ho, hs]
        simp only [hs, Bool.false_eq_true, ite_false, ih, hp, hr, hu, List.filter_cons, h1, h2,
          ite_true, List.reverse_cons, List.append_assoc, List.singleton_append]

theorem run_deleteAll (xs : List Id) (s : DB F) :
    (deleteAll xs : Model F _).run s = ((), deleteAllS xs s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => simp only [deleteAll, Model.run_bind, run_deleteOp, ih]; rfl

theorem not_has_cons (x : Id) (l : List Id) (y : Id) : (!has l y && !has [x] y) = !has (x :: l) y := by
  simp only [has]; by_cases h : x = y <;> simp [h]

theorem filter_has_nil (l : List Id) : l.filter (fun y => !has [] y) = l :=
  List.filter_eq_self.2 fun _ _ => rfl

theorem undecideAllS_eq (xs : List Id) (s : DB F) : undecideAllS xs s =
    { s with status := fun i => if has xs i then none else s.status i
             queue := s.queue.filter fun y => !has xs y
             idx := fun k => (s.idx k).filter fun y => !has xs y } := by
  induction xs generalizing s with
  | nil => show s = _; simp only [filter_has_nil]; rfl
  | cons x xs ih =>
    show undecideAllS xs (s.undecide x) = _
    rw [ih]
    simp only [DB.undecide, List.filter_filter]
    congr 1
    · funext i
      by_cases h : x = i
      · subst h; simp [has]
      · have h' : ¬ i = x := fun e => h e.symm
        simp [has, h, h']
    · congr 1; funext y; exact not_has_cons x xs y
    · funext k; congr 1; funext y; exact not_has_cons x xs y

theorem deleteAllS_eq (xs : List Id) (s : DB F) : deleteAllS xs s =
    { s with ops := fun i => if has xs i then none else s.ops i
             stored := s.stored.filter fun y => !has xs y
             waits := fun r => if has xs r then [] else (s.waits r).filter fun y => !has xs y } := by
  induction xs generalizing s with
  | nil => show s = _; simp only [filter_has_nil]; rfl
  | cons x xs ih =>
    show deleteAllS xs (s.deleteOp x) = _
    rw [ih]
    simp only [DB.deleteOp, List.filter_filter]
    congr 1
    · funext i
      by_cases h : x = i
      · subst h; simp [has]
      · have h' : ¬ i = x := fun e => h e.symm
        simp [has, h, h']
    · congr 1; funext y; exact not_has_cons x xs y
    · funext r
      by_cases h : r = x
      · subst h; simp [has]
      · have e : has (x :: xs) r = has xs r := by simp only [has]; simp [Ne.symm h]
        rw [e]
        simp only [h, ite_false]
        split
        · rfl
        · rw [List.filter_filter]; congr 1; funext y; exact not_has_cons x xs y

/-- **The engine's purge, run on the tables, is `purgeS`**, and it
returns the ops it deleted, `purgeSet`. SQLite runs this code
(`purgeSql`), so the laws of `purgeS` are laws of the running purge, as
far as SQLite answers as the model does. -/
theorem run_purge (fam : Family F) (ids : List Id) (s : DB F) :
    (purge fam ids : Model F _).run s = (some (purgeSet fam s ids), purgeS fam ids s) := by
  obtain ⟨hw, _⟩ := closeUp_walk s ids
  simp only [purge, Model.run_bind, run_countOps, run_walkDeps, hw, run_unsettle, run_deleteAll,
    run_pushAll, List.reverse_nil, List.nil_append, Model.run_pure]
  rw [deleteAllS_eq, undecideAllS_eq]
  rfl

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
