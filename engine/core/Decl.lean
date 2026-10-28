/-
Declarations: what an application declares about its facts, and what is
derived from the names.

A relation is a list a fact kind is filed in, named `<kind>.<name>`
(`admission.byDevice`), with the key arguments of each fact in it. Its
key is its names and those arguments, so keys are named, never numbered,
and distinct names give distinct keys (`mem_keysOf`); a relation key is
never an op's own key (`key_ne_opKey`). A family's keys are its
relations' (`keysOf`), and a list of a relation reads exactly the Valid
facts in it (`filed_rel`, `mem_rows_rel`).
-/
import Engine.View

namespace Engine
open Codec

/-- A relation: a list facts of one kind are filed in. -/
structure Rel (F : Type) where
  kind : String
  name : String
  /-- The key arguments of a fact in this relation; none for a fact it
  does not hold. -/
  args : F → Option (List ByteArray)

namespace Rel
variable {F : Type}

/-- `kind.name`, as screens, notices and logs show it. -/
def path (r : Rel F) : String := r.kind ++ "." ++ r.name

/-- The key of r at these arguments: its names, then the arguments. -/
def key (r : Rel F) (as : List ByteArray) : ByteArray := encode (r.kind.toUTF8, r.name.toUTF8, as)

/-- A list of r at these arguments. -/
def query (r : Rel F) (as : List ByteArray) (limit : Option Nat := none) (desc : Bool := true)
    (after before : Option Pos := none) (also : List ByteArray := []) (cap : Nat := 0) : ListQ :=
  { key := r.key as, also, after, before, desc, limit, cap }

/-- Read r at these arguments. -/
def read (r : Rel F) (as : List ByteArray) (limit : Option Nat := none) (desc : Bool := true) :
    View F (Answer F) :=
  View.read (r.query as limit desc)

/-- These relations' names are distinct (decide it for a concrete list). -/
def Distinct (rels : List (Rel F)) : Prop := (rels.map fun r => (r.kind, r.name)).Nodup

end Rel

/-- A family's keys, from its relations: each relation a fact is in. -/
def keysOf {F : Type} (rels : List (Rel F)) (f : F) : List ByteArray :=
  rels.filterMap fun r => (r.args f).map r.key

section
variable {F : Type}

theorem Rel.key_eq_iff {r r' : Rel F} {as as' : List ByteArray} :
    r.key as = r'.key as' ↔ r.kind = r'.kind ∧ r.name = r'.name ∧ as = as' := by
  constructor
  · intro h
    have := Codec.encode_inj h
    simp only [Prod.mk.injEq, String.toUTF8_eq_toByteArray, String.toByteArray_inj] at this
    exact this
  · rintro ⟨h1, h2, rfl⟩; simp [key, h1, h2]

theorem Rel.eq_of_names {rels : List (Rel F)} (hd : Rel.Distinct rels) {r r' : Rel F}
    (hr : r ∈ rels) (hr' : r' ∈ rels) (hk : r.kind = r'.kind) (hn : r.name = r'.name) : r = r' := by
  induction rels with
  | nil => cases hr
  | cons a t ih =>
    unfold Rel.Distinct at hd
    rw [List.map_cons, List.nodup_cons] at hd
    rcases List.mem_cons.1 hr with h1 | h1 <;> rcases List.mem_cons.1 hr' with h2 | h2
    · rw [h1, h2]
    · subst h1; exact (hd.1 (List.mem_map.2 ⟨r', h2, by simp [hk, hn]⟩)).elim
    · subst h2; exact (hd.1 (List.mem_map.2 ⟨r, h1, by simp [hk, hn]⟩)).elim
    · exact ih hd.2 h1 h2

/-- **Named keys are a fact's relations.** With distinct names, a fact
is filed under r's key at `as` exactly when it is in r at `as`. -/
theorem mem_keysOf {rels : List (Rel F)} (hd : Rel.Distinct rels) {r : Rel F} (hr : r ∈ rels)
    {as : List ByteArray} {f : F} : r.key as ∈ keysOf rels f ↔ r.args f = some as := by
  unfold keysOf
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨r', hr', h⟩
    cases ha : r'.args f with
    | none => rw [ha] at h; cases h
    | some as' =>
      rw [ha] at h; simp only [Option.map_some, Option.some.injEq] at h
      obtain ⟨hk, hn, rfl⟩ := Rel.key_eq_iff.1 h
      rw [← Rel.eq_of_names hd hr' hr hk hn]; exact ha
  · intro h; exact ⟨r, hr, by rw [h]; rfl⟩

theorem encNat_small {n : Nat} (h : n < 128) : Codec.encNat n = [n.toUInt8] := by
  rw [Codec.encNat]; simp [h]

/-- **A relation key is never an op's own key**: its first byte is its
kind name's length, an op key's is 0xFF. -/
theorem Rel.key_ne_opKey (r : Rel F) (hk : r.kind.toUTF8.size < 128) (as : List ByteArray) (y : Id) :
    r.key as ≠ opKey y := by
  intro h
  have := congrArg (fun b : ByteArray => b.data.toList.head?) h
  simp only [Rel.key, Codec.encode, opKey] at this
  change (Codec.encBytesL r.kind.toUTF8.data.toList ++ _).toArray.toList.head? = _ at this
  unfold Codec.encBytesL at this
  rw [Array.length_toList, encNat_small (n := r.kind.toUTF8.data.size) hk] at this
  simp at this
  have h2 := congrArg UInt8.toNat this
  have h3 := hk
  simp at h2 h3
  omega

/-! ## Lists of a relation -/

theorem perm_insertBy {α} (p : Pos × α) (l : List (Pos × α)) : (insertBy p l).Perm (p :: l) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons q t ih =>
    unfold insertBy; split
    · exact (ih.cons q).trans (List.Perm.swap p q t)
    · exact List.Perm.refl _

/-- Sorting only reorders. -/
theorem perm_sortPos {α} (l : List (Pos × α)) : (sortPos l).Perm l := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons p t ih => exact (perm_insertBy p (sortPos t)).trans (ih.cons p)

theorem mem_sortPos {α} {l : List (Pos × α)} {a : Pos × α} : a ∈ sortPos l ↔ a ∈ l :=
  (perm_sortPos l).mem_iff

variable {s : DB F}

theorem mem_matching [SortKey F] (k : ByteArray) (lim : Option Nat) {pf : Pos × F} :
    pf ∈ matching s { key := k, limit := lim } ↔
      ∃ x f, pf = ((SortKey.sortOf f, x), f) ∧ x ∈ s.idx k ∧ s.status x = some (.valid f) := by
  unfold matching
  rw [mem_sortPos, List.mem_filterMap]
  constructor
  · rintro ⟨x, hx, h⟩
    simp only [List.all_nil, ite_true] at h
    split at h
    · rename_i f hf; cases h; exact ⟨x, f, rfl, hx, hf⟩
    · cases h
  · rintro ⟨x, f, rfl, hx, hf⟩
    exact ⟨x, hx, by simp [hf]⟩

/-- Keeping and relabelling the elements of a list of distinct ids,
each by a value that names its id, gives distinct ids. -/
theorem nodup_filterMap_ids {β : Type} {g : Id → Option β} {idOf : β → Id}
    (hg : ∀ x b, g x = some b → idOf b = x) {l : List Id} (h : l.Nodup) :
    ((l.filterMap g).map idOf).Nodup := by
  unfold List.Nodup at *
  rw [List.pairwise_map, List.pairwise_filterMap]
  exact h.imp fun hne b hb c hc e => hne ((hg _ _ hb).symm.trans (e.trans (hg _ _ hc)))

/-- **A list names each op once.** Its rows' ids are distinct, so its
`total` (the matches' count) counts ops. -/
theorem matching_nodup [SortKey F] {fam : Family F} (h : Inv fam s) (q : ListQ) :
    ((matching s q).map (·.1.2)).Nodup := by
  unfold matching
  rw [((perm_sortPos _).map _).nodup_iff]
  refine nodup_filterMap_ids (fun x b hb => ?_) (h.nodup q.key)
  split at hb
  · split at hb
    · cases hb; rfl
    · cases hb
  · cases hb

/-- A whole, unranged list's rows are exactly its matches. -/
theorem mem_rows_all [SortKey F] (k : ByteArray) {pf : Pos × F} :
    pf ∈ (eval s { key := k, limit := none }).rows ↔
      ∃ x f, pf = ((SortKey.sortOf f, x), f) ∧ x ∈ s.idx k ∧ s.status x = some (.valid f) := by
  unfold eval
  simp only [ListQ.cut, ite_true, List.mem_reverse, List.mem_filter, ListQ.inside, Bool.and_self,
    and_true]
  exact mem_matching k none

theorem total_pos [SortKey F] (k : ByteArray) :
    0 < (eval s { key := k, limit := some 0 }).total ↔
      ∃ x f, x ∈ s.idx k ∧ s.status x = some (.valid f) := by
  show 0 < (matching s _).length ↔ _
  rw [List.length_pos_iff_exists_mem]
  constructor
  · rintro ⟨pf, h⟩; obtain ⟨x, f, _, hx, hf⟩ := (mem_matching k _).1 h; exact ⟨x, f, hx, hf⟩
  · rintro ⟨x, f, hx, hf⟩; exact ⟨_, (mem_matching k _).2 ⟨x, f, rfl, hx, hf⟩⟩

/-- **A relation lists exactly its Valid facts.** At rest, in a family
whose keys are its relations', op y is filed under r's key at `as` with
fact f exactly when y is Valid with f and f is in r at `as`. -/
theorem filed_rel {fam : Family F} {rels : List (Rel F)} (hk : fam.keys = keysOf rels)
    (hd : Rel.Distinct rels) {r : Rel F} (hr : r ∈ rels) (hs : r.kind.toUTF8.size < 128)
    (h : Inv fam s) (hq : s.queue = []) (as : List ByteArray) (y : Id) (f : F) :
    (y ∈ s.idx (r.key as) ∧ s.status y = some (.valid f)) ↔
      Spec fam s.ops y (.valid f) ∧ r.args f = some as := by
  constructor
  · rintro ⟨hy, hf⟩
    obtain ⟨g, hg, hkey⟩ := (h.idx _ y).1 hy
    rw [hf] at hg; cases hg
    refine ⟨(status_iff_spec h hq y _).1 hf, ?_⟩
    rcases List.mem_cons.1 hkey with he | hkey
    · exact absurd he (r.key_ne_opKey hs as y)
    · rw [hk] at hkey; exact (mem_keysOf hd hr).1 hkey
  · rintro ⟨hv, ha⟩
    have hf := (status_iff_spec h hq y _).2 hv
    refine ⟨(h.idx _ y).2 ⟨f, hf, List.mem_cons_of_mem _ ?_⟩, hf⟩
    rw [hk]; exact (mem_keysOf hd hr).2 ha

/-- The rows of a whole list of r at `as`, at rest. -/
theorem mem_rows_rel [SortKey F] {fam : Family F} {rels : List (Rel F)} (hk : fam.keys = keysOf rels)
    (hd : Rel.Distinct rels) {r : Rel F} (hr : r ∈ rels) (hs : r.kind.toUTF8.size < 128)
    (h : Inv fam s) (hq : s.queue = []) (as : List ByteArray) {pf : Pos × F} :
    pf ∈ (eval s (r.query as)).rows ↔
      ∃ y f, pf = ((SortKey.sortOf f, y), f) ∧ Spec fam s.ops y (.valid f) ∧ r.args f = some as := by
  show pf ∈ (eval s { key := r.key as, limit := none }).rows ↔ _
  rw [mem_rows_all]
  constructor
  · rintro ⟨y, f, rfl, hy⟩; exact ⟨y, f, rfl, (filed_rel hk hd hr hs h hq as y f).1 hy⟩
  · rintro ⟨y, f, rfl, hy⟩; exact ⟨y, f, rfl, (filed_rel hk hd hr hs h hq as y f).2 hy⟩

/-- Whether r at `as` holds any fact, at rest. -/
theorem total_rel [SortKey F] {fam : Family F} {rels : List (Rel F)} (hk : fam.keys = keysOf rels)
    (hd : Rel.Distinct rels) {r : Rel F} (hr : r ∈ rels) (hs : r.kind.toUTF8.size < 128)
    (h : Inv fam s) (hq : s.queue = []) (as : List ByteArray) :
    0 < (eval s (r.query as (limit := some 0))).total ↔
      ∃ y f, Spec fam s.ops y (.valid f) ∧ r.args f = some as := by
  show 0 < (eval s { key := r.key as, limit := some 0 }).total ↔ _
  rw [total_pos]
  constructor
  · rintro ⟨y, f, hy⟩; exact ⟨y, f, (filed_rel hk hd hr hs h hq as y f).1 hy⟩
  · rintro ⟨y, f, hy⟩; exact ⟨y, f, (filed_rel hk hd hr hs h hq as y f).2 hy⟩

end

end Engine
