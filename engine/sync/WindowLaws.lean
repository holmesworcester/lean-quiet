/-
Windowed rounds reconcile S (docs/SYNC.md, "Windows and order"): the
window from the round's floor, and every stored op of its room within
`params.depth` requirement steps of it, each sorted by its own time.
Both sides read S from their live index (`Index.over`), so RBSR over S
brings the windowed side what it lacks of the closure in the round
itself, and no round keeps closure state.

- `byId_add`: the index keeps each stored shared op's room and
  requirements by id; a later op of another id changes no entry.
- `over_mem`: S is exactly the room's items within k steps of the window
  (`Near`, over the index's `next`).
- `window_set_canonical`: S depends only on the stored ops (as a set,
  ids unique) and the floor, never on the order they were stored in nor
  on how the walk ran.
- `window_round_complete`: a round over S sends each side exactly the
  ids the other's S holds and its own lacks, in each window range
  (`exchange_complete` over S); `closure_delivered_under_bound`: if the
  full side's whole window closure lies within k steps, the windowed side
  ends the round holding or receiving all of it.
- `over_cost`: reading S's closure makes at most M · (|window| + |S|)
  lookups when no stored op of the room has more than M - 1 requirements:
  each id is expanded once. Plus the pass over the room's items every
  list-index answer makes (main's `within` does too): reading S is not
  O(log n); a per-floor tree on the bounds-port treap is the follow-on.
-/
import engine.sync.RoundLaws
import engine.sync.Walk
import engine.wire.NodeLaws
import engine.sync.RoundRun

namespace Engine.Sync
open Std

local instance : LawfulBEq ByteArray where
  eq_of_beq {a b} h := ByteArray.ext (eq_of_beq (show a.data == b.data from h))
  rfl {a} := show a.data == a.data from beq_self_eq_true a.data

section
variable {F : Type} (fam : Family F)

/-- **The index keeps each stored shared op's room and requirements by id**
(`byId_add`): adding o records it under its id when it has a room, and
leaves every other id's entry. -/
theorem byId_add (ix : Index) (o : Op) (x : Id) :
    (ix.add fam o).byId[x]? =
      match fam.room o with
      | some c => if o.id = x then some (c, o.reqs) else ix.byId[x]?
      | none => ix.byId[x]? := by
  unfold Index.add
  cases hr : fam.room o with
  | none => rfl
  | some c =>
    dsimp only
    split <;> simp only [HashMap.getElem?_insert, beq_iff_eq]

/-- Adding ops none of whose ids is x leaves x's entry. -/
theorem byId_foldl_other (ix : Index) (L : List Op) (x : Id) (h : ∀ o ∈ L, o.id ≠ x) :
    (L.foldl (Index.add fam) ix).byId[x]? = ix.byId[x]? := by
  induction L generalizing ix with
  | nil => rfl
  | cons o t ih =>
    rw [List.foldl_cons, ih _ (fun p hp => h p (List.mem_cons_of_mem _ hp)), byId_add]
    have := h o (List.mem_cons_self ..)
    split <;> simp [this]

/-- An entry the index holds survives adding ops that, under its id, are
the same op. -/
theorem byId_foldl_same (ix : Index) (L : List Op) (o : Op) (c : Id) (hr : fam.room o = some c)
    (h : ix.byId[o.id]? = some (c, o.reqs)) (hu : ∀ p ∈ L, p.id = o.id → p = o) :
    (L.foldl (Index.add fam) ix).byId[o.id]? = some (c, o.reqs) := by
  induction L generalizing ix with
  | nil => exact h
  | cons p t ih =>
    rw [List.foldl_cons]
    apply ih _ ?_ (fun q hq => hu q (List.mem_cons_of_mem _ hq))
    rw [byId_add]
    by_cases e : p.id = o.id
    · have := hu p (List.mem_cons_self ..) e
      subst this
      simp [hr]
    · split <;> simp [e, h]

/-- An entry after adding ops is the one before, or one of theirs. -/
theorem byId_foldl_from (ix : Index) (L : List Op) (x : Id) (v : Id × List Id)
    (h : (L.foldl (Index.add fam) ix).byId[x]? = some v) :
    ix.byId[x]? = some v ∨ ∃ o ∈ L, o.id = x ∧ ∃ c, fam.room o = some c ∧ v = (c, o.reqs) := by
  induction L generalizing ix with
  | nil => exact Or.inl h
  | cons p t ih =>
    rw [List.foldl_cons] at h
    rcases ih _ h with h | ⟨o, ho, e⟩
    · rw [byId_add] at h
      cases hr : fam.room p with
      | none => rw [hr] at h; exact Or.inl h
      | some c =>
        rw [hr] at h
        dsimp only at h
        split at h
        · rename_i e
          simp only [Option.some.injEq] at h
          exact Or.inr ⟨p, List.mem_cons_self .., e, c, hr, h.symm⟩
        · exact Or.inl h
    · exact Or.inr ⟨o, List.mem_cons_of_mem _ ho, e⟩

/-- **The cached index's entries are its stored ops'** (ids unique): an
id's entry is the room and requirements of the stored shared op of that
id; an id no stored shared op has has none. -/
theorem byId_ofOps (L : List Op) (hu : ∀ o ∈ L, ∀ p ∈ L, o.id = p.id → o = p) (x : Id)
    (v : Id × List Id) :
    (Index.ofOps fam L).byId[x]? = some v ↔
      ∃ o ∈ L, o.id = x ∧ ∃ c, fam.room o = some c ∧ v = (c, o.reqs) := by
  constructor
  · intro h
    rcases byId_foldl_from fam {} L x v h with h | e
    · simp at h
    · exact e
  · rintro ⟨o, ho, rfl, c, hr, rfl⟩
    obtain ⟨s, t, rfl⟩ := List.append_of_mem ho
    unfold Index.ofOps
    rw [List.foldl_append, List.foldl_cons]
    apply byId_foldl_same fam _ t o c hr
    · rw [byId_add, hr]; simp
    · intro p hp e
      exact hu p (List.mem_append_right _ (List.mem_cons_of_mem _ hp)) o
        (List.mem_append_right _ (List.mem_cons_self ..)) e

/-- **The cached index's items are its stored shared ops'**, each under
its key. -/
theorem items_ofOps (L : List Op) (r : Id) (a : Item) :
    a ∈ (Index.ofOps fam L).items r ↔ ∃ o ∈ L, fam.room o = some r ∧ a = (keyOf fam o, o.id) := by
  constructor
  · intro h
    rcases mem_items_foldl fam h with h | ⟨o, ho, e, hr⟩
    · simp [Index.items] at h
    · exact ⟨o, ho, hr, e⟩
  · rintro ⟨o, ho, hr, rfl⟩
    obtain ⟨b, hb, e⟩ := items_foldl_key fam (ix := {}) ho hr
    rcases mem_items_foldl fam hb with h | ⟨p, _, rfl, _⟩
    · simp [Index.items] at h
    · have := keyOf_id fam e
      simp only at e this
      rw [e, this] at hb
      exact hb

end

section
variable (ix : Index) (k : Nat) (r : Id) (f : Nat)

/-- **S is the room's items within k steps of the window** (`over_mem`):
for a windowed round (`1 < f`), an item is in S exactly when it is the
room's and within k requirement steps of the window from f, through the
index's stored ops of the room. -/
theorem over_mem (hf : 1 < f) (a : Item) :
    a ∈ ix.over k r f ↔ a ∈ ix.items r ∧ Near (ix.next r) (ix.windowIds r f) k a.2 := by
  rw [Index.over, if_neg (by omega)]
  simp only [List.mem_filter, Index.closure]
  rw [← walk_from (ix.next r) ix.cost (ix.windowIds r f) k a.2, HashSet.mem_iff_contains]

/-- S, read in key order, keeps the room's order. -/
theorem over_sorted (h : Sorted Prod.fst (ix.items r)) : Sorted Prod.fst (ix.over k r f) := by
  unfold Index.over
  split
  · exact h
  · exact h.filter _

/-- **What reading S's closure costs** (`over_cost`): when expanding any
id makes at most M lookups (its entry, and one per requirement), the
walk makes at most M times the window's size plus the ids it reaches. -/
theorem over_cost (M : Nat) (hc : ∀ x, ix.cost x ≤ M) :
    (ix.closure k r f).2 ≤ M * ((ix.windowIds r f).length + (ix.closure k r f).1.size) := by
  have := walk_cost (ix.next r) ix.cost M hc k (ix.windowIds r f) (HashSet.ofList (ix.windowIds r f))
  unfold Index.closure
  omega

end

/-- Near is a function of what `next` and the window hold. -/
theorem near_congr {n1 n2 : Id → List Id} {w1 w2 : List Id}
    (hn : ∀ x q, q ∈ n1 x ↔ q ∈ n2 x) (hw : ∀ x, x ∈ w1 ↔ x ∈ w2) :
    ∀ j x, Near n1 w1 j x ↔ Near n2 w2 j x
  | 0, x => hw x
  | j + 1, x => by
    simp only [Near]
    rw [near_congr hn hw j x]
    constructor
    · rintro (h | ⟨y, hy, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨y, (near_congr hn hw j y).1 hy, (hn y x).1 h⟩
    · rintro (h | ⟨y, hy, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨y, (near_congr hn hw j y).2 hy, (hn y x).2 h⟩

section
variable {F : Type} (fam : Family F)

/-- One step of the cached index's closure, in its stored ops (ids
unique): q is a requirement of the stored shared op x, and a stored op
of room r. -/
theorem next_ofOps (L : List Op) (hu : ∀ o ∈ L, ∀ p ∈ L, o.id = p.id → o = p) (r x q : Id) :
    q ∈ (Index.ofOps fam L).next r x ↔
      (∃ o ∈ L, o.id = x ∧ (fam.room o).isSome ∧ q ∈ o.reqs) ∧ ∃ p ∈ L, p.id = q ∧ fam.room p = some r := by
  have room : ∀ y, (Index.ofOps fam L).inRoom r y = true ↔ ∃ p ∈ L, p.id = y ∧ fam.room p = some r := by
    intro y
    unfold Index.inRoom
    cases hy : (Index.ofOps fam L).byId[y]? with
    | none =>
      simp only [Bool.false_eq_true, false_iff]
      rintro ⟨p, hp, rfl, hr⟩
      have := (byId_ofOps fam L hu p.id (r, p.reqs)).2 ⟨p, hp, rfl, r, hr, rfl⟩
      rw [hy] at this; cases this
    | some v =>
      obtain ⟨c, rs⟩ := v
      obtain ⟨p, hp, rfl, c', hr, e⟩ := (byId_ofOps fam L hu y (c, rs)).1 hy
      simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      simp only [beq_iff_eq]
      constructor
      · rintro rfl; exact ⟨p, hp, rfl, hr⟩
      · rintro ⟨p', hp', e', hr'⟩
        have := hu p' hp' p hp e'
        subst this
        rw [hr] at hr'; cases hr'; rfl
  unfold Index.next
  cases hx : (Index.ofOps fam L).byId[x]? with
  | none =>
    simp only [List.not_mem_nil, false_iff, not_and]
    rintro ⟨o, ho, rfl, hs, _⟩
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 hs
    have := (byId_ofOps fam L hu o.id (c, o.reqs)).2 ⟨o, ho, rfl, c, hc, rfl⟩
    rw [hx] at this; cases this
  | some v =>
    obtain ⟨c, rs⟩ := v
    obtain ⟨o, ho, rfl, c', hr, e⟩ := (byId_ofOps fam L hu x (c, rs)).1 hx
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    rw [List.mem_filter, room]
    constructor
    · rintro ⟨hq, hp⟩
      exact ⟨⟨o, ho, rfl, by simp [hr], hq⟩, hp⟩
    · rintro ⟨⟨o', ho', e, _, hq⟩, hp⟩
      have := hu o' ho' o ho e
      subst this
      exact ⟨hq, hp⟩

/-- The window's ids, in the cached index's stored ops. -/
theorem windowIds_ofOps (L : List Op) (r : Id) (f : Nat) (x : Id) :
    x ∈ (Index.ofOps fam L).windowIds r f ↔
      ∃ o ∈ L, fam.room o = some r ∧ inWindow f (keyOf fam o) = true ∧ o.id = x := by
  unfold Index.windowIds
  simp only [List.mem_map, List.mem_filter, items_ofOps]
  constructor
  · rintro ⟨a, ⟨⟨o, ho, hr, rfl⟩, hw⟩, rfl⟩
    exact ⟨o, ho, hr, hw, rfl⟩
  · rintro ⟨o, ho, hr, hw, rfl⟩
    exact ⟨_, ⟨⟨o, ho, hr, rfl⟩, hw⟩, rfl⟩

/-- **S depends only on the store and the window** (`window_set_canonical`):
two indexes built from the same stored ops (ids unique), in any order,
give a round the same set S in every room at every floor and depth. The
bound is the depth, a function of the ops; the walk's order never
decides what is in S. -/
theorem window_set_canonical (L1 L2 : List Op) (hL : ∀ o, o ∈ L1 ↔ o ∈ L2)
    (u1 : ∀ o ∈ L1, ∀ p ∈ L1, o.id = p.id → o = p) (k : Nat) (r : Id) (f : Nat) (a : Item) :
    a ∈ (Index.ofOps fam L1).over k r f ↔ a ∈ (Index.ofOps fam L2).over k r f := by
  have u2 : ∀ o ∈ L2, ∀ p ∈ L2, o.id = p.id → o = p :=
    fun o ho p hp e => u1 o ((hL o).2 ho) p ((hL p).2 hp) e
  have hi : ∀ a, a ∈ (Index.ofOps fam L1).items r ↔ a ∈ (Index.ofOps fam L2).items r := by
    intro a
    rw [items_ofOps, items_ofOps]
    exact ⟨fun ⟨o, ho, h⟩ => ⟨o, (hL o).1 ho, h⟩, fun ⟨o, ho, h⟩ => ⟨o, (hL o).2 ho, h⟩⟩
  by_cases hf : f ≤ 1
  · rw [Index.over_full _ _ _ _ hf, Index.over_full _ _ _ _ hf]
    exact hi a
  · rw [over_mem _ _ _ _ (by omega), over_mem _ _ _ _ (by omega), hi a]
    apply and_congr_right
    intro _
    apply near_congr
    · intro x q
      rw [next_ofOps fam L1 u1, next_ofOps fam L2 u2]
      constructor
      · rintro ⟨⟨o, ho, h⟩, ⟨p, hp, h'⟩⟩
        exact ⟨⟨o, (hL o).1 ho, h⟩, ⟨p, (hL p).1 hp, h'⟩⟩
      · rintro ⟨⟨o, ho, h⟩, ⟨p, hp, h'⟩⟩
        exact ⟨⟨o, (hL o).2 ho, h⟩, ⟨p, (hL p).2 hp, h'⟩⟩
    · intro x
      rw [windowIds_ofOps, windowIds_ofOps]
      exact ⟨fun ⟨o, ho, h⟩ => ⟨o, (hL o).1 ho, h⟩, fun ⟨o, ho, h⟩ => ⟨o, (hL o).2 ho, h⟩⟩

end

/-- The two ranges every round opens over cover every key. -/
theorem window_covers (key : Key) : ∃ w ∈ window 0, w.has key = true := by
  by_cases h : key.t = 0
  · refine ⟨⟨⟨0, 0⟩, some ⟨1, 0⟩⟩, by simp [window], ?_⟩
    rw [has_iff]
    refine ⟨?_, fun hi e => ?_⟩
    · simp [Key.lt_def]
    · cases e; simp [Key.lt_def, h]
  · refine ⟨⟨⟨1, 0⟩, none⟩, by simp [window], ?_⟩
    rw [has_iff]
    refine ⟨?_, fun hi e => by cases e⟩
    simp only [Key.lt_def]; omega

section
variable (cfg : Config) (r : Id) (k bound : Nat) (times : Nat → Nat) (states : Nat → RoundRun.State)

/-- **A round over S finds every difference of S** (`window_round_complete`):
`live_round_complete` for a run of the actual handler, each step answering
from its side's set S, the live index at the round's floor (`Index.over`:
the room for a full round; the window and its closure for a windowed one).
The round ends within the bound, and every item of S its holder keeps,
in an opening claim's range, the other side held at the opening, or holds
within the bound, or is offered or wanted on the actual wire. -/
theorem window_round_complete
    (run : RoundRun.Run cfg r k times states) (cur : RoundRun.Current r k states)
    (capacity : ∀ t, RoundRun.Capacity cfg r k (states t)) (hmax : 0 < cfg.maxIds)
    (U : List Item)
    (sub : ∀ t, ∀ a ∈ (states t).index.over cfg.params.depth r ((states t).receiving.beginRound k).roundFloor, a ∈ U)
    (sorted : ∀ t, Sorted Prod.fst
      ((states t).index.over cfg.params.depth r ((states t).receiving.beginRound k).roundFloor))
    (Z : Nat → List Item)
    (hZ : ∀ t, Z (t + 1) = (states t).index.over cfg.params.depth r ((states t).receiving.beginRound k).roundFloor)
    (named : ∀ t, Named Prod.fst Prod.snd
      ((states t).index.over cfg.params.depth r ((states t).receiving.beginRound k).roundFloor ++ Z t))
    (sound : ∀ t, Sound Prod.fst Prod.snd sha256
      ((states t).index.over cfg.params.depth r ((states t).receiving.beginRound k).roundFloor) (Z t))
    (ranks : ∀ cl ∈ (states 0).pending, RoundRun.rankIn U cl ≤ bound) :
    (∃ j, j ≤ bound + 1 ∧ (states j).pending = []) ∧
    ∀ (mine : Nat → Bool), (∀ t, mine (t + 1) = !mine t) → ∀ a : Item,
      (∀ t, mine t = true →
        a ∈ (states t).index.over cfg.params.depth r ((states t).receiving.beginRound k).roundFloor) →
      (mine 0 = false → a ∈ Z 0) →
      ∀ cl ∈ (states 0).pending, ∀ q, Honest Prod.fst Prod.snd sha256 (Z 0) q cl → q.has a.1 = true →
      (mine 0 = true ∧ a ∈ Z 0) ∨
      ∃ j, j ≤ bound ∧
        ((mine j = false ∧
          a ∈ (states j).index.over cfg.params.depth r ((states j).receiving.beginRound k).roundFloor) ∨
          RoundRun.SeenAt cfg r k (times j) a.2 (states j)) :=
  live_round_complete cfg r k bound times states run cur capacity hmax U sub sorted Z hZ named sound ranks

/-- **What fits the bound is found in one round** (`closure_delivered_under_bound`):
in such a run where one side (`mine` marks its steps) reads S from an
index ixB at a windowed floor f, if ixB's whole window closure, however
many steps down, lies within the depth bound, then every op of it (in an
opening claim's range) the other side held at the opening, or holds
within the round's bound, or is offered or wanted on the actual wire. -/
theorem closure_delivered_under_bound
    (run : RoundRun.Run cfg r k times states) (cur : RoundRun.Current r k states)
    (capacity : ∀ t, RoundRun.Capacity cfg r k (states t)) (hmax : 0 < cfg.maxIds)
    (U : List Item) (sub : ∀ t, ∀ a ∈ (states t).items cfg r k, a ∈ U)
    (sorted : ∀ t, Sorted Prod.fst ((states t).items cfg r k))
    (Z : Nat → List Item) (hZ : ∀ t, Z (t + 1) = (states t).items cfg r k)
    (named : ∀ t, Named Prod.fst Prod.snd ((states t).items cfg r k ++ Z t))
    (sound : ∀ t, Sound Prod.fst Prod.snd sha256 ((states t).items cfg r k) (Z t))
    (ranks : ∀ cl ∈ (states 0).pending, RoundRun.rankIn U cl ≤ bound)
    (mine : Nat → Bool) (alt : ∀ t, mine (t + 1) = !mine t)
    (ixB : Index) (f : Nat) (hf : 1 < f)
    (hB : ∀ t, mine t = true → ∀ b ∈ ixB.over cfg.params.depth r f, b ∈ (states t).items cfg r k)
    (hB0 : mine 0 = false → ∀ b ∈ ixB.over cfg.params.depth r f, b ∈ Z 0)
    (fits : ∀ x j, Near (ixB.next r) (ixB.windowIds r f) j x →
      Near (ixB.next r) (ixB.windowIds r f) cfg.params.depth x)
    (a : Item) (ha : a ∈ ixB.items r) (j : Nat) (hj : Near (ixB.next r) (ixB.windowIds r f) j a.2)
    (cl : Claim) (hcl : cl ∈ (states 0).pending) (q : Range)
    (honest : Honest Prod.fst Prod.snd sha256 (Z 0) q cl) (hq : q.has a.1 = true) :
    (mine 0 = true ∧ a ∈ Z 0) ∨
      ∃ j, j ≤ bound ∧ ((mine j = false ∧ a ∈ (states j).items cfg r k) ∨
        RoundRun.SeenAt cfg r k (times j) a.2 (states j)) := by
  have inB : a ∈ ixB.over cfg.params.depth r f := (over_mem ixB _ r f hf a).2 ⟨ha, fits _ _ hj⟩
  exact (live_round_complete cfg r k bound times states run cur capacity hmax U sub sorted Z hZ named
    sound ranks).2 mine alt a (fun t ht => hB t ht a inB) (fun h0 => hB0 h0 a inB) cl hcl q honest hq

end

end Engine.Sync
