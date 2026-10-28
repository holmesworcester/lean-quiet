/-
What code costs, as an effect of the code that runs (docs/PERF.md).

Code whose cost matters is written once, over a monad, and does its
costly work only through doors: a store read, a hash, a task spawned, a
join of two long numbers. Each door charges the meter (`tick`) for what
it does. Where the code runs, the meter is free: `Tick Id` (and every
runtime monad's) does nothing, and compiles away. Where the code is
measured, the same code runs in `CostT m`, which adds up what the doors
charged. A budget law is a theorem about that sum.

`CostT m` is a writer: an action returns what it charged beside its
value, and no action can read the meter. So what the code computes, and
which doors it goes through, cannot depend on what it was charged; the
value of a counted run is the value of the run (each pilot proves this
for its code: `val_*` theorems).

`Counted` (`CostT Id`) is for pure code; `CostT m` over a store's monad
(the engine's `Model`, `HeldM`, a world of nodes) counts what a node
does to its store (engine/core/CostStore.lean).
-/
namespace Engine

/-- What a run did, kind by kind. -/
@[ext] structure Meter where
  /-- Point reads of the store: an op, a status, a waiter list, a row. -/
  reads : Nat := 0
  /-- List queries (one SQL query each). -/
  lists : Nat := 0
  /-- Store writes: a row, or an op of a write turn. -/
  writes : Nat := 0
  /-- Calls to the hash. -/
  hashes : Nat := 0
  /-- Bytes given to the hash. -/
  hashed : Nat := 0
  /-- Tasks spawned. -/
  spawns : Nat := 0
  /-- Word operations of pure code: a byte read alone, a digit of a long
  number added or shifted. -/
  work : Nat := 0
  /-- Bytes copied in bulk (one allocation each copy): a byte string
  encoded, decoded or moved. -/
  copied : Nat := 0
  /-- B-tree descents in the store: what SQLite does for a point read, a
  write, or the start of a range (docs/PERF.md, the SQLite assumption:
  each costs at most log₂ N + 1 page visits for N rows). -/
  seeks : Nat := 0
  /-- Rows the store steps over in index order after a seek: a list's
  rows, a range count's. -/
  rows : Nat := 0
  deriving DecidableEq, Repr, Inhabited

namespace Meter

instance : Add Meter where
  add a b :=
    { reads := a.reads + b.reads, lists := a.lists + b.lists, writes := a.writes + b.writes
      hashes := a.hashes + b.hashes, hashed := a.hashed + b.hashed, spawns := a.spawns + b.spawns
      work := a.work + b.work, copied := a.copied + b.copied, seeks := a.seeks + b.seeks
      rows := a.rows + b.rows }

instance : OfNat Meter 0 := ⟨{}⟩

@[simp] theorem reads_add (a b : Meter) : (a + b).reads = a.reads + b.reads := rfl
@[simp] theorem lists_add (a b : Meter) : (a + b).lists = a.lists + b.lists := rfl
@[simp] theorem writes_add (a b : Meter) : (a + b).writes = a.writes + b.writes := rfl
@[simp] theorem hashes_add (a b : Meter) : (a + b).hashes = a.hashes + b.hashes := rfl
@[simp] theorem hashed_add (a b : Meter) : (a + b).hashed = a.hashed + b.hashed := rfl
@[simp] theorem spawns_add (a b : Meter) : (a + b).spawns = a.spawns + b.spawns := rfl
@[simp] theorem work_add (a b : Meter) : (a + b).work = a.work + b.work := rfl
@[simp] theorem copied_add (a b : Meter) : (a + b).copied = a.copied + b.copied := rfl
@[simp] theorem seeks_add (a b : Meter) : (a + b).seeks = a.seeks + b.seeks := rfl
@[simp] theorem rows_add (a b : Meter) : (a + b).rows = a.rows + b.rows := rfl
@[simp] theorem reads_zero : (0 : Meter).reads = 0 := rfl
@[simp] theorem lists_zero : (0 : Meter).lists = 0 := rfl
@[simp] theorem writes_zero : (0 : Meter).writes = 0 := rfl
@[simp] theorem hashes_zero : (0 : Meter).hashes = 0 := rfl
@[simp] theorem hashed_zero : (0 : Meter).hashed = 0 := rfl
@[simp] theorem spawns_zero : (0 : Meter).spawns = 0 := rfl
@[simp] theorem work_zero : (0 : Meter).work = 0 := rfl
@[simp] theorem copied_zero : (0 : Meter).copied = 0 := rfl
@[simp] theorem seeks_zero : (0 : Meter).seeks = 0 := rfl
@[simp] theorem rows_zero : (0 : Meter).rows = 0 := rfl

@[simp] theorem add_zero (a : Meter) : a + 0 = a := by ext <;> simp
@[simp] theorem zero_add (a : Meter) : 0 + a = a := by ext <;> simp
theorem add_assoc (a b c : Meter) : a + b + c = a + (b + c) := by ext <;> simp <;> omega
theorem add_comm (a b : Meter) : a + b = b + a := by ext <;> simp <;> omega

end Meter

/-- Charging the meter: free where code runs, counted where it is
measured. -/
class Tick (m : Type → Type) where
  tick : Meter → m Unit

export Tick (tick)

/-- Where code runs, nothing is counted. -/
@[reducible] def Tick.free {m : Type → Type} [Pure m] : Tick m := ⟨fun _ => pure ()⟩

instance : Tick Id := Tick.free

/-- m, with a meter: each action returns what it charged beside its
value. -/
def CostT (m : Type → Type) (α : Type) : Type := m (α × Meter)

namespace CostT
variable {m : Type → Type} [Monad m] {α β : Type}

@[inline] def run (x : CostT m α) : m (α × Meter) := x

@[inline] protected def pure (a : α) : CostT m α := (pure (a, 0) : m (α × Meter))

@[inline] protected def bind (x : CostT m α) (f : α → CostT m β) : CostT m β :=
  (do let p ← x.run; let q ← (f p.1).run; pure (q.1, p.2 + q.2) : m (β × Meter))

instance : Monad (CostT m) where
  pure := CostT.pure
  bind := CostT.bind

/-- An action of m, charged c. -/
@[inline] def charged (c : Meter) (x : m α) : CostT m α := (do let a ← x; pure (a, c) : m (α × Meter))

/-- An action of m, charged by what it returns: a list by its rows. -/
@[inline] def chargedBy (f : α → Meter) (x : m α) : CostT m α :=
  (do let a ← x; pure (a, f a) : m (α × Meter))

/-- An action of m, charged nothing. -/
@[inline] def lift (x : m α) : CostT m α := charged 0 x

instance : MonadLift m (CostT m) := ⟨lift⟩

instance : Tick (CostT m) := ⟨fun c => (pure ((), c) : m (Unit × Meter))⟩

theorem run_pure (a : α) : (pure a : CostT m α).run = pure (a, 0) := rfl

theorem run_bind (x : CostT m α) (f : α → CostT m β) :
    (x >>= f).run = (do let p ← x.run; let q ← (f p.1).run; pure (q.1, p.2 + q.2)) := rfl

omit [Monad m] in
theorem ext' {x y : CostT m α} (h : x.run = y.run) : x = y := h

instance [LawfulMonad m] : LawfulMonad (CostT m) := LawfulMonad.mk'
  (id_map := fun x => by
    apply ext'
    show (do let p ← x.run; let q ← (pure (p.1, 0) : m _); pure (q.1, p.2 + q.2)) = x.run
    simp)
  (pure_bind := fun a f => by
    apply ext'
    show (do let p ← (pure (a, 0) : m _); let q ← (f p.1).run; pure (q.1, p.2 + q.2)) = (f a).run
    simp)
  (bind_assoc := fun x f g => by
    apply ext'
    simp only [run_bind, bind_assoc, pure_bind, Meter.add_assoc])

end CostT

/-! ## Budgets over any monad

`Within g B x`: every run of x charges at most B in the meter's field g,
whatever m is (SQLite, a model, a world of nodes) and whatever its
doors return. It is `SatisfiesM` (Batteries) for the charge: x's runs
are runs of an action whose charges carry the bound. A store law
stated with it holds for every store. -/

section
variable {m : Type → Type} [Monad m] {α β : Type}

def Within (g : Meter → Nat) (B : Nat) (x : CostT m α) : Prop :=
  ∃ y : m { p : α × Meter // g p.2 ≤ B }, Subtype.val <$> y = x.run

/-- A meter field: it adds, and is 0 at 0. -/
class Field (g : Meter → Nat) : Prop where
  zero : g 0 = 0
  add : ∀ a b, g (a + b) = g a + g b

instance : Field Meter.reads := ⟨rfl, fun _ _ => rfl⟩
instance : Field Meter.lists := ⟨rfl, fun _ _ => rfl⟩
instance : Field Meter.writes := ⟨rfl, fun _ _ => rfl⟩
instance : Field Meter.hashes := ⟨rfl, fun _ _ => rfl⟩
instance : Field Meter.hashed := ⟨rfl, fun _ _ => rfl⟩
instance : Field Meter.spawns := ⟨rfl, fun _ _ => rfl⟩
instance : Field Meter.work := ⟨rfl, fun _ _ => rfl⟩
instance : Field Meter.copied := ⟨rfl, fun _ _ => rfl⟩
instance : Field Meter.seeks := ⟨rfl, fun _ _ => rfl⟩
instance : Field Meter.rows := ⟨rfl, fun _ _ => rfl⟩

variable [LawfulMonad m] {g : Meter → Nat}

theorem Within.mono {A B : Nat} {x : CostT m α} (h : A ≤ B) (hx : Within g A x) : Within g B x := by
  obtain ⟨y, hy⟩ := hx
  exact ⟨(fun p => ⟨p.1, Nat.le_trans p.2 h⟩) <$> y, by rw [← hy, Functor.map_map]⟩

theorem within_pure [Field g] (a : α) : Within g 0 (pure a : CostT m α) :=
  ⟨pure ⟨(a, 0), by rw [Field.zero (g := g)]; exact Nat.le_refl 0⟩, by rw [map_pure]; rfl⟩

theorem within_charged (c : Meter) (x : m α) : Within g (g c) (CostT.charged c x) :=
  ⟨(fun a => ⟨(a, c), Nat.le_refl _⟩) <$> x, by
    show _ = (do let a ← x; pure (a, c))
    rw [Functor.map_map, map_eq_pure_bind]⟩

theorem within_lift [Field g] (x : m α) : Within g 0 (CostT.lift x) := by
  have := within_charged (g := g) 0 x
  rwa [Field.zero (g := g)] at this

theorem within_tick (c : Meter) : Within g (g c) (tick c : CostT m Unit) :=
  ⟨pure ⟨((), c), Nat.le_refl _⟩, by rw [map_pure]; rfl⟩

/-- **Budgets add along a bind.** -/
theorem within_bind [Field g] {A B : Nat} {x : CostT m α} {f : α → CostT m β}
    (hx : Within g A x) (hf : ∀ a, Within g B (f a)) : Within g (A + B) (x >>= f) := by
  obtain ⟨y, hy⟩ := hx
  have hf' : ∀ a, ∃ z : m { q : β × Meter // g q.2 ≤ B }, Subtype.val <$> z = (f a).run := hf
  let z := fun a => Classical.choose (hf' a)
  have hz : ∀ a, (f a).run = Subtype.val <$> z a := fun a => (Classical.choose_spec (hf' a)).symm
  refine ⟨do
      let p ← y
      let q ← z p.1.1
      pure ⟨(q.1.1, p.1.2 + q.1.2), by rw [Field.add (g := g)]; exact Nat.add_le_add p.2 q.2⟩, ?_⟩
  show _ = (do let p ← x.run; let q ← (f p.1).run; pure (q.1, p.2 + q.2))
  rw [← hy]
  simp only [hz, map_bind, bind_map_left, map_pure]

theorem within_bind_le [Field g] {A B C : Nat} {x : CostT m α} {f : α → CostT m β}
    (hx : Within g A x) (hf : ∀ a, Within g B (f a)) (h : A + B ≤ C) : Within g C (x >>= f) :=
  (within_bind hx hf).mono h

omit [LawfulMonad m] in
theorem within_ite {c : Prop} [Decidable c] {B : Nat} {x y : CostT m α}
    (hx : c → Within g B x) (hy : ¬ c → Within g B y) : Within g B (if c then x else y) := by
  by_cases h : c
  · rw [ite_eq_left h]; exact hx h
  · rw [ite_eq_right h]; exact hy h

/-! ### What a door returns

A bound can depend on what the store holds: an op's requirements, a
waiter list. `Sat P y` (Batteries' `SatisfiesM`) says every run of an
action of m returns a value with P: an assumption about the store the
code runs on, stated per door. `WithinP` carries it through a counted
door, and `within_bindP` lets the rest of the code use it. -/

omit [LawfulMonad m] in
/-- Every run of y returns a value satisfying P. -/
def Sat (P : α → Prop) (y : m α) : Prop := ∃ z : m { a // P a }, Subtype.val <$> z = y

/-- Every run of x charges at most B in g, and returns a value with P. -/
def WithinP (g : Meter → Nat) (B : Nat) (P : α → Prop) (x : CostT m α) : Prop :=
  ∃ y : m { p : α × Meter // g p.2 ≤ B ∧ P p.1 }, Subtype.val <$> y = x.run

theorem WithinP.within {B : Nat} {P : α → Prop} {x : CostT m α} (h : WithinP g B P x) : Within g B x :=
  let ⟨y, hy⟩ := h
  ⟨(fun p => ⟨p.1, p.2.1⟩) <$> y, by rw [← hy, Functor.map_map]⟩

/-- A door charged by its value, whose values all have P. -/
theorem withinP_chargedBy {B : Nat} {P : α → Prop} {f : α → Meter} {y : m α} (hy : Sat P y)
    (hf : ∀ a, P a → g (f a) ≤ B) : WithinP g B P (CostT.chargedBy f y) := by
  obtain ⟨z, hz⟩ := hy
  refine ⟨(fun a => ⟨(a.1, f a.1), hf a.1 a.2, a.2⟩) <$> z, ?_⟩
  show _ = (do let a ← y; pure (a, f a))
  rw [← hz, Functor.map_map, bind_map_left, map_eq_pure_bind]

theorem withinP_charged {P : α → Prop} {y : m α} (c : Meter) (hy : Sat P y) :
    WithinP g (g c) P (CostT.charged c y) :=
  withinP_chargedBy (f := fun _ => c) hy fun _ _ => Nat.le_refl _

/-- **Budgets add along a bind whose rest may use what the first part
returned.** -/
theorem within_bindP [Field g] {A B : Nat} {P : α → Prop} {x : CostT m α} {f : α → CostT m β}
    (hx : WithinP g A P x) (hf : ∀ a, P a → Within g B (f a)) : Within g (A + B) (x >>= f) := by
  obtain ⟨y, hy⟩ := hx
  have hf' : ∀ a : { a // P a }, ∃ z : m { q : β × Meter // g q.2 ≤ B }, Subtype.val <$> z = (f a.1).run :=
    fun a => hf a.1 a.2
  let z := fun a => Classical.choose (hf' a)
  have hz : ∀ a : { a // P a }, (f a.1).run = Subtype.val <$> z a :=
    fun a => (Classical.choose_spec (hf' a)).symm
  refine ⟨do
      let p ← y
      let q ← z ⟨p.1.1, p.2.2⟩
      pure ⟨(q.1.1, p.1.2 + q.1.2), by rw [Field.add (g := g)]; exact Nat.add_le_add p.2.1 q.2⟩, ?_⟩
  show _ = (do let p ← x.run; let q ← (f p.1).run; pure (q.1, p.2 + q.2))
  rw [← hy, bind_map_left, map_bind]
  refine congrArg (y >>= ·) (funext fun p => ?_)
  show _ = (f p.1.1).run >>= _
  rw [hz ⟨p.1.1, p.2.2⟩, map_bind, bind_map_left]
  simp only [map_pure]

theorem within_bindP_le [Field g] {A B C : Nat} {P : α → Prop} {x : CostT m α} {f : α → CostT m β}
    (hx : WithinP g A P x) (hf : ∀ a, P a → Within g B (f a)) (h : A + B ≤ C) :
    Within g C (x >>= f) :=
  (within_bindP hx hf).mono h

end

/-! ## From counts to time

A law counts; time is the count weighed. `Units` are what one unit of
each kind costs on the slowest phone a guarantee is for (measured, not
proven: docs/PERF.md has the table). `Meter.time U N` is a meter's time
on a store of N rows, and it is a `Field` like any count, so a budget
proven for every field is a time bound for every phone (`Costs`). -/

/-- **The SQLite assumption** (docs/PERF.md): a seek in a B-tree of N
rows visits at most log₂ N + 1 pages, since every page of SQLite's
tables and indexes but the root holds at least two entries; a row after
the seek, in index order, is the next entry of the same or the next
leaf page. Not proven: it is SQLite's file format. -/
def levels (N : Nat) : Nat := Nat.log2 N + 1

/-- What one unit of each kind costs (a phone's nanoseconds, say). -/
structure Units where
  read : Nat := 0
  list : Nat := 0
  write : Nat := 0
  hash : Nat := 0
  hashByte : Nat := 0
  spawn : Nat := 0
  cell : Nat := 0
  byte : Nat := 0
  /-- A page visited in a seek: `levels N` of them per seek. -/
  page : Nat := 0
  row : Nat := 0

/-- A meter's time on a store of N rows. -/
def Meter.time (U : Units) (N : Nat) (c : Meter) : Nat :=
  c.reads * U.read + c.lists * U.list + c.writes * U.write + c.hashes * U.hash +
    c.hashed * U.hashByte + c.spawns * U.spawn + c.work * U.cell + c.copied * U.byte +
    c.seeks * (U.page * levels N) + c.rows * U.row

instance (U : Units) (N : Nat) : Field (Meter.time U N) where
  zero := by simp [Meter.time]
  add a b := by simp only [Meter.time, Meter.reads_add, Meter.lists_add, Meter.writes_add,
    Meter.hashes_add, Meter.hashed_add, Meter.spawns_add, Meter.work_add, Meter.copied_add,
    Meter.seeks_add, Meter.rows_add, Nat.add_mul]; omega

namespace Meter

/-- One meter at most another, kind by kind. -/
instance : LE Meter := ⟨fun a b => a.reads ≤ b.reads ∧ a.lists ≤ b.lists ∧ a.writes ≤ b.writes ∧
  a.hashes ≤ b.hashes ∧ a.hashed ≤ b.hashed ∧ a.spawns ≤ b.spawns ∧ a.work ≤ b.work ∧
  a.copied ≤ b.copied ∧ a.seeks ≤ b.seeks ∧ a.rows ≤ b.rows⟩

/-- Kind by kind, what b has beyond a. -/
def diff (b a : Meter) : Meter :=
  { reads := b.reads - a.reads, lists := b.lists - a.lists, writes := b.writes - a.writes
    hashes := b.hashes - a.hashes, hashed := b.hashed - a.hashed, spawns := b.spawns - a.spawns
    work := b.work - a.work, copied := b.copied - a.copied, seeks := b.seeks - a.seeks
    rows := b.rows - a.rows }

theorem le_iff {a b : Meter} : a ≤ b ↔ a.reads ≤ b.reads ∧ a.lists ≤ b.lists ∧ a.writes ≤ b.writes ∧
    a.hashes ≤ b.hashes ∧ a.hashed ≤ b.hashed ∧ a.spawns ≤ b.spawns ∧ a.work ≤ b.work ∧
    a.copied ≤ b.copied ∧ a.seeks ≤ b.seeks ∧ a.rows ≤ b.rows := Iff.rfl

instance (a b : Meter) : Decidable (a ≤ b) := decidable_of_iff _ le_iff.symm

theorem add_diff {a b : Meter} (h : a ≤ b) : a + b.diff a = b := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  ext <;> simp [diff] <;> omega

end Meter

/-- `a ≤ b` between meters, kind by kind, by `omega`. -/
macro "meter_le" : tactic => `(tactic|
  (refine Meter.le_iff.2 ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp <;> omega))

/-- **Every field is monotone**: it adds, and a meter at most another is
it plus what is left. -/
theorem Field.mono {g : Meter → Nat} [Field g] {a b : Meter} (h : a ≤ b) : g a ≤ g b := by
  rw [← Meter.add_diff h, Field.add (g := g)]; exact Nat.le_add_right _ _

/-! ## The bound template: `Costs`

`Costs B x`: x costs at most the meter B, in every field, and so in its
time on every phone (`Costs.time`). A law is stated as `Costs B x`
with B a meter built from the inputs and the Budget (a3's record of
constants); it is proven with the rules below, one per way code is put
together; and it comes with a mutant control (the old code, or the
obvious wrong one, shown over B). docs/PERF.md works an example. -/

section
variable {m : Type → Type} [Monad m] {α β : Type}

def Costs (B : Meter) (x : CostT m α) : Prop := ∀ (g : Meter → Nat) [Field g], Within g (g B) x

variable [LawfulMonad m]

omit [LawfulMonad m] in
theorem Costs.field {B : Meter} {x : CostT m α} (h : Costs B x) (g : Meter → Nat) [Field g] :
    Within g (g B) x := h g

omit [LawfulMonad m] in
/-- **A time bound**, on a store of N rows, for every phone's units. -/
theorem Costs.time {B : Meter} {x : CostT m α} (h : Costs B x) (U : Units) (N : Nat) :
    Within (Meter.time U N) (B.time U N) x := h _

theorem Costs.mono {A B : Meter} {x : CostT m α} (h : A ≤ B) (hx : Costs A x) : Costs B x :=
  fun g _ => (hx g).mono (Field.mono h)

theorem costs_pure (a : α) : Costs 0 (pure a : CostT m α) := fun g _ => by
  rw [Field.zero (g := g)]; exact within_pure a

theorem costs_charged (c : Meter) (y : m α) : Costs c (CostT.charged c y) := fun _ _ =>
  within_charged c y

theorem costs_lift (y : m α) : Costs 0 (CostT.lift y) := costs_charged 0 y

theorem costs_tick (c : Meter) : Costs c (tick c : CostT m Unit) := fun _ _ => within_tick c

theorem costs_bind {A B : Meter} {x : CostT m α} {f : α → CostT m β} (hx : Costs A x)
    (hf : ∀ a, Costs B (f a)) : Costs (A + B) (x >>= f) := fun g _ => by
  rw [Field.add (g := g)]; exact within_bind (hx g) (fun a => hf a g)

theorem costs_bind_le {A B C : Meter} {x : CostT m α} {f : α → CostT m β} (hx : Costs A x)
    (hf : ∀ a, Costs B (f a)) (h : A + B ≤ C) : Costs C (x >>= f) :=
  (costs_bind hx hf).mono h

omit [LawfulMonad m] in
theorem costs_ite {c : Prop} [Decidable c] {B : Meter} {x y : CostT m α} (hx : c → Costs B x)
    (hy : ¬ c → Costs B y) : Costs B (if c then x else y) := by
  by_cases h : c
  · rw [ite_eq_left h]; exact hx h
  · rw [ite_eq_right h]; exact hy h

/-- A door charged by its value, whose values all have P, then code that
may use P. -/
theorem costs_bindP {A B : Meter} {P : α → Prop} {f : α → Meter} {y : m α} {k : α → CostT m β}
    (hy : Sat P y) (hf : ∀ a, P a → f a ≤ A) (hk : ∀ a, P a → Costs B (k a)) :
    Costs (A + B) (CostT.chargedBy f y >>= k) := fun g _ => by
  rw [Field.add (g := g)]
  exact within_bindP (withinP_chargedBy hy fun a ha => Field.mono (hf a ha)) fun a ha => hk a ha g

end

/-! ## Pure code, counted -/

/-- Pure code, counted: a value and what computing it charged. -/
abbrev Counted := CostT Id

namespace Counted
variable {α β : Type}

/-- What a counted run computed. -/
def val (x : Counted α) : α := (Id.run x.run).1

/-- What a counted run charged. -/
def cost (x : Counted α) : Meter := (Id.run x.run).2

@[simp] theorem val_pure (a : α) : val (pure a : Counted α) = a := rfl
@[simp] theorem cost_pure (a : α) : cost (pure a : Counted α) = 0 := rfl
@[simp] theorem val_bind (x : Counted α) (f : α → Counted β) : val (x >>= f) = val (f (val x)) := rfl
@[simp] theorem cost_bind (x : Counted α) (f : α → Counted β) :
    cost (x >>= f) = cost x + cost (f (val x)) := rfl
@[simp] theorem val_map (g : α → β) (x : Counted α) : val (g <$> x) = g (val x) := rfl
@[simp] theorem cost_map (g : α → β) (x : Counted α) : cost (g <$> x) = cost x := by
  show cost x + 0 = cost x; simp
@[simp] theorem val_tick (c : Meter) : val (tick c : Counted Unit) = () := rfl
@[simp] theorem cost_tick (c : Meter) : cost (tick c : Counted Unit) = c := rfl

theorem ext {x y : Counted α} (h1 : val x = val y) (h2 : cost x = cost y) : x = y := by
  show (Id.run x.run) = (Id.run y.run)
  exact Prod.ext h1 h2

/-! ### Arrays built by a counted function -/

@[simp] theorem val_ofFnM {n : Nat} (f : Fin n → Counted α) :
    val (Array.ofFnM f) = Array.ofFn fun i => val (f i) := by
  induction n with
  | zero => rw [Array.ofFnM_zero, Array.ofFn_zero]; rfl
  | succ n ih =>
    rw [Array.ofFnM_succ', val_bind, val_bind, val_pure, ih, Array.ofFn_succ']

/-- **A field of an array's cost is the sum of its elements'.** `g` is
one of the meter's fields (it adds). -/
theorem field_ofFnM (g : Meter → Nat) (hg0 : g 0 = 0) (hga : ∀ a b, g (a + b) = g a + g b)
    {n : Nat} (f : Fin n → Counted α) (b : Nat → Nat) (hb : ∀ i : Fin n, g (cost (f i)) = b i) :
    g (cost (Array.ofFnM f)) = ((List.range n).map b).sum := by
  induction n with
  | zero => rw [Array.ofFnM_zero, cost_pure, hg0]; rfl
  | succ n ih =>
    rw [Array.ofFnM_succ, cost_bind, cost_bind, cost_pure, hga, hga,
      ih (fun i => f i.castSucc) (fun i => hb i.castSucc), List.range_succ, List.map_append,
      List.sum_append, hb (Fin.last n), hg0]
    simp

theorem field_ofFnM_le (g : Meter → Nat) (hg0 : g 0 = 0) (hga : ∀ a b, g (a + b) = g a + g b)
    {n : Nat} (f : Fin n → Counted α) (b : Nat → Nat) (hb : ∀ i : Fin n, g (cost (f i)) ≤ b i) :
    g (cost (Array.ofFnM f)) ≤ ((List.range n).map b).sum := by
  induction n with
  | zero => rw [Array.ofFnM_zero, cost_pure, hg0]; exact Nat.zero_le _
  | succ n ih =>
    rw [Array.ofFnM_succ, cost_bind, cost_bind, cost_pure, hga, hga, hg0, List.range_succ,
      List.map_append, List.sum_append]
    have := ih (fun i => f i.castSucc) (fun i => hb i.castSucc)
    have := hb (Fin.last n)
    simp only [Fin.val_last, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at *
    omega

end Counted

/-! ## Monads with a value

`Valued` names what `Id` (where code runs) and `Counted` (where it is
measured) share: a value that binds compose and ticks leave alone. So a
counted function is proven once to compute its spec, at any `Valued`
monad, and its cost law is about the code that runs. (a3's
ops/sync/Sum.lean had this class first, as `Engine.Sync.Valued`.) -/

class Valued (m : Type → Type) [Monad m] [Tick m] where
  val : {α : Type} → m α → α
  val_pure {α : Type} (a : α) : val (pure a : m α) = a
  val_bind {α β : Type} (x : m α) (f : α → m β) : val (x >>= f) = val (f (val x))
  val_tick (c : Meter) : val (tick c : m Unit) = ()

instance : Valued Id where
  val x := Id.run x
  val_pure _ := rfl
  val_bind _ _ := rfl
  val_tick _ := rfl

instance : Valued Counted where
  val := Counted.val
  val_pure _ := rfl
  val_bind _ _ := rfl
  val_tick _ := rfl

end Engine
