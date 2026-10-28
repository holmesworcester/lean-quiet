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
  /-- Bytes copied in bulk (one allocation each copy). -/
  copied : Nat := 0
  deriving DecidableEq, Repr, Inhabited

namespace Meter

instance : Add Meter :=
  ⟨fun a b => ⟨a.reads + b.reads, a.lists + b.lists, a.writes + b.writes, a.hashes + b.hashes,
    a.hashed + b.hashed, a.spawns + b.spawns, a.work + b.work, a.copied + b.copied⟩⟩

instance : OfNat Meter 0 := ⟨{}⟩

@[simp] theorem reads_add (a b : Meter) : (a + b).reads = a.reads + b.reads := rfl
@[simp] theorem lists_add (a b : Meter) : (a + b).lists = a.lists + b.lists := rfl
@[simp] theorem writes_add (a b : Meter) : (a + b).writes = a.writes + b.writes := rfl
@[simp] theorem hashes_add (a b : Meter) : (a + b).hashes = a.hashes + b.hashes := rfl
@[simp] theorem hashed_add (a b : Meter) : (a + b).hashed = a.hashed + b.hashed := rfl
@[simp] theorem spawns_add (a b : Meter) : (a + b).spawns = a.spawns + b.spawns := rfl
@[simp] theorem work_add (a b : Meter) : (a + b).work = a.work + b.work := rfl
@[simp] theorem copied_add (a b : Meter) : (a + b).copied = a.copied + b.copied := rfl
@[simp] theorem reads_zero : (0 : Meter).reads = 0 := rfl
@[simp] theorem lists_zero : (0 : Meter).lists = 0 := rfl
@[simp] theorem writes_zero : (0 : Meter).writes = 0 := rfl
@[simp] theorem hashes_zero : (0 : Meter).hashes = 0 := rfl
@[simp] theorem hashed_zero : (0 : Meter).hashed = 0 := rfl
@[simp] theorem spawns_zero : (0 : Meter).spawns = 0 := rfl
@[simp] theorem work_zero : (0 : Meter).work = 0 := rfl
@[simp] theorem copied_zero : (0 : Meter).copied = 0 := rfl

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

end Engine
