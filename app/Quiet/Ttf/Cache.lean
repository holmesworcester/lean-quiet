/-
A bounded FIFO glyph cache. The hash index contains slot numbers, never
bitmaps; only the fixed ring retains coverage. The running put operation
checks both byte charge and index capacity. Laws cover that operation,
not a second cache model. Runtime allocator/scratch memory is not modeled.
-/
import Quiet.Ttf.Raster

namespace Ttf.Cache

/-- Four MiB including a conservative per-entry/capacity charge. -/
def budget : Nat := 4 * 1024 * 1024
def capacity : Nat := 1024

structure Key where
  font : Nat
  glyph : Nat
  size : Nat
  cell : Nat
  deriving BEq, Hashable, Inhabited

structure Entry where
  key : Key
  bitmap : Bitmap
  deriving Inhabited

/-- Twice the payload allows ByteArray growth capacity; 512 bytes charges
bitmap, key, option, hash node and slot metadata. Not a bound on process RSS. -/
def charge (e : Entry) : Nat := 2 * e.bitmap.pixels.size + 512

structure Store where
  slots : Array (Option Entry)
  index : Std.HashMap Key Nat
  hand : Nat
  deriving Inhabited

def empty : Store := ⟨Array.replicate capacity none, {}, 0⟩

def bytes (s : Store) : Nat :=
  16 * capacity + (s.slots.toList.map (fun e => (e.map charge).getD 0)).sum

def Valid (s : Store) : Prop :=
  bytes s ≤ budget ∧ s.slots.size = capacity ∧ s.index.size ≤ capacity ∧ s.hand < capacity
  deriving Decidable

def checked (s : Store) : Store := if Valid s then s else empty

/-- Checking the key in the slot also makes stale indices harmless. -/
def get? (s : Store) (key : Key) : Option Bitmap := do
  let i ← s.index[key]?
  let e ← (← s.slots[i]?)
  if e.key == key then some e.bitmap else none

private def remove (s : Store) (i : Nat) : Store :=
  match (s.slots[i]?.getD none) with
  | none => s
  | some e => { s with slots := s.slots.modify i (fun _ => none), index := s.index.erase e.key }

/-- Insertion order eviction; hits leave the ring alone. Oversized glyphs
can be painted by the caller but are not retained. -/
def putRaw (s : Store) (key : Key) (bitmap : Bitmap) : Store := Id.run do
  let e := Entry.mk key bitmap
  if charge e + 16 * capacity > budget then return s
  if (get? s key).isSome then return s
  let mut s := remove s s.hand
  s := { s with slots := s.slots.modify s.hand (fun _ => some e), index := s.index.insert key s.hand, hand := (s.hand + 1) % capacity }
  let mut used := bytes s
  for _ in [0:capacity] do
    if used ≤ budget then break
    let old := ((s.slots[s.hand]?.getD none).map charge).getD 0
    s := remove s s.hand
    s := { s with hand := (s.hand + 1) % capacity }
    used := used - old
  return s

def put (s : Store) (key : Key) (bitmap : Bitmap) : Store := checked (putRaw s key bitmap)

theorem empty_valid : Valid empty := by
  simp only [Valid, bytes, empty, Array.toList_replicate, List.map_replicate,
    Option.map_none, Option.getD_none, List.sum_replicate_nat, Nat.mul_zero, Nat.add_zero,
    Array.size_replicate, Std.HashMap.size_empty]
  decide

theorem checked_valid (s : Store) : Valid (checked s) := by
  unfold checked
  split
  · assumption
  · exact empty_valid

/-- This is the insertion used by the shared runtime cache. -/
theorem put_bound (s : Store) (key : Key) (bitmap : Bitmap) :
    bytes (put s key bitmap) ≤ budget ∧ (put s key bitmap).slots.size = capacity ∧
    (put s key bitmap).index.size ≤ capacity ∧ (put s key bitmap).hand < capacity :=
  checked_valid (putRaw s key bitmap)

def payload (s : Store) : Nat :=
  (s.slots.toList.map (fun e => (e.map (·.bitmap.pixels.size)).getD 0)).sum

theorem payload_le_bytes (s : Store) : payload s ≤ bytes s := by
  have aux : ∀ l : List (Option Entry),
      (l.map (fun e => (e.map (·.bitmap.pixels.size)).getD 0)).sum ≤
        (l.map (fun e => (e.map charge).getD 0)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons e t ih =>
      cases e <;> simp [charge] at * <;> omega
  have h := aux s.slots.toList
  unfold payload bytes
  omega

theorem put_payload_bound (s : Store) (key : Key) (bitmap : Bitmap) :
    payload (put s key bitmap) ≤ budget :=
  Nat.le_trans (payload_le_bytes _) (put_bound s key bitmap).1

end Ttf.Cache
