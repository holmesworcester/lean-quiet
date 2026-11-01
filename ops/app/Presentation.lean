/- A bounded FIFO of explicit local sends awaiting visible committed
presentation. Positions use the same root/child Reader windows as chat.
Admission refuses when full; an older accepted obligation is never replaced.
-/
import engine.core.Query

namespace App.Presentation
open Engine

def capacity : Nat := 8

structure Entry where
  acceptance : Id
  community : Id
  root : Pos
  message : Pos
  deriving BEq, Inhabited

structure Queue where
  entries : List Entry := []
  bound : entries.length ≤ capacity := by decide

instance : Inhabited Queue := ⟨{}⟩

def Queue.head (q : Queue) : Option Entry := q.entries.head?

def Queue.contains (q : Queue) (message : Id) : Bool :=
  q.entries.any (·.message.2 == message)

def Queue.offer (q : Queue) (e : Entry) : Option Queue :=
  if h : (q.entries ++ [e]).length ≤ capacity then
    some ⟨q.entries ++ [e], h⟩
  else none

def Queue.pop (q : Queue) : Queue :=
  ⟨q.entries.drop 1, by simp only [List.length_drop]; exact Nat.le_trans (Nat.sub_le ..) q.bound⟩

def Queue.keep (q : Queue) (p : Entry → Bool) : Queue :=
  ⟨q.entries.filter p, Nat.le_trans (List.length_filter_le ..) q.bound⟩

/-- The invariant is carried by the actual runtime queue representation. -/
theorem bounded (q : Queue) : q.entries.length ≤ capacity := q.bound

/-- Successful admission appends; it does not overwrite an unpresented send. -/
theorem offer_append (q q' : Queue) (e : Entry) (h : q.offer e = some q') :
    q'.entries = q.entries ++ [e] := by
  unfold Queue.offer at h
  split at h
  · simp only [Option.some.injEq] at h
    cases h
    rfl
  · simp at h

/-- A full queue refuses a new send without manufacturing another state. -/
theorem offer_full (q : Queue) (e : Entry) (h : q.entries.length = capacity) :
    q.offer e = none := by simp [Queue.offer, h]

/-- A single recorded qualifying frame is acknowledged only by its exact
native completion ticket. The caller also revalidates message ownership,
lifetime and raster ticket before passing this candidate. -/
def acknowledge (candidate : Option (UInt64 × Id)) (completed : Option UInt64) : Option Id := do
  let (frame, message) ← candidate
  let done ← completed
  if done == frame then some message else none

theorem acknowledge_matches (candidate : Option (UInt64 × Id)) (completed : Option UInt64)
    (message : Id) (h : acknowledge candidate completed = some message) :
    ∃ frame, candidate = some (frame, message) ∧ completed = some frame := by
  cases candidate with
  | none => simp [acknowledge] at h
  | some c =>
    rcases c with ⟨frame, id⟩
    cases completed with
    | none => simp [acknowledge] at h
    | some done =>
      by_cases hd : done = frame
      · subst done
        simp [acknowledge] at h
        subst id
        exact ⟨frame, rfl, rfl⟩
      · simp [acknowledge, hd] at h

end App.Presentation
