import engine.core.Query

/- A bounded FIFO of explicit local sends awaiting visible committed
presentation. Positions use the same root/child Reader windows as chat.
Admission refuses when full; an older accepted obligation is never replaced.
-/

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

/-- Consume a receipt independently of whether staging the next frame worked.
The caller has revalidated prior ownership and qualified the fresh pixels.
An unsuccessful new publication cannot replace an unresolved prior candidate. -/
def transition {α : Type} (qualifies : α → Bool) (prior fresh : Option α)
    (accepted : Bool) : Bool × Option α :=
  if prior.any qualifies || (accepted && fresh.any qualifies) then (true, none)
  else (false, if accepted then fresh else prior)

/-- Once the prior receipt is available, this completed transition releases
the obligation even if all subsequent publications are refused. -/
theorem transition_prior {α : Type} (qualifies : α → Bool) (prior fresh : Option α)
    (accepted : Bool) (h : prior.any qualifies = true) :
    transition qualifies prior fresh accepted = (true, none) := by
  simp [transition, h]

/-- Failed staging preserves an unresolved, still-current candidate. -/
theorem transition_rejected {α : Type} (qualifies : α → Bool) (prior fresh : Option α)
    (h : prior.any qualifies = false) :
    transition qualifies prior fresh false = (false, prior) := by
  simp [transition, h]

/-- A successful transition must use a prior receipt or an accepted new one. -/
theorem transition_sound {α : Type} (qualifies : α → Bool) (prior fresh : Option α)
    (accepted : Bool) (h : (transition qualifies prior fresh accepted).1 = true) :
    prior.any qualifies = true ∨ accepted = true ∧ fresh.any qualifies = true := by
  unfold transition at h
  split at h
  · rename_i receipt
    simpa only [Bool.or_eq_true, Bool.and_eq_true] using receipt
  · simp at h

end App.Presentation
