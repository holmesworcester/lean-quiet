/- Stable order for the running Node's catalog-retry pass. Ordinary
connection work and the outer UI-first selector retain their own order. -/
import Std

namespace Engine.Sync.RetryOrder

variable {α : Type} [BEq α]

/-- The actual admission decision. Candidates are considered one at a time;
one eligible candidate can claim each currently vacant socket reservation. -/
def claim (address : Option α) (candidate : Bool) (claimed : List α) : Bool × List α :=
  match address with
  | none => (false, claimed)
  | some a => if candidate && !claimed.contains a then (true, claimed ++ [a])
      else (false, claimed)

/-- Admission over a candidate stream. The Node feeds each observed candidate
as a singleton, immediately retaining or discarding its payload. `scan_append`
relates these actual calls without materializing all candidate frames. -/
def scan {β : Type} [BEq β] (address : α → Option β) (candidate : α → Bool) :
    List β → List α → List α × List β
  | claimed, [] => ([], claimed)
  | claimed, id :: rest =>
    let decision := claim (address id) (candidate id) claimed
    let tail := scan address candidate decision.2 rest
    (if decision.1 then id :: tail.1 else tail.1, tail.2)

/-- Keep live waiters in place. A newly observed session joins the tail. -/
def reconcile (live queued : List α) : List α :=
  queued.filter live.contains ++ live.filter (fun id => !queued.contains id)

/-- Only a generated retry offer spends a turn. Busy sockets, holes and
sweep boundaries cannot rotate a waiter behind later arrivals. -/
def offered (sent queued : List α) : List α :=
  queued.filter (fun id => !sent.contains id) ++ queued.filter sent.contains

/-- All earlier entries count, including currently ineligible sessions. -/
def rank (target : α) (queued : List α) : Nat :=
  queued.idxOf target

end Engine.Sync.RetryOrder
