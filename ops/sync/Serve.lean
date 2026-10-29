/-
A session's queue of wanted ids, served as a read program (`serve`,
`fetch`). The interpreter is the running store reader; trace runs that
same program with a lookup and records every read. Authorization
happens before an id joins the queue (`Conn.onWant`).
-/
import engine.core.Sync

namespace Engine.Sync

inductive Read (α : Type) where
  | done (a : α)
  | get (id : Id) (next : Option Op → Read α)

namespace Read

def map (f : α → β) : Read α → Read β
  | .done a => .done (f a)
  | .get i next => .get i (fun o => (next o).map f)

def run {m : Type → Type} [Monad m] (get : Id → m (Option Op)) : Read α → m α
  | .done a => pure a
  | .get i next => do (next (← get i)).run get

/-- Exactly the reads the interpreter performs, in order. -/
def trace (get : Id → Option Op) : Read α → α × List Id
  | .done a => (a, [])
  | .get i next => let (a, ids) := (next (get i)).trace get; (a, i :: ids)

theorem trace_map (f : α → β) (get : Id → Option Op) (p : Read α) :
    (p.map f).trace get = (f (p.trace get).1, (p.trace get).2) := by
  induction p with
  | done a => rfl
  | get i next ih => simp [map, trace, ih]

end Read

/-- Serve a queue from its front: read each id, send its op if shown,
until the ops sent reach the byte budget (that last op goes whole);
an id not stored, or not shown, leaves the queue unanswered. The ops
sent, and the ids left, unread. -/
def serve (shows : Op → Bool) (budget : Nat) : List Id → Read (List Op × List Id)
  | [] => .done ([], [])
  | i :: ids =>
    if budget = 0 then .done ([], i :: ids) else
    .get i fun found => match found with
      | none => serve shows budget ids
      | some o =>
        if shows o then
          if budget ≤ o.bytes.size then .done ([o], ids)
          else (serve shows (budget - o.bytes.size) ids).map fun p => (o :: p.1, p.2)
        else serve shows budget ids

/-- Read every id of the list, and keep the ops shown. -/
def fetch (shows : Op → Bool) : List Id → Read (List Op)
  | [] => .done []
  | i :: ids => .get i fun found => match found with
    | some o => if shows o then (fetch shows ids).map (o :: ·) else fetch shows ids
    | none => fetch shows ids

/-- Encoded payload bytes, before the transport's frame envelope. -/
def replyBytes (ops : List Op) : Nat := (ops.map (·.bytes.size)).sum

def largestOp (ops : List Op) : Nat := (ops.map (·.bytes.size)).foldr max 0

end Engine.Sync
