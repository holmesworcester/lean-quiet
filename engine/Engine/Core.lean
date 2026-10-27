/-
The engine: ops in, verdicts out, everything persisted.

An op names the ops it requires by id. Its verdict is inductive and
local, as in libquiet's DESIGN.md ("Op types and facts: validity from
direct requirements"): an op citing an Invalid requirement is Invalid
(poisoning); once every requirement is Valid, the op type's validator
reads the op and the facts its requirements produced, and returns the
op's own fact or refuses it. Anything else waits, Unresolved.

`judge` is that rule on one op. The engine applies it incrementally:
`ingest` stores an op and queues it; `step` judges one queued op. A
judged op wakes the ops waiting on it; an op that cannot be judged yet
waits on each of its undecided requirements. Every table the engine
reads or writes goes through `Store`, so the same code runs on SQLite
(Engine/Sqlite.lean) and on the pure model the proofs use
(Engine/Model.lean). Nothing is held in memory between steps.
-/
namespace Engine

abbrev Id := ByteArray

/-- An op: its id (the hash of its canonical bytes, computed where the
bytes are decoded), its type, the ops it requires in slot order, and its
body. -/
structure Op where
  id : Id
  kind : UInt8
  reqs : List Id
  body : ByteArray
  deriving DecidableEq, Inhabited

/-- A decided op: Valid with the fact it produced, or Invalid. -/
inductive Verdict (F : Type) where
  | valid (f : F)
  | invalid
  deriving DecidableEq, Inhabited

/-- What an application supplies: each op type's validator, and the
index keys each fact is found under. -/
structure Family (F : Type) where
  validate : Op → List F → Option F
  keys : F → List ByteArray

/-- The facts of requirements that are all Valid, in order; none if any
is undecided or Invalid. -/
def allValid {F} : List (Option (Verdict F)) → Option (List F)
  | [] => some []
  | some (.valid f) :: rest => (allValid rest).map (f :: ·)
  | _ :: _ => none

/-- Whether any requirement is Invalid. -/
def anyInvalid {F} : List (Option (Verdict F)) → Bool
  | [] => false
  | some .invalid :: _ => true
  | _ :: rest => anyInvalid rest

/-- One op's verdict from its requirements' statuses: Invalid if any is
Invalid, the validator's answer if all are Valid, else none (wait). -/
def judge {F} (fam : Family F) (o : Op) (sts : List (Option (Verdict F))) : Option (Verdict F) :=
  if anyInvalid sts then some .invalid
  else match allValid sts with
    | some fs => some (match fam.validate o fs with
      | some f => .valid f
      | none => .invalid)
    | none => none

/-- The engine's tables: ops by id, verdicts by id, the ops waiting on
each op, the queue of ops to judge, and the index from keys to Valid
ops. -/
class Store (F : outParam Type) (m : Type → Type) where
  getOp : Id → m (Option Op)
  putOp : Op → m Unit
  getStatus : Id → m (Option (Verdict F))
  setStatus : Id → Verdict F → m Unit
  addWait : Id → Id → m Unit
  waiters : Id → m (List Id)
  clearWaiters : Id → m Unit
  push : Id → m Unit
  pop : m (Option Id)
  index : ByteArray → Id → m Unit
  lookup : ByteArray → m (List Id)

section
variable {F : Type} {m : Type → Type} [Monad m] [Store F m]
open Store

def statuses : List Id → m (List (Option (Verdict F)))
  | [] => pure []
  | r :: rest => do
    let s ← getStatus r
    let ss ← statuses rest
    pure (s :: ss)

/-- x waits on each of these requirements that is undecided. -/
def waitOn (x : Id) : List Id → m Unit
  | [] => pure ()
  | r :: rest => do
    if (← getStatus (F := F) r).isNone then addWait r x
    waitOn x rest

def pushAll : List Id → m Unit
  | [] => pure ()
  | w :: rest => do push (F := F) w; pushAll rest

def indexAll (x : Id) : List ByteArray → m Unit
  | [] => pure ()
  | k :: rest => do index (F := F) k x; indexAll x rest

/-- Store an op not seen before, and queue it. -/
def ingest (o : Op) : m Unit := do
  match ← getOp (F := F) o.id with
  | some _ => pure ()
  | none => do putOp (F := F) o; push (F := F) o.id

/-- Record x's verdict, index its fact, and wake the ops waiting on it. -/
def decide (fam : Family F) (x : Id) (v : Verdict F) : m Unit := do
  setStatus x v
  match v with
  | .valid f => indexAll x (fam.keys f)
  | .invalid => pure ()
  let ws ← waiters (F := F) x
  clearWaiters (F := F) x
  pushAll (F := F) ws

/-- Judge one queued op; false when the queue was empty. -/
def step (fam : Family F) : m Bool := do
  match ← pop (F := F) with
  | none => pure false
  | some x => do
    match ← getStatus (F := F) x with
    | some _ => pure true
    | none => do
      match ← getOp (F := F) x with
      | none => pure true
      | some o => do
        match judge fam o (← statuses o.reqs) with
        | some v => decide fam x v
        | none => waitOn (F := F) x o.reqs
        pure true

/-- Judge queued ops until the queue is empty, at most n of them. -/
def drain (fam : Family F) : Nat → m Unit
  | 0 => pure ()
  | n + 1 => do if ← step fam then drain fam n

end
end Engine
