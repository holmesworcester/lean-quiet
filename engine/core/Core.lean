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
import engine.core.Codec

namespace Engine

abbrev Id := ByteArray

/-- SHA-256 (libsodium, through native/glue.c). The proofs treat it as
an unknown function: wherever they need two ops' ids to differ, they
assume it has no collision on those ops' bytes (`Distinct`). -/
@[extern "le_sha256"] opaque sha256 (b : @& ByteArray) : ByteArray

/-- An op: its type, the ops it requires in slot order, and its body.
Its id is the SHA-256 of its bytes (`Op.bytes`), set by `Op.make`; any
other construction must prove the same id (`id_eq`), so no one can name an op: whoever builds one
or decodes one from bytes gets the id its bytes give. Its bytes are the
same on the wire and in SQLite. -/
structure Op where
  id : Id
  kind : UInt8
  reqs : List Id
  body : ByteArray
  id_eq : id = sha256 (Codec.encode (kind, reqs, body))

/-- The op with this type, requirements and body, named by its bytes. -/
def Op.make (kind : UInt8) (reqs : List Id) (body : ByteArray) : Op :=
  ⟨sha256 (Codec.encode (kind, reqs, body)), kind, reqs, body, rfl⟩

@[simp] theorem Op.make_kind (k : UInt8) (r : List Id) (b : ByteArray) : (Op.make k r b).kind = k := rfl
@[simp] theorem Op.make_reqs (k : UInt8) (r : List Id) (b : ByteArray) : (Op.make k r b).reqs = r := rfl
@[simp] theorem Op.make_body (k : UInt8) (r : List Id) (b : ByteArray) : (Op.make k r b).body = b := rfl

/-- Ops with the same type, requirements and body are the same op. -/
theorem Op.ext' {a b : Op} (hk : a.kind = b.kind) (hr : a.reqs = b.reqs) (hb : a.body = b.body) :
    a = b := by
  obtain ⟨i, k, r, d, h⟩ := a
  obtain ⟨i', k', r', d', h'⟩ := b
  simp only at hk hr hb
  subst hk hr hb h h'
  rfl

theorem Op.make_eta (o : Op) : Op.make o.kind o.reqs o.body = o := Op.ext' rfl rfl rfl

instance : DecidableEq Op := fun a b =>
  if h : a.kind = b.kind ∧ a.reqs = b.reqs ∧ a.body = b.body then
    isTrue (Op.ext' h.1 h.2.1 h.2.2)
  else
    isFalse fun e => h (by subst e; exact ⟨rfl, rfl, rfl⟩)

instance : Inhabited Op := ⟨Op.make 0 [] .empty⟩

open Codec in
instance : Codec Op where
  enc o := enc (o.kind, o.reqs, o.body)
  dec bs := (dec bs : Option ((UInt8 × List Id × ByteArray) × List UInt8)).map
    fun p => (Op.make p.1.1 p.1.2.1 p.1.2.2, p.2)
  round o rest := by simp [round, Op.make_eta]

/-- An op's bytes: what travels, what SQLite stores, what its id hashes. -/
def Op.bytes (o : Op) : ByteArray := Codec.encode o

/-- The op these bytes are, if they are one op's bytes exactly. -/
def Op.decode (b : ByteArray) : Option Op := Codec.decode b

/-- **An op's id is the hash of its bytes.** -/
theorem Op.id_bytes (o : Op) : o.id = sha256 o.bytes := o.id_eq

/-- **An op read from bytes is named by those bytes:** its id is their
hash, whoever sent them. -/
theorem Op.id_decode {b : ByteArray} {o : Op} (h : Op.decode b = some o) : o.id = sha256 b := by
  rw [Op.id_bytes, Op.bytes, Codec.encode_decode h]

theorem Op.decode_bytes (o : Op) : Op.decode o.bytes = some o := Codec.decode_encode o

/-- A decided op: Valid with the fact it produced, or Invalid. -/
inductive Verdict (F : Type) where
  | valid (f : F)
  | invalid
  deriving DecidableEq, Inhabited

open Codec in
instance {F} [Codec F] : Codec (Verdict F) where
  enc | .valid f => 1 :: enc f
      | .invalid => [0]
  dec | 1 :: rest => (dec rest).map fun p => (.valid p.1, p.2)
      | 0 :: rest => some (.invalid, rest)
      | _ => none
  round v rest := by
    cases v with
    | valid f => simp [round]
    | invalid => rfl

/-- Where ops of a kind travel. Shared ops are what sync offers and
takes, in their room (a community). Conn ops cross the bare wire to one
peer during a connection's handshake and are never synced. Local ops
are a node's own bookkeeping (its accepted communities, pending links,
secrets), judged and stored like any op, but never offered to a peer
and never taken from one (Engine.Sync). -/
inductive Scope where
  | shared (room : Id)
  | conn
  | «local»
  deriving DecidableEq, Inhabited

/-- What an application supplies: each op type's validator, the index
keys each fact is filed under, where each op travels, and where it
sorts in sync. Scope and order are read from the op's body: they never
depend on the header's kind.

- `scope`: shared in a room, conn, or local (`Scope`).
- `order`: the op's claimed time, which sync ranges are over (a window
  is "from this time on"); 0 for ops without one, which every window
  includes. -/
structure Family (F : Type) where
  validate : Op → List F → Option F
  keys : F → List ByteArray
  scope : Op → Scope := fun _ => .shared .empty
  order : Op → Nat := fun _ => 0

/-- The room an op is synced in; none unless it is shared. -/
def Family.room {F} (fam : Family F) (o : Op) : Option Id :=
  match fam.scope o with
  | .shared r => some r
  | _ => none

/-- Op x's own key: what its verdict is watched under, and the key its
Valid fact is filed under by id (`self`), so reading one fact is a list
of one. The 0xFF lead byte keeps it apart from a family's keys. -/
def opKey (x : Id) : ByteArray := ⟨#[0xFF] ++ x.data⟩

/-- Every key op x's Valid fact f is filed under: its own, then the
family's. -/
def Family.fileKeys {F} (fam : Family F) (x : Id) (f : F) : List ByteArray := opKey x :: fam.keys f

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

/-- Record x's verdict, file its fact (under its own key and the
family's, in this one step), and wake the ops waiting on it. -/
def decide (fam : Family F) (x : Id) (v : Verdict F) : m Unit := do
  setStatus x v
  match v with
  | .valid f => indexAll x (fam.fileKeys x f)
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
