/-
Notices: what a connection gives a removed member's node
(docs/REMOVAL.md). A connection carries rooms, each synced both ways,
or a notice: op x of room r with its requirement closure, given once
and never taken. The family's view gives the rooms afresh on every step;
`give` sends each notice not given yet, records it, and reports it
settled. The laws are in NoticeLaws.lean.

Not yet called by `filed` and `tick`, nor carried by `Hooks.rooms`:
that is the Node and Conn step, after a3's hostile branch lands.
-/
import ops.sync.Conn

namespace Engine.Sync
open Std

/-- What a connection carries of a room, as its family reads it afresh
on every step: the room, synced both ways; or a notice, op x of room r
with its requirement closure, given once and never taken (a removed
member's node is told its removal, and what it needs to judge it). -/
inductive Room where
  | sync (r : Id)
  | notice (r x : Id)
  deriving Inhabited

/-- The rooms synced. -/
def Room.syncs : List Room → List Id
  | [] => []
  | .sync r :: t => r :: Room.syncs t
  | .notice .. :: t => Room.syncs t

/-- The notices: (room, op). -/
def Room.notices : List Room → List (Id × Id)
  | [] => []
  | .sync _ :: t => Room.notices t
  | .notice r x :: t => (r, x) :: Room.notices t

section
variable {F : Type} {m : Type → Type} [Monad m] [Store F m] (fam : Family F) (cfg : Config)

/-- The connection carrying these rooms, as each step reads them afresh:
a synced room no longer carried forgets its rounds. -/
def Conn.carry (c : Conn) (rs : List Room) : Conn :=
  { c.setRooms (Room.syncs rs) with notices := Room.notices rs }

/-- The stored ops of room r reached from `todo` through requirements,
each id visited once, in visiting order, at most `fuel` of them. An op
of another room, or an id not stored, is not followed. -/
def closureOps (r : Id) (fuel : Nat) (todo seen : List Id) : m (List Op) :=
  match fuel, todo with
  | 0, _ => pure []
  | _, [] => pure []
  | n + 1, y :: rest =>
    if has seen y then closureOps r (n + 1) rest seen
    else do
      match ← Store.getOp (F := F) y with
      | some o =>
        if fam.room o = some r then
          return o :: (← closureOps r n (o.reqs ++ rest) (y :: seen))
        else closureOps r n rest (y :: seen)
      | none => closureOps r n rest (y :: seen)
termination_by (fuel, todo.length)

/-- Give each notice not given yet on this connection: its op and the
op's requirement closure in its room, less what the peer is known to
hold, requirements first. Each is reported settled and recorded, so a
connection gives a notice once. -/
def Conn.give (c : Conn) : List (Id × Id) → m Step
  | [] => pure { conn := c }
  | (r, x) :: rest => do
    if has c.settled x then c.give rest
    else
      let ops ← closureOps fam r cfg.walk [x] []
      let c' := { c with
        settled := x :: c.settled
        known := ops.foldl (fun (k : HashSet Id) (o : Op) => k.insert o.id) c.known }
      let s ← c'.give rest
      return { s with
        send := (ops.filter fun (o : Op) => !c.known.contains o.id).reverse ++ s.send
        status := .settled x :: s.status }

/-- The notices this connection carries and has not given, given. -/
def Conn.notify (c : Conn) : m Step := c.give fam cfg c.notices

end

end Engine.Sync
