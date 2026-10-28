/-
Notices: what a connection gives a removed member's node
(docs/REMOVAL.md). A connection carries rooms, each synced both ways,
or a notice: op x of room r with its requirement closure, given once
and never taken. The family's view gives the rooms afresh on every step
(`Hooks.rooms`, `Node.refresh`, `carry`).

`notify` gives each notice not given yet: it sends x and its closure,
records x in `given`, and reports it (`Status.given`), which the node's
settle hook writes as an op. The node runs it on every connection where
it runs `filed` and `tick` (`filedGive`, `tickGive`), so `filed` and
`tick` themselves stay sync only (`filed_send`, `tick_send`, and
`have_shown` for the synced rooms). The laws are in NoticeLaws.lean.
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

@[simp] theorem Room.syncs_sync (l : List Id) : Room.syncs (l.map .sync) = l := by
  induction l <;> simp_all [Room.syncs]

@[simp] theorem Room.notices_sync (l : List Id) : Room.notices (l.map .sync) = [] := by
  induction l <;> simp_all [Room.notices]

/-- The connection carrying these rooms, as each step reads them afresh:
a synced room no longer carried forgets its rounds. -/
def Conn.carry (c : Conn) (rs : List Room) : Conn :=
  { c.setRooms (Room.syncs rs) with notices := Room.notices rs }

/-- Step g, then step s on g's connection: s's connection, and both
steps' sends, takes and statuses in order. -/
def Step.then (g s : Step) : Step :=
  { s with send := g.send ++ s.send, take := g.take ++ s.take, status := g.status ++ s.status,
           drop := g.drop || s.drop }

/-- A step that does nothing, then s, is s. -/
@[simp] theorem Step.then_quiet (c : Conn) (s : Step) : Step.then { conn := c } s = s := by
  cases s; simp [Step.then]

section
variable {F : Type} {m : Type → Type} [Monad m] [Store F m] (fam : Family F) (cfg : Config)

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

@[simp] theorem closureOps_nil (r : Id) (fuel : Nat) (seen : List Id) :
    (closureOps fam r fuel [] seen : m (List Op)) = pure [] := by
  cases fuel <;> rw [closureOps]; simp

/-- Give each notice not given yet on this connection: its op and the
op's requirement closure in its room, less what the peer is known to
hold, requirements first. Each is recorded in `given` and reported, so
a connection gives a notice once. -/
def Conn.give (c : Conn) : List (Id × Id) → m Step
  | [] => pure { conn := c }
  | (r, x) :: rest => do
    if has c.given x then c.give rest
    else
      let ops ← closureOps fam r cfg.walk [x] []
      let s ← ({ c with given := x :: c.given } : Conn).give rest
      return { s with
        send := (ops.filter fun (o : Op) => !c.known.contains o.id).reverse ++ s.send
        status := .given x :: s.status }

/-- The notices this connection carries and has not given, given. -/
def Conn.notify (c : Conn) : m Step := c.give fam cfg c.notices

/-- Ops just stored here, as the node runs them on a connection: its
notices given, then the ops offered (`filed`). -/
def Conn.filedGive (c : Conn) (ids : List Id) : m Step := do
  let g ← c.notify fam cfg
  return g.then (← g.conn.filed fam cfg ids)

/-- The clock, as the node runs it on a connection: its notices given,
then `tick`. A tick that drops the connection gives nothing. -/
def Conn.tickGive (ix : Index) (c : Conn) (now : Nat) : m Step := do
  let g ← c.notify fam cfg
  let s ← g.conn.tick fam cfg ix now
  return if s.drop then s else g.then s

end

end Engine.Sync
