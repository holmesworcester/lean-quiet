/-
A sync connection: one peer, the rooms it may see, both sides' windows.
Pure: the transport calls these with what it read and the time, sends
`step.send` (each op as its bytes), passes `step.take` to the writer
through `intake fam false`, writes `step.status` as local ops, and
closes the connection when `step.drop`.

- **Hello.** Each side opens by saying its window floor. A window is
  every op with no claimed time (roots, admissions, removals, ...) and
  every op claimed at or after the floor; a round runs over the overlap
  of the two windows (`window`).
- **Rounds.** The dialer opens a round per room once it knows the
  peer's floor, and again every `cfg.every` ms when none is in flight.
  Each side answers a round's claims from a snapshot of the room taken
  when it first saw the round, so the round is `exchange`, and
  `exchange_complete` applies. A message with no claims ends the round.
- **Have and want.** What `answer` says this side holds and the peer
  lacks is offered (`sync.have`, naming its room); the peer wants what
  it lacks in that room (`sync.want`); wanted ops are sent as their
  bytes. A want for an id the peer did not offer, outside the rooms, or
  unknown, is ignored silently: the peer learns nothing about it. A have
  is answered from this side's ops of its room only, and a have for a
  room the peer may not see is ignored, so a peer cannot ask whether
  this side holds an op of any other room.
- **Stream.** Ops stored after the round are offered as they are filed
  (`filed`), unless the peer is known to hold them.
- **Closure.** With each op sent goes an offer of its requirement
  closure, the ids the peer is not known to hold. The walk stops at ops
  whose closure this connection already offered and that are Valid
  here (a Valid op's closure is complete and fixed); it goes at most
  `cfg.walk` ops per call and continues on the next tick.
- **Patience.** While this side waits (for the peer's hello, a round's
  answer, or ops it wanted after the peer said it holds them), a peer
  silent for `cfg.patience` ms drops the connection; the next
  connection's round finds what is still missing.
- **Status.** `settled room` once per room per connection: its first
  round has ended and nothing this side wanted is outstanding.

What a connection keeps (known, offered, asked, snapshots) is memory
only and dies with it: losing it can only cause resends.
-/
import ops.sync.Wire
import ops.sync.RoundLaws
import engine.core.Sync
import Std.Data.HashSet

namespace Engine.Sync
open Std

/-- An item of a room's sync set: an op's key and id. -/
abbrev Item := Key × Id

/-! ## The room index -/

section
variable {F : Type} (fam : Family F)

/-- Where an op sorts in sync: its claimed time, then its id's number. -/
def keyOf (o : Op) : Key := ⟨fam.order o, num o.id.data.toList⟩

/-- l with a, in key order, once. -/
def ins (a : Item) : List Item → List Item
  | [] => [a]
  | b :: t => if a.1 < b.1 then a :: b :: t else if a.1 = b.1 then b :: t else b :: ins a t

/-- Each room's items in key order: what sync reconciles, kept in
memory. Built from the stored ops once (`ofOps`), then grown by each op
stored after (`add`), from the writer's notices. -/
structure Index where
  rooms : List (Id × List Item) := []
  deriving Inhabited

def Index.items (ix : Index) (c : Id) : List Item :=
  match ix.rooms.find? fun p => Decidable.decide (p.1 = c) with
  | some (_, l) => l
  | none => []

/-- The index with a stored op added; a local op is no room's. -/
def Index.add (ix : Index) (o : Op) : Index :=
  match fam.room o with
  | none => ix
  | some c =>
    let a := (keyOf fam o, o.id)
    if ix.rooms.any (fun p => Decidable.decide (p.1 = c)) then
      ⟨ix.rooms.map fun p => if p.1 = c then (p.1, ins a p.2) else p⟩
    else ⟨(c, [a]) :: ix.rooms⟩

def Index.ofOps (ops : List Op) : Index := ops.foldl (Index.add fam) {}

/-- The index without a purged op. -/
def Index.remove (ix : Index) (x : Id) : Index :=
  ⟨ix.rooms.map fun p => (p.1, p.2.filter fun a => !Decidable.decide (a.2 = x))⟩

end

/-! ## Connections -/

/-- The window from floor f: every op with no claimed time, and every op
claimed at f or later. -/
def window (f : Nat) : List Range :=
  if f ≤ 1 then [⟨⟨0, 0⟩, none⟩] else [⟨⟨0, 0⟩, some ⟨1, 0⟩⟩, ⟨⟨f, 0⟩, none⟩]

structure Config where
  params : Params := {}
  /-- ms between rounds the dialer opens. -/
  every : Nat := 30000
  /-- ms of silence while waiting before the connection drops. -/
  patience : Nat := 20000
  /-- ids per have or want op; a want for more is ignored. -/
  maxIds : Nat := 4096
  /-- ops the closure walk visits per call. -/
  walk : Nat := 100000
  /-- bytes of payloads sealed together in one frame. -/
  bundle : Nat := 49152

inductive Status where
  | settled (room : Id)
  deriving Inhabited, BEq

structure Conn where
  dialer : Bool
  rooms : List Id
  /-- The notices carried (ops/sync/Notice.lean): (room, op). One
  given here is in `settled`. -/
  notices : List (Id × Id) := []
  floor : Nat
  peerFloor : Option Nat := none
  round : Nat := 0
  lastRound : Nat := 0
  /-- The rounds in flight here, each with the snapshot it is answered from. -/
  snaps : List ((Id × Nat) × List Item) := []
  /-- Rooms whose first round has ended, and rooms reported settled. -/
  rounded : List Id := []
  settled : List Id := []
  /-- Ids the peer holds; ids offered to it; ops whose closure was offered. -/
  known : HashSet Id := {}
  offered : HashSet Id := {}
  closed : HashSet Id := {}
  /-- Ids wanted from the peer after it said it holds them. -/
  asked : HashSet Id := {}
  /-- When the peer was last heard. -/
  heard : Nat := 0
  /-- Requirement closure still to walk. -/
  frontier : List Id := []

/-- What a call does. -/
structure Step where
  conn : Conn
  send : List Op := []
  take : List Op := []
  status : List Status := []
  drop : Bool := false

section
variable {F : Type} {m : Type → Type} [Monad m] [Store F m] (fam : Family F) (cfg : Config)

/-- Whether this connection may show the peer op o: o is in one of its
rooms (so it is shared). -/
def Conn.shows (c : Conn) (o : Op) : Bool :=
  match fam.room o with
  | some r => has c.rooms r
  | none => false

/-- l in pieces of at most n, within `fuel` pieces. -/
def pieceIds (n : Nat) : Nat → List Id → List (List Id)
  | 0, _ => []
  | _, [] => []
  | k + 1, l => l.take n :: pieceIds n k (l.drop n)

/-- ids in ops of at most `cfg.maxIds`. -/
def chunks (ids : List Id) (mk : List Id → Msg) : List Op :=
  (pieceIds cfg.maxIds ids.length ids).map fun l => (mk l).op

def Conn.open (dialer : Bool) (rooms : List Id) (floor : Nat) (now : Nat) : Step :=
  { conn := { dialer, rooms, floor, heard := now, lastRound := now }, send := [(Msg.hello floor).op] }

/-- Rooms whose first round has ended with nothing wanted outstanding,
reported once. -/
def Conn.report (c : Conn) : Conn × List Status :=
  if c.asked.isEmpty then
    let fresh := c.rounded.filter fun r => !has c.settled r
    ({ c with settled := fresh ++ c.settled }, fresh.map .settled)
  else (c, [])

def Conn.finish (s : Step) : Step :=
  let (c, st) := s.conn.report
  { s with conn := c, status := s.status ++ st }

/-- The dialer opens a round in every room. -/
def Conn.start (ix : Index) (c : Conn) (now : Nat) : Step :=
  match c.peerFloor with
  | none => { conn := c }
  | some pf =>
    let k := c.round + 1
    let w := window (max c.floor pf)
    let snaps := c.rooms.map fun r => ((r, k), ix.items r)
    let send := snaps.map fun ((r, _), s) =>
      (Msg.rbsr r k (w.map (opening Prod.fst Prod.snd sha256 cfg.params s))).op
    { conn := { c with round := k, lastRound := now, snaps }, send }

/-- The snapshot round k in room r is answered from: the one taken when
this side first saw the round, or the room as it is now. -/
def Conn.snap (ix : Index) (c : Conn) (r : Id) (k : Nat) : List Item :=
  match c.snaps.find? fun p => Decidable.decide (p.1 = (r, k)) with
  | some (_, s) => s
  | none => ix.items r

/-- A round's message about room r: answer its claims from the round's
snapshot; no claims ends the round. -/
def Conn.onRbsr (ix : Index) (c : Conn) (r : Id) (k : Nat) (cs : List Claim) (now : Nat) : Step :=
  if !has c.rooms r then { conn := c } else
  let snap := c.snap ix r k
  let others := c.snaps.filter fun p => !Decidable.decide (p.1.1 = r)
  let ended (c : Conn) : Conn :=
    { c with snaps := others, rounded := if has c.rounded r then c.rounded else r :: c.rounded }
  if cs.isEmpty then { conn := ended c } else
  let outs := cs.flatMap (answer Prod.fst Prod.snd sha256 cfg.params snap)
  let claims := outs.filterMap fun | .claim x => some x | _ => none
  let holds := outs.flatMap fun | .hold xs => xs | _ => []
  let wants := outs.flatMap fun | .want xs => xs | _ => []
  let c := if claims.isEmpty then ended c else { c with snaps := ((r, k), snap) :: others }
  let c := { c with
    offered := holds.foldl (·.insert ·) c.offered
    asked := wants.foldl (·.insert ·) c.asked }
  { conn := c, send := (Msg.rbsr r k claims).op :: (chunks cfg holds (.hold r) ++ chunks cfg wants .want) }

/-- Offers, each with its op's room, as haves: per room, in the order
the rooms first appear, ids in ops of at most `cfg.maxIds`. -/
def holdsOf (offer : List (Id × Id)) : List Op :=
  ((offer.map (·.1)).foldl Engine.ins []).flatMap fun r =>
    chunks cfg (offer.filterMap fun p => if p.1 = r then some p.2 else none) (.hold r)

/-- Whether this side holds op i in room r. -/
def holdsIn (r i : Id) : m Bool := do
  return match ← Store.getOp (F := F) i with
    | some o => Decidable.decide (fam.room o = some r)
    | none => false

/-- The peer holds these in room r: want the ones this side does not
hold there. A have for a room the peer may not see is ignored. The
reply reads only this side's ops of room r, so it says nothing of what
this side holds elsewhere (`hold_reply_local`). -/
def Conn.onHold (c : Conn) (r : Id) (ids : List Id) : m Step := do
  if !has c.rooms r then return { conn := c }
  let mut want : List Id := []
  for i in ids do
    if !c.asked.contains i then
      if !(← holdsIn fam r i) then want := i :: want
  let c := { c with
    known := ids.foldl (·.insert ·) c.known
    asked := want.foldl (·.insert ·) c.asked }
  return { conn := c, send := chunks cfg want.reverse .want }

/-- At most `budget` steps of the walk, with what it has offered so far
(newest first), each with its room. -/
def Conn.walkN (c : Conn) (offer : List (Id × Id)) : Nat → m (Conn × List (Id × Id))
  | 0 => return (c, offer.reverse)
  | budget + 1 => do
    match c.frontier with
    | [] => return (c, offer.reverse)
    | x :: rest =>
      let mut c := { c with frontier := rest }
      let mut offer := offer
      if !c.closed.contains x then
        match ← Store.getOp (F := F) x with
        | none => pure ()
        | some o =>
          if c.shows fam o then
            if !c.known.contains x && !c.offered.contains x then
              -- Shown, so its room is one of the connection's.
              offer := ((fam.room o).getD .empty, x) :: offer
              c := { c with offered := c.offered.insert x }
            if let some (.valid _) ← Store.getStatus (F := F) x then
              c := { c with closed := c.closed.insert x }
            c := { c with frontier := o.reqs ++ c.frontier }
      c.walkN offer budget

/-- Walk requirement closures from the frontier, at most `cfg.walk` ops:
offer every stored op the peer may see and is not known to hold or
already offered. -/
def Conn.walk (c : Conn) : m (Conn × List (Id × Id)) := c.walkN fam [] cfg.walk

/-- The peer wants these: send each stored op it may see, and offer
their closures. Anything else is ignored. -/
def Conn.onWant (c : Conn) (ids : List Id) : m Step := do
  if ids.length > cfg.maxIds then return { conn := c }
  let found ← ids.filterMapM fun i => Store.getOp (F := F) i
  let sent := found.filter (c.shows fam)
  let c := { c with
    known := sent.foldl (fun (k : HashSet Id) (o : Op) => k.insert o.id) c.known
    offered := sent.foldl (fun (k : HashSet Id) (o : Op) => k.insert o.id) c.offered
    frontier := c.frontier ++ sent.flatMap Op.reqs }
  let (c, offer) ← c.walk fam cfg
  return { conn := c, send := sent ++ holdsOf cfg offer }

/-- Bytes from the peer. -/
def Conn.recv (ix : Index) (c : Conn) (bytes : ByteArray) (now : Nat) : m Step := do
  match Op.decode bytes with
  | none => return { conn := c }
  | some o =>
    let c := { c with heard := now }
    match Msg.ofOp o with
    | some (.hello f) =>
      let c := { c with peerFloor := some f }
      return Conn.finish (if c.dialer then c.start cfg ix now else { conn := c })
    | some (.rbsr r k cs) => return Conn.finish (c.onRbsr cfg ix r k cs now)
    | some (.hold r ids) => return Conn.finish (← c.onHold fam cfg r ids)
    | some (.want ids) => return Conn.finish (← c.onWant fam cfg ids)
    | none =>
      if isWire o.kind || !c.shows fam o then return { conn := c }
      else
        let c := { c with asked := c.asked.erase o.id, known := c.known.insert o.id }
        return Conn.finish { conn := c, take := [o] }

/-- Ops just stored here: offer the ones the peer may see and is not
known to hold. -/
def Conn.filed (c : Conn) (ids : List Id) : m Step := do
  let mut offer : List (Id × Id) := []
  let mut c := c
  for i in ids do
    if !c.known.contains i && !c.offered.contains i then
      match ← Store.getOp (F := F) i with
      | some o =>
        if c.shows fam o then
          offer := ((fam.room o).getD .empty, i) :: offer
          c := { c with offered := c.offered.insert i }
      | none => pure ()
  return Conn.finish { conn := c, send := holdsOf cfg offer.reverse }

/-- Whether this side is waiting on the peer. -/
def Conn.waiting (c : Conn) : Bool :=
  c.peerFloor.isNone || !c.asked.isEmpty || (c.dialer && !c.snaps.isEmpty)

/-- The clock: drop if the peer is silent while this side waits; the
dialer opens rounds on its cadence; the closure walk continues. -/
def Conn.tick (ix : Index) (c : Conn) (now : Nat) : m Step := do
  if c.waiting && c.heard + cfg.patience < now then
    return { conn := c, drop := true }
  let (c, offer) ← c.walk fam cfg
  let s := if c.dialer && c.snaps.isEmpty && c.lastRound + cfg.every ≤ now then c.start cfg ix now
    else { conn := c }
  return Conn.finish { s with send := s.send ++ holdsOf cfg offer }

/-- The rooms the peer may see changed: forget the others' rounds. -/
def Conn.setRooms (c : Conn) (rooms : List Id) : Conn :=
  { c with rooms, snaps := c.snaps.filter fun p => has rooms p.1.1 }

end

end Engine.Sync
