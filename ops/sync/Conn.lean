/-
A sync connection: one peer, the rooms it may see, both sides' windows.
Pure: the transport calls these with what it read and the time, sends
`step.send` (each op as its bytes), passes `step.take` to the writer
through `intake fam false`, and
closes the connection when `step.drop`.

- **Hello.** Each side opens by saying its window floor. A window is
  every op with no claimed time (roots, admissions, removals, ...) and
  every op claimed at or after the floor; a round runs over the overlap
  of the two windows (`window`).
- **Rounds.** The dialer opens a round per room once it knows the
  peer's floor, and again every `cfg.every` ms for each idle room.
  Each side answers a round's claims from a snapshot of the room taken
  when it first saw the round, so the round is `exchange`, and
  `exchange_complete` applies. A message with no claims ends the round.
- **Have and want.** What `answer` says this side holds and the peer
  lacks is offered (`sync.have`, naming its room); the peer wants what
  it lacks in that room (`sync.want`); wanted ops are sent as their
  bytes. A want for an id outside the rooms or unknown is ignored
  silently: the peer learns nothing about it. A have
  is answered from this side's ops of its room only, and a have for a
  room the peer may not see is ignored, so a peer cannot ask whether
  this side holds an op of any other room.
- **Stream.** Ops stored after the round are offered as they are filed
  (`filed`), unless the peer is known to hold them.
- **Closure.** Full rounds keep no sender bookkeeping. Only windowed
  rounds queue requirements, with distinct pending plus visited ids
  capped by `closureCap`; overflow sets `closureCut`. Ticks drain the
  admitted prefix. The stream's `offered` is a separate bounded hint.
- **Liveness.** Both sides drop only after `cfg.live` ms of silence.
  A quiet tick sends an empty have every `live/3`; asks expire separately
  after `askTime`. Node records every outgoing payload's time.
- **Sessions.** Dialing, Hello, Live, Closed; a closed phase is terminal.

What a connection keeps is memory only and dies with it. Forgetting
stream hints can cause resends; cutting closure leaves explicit partial
knowledge, described in docs/SYNC.md.
-/
import ops.sync.Wire
import ops.sync.Session
import ops.sync.Serve
import ops.sync.Closure
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
  /-- ms before an unserved ask expires, independently of session liveness. -/
  askTime : Nat := 20000
  /-- ms between retries of wanted ids (less than askTime by default). -/
  retry : Nat := 1000
  /-- ms of silence before either side drops; keepalives use live / 3. -/
  live : Nat := 90000
  /-- ids retained in each of known and asked. Full hints reset; full asks defer. -/
  maxKnown : Nat := 65536
  /-- encoded op bytes served by one want, plus at most its last op. -/
  wantBytes : Nat := 4 * 1024 * 1024
  /-- ids per have or want op; a want for more is ignored. -/
  maxIds : Nat := 4096
  /-- Distinct requirement ids retained by a windowed round. -/
  closureCap : Nat := 4096
  /-- ops the closure walk visits per call. -/
  walk : Nat := 100000
  /-- bytes of payloads sealed together in one frame. -/
  bundle : Nat := 49152

structure Conn where
  session : Session := .dialing
  dialer : Bool
  rooms : List Id
  /-- The notices carried (ops/sync/Notice.lean): (room, op); and the
  ops of those given here. -/
  notices : List (Id × Id) := []
  given : List Id := []
  floor : Nat
  peerFloor : Option Nat := none
  round : Nat := 0
  lastRound : Nat := 0
  lastAsk : Nat := 0
  /-- The rounds in flight here, each with the snapshot it is answered from. -/
  snaps : List ((Id × Nat) × List Item) := []
  /-- Captured overlap floor, retained after the round ends for delayed wants. -/
  roundFloor : Nat := 0
  /-- A window closure ran out of slots in this round. -/
  closureCut : Bool := false
  /-- Peer possession hints; stream offer hints; visited closure ids. -/
  known : HashSet Id := {}
  offered : HashSet Id := {}
  closed : HashSet Id := {}
  /-- Ids wanted from the peer after it said it holds them. -/
  asked : HashSet Id := {}
  /-- Original ask times; retries and repeat offers do not renew them. -/
  askTime : HashMap Id Nat := {}
  /-- When the peer was last heard. -/
  heard : Nat := 0
  /-- Last outgoing payload, recorded by Node when it hands out sends. -/
  sent : Nat := 0
  /-- Requirement closure still to walk. -/
  frontier : List Id := []

/-- What a call does. -/
structure Step where
  conn : Conn
  send : List Op := []
  take : List Op := []
  /-- Notice ids to record through the family's onGiven hook. -/
  given : List Id := []
  drop : Bool := false

/-- An empty have is a liveness pulse. Other output substitutes for it. -/
def Step.pulse (cfg : Config) (sent now : Nat) (s : Step) : Step :=
  if s.send.isEmpty && sent + cfg.live / 3 ≤ now then
    { s with send := [(Msg.hold .empty []).op] }
  else s

@[simp] theorem Step.pulse_conn (cfg : Config) (sent now : Nat) (s : Step) :
    (s.pulse cfg sent now).conn = s.conn := by unfold pulse; split <;> rfl
@[simp] theorem Step.pulse_take (cfg : Config) (sent now : Nat) (s : Step) :
    (s.pulse cfg sent now).take = s.take := by unfold pulse; split <;> rfl
@[simp] theorem Step.pulse_drop (cfg : Config) (sent now : Nat) (s : Step) :
    (s.pulse cfg sent now).drop = s.drop := by unfold pulse; split <;> rfl

/-- The original known/asked bounds; StateLaws extends these to all sets. -/
def Conn.Bounded (cfg : Config) (c : Conn) : Prop :=
  c.known.size ≤ cfg.maxKnown ∧ c.asked.size ≤ cfg.maxKnown


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
  { conn := { session := Session.dialing.sayHello, dialer, rooms, floor, heard := now, sent := now, lastRound := now }, send := [(Msg.hello floor).op] }

/-- Capture the round's overlap once, including on the responder. All rooms
in a round use this window. A later hello cannot change delayed wants. -/
def Conn.beginRound (c : Conn) (k : Nat) : Conn :=
  { c with
    round := k
    roundFloor := if c.round = k then c.roundFloor else max c.floor (c.peerFloor.getD c.floor),
    closed := if c.round = k then c.closed else {},
    frontier := if c.round = k then c.frontier else [],
    closureCut := c.round = k && c.closureCut }

/-- Queue requirements only for a captured windowed round. -/
def Conn.queue (c : Conn) (ids : List Id) : Conn :=
  let (frontier, cut) := if c.roundFloor ≤ 1 then (c.frontier, false)
    else queueClosure cfg.closureCap c.closed c.frontier ids
  { c with frontier, closureCut := c.closureCut || cut }

/-- The dialer opens a round in every room. -/
def Conn.start (ix : Index) (c : Conn) (now : Nat) : Step :=
  match c.peerFloor with
  | none => { conn := c }
  | some pf =>
    let k := c.round + 1
    let w := window (max c.floor pf)
    let ready := c.rooms.filter fun r => !c.snaps.any (fun p => p.1.1 == r)
    let snaps := ready.map fun r => ((r, k), ix.items r)
    let send := snaps.map fun ((r, _), s) =>
      (Msg.rbsr r k (w.map (opening Prod.fst Prod.snd sha256 cfg.params s))).op
    { conn := { c.beginRound k with lastRound := now, snaps := (c.snaps ++ snaps).take c.rooms.length }, send }

/-- The snapshot round k in room r is answered from: the one taken when
this side first saw the round, or the room as it is now. -/
def Conn.snap (ix : Index) (c : Conn) (r : Id) (k : Nat) : List Item :=
  match c.snaps.find? fun p => Decidable.decide (p.1 = (r, k)) with
  | some (_, s) => s
  | none => ix.items r

/-- A round's message about room r: answer its claims from the round's
snapshot; no claims ends the round. -/
def Conn.onRbsr (ix : Index) (c : Conn) (r : Id) (k : Nat) (cs : List Claim) (now : Nat) : Step :=
  if !has c.rooms r then { conn := c, send := [(Msg.rbsr r k []).op] } else
  let snap := c.snap ix r k
  let c := c.beginRound k
  let others := c.snaps.filter fun p => !Decidable.decide (p.1.1 = r)
  let ended (c : Conn) : Conn :=
    { c with snaps := others }
  if cs.isEmpty then { conn := ended c } else
  let outs := cs.flatMap (answer Prod.fst Prod.snd sha256 cfg.params snap)
  let claims := outs.filterMap fun | .claim x => some x | _ => none
  let holds := outs.flatMap fun | .hold xs => xs | _ => []
  let wants := outs.flatMap fun | .want xs => xs | _ => []
  let c := if claims.isEmpty then ended c else { c with snaps := (((r, k), snap) :: others).take c.rooms.length }
  let wants := admitAsks cfg.maxKnown c.asked wants
  let c := { c with
    askTime := wants.foldl (fun ts i => ts.insert i now) c.askTime
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
  if ids.length > cfg.maxIds then return { conn := c }
  let mut want : List Id := []
  for i in ids do
    if !c.asked.contains i then
      if !(← holdsIn fam r i) then want := i :: want
  let missing := want
  let accepted := admitAsks cfg.maxKnown c.asked want.reverse
  let kept := ids.filter fun i => !missing.contains i || accepted.contains i
  let c := { c with
    known := kept.foldl (remember cfg.maxKnown) c.known
    asked := accepted.foldl (·.insert ·) c.asked
    askTime := accepted.foldl (fun ts i => ts.insert i c.heard) c.askTime }
  return { conn := c, send := chunks cfg accepted .want }

/-- At most `budget` steps of the walk, with what it has offered so far
(newest first), each with its room. -/
def Conn.walkN (c : Conn) (offer : List (Id × Id)) : Nat → m (Conn × List (Id × Id))
  | 0 => return (c, offer.reverse)
  | budget + 1 => do
    match c.frontier with
    | [] => return (c, offer.reverse)
    | x :: rest =>
      let c := { c with frontier := rest }
      if c.closed.contains x then return ← c.walkN offer budget
      -- Transferring one pending slot to visited never needs another slot.
      let c := { c with closed := c.closed.insert x }
      match ← Store.getOp (F := F) x with
      | none => c.walkN offer budget
      | some o =>
        if c.shows fam o then
          let offer := if !c.known.contains x && !c.offered.contains x then
            ((fam.room o).getD .empty, x) :: offer else offer
          (c.queue cfg o.reqs).walkN offer budget
        else c.walkN offer budget

/-- Walk the admitted requirement prefix. Visited ids include missing and
invalid ops: their bytes cannot change, and the next round retries them. -/
def Conn.walk (c : Conn) : m (Conn × List (Id × Id)) := c.walkN fam cfg [] cfg.walk

/-- Authorize ids using only the shown rooms' index, before any blob read. -/
def authorize (ix : Index) (c : Conn) (ids : List Id) : List Id :=
  ids.filter fun i => c.rooms.any fun r => (ix.items r).any fun a => Decidable.decide (a.2 = i)

/-- The peer wants these: authorize first, then read within the byte
budget. Closure reads continue on ticks, outside this response. -/
def Conn.onWant (ix : Index) (c : Conn) (ids : List Id) : m Step := do
  if ids.length > cfg.maxIds then return { conn := c }
  let sent ← (serve (c.shows fam) cfg.wantBytes (authorize ix c ids)).run (Store.getOp (F := F))
  let c := { c with
    known := sent.foldl (fun (k : HashSet Id) (o : Op) => remember cfg.maxKnown k o.id) c.known }
  let c := c.queue cfg (sent.flatMap Op.reqs)
  return { conn := c, send := sent }

/-- Bytes from the peer. -/
def Conn.recv (ix : Index) (c : Conn) (bytes : ByteArray) (now : Nat) : m Step := do
  match Op.decode bytes with
  | none => return { conn := c }
  | some o =>
    let c := { c with heard := now }
    match Msg.ofOp o with
    | some (.hello f) =>
      let c := { c with peerFloor := some f, session := c.session.hearHello }
      -- The first hello may precede the dialer's keys if the bare answer
      -- was lost. Answer its hello once it can open session frames.
      return (if c.dialer then c.start cfg ix now else
        { conn := c, send := [(Msg.hello c.floor).op] })
    | some (.rbsr r k cs) => return (c.onRbsr cfg ix r k cs now)
    | some (.hold r ids) => return (← c.onHold fam cfg r ids)
    | some (.want ids) => return (← c.onWant fam cfg ix ids)
    | none =>
      if isWire o.kind || !c.shows fam o then return { conn := c }
      else
        let c := { c with
          asked := c.asked.erase o.id
          askTime := c.askTime.erase o.id
          known := remember cfg.maxKnown c.known o.id }
        return ({ conn := c, take := [o] })

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
          c := { c with offered := remember cfg.maxKnown c.offered i }
      | none => pure ()
  return { conn := c, send := holdsOf cfg offer.reverse }

/-- Expire individual asks even while other peer traffic keeps the session live. -/
def Conn.expireAsks (cfg : Config) (c : Conn) (now : Nat) : Conn :=
  let live := fun (i : Id) => Decidable.decide (now ≤ (c.askTime[i]?.getD c.heard) + cfg.askTime)
  { c with
    asked := c.asked.filter live
    askTime := c.askTime.filter fun i t => c.asked.contains i && now ≤ t + cfg.askTime }

/-- One tick retries at most one want's worth, without renewing ask times. -/
def Conn.retryIds (cfg : Config) (c : Conn) (now : Nat) : List Id :=
  if c.lastAsk + cfg.retry ≤ now then c.asked.toList.take cfg.maxIds else []

/-- Work due on a live session: rounds, closure and retries. -/
def Conn.work (ix : Index) (c : Conn) (now : Nat) : m Step := do
  let (c, offer) ← c.walk fam cfg
  let c := c.expireAsks cfg now
  let s := if c.dialer && c.lastRound + cfg.every ≤ now then c.start cfg ix now
    else { conn := c }
  let due := c.lastAsk + cfg.retry ≤ now
  return { s with
    conn := { s.conn with lastAsk := if due then now else c.lastAsk }
    send := s.send ++ (holdsOf cfg offer ++ chunks cfg (c.retryIds cfg now) .want) }

/-- The clock has one drop rule, independent of rooms and outstanding work. -/
def Conn.tick (ix : Index) (c : Conn) (now : Nat) : m Step := do
  if c.heard + cfg.live < now then return { conn := { c with session := c.session.close }, drop := true }
  return (← c.work fam cfg ix now).pulse cfg c.sent now

/-- The rooms the peer may see changed: forget the others' rounds. -/
def Conn.setRooms (c : Conn) (rooms : List Id) : Conn :=
  { c with rooms, snaps := (c.snaps.filter fun p => has rooms p.1.1).take rooms.length }

end

end Engine.Sync
