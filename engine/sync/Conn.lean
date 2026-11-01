/-
A sync connection: one peer, the rooms it may see, both sides' windows.
Pure: the transport calls these with what it read and the time, sends
`step.send` (each op as its bytes), passes `step.take` to the writer
through `intake fam false`, and
closes the connection when `step.drop`.

- **Hello.** Each side opens by saying its window floor. A window is
  every op with no claimed time (roots, admissions, removals, ...) and
  every op claimed at or after the floor; a round runs over the overlap
  of the two windows (`window`), structure first, then newest first
  (`newest_first`).
- **Rounds.** Only the dialer opens rounds, and only on an event: once
  it knows the peer's floor it opens one in every room the session
  shows; on its clock it opens one in each shown room that is due
  (`due`): a room it has not opened a round in on this session (newly
  shown, or the responder asked), and every `cfg.safety` ms in each
  room. The responder asks for a round in a room it starts showing
  mid-session with an empty have naming it (`ask`). A newer round in a
  room supersedes the one in flight there. A room whose wants did not
  all fit in `asked` (`short`) is due again, once the asks are at most
  half full and its round has ended: the next round finds what the last
  could not ask for.
- **Live answers.** Each side answers each claim from the live index as
  it is at that instant (`ix.items r`); a connection keeps no copy of a
  room, only which rounds are in flight (`active`). A matching
  fingerprint means equal sets at that instant (`lbl_inj`), and ops
  stored later reach the peer by the stream, so a round needs no calm
  (RoundRun.lean, `live_round_complete`). A message with no claims ends
  the round.
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
- **Closure.** A windowed round reconciles S: its window and every
  stored op of the room within `params.depth` requirement steps of it,
  each sorted by its own time (`Index.over`). Both sides read S from
  their live index, so what the windowed side lacks of the closure
  arrives in the round itself, and no round keeps sender bookkeeping
  (docs/SYNC.md, "Windows and order"). The stream's `offered` is a
  bounded hint.
- **Liveness.** Both sides drop only after `cfg.live` ms of silence.
  A quiet tick sends an empty have every `live/3`; asks expire separately
  after `askTime`. Node records every outgoing payload's time.
- **Sessions.** Dialing, Hello, Live, Closed; a closed phase is terminal.

What a connection keeps is memory only and dies with it. Forgetting
stream hints can cause resends; cutting closure leaves explicit partial
knowledge, described in docs/SYNC.md.
-/
import engine.sync.Wire
import engine.sync.Session
import engine.sync.Serve
import engine.sync.Closure
import engine.sync.Walk
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
stored after (`add`), from the writer's notices. `byId` is each stored
shared op's room and requirements, by id: what a windowed round's
closure reads (`over`). -/
structure Index where
  rooms : List (Id × List Item) := []
  byId : Std.HashMap Id (Id × List Id) := {}
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
    let byId := ix.byId.insert o.id (c, o.reqs)
    if ix.rooms.any (fun p => Decidable.decide (p.1 = c)) then
      ⟨ix.rooms.map (fun p => if p.1 = c then (p.1, ins a p.2) else p), byId⟩
    else ⟨(c, [a]) :: ix.rooms, byId⟩

def Index.ofOps (ops : List Op) : Index := ops.foldl (Index.add fam) {}

/-- The index without a purged op. -/
def Index.remove (ix : Index) (x : Id) : Index :=
  ⟨ix.rooms.map (fun p => (p.1, p.2.filter fun a => !Decidable.decide (a.2 = x))), ix.byId.erase x⟩

/-- Whether x is a stored op of room r. -/
def Index.inRoom (ix : Index) (r x : Id) : Bool :=
  match ix.byId[x]? with
  | some (r', _) => r' == r
  | none => false

/-- The requirements of x that are stored ops of room r: one step of a
window's closure. -/
def Index.next (ix : Index) (r x : Id) : List Id :=
  match ix.byId[x]? with
  | some (_, rs) => rs.filter (ix.inRoom r)
  | none => []

/-- The lookups expanding x makes: its own, and one per requirement. -/
def Index.cost (ix : Index) (x : Id) : Nat :=
  1 + match ix.byId[x]? with
  | some (_, rs) => rs.length
  | none => 0

/-- Whether a key is in the window from floor f: no claimed time, or at
f or later. -/
def inWindow (f : Nat) (k : Key) : Bool := k.t == 0 || Decidable.decide (f ≤ k.t)

/-- The ids of room r's window from floor f. -/
def Index.windowIds (ix : Index) (r : Id) (f : Nat) : List Id :=
  ((ix.items r).filter fun a => inWindow f a.1).map (·.2)

/-- The window's closure: every stored op of room r within k requirement
steps of the window from floor f (`walk_from`), and the lookups made
(`walk_cost`). -/
def Index.closure (ix : Index) (k : Nat) (r : Id) (f : Nat) : Std.HashSet Id × Nat :=
  walk (ix.next r) ix.cost k (ix.windowIds r f) (Std.HashSet.ofList (ix.windowIds r f))

/-- S, what a round in room r at floor f reconciles, in key order: the
room's items when the round is full (`f ≤ 1`); otherwise the window and
its requirements within k steps, each sorted by its own time
(`over_mem`). Both sides compute it from their own stores. -/
def Index.over (k : Nat) (ix : Index) (r : Id) (f : Nat) : List Item :=
  if f ≤ 1 then ix.items r else
  let seen := (ix.closure k r f).1
  (ix.items r).filter fun a => seen.contains a.2

/-- How this side opens a round over w in room r at floor f, from S. -/
def Index.opening (P : Params) (ix : Index) (r : Id) (f : Nat) (w : Range) : Claim :=
  Engine.Sync.opening Prod.fst Prod.snd sha256 P (ix.over P.depth r f) w
/-- What this side answers to claim c in room r at floor f, from S. -/
def Index.answer (P : Params) (ix : Index) (r : Id) (f : Nat) (c : Claim) : List Out :=
  Engine.Sync.answer Prod.fst Prod.snd sha256 P (ix.over P.depth r f) c
theorem Index.opening_eq (P : Params) (ix : Index) (r : Id) (f : Nat) (w : Range) :
    ix.opening P r f w = Engine.Sync.opening Prod.fst Prod.snd sha256 P (ix.over P.depth r f) w := rfl
theorem Index.answer_eq (P : Params) (ix : Index) (r : Id) (f : Nat) (c : Claim) :
    ix.answer P r f c = Engine.Sync.answer Prod.fst Prod.snd sha256 P (ix.over P.depth r f) c := rfl
/-- The two as functions, for rewriting under `map` and `flatMap`. -/
theorem Index.opening_fun (P : Params) (ix : Index) (r : Id) (f : Nat) :
    ix.opening P r f = Engine.Sync.opening Prod.fst Prod.snd sha256 P (ix.over P.depth r f) :=
  funext (Index.opening_eq P ix r f)
theorem Index.answer_fun (P : Params) (ix : Index) (r : Id) (f : Nat) :
    ix.answer P r f = Engine.Sync.answer Prod.fst Prod.snd sha256 P (ix.over P.depth r f) :=
  funext (Index.answer_eq P ix r f)
/-- S is a subset of the room's items. -/
theorem Index.over_sub (k : Nat) (ix : Index) (r : Id) (f : Nat) {a : Item} (h : a ∈ ix.over k r f) :
    a ∈ ix.items r := by
  unfold Index.over at h
  split at h
  · exact h
  · exact (List.mem_filter.1 h).1

/-- A full round's set is the room's items. -/
@[simp] theorem Index.over_full (k : Nat) (ix : Index) (r : Id) (f : Nat) (h : f ≤ 1) :
    ix.over k r f = ix.items r := by simp [Index.over, h]

end

/-! ## Connections -/

/-- The window from floor f: every op with no claimed time (the
structure range, first: everything else needs it), then every op claimed
at f or later (at 1 or later for a full window, `f ≤ 1`). Answers go
newest first within each (`newest_first`). -/
def window (f : Nat) : List Range :=
  [⟨⟨0, 0⟩, some ⟨1, 0⟩⟩, ⟨⟨max f 1, 0⟩, none⟩]

structure Config where
  params : Params := {}
  /-- ms after a room's last round before the dialer opens a safety
  round in it. Otherwise rounds open only when a session starts showing
  a room, or the responder asks for one. -/
  safety : Nat := 600000
  /-- ops a notice's requirement closure visits per call (Notice.lean). -/
  walk : Nat := 100000
  /-- ms before an unserved ask expires, independently of session liveness. -/
  askTime : Nat := 20000
  /-- ms between retries of wanted ids (less than askTime by default). -/
  retry : Nat := 1000
  /-- ms of silence before either side drops; keepalives use live / 3. -/
  live : Nat := 90000
  /-- ids retained in each of known and asked. Full hints reset; full asks defer. -/
  maxKnown : Nat := 65536
  /-- ids per have or want op; a want for more is ignored. -/
  maxIds : Nat := 4096
  /-- bytes of payloads sealed together in one frame. -/
  bundle : Nat := 49152
  /-- Serve-lane bytes released per step, plus at most one whole op. -/
  burst : Nat := 131072
  urgentIds : Nat := 64
  hotMs : Nat := 20000
  hotCap : Nat := 256

structure Conn where
  session : Session := .dialing
  dialer : Bool
  rooms : List Id
  /-- The notices carried (engine/sync/Notice.lean): (room, op); and the
  ops of those given here. -/
  notices : List (Id × Id) := []
  given : List Id := []
  floor : Nat
  peerFloor : Option Nat := none
  round : Nat := 0
  /-- Each shown room with when its last round opened here (the dialer),
  or when this side last saw or asked for one (the responder). A shown
  room with no entry is due. -/
  rounded : List (Id × Nat) := []
  lastAsk : Nat := 0
  /-- The rounds in flight here: room and epoch, at most one per room.
  No items: every claim is answered from the live index. -/
  active : List (Id × Nat) := []
  /-- Rooms where a round or a have found more ids missing than `asked`
  had room for: each is due another round once the asks drain. -/
  short : List Id := []
  /-- Latest epoch seen in each room, retained after its round ends.
  Delayed terminal markers and replayed claims cannot rewind another round. -/
  epochs : List (Id × Nat) := []
  /-- Captured overlap floor, retained after the round ends for delayed wants. -/
  roundFloor : Nat := 0
  /-- Peer possession hints; stream offer hints. -/
  known : HashSet Id := {}
  offered : HashSet Id := {}
  /-- Ids wanted from the peer after it said it holds them. -/
  asked : HashSet Id := {}
  /-- Original ask times; retries and repeat offers do not renew them. -/
  askTime : HashMap Id Nat := {}
  /-- Authorized wants queued in order, and their membership set. -/
  owed : List Id := []
  owing : HashSet Id := {}
  /-- When the peer was last heard. -/
  heard : Nat := 0
  /-- Last outgoing payload, recorded by Node when it hands out sends. -/
  sent : Nat := 0

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
  { conn := { session := Session.dialing.sayHello, dialer, rooms, floor, heard := now, sent := now }, send := [(Msg.hello floor).op] }

/-- Remember a room's newest round, with at most one record per room. -/
def noteEpoch (limit : Nat) (epochs : List (Id × Nat)) (r : Id) (k : Nat) : List (Id × Nat) :=
  ((r, k) :: epochs.filter (fun p => !Decidable.decide (p.1 = r))).take limit

/-- Remember a room, once. -/
def noteRoom (limit : Nat) (rs : List Id) (r : Id) : List Id :=
  (r :: rs.filter (fun x => !Decidable.decide (x = r))).take limit

/-- Wanting these would ask for more ids than `asked` has room for. -/
def deferred (cap : Nat) (asked : HashSet Id) (ids : List Id) : Bool :=
  Decidable.decide (cap - asked.size < ((ids.filter fun i => !asked.contains i).eraseDups).length)

/-- When room r's last round opened here (or, at the responder, when it
last saw or asked for one), if any did on this session. -/
def Conn.roundedAt (c : Conn) (r : Id) : Option Nat :=
  (c.rounded.find? fun p => Decidable.decide (p.1 = r)).map (·.2)

/-- An older epoch, a completed duplicate, or a reply to a round the dialer
never opened. Other rooms can lag behind the global counter. -/
def Conn.oldRound (c : Conn) (r : Id) (k : Nat) : Bool :=
  let active := c.active.any (fun p => Decidable.decide (p = (r, k)))
  (c.dialer && !active) ||
    match c.epochs.find? (fun p => Decidable.decide (p.1 = r)) with
    | none => false
    | some (_, seen) => Decidable.decide (k < seen) || (Decidable.decide (k = seen) && !active)

/-- Capture a newer round's overlap (the floor its set S is read at),
including on the responder. Replies for a room still on an earlier epoch
do not rewind the global counter. -/
def Conn.beginRound (c : Conn) (k : Nat) : Conn :=
  { c with
    round := max c.round k
    roundFloor := if c.round < k then max c.floor (c.peerFloor.getD c.floor) else c.roundFloor }

/-- Room r is due a round at `now`: none has opened in it on this session
(it is newly shown, or the responder asked), or the last opened
`safety` ms ago or more. -/
def Conn.due (c : Conn) (r : Id) (now : Nat) : Bool :=
  match c.roundedAt r with
  | none => true
  | some t => Decidable.decide (t + cfg.safety ≤ now)

/-- Room r is due again for what its last round could not ask for: it is
`short`, no round of it is in flight here, and the asks are at most half
full (and have room). -/
def Conn.retake (c : Conn) (r : Id) : Bool :=
  has c.short r && !c.active.any (fun p => Decidable.decide (p.1 = r)) &&
    Decidable.decide (2 * c.asked.size ≤ cfg.maxKnown) && Decidable.decide (c.asked.size < cfg.maxKnown)

/-- The dialer opens a round in every shown room that is due, all with
the next epoch; a room's newer round supersedes the one in flight there.
With no room due it does nothing. -/
def Conn.start (ix : Index) (c : Conn) (now : Nat) : Step :=
  match c.peerFloor with
  | none => { conn := c }
  | some pf =>
    let ready := c.rooms.filter fun r => c.due cfg r now || c.retake cfg r
    if ready.isEmpty then { conn := c } else
    let k := c.round + 1
    let f := max c.floor pf
    let send := ready.map fun r =>
      (Msg.rbsr r k ((window 0).map (ix.opening cfg.params r f))).op
    { conn := { c.beginRound k with
        active := (ready.map (·, k) ++ c.active.filter fun p => !has ready p.1).take c.rooms.length
        rounded := ready.foldl (fun rs r => noteEpoch c.rooms.length rs r now) c.rounded
        short := c.short.filter fun r => !has ready r
        epochs := ready.foldl (fun es r => noteEpoch c.rooms.length es r k) c.epochs }, send }

/-- The responder asks for a round in each shown room it has neither seen
a round in nor asked about on this session, and in each it is `short`
in (`retake`): an empty have naming it. -/
def Conn.ask (c : Conn) (now : Nat) : Step :=
  match c.peerFloor with
  | none => { conn := c }
  | some _ =>
    let fresh := c.rooms.filter fun r => (c.roundedAt r).isNone || c.retake cfg r
    if fresh.isEmpty then { conn := c } else
    { conn := { c with
        rounded := fresh.foldl (fun rs r => noteEpoch c.rooms.length rs r now) c.rounded
        short := c.short.filter fun r => !has fresh r }
      send := fresh.map fun r => (Msg.hold r []).op }

@[simp] theorem Conn.start_drop (ix : Index) (c : Conn) (now : Nat) : (c.start cfg ix now).drop = false := by
  unfold Conn.start; split
  · rfl
  · dsimp only; split <;> rfl

@[simp] theorem Conn.start_take (ix : Index) (c : Conn) (now : Nat) : (c.start cfg ix now).take = [] := by
  unfold Conn.start; split
  · rfl
  · dsimp only; split <;> rfl

@[simp] theorem Conn.start_given (ix : Index) (c : Conn) (now : Nat) :
    (c.start cfg ix now).conn.given = c.given ∧ (c.start cfg ix now).given = [] := by
  unfold Conn.start; split
  · exact ⟨rfl, rfl⟩
  · dsimp only; split
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩

@[simp] theorem Conn.ask_drop (c : Conn) (now : Nat) : (c.ask cfg now).drop = false := by
  unfold Conn.ask; split
  · rfl
  · dsimp only; split <;> rfl

@[simp] theorem Conn.ask_take (c : Conn) (now : Nat) : (c.ask cfg now).take = [] := by
  unfold Conn.ask; split
  · rfl
  · dsimp only; split <;> rfl

@[simp] theorem Conn.ask_given (c : Conn) (now : Nat) :
    (c.ask cfg now).conn.given = c.given ∧ (c.ask cfg now).given = [] := by
  unfold Conn.ask; split
  · exact ⟨rfl, rfl⟩
  · dsimp only; split
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩

/-- The peer asks for a round in room r (an empty have naming it): the
dialer makes a shown room with no round in flight due. -/
def Conn.onAsk (c : Conn) (r : Id) : Conn :=
  if c.dialer && has c.rooms r && !c.active.any (fun p => Decidable.decide (p.1 = r)) then
    { c with rounded := c.rounded.filter fun p => !Decidable.decide (p.1 = r) }
  else c

/-- What `start` changes: nothing, or the round state only (the round
counter and closure capture, the rounds in flight, when each room's
round opened, the epochs). -/
theorem Conn.start_conn (ix : Index) (c : Conn) (now : Nat) :
    (c.start cfg ix now).conn = c ∨ ∃ k a rs ss es,
      (c.start cfg ix now).conn = { c.beginRound k with active := a, rounded := rs, short := ss, epochs := es } := by
  unfold Conn.start; split
  · exact Or.inl rfl
  · dsimp only; split
    · exact Or.inl rfl
    · exact Or.inr ⟨_, _, _, _, _, rfl⟩

/-- What `ask` changes: when each room's round was asked for, and which
rooms are short, only. -/
theorem Conn.ask_conn (c : Conn) (now : Nat) :
    ∃ rs ss, (c.ask cfg now).conn = { c with rounded := rs, short := ss } := by
  unfold Conn.ask; split
  · exact ⟨c.rounded, c.short, rfl⟩
  · dsimp only; split
    · exact ⟨c.rounded, c.short, rfl⟩
    · exact ⟨_, _, rfl⟩

/-- What `onAsk` changes: when each room's round opened, only. -/
theorem Conn.onAsk_eq (c : Conn) (r : Id) : ∃ rs, c.onAsk r = { c with rounded := rs } := by
  unfold Conn.onAsk; split
  · exact ⟨_, rfl⟩
  · exact ⟨c.rounded, rfl⟩

@[simp] theorem Conn.onAsk_heard (c : Conn) (r : Id) : (c.onAsk r).heard = c.heard := by
  obtain ⟨rs, e⟩ := Conn.onAsk_eq c r; rw [e]
@[simp] theorem Conn.onAsk_rooms (c : Conn) (r : Id) : (c.onAsk r).rooms = c.rooms := by
  obtain ⟨rs, e⟩ := Conn.onAsk_eq c r; rw [e]
@[simp] theorem Conn.onAsk_sent (c : Conn) (r : Id) : (c.onAsk r).sent = c.sent := by
  obtain ⟨rs, e⟩ := Conn.onAsk_eq c r; rw [e]
@[simp] theorem Conn.onAsk_given (c : Conn) (r : Id) : (c.onAsk r).given = c.given := by
  obtain ⟨rs, e⟩ := Conn.onAsk_eq c r; rw [e]
@[simp] theorem Conn.onAsk_session (c : Conn) (r : Id) : (c.onAsk r).session = c.session := by
  obtain ⟨rs, e⟩ := Conn.onAsk_eq c r; rw [e]
@[simp] theorem Conn.onAsk_dialer (c : Conn) (r : Id) : (c.onAsk r).dialer = c.dialer := by
  obtain ⟨rs, e⟩ := Conn.onAsk_eq c r; rw [e]

/-- A round's message about room r: answer its claims from the room as
the live index holds it now; no claims ends the round. -/
def Conn.onRbsr (ix : Index) (c : Conn) (r : Id) (k : Nat) (cs : List Claim) (now : Nat) : Step :=
  if !has c.rooms r then { conn := c, send := [(Msg.rbsr r k []).op] } else
  if c.oldRound r k then { conn := c } else
  let c := { c.beginRound k with
    epochs := noteEpoch c.rooms.length c.epochs r k
    rounded := if c.dialer then c.rounded else noteEpoch c.rooms.length c.rounded r now }
  let others := c.active.filter fun p => !Decidable.decide (p.1 = r)
  let ended (c : Conn) : Conn :=
    { c with active := others }
  if cs.isEmpty then { conn := ended c } else
  let outs := cs.flatMap (ix.answer cfg.params r c.roundFloor)
  let claims := claimsOf outs
  let holds := outs.flatMap holdIds
  let wants := outs.flatMap fun | .want xs => xs | _ => []
  let c := if claims.isEmpty then ended c else { c with active := ((r, k) :: others).take c.rooms.length }
  let cut := deferred cfg.maxKnown c.asked wants
  let wants := admitAsks cfg.maxKnown c.asked wants
  let c := { c with
    askTime := wants.foldl (fun ts i => ts.insert i now) c.askTime
    asked := wants.foldl (·.insert ·) c.asked
    short := if cut then noteRoom c.rooms.length c.short r else c.short }
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
  let cut := deferred cfg.maxKnown c.asked want.reverse
  let accepted := admitAsks cfg.maxKnown c.asked want.reverse
  let kept := ids.filter fun i => !missing.contains i || accepted.contains i
  let c := { c with
    known := kept.foldl (remember cfg.maxKnown) c.known
    asked := accepted.foldl (·.insert ·) c.asked
    askTime := accepted.foldl (fun ts i => ts.insert i c.heard) c.askTime
    short := if cut then noteRoom c.rooms.length c.short r else c.short }
  return { conn := c, send := chunks cfg accepted .want }


/-- Authorize ids using only the shown rooms' index, before any blob read. -/
def authorize (ix : Index) (c : Conn) (ids : List Id) : List Id :=
  ids.filter fun i => c.rooms.any fun r => (ix.items r).any fun a => Decidable.decide (a.2 = i)

/-- The peer wants these: the ids authorized from the shown rooms'
index (before any read) and not queued already join the session's
queue, in order, while it holds fewer than `maxKnown`; `serveOwed`
serves them all. A want for more than `maxIds` ids is ignored. -/
def Conn.onWant (ix : Index) (c : Conn) (ids : List Id) : Step :=
  if ids.length > cfg.maxIds then { conn := c } else
  let add := ((authorize ix c ids).filter fun i => !c.owing.contains i).eraseDups.take (cfg.maxKnown - c.owed.length)
  { conn := { c with owed := c.owed ++ add, owing := add.foldl (·.insert ·) c.owing } }

/-- At most one urgent id per service: the first requested id from this
node's fresh writes. All unselected ids remain in the ordinary FIFO. -/
def Conn.hotOf (c : Conn) (first : List Id) : List Id := (first.filter c.owing.contains).eraseDups.take 1

/-- The rest of the queue, served in order. -/
def Conn.owedAfter (c : Conn) (first : List Id) : List Id :=
  if (c.hotOf first).isEmpty then c.owed else c.owed.filter fun i => !(c.hotOf first).contains i

/-- The queue after a step: `gone` left it, `rest` is what remains, and
the ops `sent` the peer now holds. -/
def Conn.served (c : Conn) (gone rest : List Id) (sent : List Op) : Conn :=
  { c with
    owed := rest
    owing := gone.foldl (·.erase ·) c.owing
    known := sent.foldl (fun (k : HashSet Id) (o : Op) => remember cfg.maxKnown k o.id) c.known }

/-- Serve the queue (docs/SYNC.md, "Lanes"): first the queued ids in
`first` (this node's fresh writes), at most one, whatever the budget;
then from the
front, until `budget` bytes are out (the op that reaches it goes
whole). An id not stored, or not in a room the session shows now,
leaves the queue unanswered: the peer's ask for it expires. The urgent
ops, and the serve lane's. -/
def Conn.serveOwed (c : Conn) (budget : Nat) (first : List Id) : m (Conn × List Op × List Op) := do
  let urgent ← (fetch (c.shows fam) (c.hotOf first)).run (Store.getOp (F := F))
  let owed := c.owedAfter first
  let (bulk, rest) ← (serve (c.shows fam) budget owed).run (Store.getOp (F := F))
  return (c.served cfg (c.hotOf first ++ owed.take (owed.length - rest.length)) rest (urgent ++ bulk), urgent, bulk)

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
      -- was lost. Answer its hello once it can open session frames. The
      -- dialer's answer opens a round in every room it shows, so the
      -- responder asks for none of the rooms it shows now.
      return (if c.dialer then c.start cfg ix now else
        { conn := { c with rounded := c.rooms.map (·, now) }, send := [(Msg.hello c.floor).op] })
    | some (.rbsr r k cs) => return (c.onRbsr cfg ix r k cs now)
    | some (.hold r ids) =>
      if ids.isEmpty then return { conn := c.onAsk r }
      else return (← c.onHold fam cfg r ids)
    | some (.want ids) => return c.onWant cfg ix ids
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

/-- Work due on a live session: the rounds due (the dialer) or asked for
(the responder), and retries. It reads no op: a windowed round reads its
closure in the round (S), with no walk left for ticks; the family stays
a parameter, as for every connection step. -/
def Conn.work (_fam : Family F) (cfg : Config) (ix : Index) (c : Conn) (now : Nat) : m Step := do
  let c := c.expireAsks cfg now
  let s := if c.dialer then c.start cfg ix now else c.ask cfg now
  let due := c.lastAsk + cfg.retry ≤ now
  return { s with
    conn := { s.conn with lastAsk := if due then now else c.lastAsk }
    send := s.send ++ chunks cfg (c.retryIds cfg now) .want }

/-- The clock has one drop rule, independent of rooms and outstanding work. -/
def Conn.tick (ix : Index) (c : Conn) (now : Nat) : m Step := do
  if c.heard + cfg.live < now then return { conn := { c with session := c.session.close }, drop := true }
  return (← c.work fam cfg ix now).pulse cfg c.sent now

/-- The rooms the peer may see changed: forget the others' rounds. A
room's round record is kept only if it was shown before and is still,
so a room the session starts showing is due (`shown_due`). -/
def Conn.setRooms (c : Conn) (rooms : List Id) : Conn :=
  { c with
    rooms
    active := (c.active.filter fun p => has rooms p.1).take rooms.length
    rounded := (c.rounded.filter fun p => has rooms p.1 && has c.rooms p.1).take rooms.length
    short := (c.short.filter fun r => has rooms r).take rooms.length
    epochs := (c.epochs.filter fun p => has rooms p.1).take rooms.length }

end

end Engine.Sync
