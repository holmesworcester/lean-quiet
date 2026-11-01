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
import engine.sync.Wire
import engine.sync.Session
import engine.sync.Serve
import engine.sync.Closure
import engine.sync.TreapAnswer
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

theorem ins_mem {a c : Item} : ∀ {l : List Item}, c ∈ ins a l → c = a ∨ c ∈ l
  | [], h => by simp only [ins, List.mem_singleton] at h; exact Or.inl h
  | b :: t, h => by
    unfold ins at h
    split at h
    · rcases List.mem_cons.1 h with h | h
      · exact Or.inl h
      · exact Or.inr h
    · split at h
      · exact Or.inr h
      · rcases List.mem_cons.1 h with h | h
        · exact Or.inr (h ▸ List.mem_cons_self ..)
        · rcases ins_mem h with h | h
          · exact Or.inl h
          · exact Or.inr (List.mem_cons_of_mem _ h)

theorem ins_sorted (a : Item) : ∀ {l : List Item}, Sorted Prod.fst l → Sorted Prod.fst (ins a l)
  | [], _ => List.pairwise_singleton _ _
  | b :: t, hs => by
    have hb := (List.pairwise_cons.1 hs).1
    have ht := (List.pairwise_cons.1 hs).2
    unfold ins
    split
    · rename_i hab
      refine List.pairwise_cons.2 ⟨fun c hc => ?_, hs⟩
      rcases List.mem_cons.1 hc with rfl | hc
      · exact hab
      · exact Key.lt_trans hab (hb c hc)
    · split
      · exact hs
      · rename_i hab hne
        have hba : b.1 < a.1 := by
          rcases Key.lt_trichotomy a.1 b.1 with h | h | h
          · exact absurd h hab
          · exact absurd h hne
          · exact h
        refine List.pairwise_cons.2 ⟨fun c hc => ?_, ins_sorted a ht⟩
        rcases ins_mem hc with rfl | hc
        · exact hba
        · exact hb c hc

end

/-! ## Rooms: each its canonical Merkle treap -/

/-- A room's items, held as their canonical Merkle treap
(engine/sync/TreapAnswer.lean), with what makes it theirs: it is the
canonical treap of its items in key order, and they are sorted. A range's
fingerprint is then two splits (`Index.opening`, `Index.answer`); an
insert hashes once per level. -/
structure RoomTree where
  tree : Treap Item
  canonical : tree = canon Prod.fst Prod.snd sha256 tree.toList ∧ Sorted Prod.fst tree.toList

/-- The room of these sorted items. -/
def RoomTree.ofSorted (l : List Item) (hs : Sorted Prod.fst l) : RoomTree :=
  ⟨canon Prod.fst Prod.snd sha256 l, by
    rw [toList_canon' Prod.fst Prod.snd sha256 hs]; exact ⟨rfl, hs⟩⟩

instance : Inhabited RoomTree := ⟨RoomTree.ofSorted [] List.Pairwise.nil⟩

/-- The room's items in key order. -/
def RoomTree.items (rm : RoomTree) : List Item := rm.tree.toList

theorem RoomTree.tree_eq (rm : RoomTree) : rm.tree = canon Prod.fst Prod.snd sha256 rm.items := rm.canonical.1
theorem RoomTree.sorted (rm : RoomTree) : Sorted Prod.fst rm.items := rm.canonical.2

/-- ins of an item whose key is new: the list with it, in some order. -/
theorem ins_perm (a : Item) : ∀ {l : List Item}, (∀ b ∈ l, b.1 ≠ a.1) → (ins a l).Perm (a :: l)
  | [], _ => List.Perm.refl _
  | b :: t, hk => by
    unfold ins
    split
    · exact List.Perm.refl _
    · split
      · rename_i h; exact absurd h.symm (hk b (List.mem_cons_self ..))
      · exact ((ins_perm a fun c hc => hk c (List.mem_cons_of_mem _ hc)).cons b).trans (List.Perm.swap a b t)

/-- ins of an item whose key a sorted list holds already leaves it. -/
theorem ins_held (a : Item) : ∀ {l : List Item}, Sorted Prod.fst l → (∃ b ∈ l, b.1 = a.1) → ins a l = l
  | [], _, ⟨_, hb, _⟩ => by cases hb
  | b :: t, hs, ⟨c, hc, e⟩ => by
    have hb := (List.pairwise_cons.1 hs).1
    unfold ins
    rcases List.mem_cons.1 hc with rfl | hc
    · rw [if_neg (by rw [e]; exact Key.lt_irrefl _), if_pos e.symm]
    · have hbc := hb c hc
      rw [if_neg (by rw [← e]; exact Key.lt_asymm hbc), if_neg (by rw [← e]; exact fun h => Key.lt_irrefl _ (h ▸ hbc))]
      rw [ins_held a (List.pairwise_cons.1 hs).2 ⟨c, hc, e⟩]

theorem RoomTree.sorted_filter (rm : RoomTree) (q : Item → Bool) : Sorted Prod.fst (rm.items.filter q) :=
  List.Pairwise.filter _ rm.sorted

/-- An item whose key is new, before sorted items: no two share a key. -/
theorem untied_cons {a : Item} {l : List Item} (hs : Sorted Prod.fst l) (hn : ∀ b ∈ l, b.1 ≠ a.1) :
    Untied Prod.fst (a :: l) := by
  intro x hx y hy exy
  cases List.mem_cons.1 hx with
  | inl hxa =>
    cases List.mem_cons.1 hy with
    | inl hya => rw [hxa, hya]
    | inr hyu => exact absurd (by rw [← exy, hxa]) (hn y hyu)
  | inr hxu =>
    cases List.mem_cons.1 hy with
    | inl hya => exact absurd (by rw [exy, hya]) (hn x hxu)
    | inr hyu => exact sorted_prio Prod.fst hs x hxu y hyu exy

/-- The room with an item: unchanged if its key is the room's already;
otherwise inserted into the treap, one hash per level and one more. -/
def RoomTree.add (rm : RoomTree) (a : Item) : RoomTree :=
  if hk : rm.tree.hasKey Prod.fst a.1 = true then rm
  else ⟨rm.tree.insert Prod.fst Prod.snd sha256 a, by
    have e := rm.tree_eq
    have hs := rm.sorted
    have hn : ∀ b ∈ rm.items, b.1 ≠ a.1 := fun b hb e' => hk (by
      rw [e]; exact (hasKey_canon' Prod.fst Prod.snd sha256 hs a.1).2 ⟨b, hb, e'⟩)
    have hna : a ∉ rm.items := fun h => hn a h rfl
    have hapart : Untied Prod.fst (a :: rm.items) := untied_cons hs hn
    have hi : rm.tree.insert Prod.fst Prod.snd sha256 a = canon Prod.fst Prod.snd sha256 (ins a rm.items) := by
      rw [e, insert_canon Prod.fst Prod.snd sha256 a _ _ (Nat.le_refl _) hna hapart hapart]
      exact canon_perm Prod.fst Prod.snd sha256 _ _ _ (Nat.le_refl _) hapart (ins_perm a hn).symm
    rw [hi, toList_canon' Prod.fst Prod.snd sha256 (ins_sorted a hs)]
    exact ⟨rfl, ins_sorted a hs⟩⟩

@[simp] theorem RoomTree.default_items : (default : RoomTree).items = [] := by
  show (canon Prod.fst Prod.snd sha256 ([] : List Item)).toList = []
  rw [canon_nil]; rfl

/-- **A room's items after an add are `ins`'s.** -/
theorem RoomTree.items_add (rm : RoomTree) (a : Item) : (rm.add a).items = ins a rm.items := by
  unfold RoomTree.add
  split
  · rename_i hk
    rw [rm.tree_eq] at hk
    exact (ins_held a rm.sorted ((hasKey_canon' Prod.fst Prod.snd sha256 rm.sorted a.1).1 hk)).symm
  · show (Treap.insert Prod.fst Prod.snd sha256 a rm.tree).toList = _
    rename_i hk
    have e := rm.tree_eq
    have hs := rm.sorted
    have hn : ∀ b ∈ rm.items, b.1 ≠ a.1 := fun b hb e' => hk (by
      rw [e]; exact (hasKey_canon' Prod.fst Prod.snd sha256 hs a.1).2 ⟨b, hb, e'⟩)
    have hapart : Untied Prod.fst (a :: rm.items) := untied_cons hs hn
    rw [e, insert_canon Prod.fst Prod.snd sha256 a _ _ (Nat.le_refl _) (fun h => hn a h rfl) hapart hapart,
      canon_perm Prod.fst Prod.snd sha256 _ _ _ (Nat.le_refl _) hapart (ins_perm a hn).symm,
      toList_canon' Prod.fst Prod.snd sha256 (ins_sorted a hs)]

/-- The room of these items, added in order (for tests and fixtures). -/
def RoomTree.ofList (l : List Item) : RoomTree := l.foldl RoomTree.add default

/-- Its items are `ins`'s, one at a time. -/
theorem RoomTree.ofList_items (l : List Item) : (RoomTree.ofList l).items = l.foldl (fun acc a => ins a acc) [] := by
  unfold RoomTree.ofList
  suffices ∀ (rm : RoomTree), (l.foldl RoomTree.add rm).items = l.foldl (fun acc a => ins a acc) rm.items by
    rw [this]; simp
  induction l with
  | nil => intro rm; rfl
  | cons a t ih => intro rm; simp only [List.foldl_cons]; rw [ih, RoomTree.items_add]

/-- Each room's canonical treap: what sync reconciles, kept in memory.
Built from the stored ops once (`ofOps`), then grown by each op stored
after (`add`), from the writer's notices. -/
structure Index where
  rooms : List (Id × RoomTree) := []
  deriving Inhabited

/-- RoomTree c, if it has items. -/
def Index.room? (ix : Index) (c : Id) : Option RoomTree :=
  (ix.rooms.find? fun p => Decidable.decide (p.1 = c)).map (·.2)

def Index.items (ix : Index) (c : Id) : List Item := ((ix.room? c).map (·.items)).getD []

/-- RoomTree c's treap (a leaf for a room with no items). -/
def Index.tree (ix : Index) (c : Id) : Treap Item := ((ix.room? c).map (·.tree)).getD .leaf

theorem Index.tree_eq (ix : Index) (c : Id) : ix.tree c = canon Prod.fst Prod.snd sha256 (ix.items c) := by
  unfold Index.tree Index.items
  cases ix.room? c with
  | none => exact (canon_nil Prod.fst Prod.snd sha256).symm
  | some rm => exact rm.tree_eq

theorem Index.sorted (ix : Index) (c : Id) : Sorted Prod.fst (ix.items c) := by
  unfold Index.items
  cases ix.room? c with
  | none => exact List.Pairwise.nil
  | some rm => exact rm.sorted

section
variable {F : Type} (fam : Family F)

/-- The index with a stored op added; a local op is no room's. -/
def Index.add (ix : Index) (o : Op) : Index :=
  match fam.room o with
  | none => ix
  | some c =>
    let a := (keyOf fam o, o.id)
    if ix.rooms.any (fun p => Decidable.decide (p.1 = c)) then
      ⟨ix.rooms.map fun p => if p.1 = c then (p.1, p.2.add a) else p⟩
    else ⟨(c, (default : RoomTree).add a) :: ix.rooms⟩

def Index.ofOps (ops : List Op) : Index := ops.foldl (Index.add fam) {}

end

/-- The index without a purged op (a room rebuilt; nothing on the
running path calls it: a purge takes no shared op). -/
def Index.remove (ix : Index) (x : Id) : Index :=
  ⟨ix.rooms.map fun p => (p.1, RoomTree.ofSorted (p.2.items.filter fun a => !Decidable.decide (a.2 = x))
    (RoomTree.sorted_filter p.2 _))⟩

/-- How this side opens a round over w in room r: two splits of the
room's treap at w's ends (`openingTM`, at most twice its height in
hashes). -/
def Index.opening (P : Params) (ix : Index) (r : Id) (w : Range) : Claim :=
  _root_.Id.run (openingTM Prod.fst Prod.snd sha256 P (ix.tree r) w)
/-- What this side answers to claim c in room r: from the room's treap
(`answerTM`, at most 2·(fan + 1)·height hashes). -/
def Index.answer (P : Params) (ix : Index) (r : Id) (c : Claim) : List Out :=
  _root_.Id.run (answerTM Prod.fst Prod.snd sha256 P (ix.tree r) c)
/-- **The opening that runs is `opening`'s** over the room's items. -/
theorem Index.opening_eq (P : Params) (ix : Index) (r : Id) (w : Range) :
    ix.opening P r w = Engine.Sync.opening Prod.fst Prod.snd sha256 P (ix.items r) w := by
  unfold Index.opening
  rw [run_eq_val, val_openingTM, ix.tree_eq, openingT_canon Prod.fst Prod.snd sha256 P (ix.sorted r)]
/-- **The answer that runs is `answer`'s** over the room's items. -/
theorem Index.answer_eq (P : Params) (ix : Index) (r : Id) (c : Claim) :
    ix.answer P r c = Engine.Sync.answer Prod.fst Prod.snd sha256 P (ix.items r) c := by
  unfold Index.answer
  rw [run_eq_val, val_answerTM, ix.tree_eq, answerT_canon Prod.fst Prod.snd sha256 P (ix.sorted r)]
/-- The two as functions, for rewriting under `map` and `flatMap`. -/
theorem Index.opening_fun (P : Params) (ix : Index) (r : Id) :
    ix.opening P r = Engine.Sync.opening Prod.fst Prod.snd sha256 P (ix.items r) :=
  funext (Index.opening_eq P ix r)
theorem Index.answer_fun (P : Params) (ix : Index) (r : Id) :
    ix.answer P r = Engine.Sync.answer Prod.fst Prod.snd sha256 P (ix.items r) :=
  funext (Index.answer_eq P ix r)

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
  /-- ids per have or want op; a want for more is ignored. -/
  maxIds : Nat := 4096
  /-- Distinct requirement ids retained by a windowed round. -/
  closureCap : Nat := 4096
  /-- ops the closure walk visits per call. -/
  walk : Nat := 100000
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
  lastRound : Nat := 0
  lastAsk : Nat := 0
  /-- The rounds in flight here, each with the snapshot it is answered from. -/
  snaps : List ((Id × Nat) × List Item) := []
  /-- Latest epoch seen in each room, retained after its snapshot is retired.
  Delayed terminal markers and replayed claims cannot rewind another round. -/
  epochs : List (Id × Nat) := []
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
  /-- Authorized wants queued in order, and their membership set. -/
  owed : List Id := []
  owing : HashSet Id := {}
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

/-- Remember a room's newest round, with at most one record per room. -/
def noteEpoch (limit : Nat) (epochs : List (Id × Nat)) (r : Id) (k : Nat) : List (Id × Nat) :=
  ((r, k) :: epochs.filter (fun p => !Decidable.decide (p.1 = r))).take limit

/-- An older epoch, a completed duplicate, or a reply to a round the dialer
never opened. Other rooms can lag behind the global counter. -/
def Conn.oldRound (c : Conn) (r : Id) (k : Nat) : Bool :=
  let active := c.snaps.any (fun p => Decidable.decide (p.1 = (r, k)))
  (c.dialer && !active) ||
    match c.epochs.find? (fun p => Decidable.decide (p.1 = r)) with
    | none => false
    | some (_, seen) => Decidable.decide (k < seen) || (Decidable.decide (k = seen) && !active)

/-- Capture a newer round's overlap, including on the responder. Replies
for a room still on an earlier epoch do not rewind the global counter or
clear the newer round's closure work. -/
def Conn.beginRound (c : Conn) (k : Nat) : Conn :=
  { c with
    round := max c.round k
    roundFloor := if c.round < k then max c.floor (c.peerFloor.getD c.floor) else c.roundFloor,
    closed := if c.round < k then {} else c.closed,
    frontier := if c.round < k then [] else c.frontier,
    closureCut := if c.round < k then false else c.closureCut }

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
    { conn := { c.beginRound k with
        lastRound := now
        snaps := (c.snaps ++ snaps).take c.rooms.length
        epochs := ready.foldl (fun es r => noteEpoch c.rooms.length es r k) c.epochs }, send }

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
  if c.oldRound r k then { conn := c } else
  let snap := c.snap ix r k
  let c := { c.beginRound k with epochs := noteEpoch c.rooms.length c.epochs r k }
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
the ops `sent` the peer now holds (their requirement closure is offered
on later ticks). -/
def Conn.served (c : Conn) (gone rest : List Id) (sent : List Op) : Conn :=
  { c with
    owed := rest
    owing := gone.foldl (·.erase ·) c.owing
    known := sent.foldl (fun (k : HashSet Id) (o : Op) => remember cfg.maxKnown k o.id) c.known } |>.queue cfg (sent.flatMap Op.reqs)

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
      -- was lost. Answer its hello once it can open session frames.
      return (if c.dialer then c.start cfg ix now else
        { conn := c, send := [(Msg.hello c.floor).op] })
    | some (.rbsr r k cs) => return (c.onRbsr cfg ix r k cs now)
    | some (.hold r ids) => return (← c.onHold fam cfg r ids)
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
  { c with
    rooms
    snaps := (c.snaps.filter fun p => has rooms p.1.1).take rooms.length
    epochs := (c.epochs.filter fun p => has rooms p.1).take rooms.length }

end

end Engine.Sync
