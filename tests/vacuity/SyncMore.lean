import tests.vacuity.FairScheduler
import tests.vacuity.Network
import engine.sync.RetryLaws
import engine.sync.StateLaws
import engine.sync.ClosureComplete
import engine.sync.TreeLaws
import engine.wire.Slots
import engine.wire.Frame
import engine.wire.CloseLaws

set_option maxRecDepth 4096

namespace Vacuity.SyncMore
open Engine Engine.Sync
open Vacuity.Network
attribute [local instance] byteArray_lawfulBEq

-- Concrete small socket frames; both queues are occupied.
def urgentFrame : ByteArray := "hello".toUTF8
def bulkFrame : ByteArray := "chunk-0001".toUTF8
def lanes : Lanes := { urgent := [urgentFrame], serve := [bulkFrame, bulkFrame] }
def pushes : List (Lane × ByteArray) := [(.serve, bulkFrame), (.urgent, urgentFrame)]

theorem urgentFirst : (((lanes.push .urgent urgentFrame).pushAll pushes).take 12).1 =
    lanes.urgent ++ urgentFrame :: (urgents pushes ++ (cut 12 (lanes.serve ++ serves pushes)).1) :=
  urgent_ahead 12 lanes urgentFrame pushes

example : (((lanes.push .urgent urgentFrame).pushAll pushes).take 12).1 =
    [urgentFrame, urgentFrame, urgentFrame, bulkFrame] := by decide

theorem burstBound : bytesOf (cut 12 [bulkFrame, bulkFrame]).1 ≤ max 12 bulkFrame.size :=
  cut_bytes 12 [bulkFrame, bulkFrame]

-- The push is admitted under 64 bytes, and whatever admission returns is
-- the lanes with both pushes, within the cap.
theorem pushBound : (lanes.admit 64 pushes).isSome ∧
    ∀ q', lanes.admit 64 pushes = some q' → q' = lanes.pushAll pushes ∧ q'.bytes ≤ 64 :=
  ⟨by decide, fun q' h => push_capped 64 lanes q' pushes h⟩

example : lanes.admit 20 pushes = none := by decide

theorem firstWrite : (Inbox.next true popW popE).run (["send Alice", "send Bob"], ["frame1", "frame2"]) =
    ((some (.inl "send Alice"), false), (["send Bob"], ["frame1", "frame2"])) :=
  write_first "send Alice" ["send Bob"] ["frame1", "frame2"]

theorem writeDeadline : ∃ j, 0 ≤ j ∧ j < 4 ∧
    Vacuity.FairScheduler.queues.selected j = some (.inl "send Bob") :=
  write_within Vacuity.FairScheduler.queues 0 ["send Alice"] [] "send Bob" rfl

theorem socketAdmission : ("10.0.0.2" :: ["10.0.0.1"]).length ≤ ({} : RunConfig).maxSocks ∧
    (("10.0.0.2" :: ["10.0.0.1"]).filter (· == "10.0.0.2")).length ≤ ({} : RunConfig).perAddr :=
  admit_bounded {} ["10.0.0.1"] "10.0.0.2" (by decide)

def afterWant : Conn := (conn.onWant cfg ix [msg.id]).conn

theorem afterWantReachable : afterWant.Reachable fam cfg :=
  .want (.open false [room] 0 0) ix [msg.id]

theorem knownAskedBounds : afterWant.known.size ≤ cfg.maxKnown ∧ afterWant.asked.size ≤ cfg.maxKnown :=
  conn_bounded fam cfg afterWantReachable

theorem stateBounds : afterWant.known.size ≤ cfg.maxKnown ∧ afterWant.asked.size ≤ cfg.maxKnown ∧
    afterWant.offered.size ≤ cfg.maxKnown ∧ afterWant.closed.size + afterWant.frontier.length ≤ cfg.closureCap ∧
    afterWant.active.length ≤ afterWant.rooms.length ∧ afterWant.rounded.length ≤ afterWant.rooms.length ∧
    afterWant.epochs.length ≤ afterWant.rooms.length ∧ afterWant.short.length ≤ afterWant.rooms.length :=
  conn_state_bounded fam cfg afterWantReachable

theorem holdBounds : ((conn.onHold fam cfg room [msg.id] : HeldM Unit Step) {}).1.conn.Bounded cfg :=
  hold_bounded fam cfg conn room [msg.id] {} (by simp [Conn.Bounded, conn, Conn.open, cfg])

theorem serviceBytes :
    let bulk := ((queued.serveOwed fam cfg 1024 [] : HeldM Unit _) held).1.2.2
    replyBytes bulk ≤ 1024 + largestOp bulk := serveOwed_budget fam cfg queued 1024 [] held

theorem timeoutReason : conn.heard + cfg.live < 90001 :=
  honest_no_drop fam cfg conn 90001 held _ (.tick {}) timesOut

-- A real outstanding ask exists before expiring.
def asking : Conn := { conn with asked := ({} : Std.HashSet Id).insert msg.id }
example : msg.id ∈ asking.asked := by simp [asking]
theorem askExpired : msg.id ∉ (asking.expireAsks cfg 20001).asked :=
  asks_expire cfg asking 20001 msg.id (by simp [asking, conn, Conn.open, cfg])

-- A nonempty closure frontier visits a stored leaf, under a windowed round.
def walking : Conn := { conn with roundFloor := 100, frontier := [msg.id] }
theorem walkBound : ((walking.walkN fam cfg [] 1 : HeldM Unit _) held).1.1.ClosureBounded cfg :=
  closure_capped fam cfg held 1 walking [] (by simp [Conn.ClosureBounded, walking, conn, Conn.open, cfg])

theorem wholeLeaf : Whole fam held walking [msg.id] := by
  intro i hi
  obtain rfl := List.mem_singleton.mp hi
  exact ⟨msg, stored, shown, by simp [msg]⟩

theorem closureComplete :
    let result := ((walking.walk fam cfg : HeldM Unit _) held).1
    result.1.frontier = [] ∧ ∀ seed ∈ walking.frontier, ∀ i,
      Reach held.db.ops seed i → covered result.1 result.2 i :=
  closure_complete_under_cap fam cfg held walking [msg.id] (by decide) rfl
    (by simp [walking]) (by simp [walking]) wholeLeaf (by decide) (by decide)

theorem fullRound :
    let d := queued.served cfg [msg.id] [] [msg]
    d.offered = queued.offered ∧ d.closed = queued.closed ∧ d.frontier = queued.frontier :=
  full_round_stateless cfg queued [msg.id] [] [msg] (by decide)

-- A partial frame retains a nonempty prefix, while an oversized declared
-- length is rejected before its payload is received.
def partialFrame : ByteArray := be32 5 ++ "he".toUTF8

theorem partialKept : (frames partialFrame).2 = some partialFrame := by
  rw [frames, show unframe partialFrame = .more from rfl]

theorem keptBound : partialFrame.size < 4 + maxFrame ∧
    ∀ n, lenAt partialFrame = some n → n ≤ maxFrame := frames_kept partialKept

theorem readerBound : partialFrame.size < 4 + maxFrame :=
  buffer_bounded [partialFrame] partialFrame (by simp [keeps, partialKept])

theorem oversizedRejected : frames (be32 1048577) = ([], none) :=
  frames_tooBig (n := 1048577) (by decide) (by decide)

-- Finite round fixture: two peers each have two items, one shared. Identity
-- hashing witnesses collision-freedom without an assumed SHA-256 property.
def key (n : Nat) : Key := ⟨0, n⟩
def ident (n : Nat) : ByteArray := Codec.encode n
def digest (b : ByteArray) : ByteArray := b
def xs : List Nat := [1, 2]
def ys : List Nat := [2, 3]
def range : Range := ⟨⟨0, 0⟩, none⟩
def params : Params := {}

theorem sortedX : Sorted key xs := by unfold Sorted xs; decide
theorem sortedY : Sorted key ys := by unfold Sorted ys; decide
theorem namedXY : Named key ident (xs ++ ys) := by
  intro a _ b _
  constructor
  · intro h
    exact congrArg Key.n h
  · intro h
    have h' := congrArg (Codec.decode (α := Nat)) h
    simpa [ident, Codec.decode_encode] using h'

theorem soundXY : Sound key ident digest xs ys := by
  intro r a _ b _ h
  exact h

theorem openingHonest : Honest key ident digest ys range (opening key ident digest params ys range) :=
  opening_honest ys range

theorem roundComplete :
    (ident 1 ∈ (exchange key ident digest params 5 xs ys (opening key ident digest params ys range)).1 ↔
      named ident (within key range xs) (ident 1) = true ∧ named ident (within key range ys) (ident 1) = false) ∧
    (ident 1 ∈ (exchange key ident digest params 5 xs ys (opening key ident digest params ys range)).2 ↔
      named ident (within key range ys) (ident 1) = true ∧ named ident (within key range xs) (ident 1) = false) :=
  exchange_complete 5 xs ys range _ sortedX sortedY namedXY soundXY openingHonest (by decide) (ident 1)

theorem sendsMissing : ident 1 ∈
    (exchange key ident digest params 5 xs ys (opening key ident digest params ys range)).1 :=
  roundComplete.1.mpr (by
    constructor
    · apply named_iff.mpr
      exact ⟨1, by decide, rfl⟩
    · apply named_false.mpr
      intro a ha he
      have h := congrArg (Codec.decode (α := Nat)) he
      have eq : a = 1 := by simpa [ident, Codec.decode_encode] using h
      subst a
      exact (by decide : 1 ∉ within key range ys) ha)

-- The overlapping item is not sent in either direction.
example : named ident (within key range xs) (ident 2) = true ∧
    named ident (within key range ys) (ident 2) = true  := by
  constructor <;> apply named_iff.mpr <;> exact ⟨2, by decide, rfl⟩

theorem roundLog :
    (ident 1 ∈ (exchange key ident digest params 2 xs ys (opening key ident digest params ys range)).1 ↔
      named ident (within key range xs) (ident 1) = true ∧ named ident (within key range ys) (ident 1) = false) ∧
    (ident 1 ∈ (exchange key ident digest params 2 xs ys (opening key ident digest params ys range)).2 ↔
      named ident (within key range ys) (ident 1) = true ∧ named ident (within key range xs) (ident 1) = false) :=
  Tree.exchange_log ident digest params 2 xs ys range _ 0 0 sortedX sortedY namedXY soundXY openingHonest
    (by decide) (by decide) (by decide) (ident 1)

theorem idsStable : exchange key ident digest params 1 xs ys (.ids range [ident 2, ident 3]) =
    exchange key ident digest params 5 xs ys (.ids range [ident 2, ident 3]) :=
  Tree.exchange_ids_stable ident digest params 0 4 xs ys range [ident 2, ident 3]

theorem fingerprintStable : exchange key ident digest params 2 xs ys
    (.fp range 2 (lbl key ident digest ys)) = exchange key ident digest params 5 xs ys
    (.fp range 2 (lbl key ident digest ys)) :=
  Tree.exchange_stable ident digest params 2 5 xs ys range 2 (lbl key ident digest ys) 0 0
    sortedX sortedY (by decide) (by decide) (by decide) (by decide)

def setup : Setup Unit := ⟨fam, cfg, fun _ _ => [room]⟩
def freshNode : Node := { ix, floor := 0, hot := [(msg.id, 100)] }

theorem controlUrgent : wireLane (setup.sync .a) (Msg.want [msg.id]).op = .urgent :=
  lane_control (setup.sync .a) _ (by simp [Msg.op, setup, Setup.sync, cfg])

theorem freshHot : msg.id ∈ freshNode.hotIds (setup.sync .a) 200 :=
  hot_ids (setup.sync .a) freshNode msg.id 100 200 (by simp [freshNode]) (by decide)

theorem bootCache : Cached fam (Node.boot fam (held.db.stored.filterMap held.db.ops) 0) held.db :=
  boot_cached fam held.db 0

-- Closing hook really names a stored local secret, so the removal premise
-- is inhabited rather than an empty closing list.
def closeSync : Sync Unit (HeldM Unit) :=
  { fam := localFamily, cfg, hooks := { (setup.sync .a).hooks with closing := fun _ => pure [secret.id] } }

theorem localSecretStored : secretHeld.db.ops secret.id = some secret := by
  simp [secretHeld, DB.putOp]

theorem closeErases : ((Node.endSession closeSync sessionId : HeldM Unit Effects) secretHeld).2.db.ops secret.id = none :=
  close_gone closeSync sessionId secretHeld [secret.id] rfl secret.id secret (by simp)
    localSecretStored secretNotShared

theorem namedSecretPurged :
    (purgeS localFamily [secret.id] secretHeld.db).ops secret.id = none ∧
    ∀ k, secret.id ∉ (purgeS localFamily [secret.id] secretHeld.db).idx k :=
  purge_named secretHeld.db (by simp) localSecretStored secretNotShared

end Vacuity.SyncMore
