import tests.vacuity.SyncCache
import tests.vacuity.Query

namespace Vacuity.WireMore
open Engine Engine.Sync Vacuity.Network Vacuity.SyncMore
attribute [local instance] byteArray_lawfulBEq
private instance : LawfulMonad (HeldM Unit) := inferInstanceAs (LawfulMonad (StateM (Held Unit)))

def address : ByteArray := "127.0.0.1:43102".toUTF8
def sealedBytes : ByteArray := ⟨#[1, 99, 12, 0, 255]⟩
def rejectSync : Sync Unit (HeldM Unit) :=
  { closeSync with hooks := { closeSync.hooks with openFrame := fun _ => pure none } }

theorem sealedDispatch : freshNode.onFrame rejectSync address sealedBytes 200 =
    (rejectSync.hooks.openFrame (sealedBytes.extract 1 sealedBytes.size) >>= fun r =>
      freshNode.onSealed rejectSync address r 200) :=
  onFrame_sealed rejectSync freshNode address sealedBytes 200 rfl

theorem sealedRejected : freshNode.onFrame rejectSync address sealedBytes 200 held = ((freshNode, {}), held) :=
  sealed_unopened rejectSync freshNode address sealedBytes 200 held rfl rfl

-- A nonempty drop list uses the closing hook that names the stored local
-- secret. closeErases independently verifies the actual deletion.
def closeRunner := close_purges closeSync freshNode { drop := [sessionId] } 200

def purgeReported := purges_notified closeSync [secret.id] true

def courierBox : List (Id × ByteArray × ByteArray) := [(secret.id, address, sealedBytes)]
def courierSync : Sync Unit (HeldM Unit) :=
  { closeSync with hooks := { closeSync.hooks with outbox := pure courierBox } }
theorem courierNotified :
    ((freshNode.flush courierSync {} : HeldM Unit _) secretHeld).1.1.purged = freshNode.purged ++ courierBox.map (·.1) :=
  flush_notifies courierSync freshNode {} secretHeld courierBox rfl

-- The waiting-store queue differs while the requested bytes agree; serving
-- reads only the owed/priority ids and ignores that pending processing work.
def queuedStore : Held Unit := { held with db := { held.db with queue := [msg.id] } }
theorem servingBlind : ((queued.serveOwed fam cfg 1024 [msg.id] : HeldM Unit _) held).1 =
    ((queued.serveOwed fam cfg 1024 [msg.id] : HeldM Unit _) queuedStore).1 :=
  serveOwed_blind fam cfg queued 1024 [msg.id] held queuedStore (fun _ _ => rfl)

def openPremises := have_shown_premises fam false [room] 0 100

def secrecyRun := secrecy_runs room

-- Fresh urgent frame arrives while a prior nonempty write is in flight.
def initialPushes : List (Lane × ByteArray) :=
  [(.urgent, urgentFrame), (.serve, bulkFrame), (.serve, bulkFrame)]
theorem lanesReach : Lanes.Reach 64 12 lanes := by
  apply Lanes.Reach.push initialPushes .empty
  unfold Lanes.admit
  rw [ite_eq_left (by decide)]
  rfl

def ahead := ahead_bytes 64 12 lanes pushes [(.serve, bulkFrame)] urgentFrame lanesReach (by decide)

theorem popsWrite : (popW (W := String) (E := String)).run (["Alice sends hello", "Bob replies"], ["TCP frame"]) =
    (some "Alice sends hello", (["Bob replies"], ["TCP frame"])) := rfl

-- The journal executor is witnessed through a genuinely newly visible row.
theorem runJFiles : Vacuity.Query.row ∈ (eval Vacuity.Query.afterStep Vacuity.Query.allRows).rows :=
  Vacuity.Query.actualRead

-- A proved-injective digest for the two-item label check; this is not a
-- claim that fixed-size SHA-256 is injective.
theorem namedReordered : Named key ident (xs ++ xs.reverse) := by
  intro a _ b _
  constructor
  · exact fun h => congrArg Key.n h
  · intro h
    have h' := congrArg (Codec.decode (α := Nat)) h
    simpa [ident, Codec.decode_encode] using h'

theorem labelsAgree : lbl key ident digest xs = lbl key ident digest xs.reverse := by
  rw [lbl_eq xs, lbl_eq xs.reverse]
  have h1 : top key xs = some 2 := by decide
  have h2 : top key xs.reverse = some 2 := by decide
  rw [h1, h2]
  rfl

theorem labelsInject : ∀ a, a ∈ xs ↔ a ∈ xs.reverse :=
  lbl_inj (key := key) (ident := ident) (h := digest) 4 xs xs.reverse (by decide) namedReordered
    (fun _ _ _ _ h => h) labelsAgree

theorem numberDecode : ([65, 0, 255] : List UInt8) = ([65] ++ [0, 255] : List UInt8) :=
  num_inj (by rfl)
example : num [1] ≠ num [1, 0] := by decide

def claim : Claim := .ids range [ident 1]
def output : List Out := [.claim claim, .hold [ident 2], .want [ident 3]]
def reply1 (_ : Claim) : List ByteArray × List ByteArray := ([ident 1], [ident 4])
def reply2 : Claim → List ByteArray × List ByteArray
  | .ids _ _ => ([ident 1], [ident 4])
  | .fp _ _ _ => ([], [])

theorem repliesAgree : ∀ c, Out.claim c ∈ output → reply1 c = reply2 c := by
  intro c hc
  simp only [output, List.mem_cons, List.mem_nil_iff, Out.claim.injEq, reduceCtorEq, or_false] at hc
  subst c
  rfl

def foldsAgree := Tree.fold_congr reply1 reply2 output repliesAgree

def peerNode : Node := { freshNode with conns := [(sessionId, conn)], addrs := [(sessionId, address)] }
theorem peerAddress : peerNode.addr? sessionId = some address := by simp [peerNode, Node.addr?]

def offered := write_offers setup .a peerNode sessionId conn msg room address ({} : Held Unit) 100
  rfl rfl peerAddress rfl (by simp [conn, Conn.open]) (by simp [conn, Conn.open]) rfl
  (by simp [setup]) (by decide)

def wanted := hold_wants setup .b peerNode sessionId conn address room msg.id ({} : Held Unit) 101
  rfl rfl rfl (by simp [conn, Conn.open]) rfl (by simp [setup]) (by decide)
  (by simp [conn, Conn.open, setup, cfg, Std.HashSet.size_insert])

def wantAnswered := want_sends setup .a peerNode sessionId conn address msg room held 102
  rfl rfl stored rfl (by simp [setup]) (by decide) (by simp [authorize, peerNode, freshNode, setup, Conn.setRooms, ix, Index.items, conn, Conn.open])
  rfl rfl (by decide) (by decide)

def taken := op_taken setup .b peerNode sessionId conn address msg room [(Msg.hold room [msg.id]).op.bytes]
  ({} : Held Unit) 103 rfl rfl (by decide) rfl (by simp [setup])
  (by intro b hb; obtain rfl := List.mem_singleton.mp hb; exact ⟨room, [msg.id], rfl⟩)

def freshServed := fresh_served setup .a freshNode sessionId queued [(sessionId, address)] msg held 200 100
  rfl rfl stored (by simp [Conn.shows, Conn.setRooms, setup, fam, oneRoom, Family.room, has]) (by decide)
  (by simp [freshNode]) (by decide)

def offeredEverywhere := write_offers_all setup .a peerNode [msg] 100 ({} : Held Unit) rfl
  msg (by simp) rfl (by intro y hy _; exact List.mem_singleton.mp hy) sessionId conn
  (by simp [peerNode]) room rfl (by simp [setup]) (by simp [conn, Conn.open])
  (by simp [conn, Conn.open]) address peerAddress (by decide)

def blankNode : Node := { ix := {}, floor := 0 }
theorem writtenIds : ((blankNode.onWrite (setup.sync .a) [msg] 100).run ({} : Held Unit)).1.2.stored = [msg.id] := by
  simp only [Node.onWrite, HeldM.run_bind, store_run, Node.put, intake, ite_true]
  rw [write_one (setup.sync .a) blankNode msg ({} : Held Unit) rfl]
  simp [Node.fanout, blankNode, -bind_pure_comp, map_eq_pure_bind, HeldM.run_bind, HeldM.run_pure, finish_run, Node.heat]

theorem writtenHot : (msg.id, 100) ∈ ((blankNode.onWrite (setup.sync .a) [msg] 100).run ({} : Held Unit)).1.1.hot :=
  write_hot setup .a blankNode [msg] 100 ({} : Held Unit) rfl
    (by rw [writtenIds]; decide) msg.id (by rw [writtenIds]; simp)

-- Mixed incoming bare-wire batch: shared message and local secret are
-- rejected, while the connection handshake is admitted.
def handshake : Op := Op.make 3 [] "synthetic handshake payload".toUTF8
def wireFamily : Family Unit :=
  { fam with scope := fun o => if o.kind = 1 then Scope.shared room else if o.kind = 3 then Scope.conn else Scope.local }
def mixedInput : List Op := [msg, secret, handshake]
theorem connectionOnly : intakeConn wireFamily mixedInput = [handshake] := rfl

theorem connectionScope : wireFamily.scope handshake = .conn ∧ handshake ∈ mixedInput :=
  intakeConn_conn wireFamily (by rw [connectionOnly]; simp)

theorem localRejected : secret ∉ intakeConn wireFamily mixedInput := by
  rw [connectionOnly]
  intro h
  have hk := congrArg Op.kind (List.mem_singleton.mp h)
  change (2 : UInt8) = 3 at hk
  cases hk

theorem sharedRejected : msg ∉ intakeConn wireFamily mixedInput := by
  rw [connectionOnly]
  intro h
  have hk := congrArg Op.kind (List.mem_singleton.mp h)
  change (1 : UInt8) = 3 at hk
  cases hk

end Vacuity.WireMore
