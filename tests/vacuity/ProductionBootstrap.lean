import app.Proofs
import tests.engine.Checks

/-! Synthetic identities and text, real crypto and the production Node/hooks.
Finite native premise certificates are kept separate from kernel fairness.
JoinFair covers SQLite/TCP; this executable covers the exact pure execution
to which the infinite fair-tail theorem applies. -/
namespace Vacuity.ProductionBootstrap
open Engine Engine.Sync Community Connection.Execution

def setup : Setup := { addr := fun | .a => "alice:7001".toUTF8 | .b => "bob:7001".toUTF8 }
def entropy (side : String) (i : Nat) : ByteArray := sha256 s!"fair-witness/{side}/{i}".toUTF8
def initial : World := empty (entropy "alice") (entropy "bob")
def seedA := sha256 "fair-witness/alice/device".toUTF8
def seedB := sha256 "fair-witness/bob/device".toUTF8
def nkA := sha256 "fair-witness/alice/node".toUTF8
def nkB := sha256 "fair-witness/bob/node".toUTF8
def alice := Device.ofSeed seedA
def bob := Device.ofSeed seedB
def keyA := cryptoSeal.pub nkA
def keyB := cryptoSeal.pub nkB
def c := (root alice keyA).id
def content := sha256 "fair-witness/community-key".toUTF8

def view {α} (w : World) (s : Connection.Execution.Side) (v : View Community.Fact α) : α :=
  ((v.liftL : View Connection.F α).run : M α) (w.peer s).memory |>.1

def foundOps : List Op :=
  (view initial .a (found seedA "Fair execution".toUTF8 "Alice".toUTF8 1
    content (entropy "wrap" 0) nkA)).ops

def founded : World := step setup initial (.write .a foundOps)
def invitation : Option (Write × Invite) :=
  view founded .a (inviteTo c c alice (entropy "bearer" 0) [setup.addr .a])

def drive (n : Nat) : List Action := (List.range n).map schedule
def noDelivery (n : Nat) : List Action :=
  (List.range n).map fun i => if i % 2 = 0 then .tick .a else .tick .b

structure Scenario where
  request : Op
  message : Op
  recoveryMessage : Op
  startup : List Action
  approved : List Action
  completed : List Action
  recovered : List Action

def scenario : Option Scenario := do
  let (wi, link) ← invitation
  let joinOps := (view initial .b (join link seedB "Bob".toUTF8 nkB)).ops
  let request := link.request bob keyB
  let startup := [.write .a foundOps, .write .a wi.ops, .write .b joinOps] ++ drive 90
  let before := trace setup initial startup
  let approval := (view before .a (approveReq c request.id c alice (entropy "wrap" 1))).ops
  let approved := startup ++ [.write .a approval]
  let after := trace setup initial (approved ++ drive 240)
  let message := sealedPost c c alice content ((entropy "message-nonce" 0).extract 0 24)
    "Bob, this arrived through the production hooks.".toUTF8 1 1
  -- The durable catalog also emits background retry traffic. This finite
  -- witness services enough FIFO deliveries for the new post to reach Bob;
  -- the number is a fixture length, not a runtime latency bound.
  let completed := approved ++ drive 240 ++ [.write .a [message]] ++ drive 1320
  let recoveryMessage := sealedPost c c alice content ((entropy "recovery-message-nonce" 0).extract 0 24)
    "Bob, this new message crossed the replacement session.".toUTF8 2 2
  let recovered := completed ++ [.close] ++ drive 240 ++ [.write .a [recoveryMessage]] ++ drive 1320
  -- Ensure preparation itself did not substitute a completed store.
  if after.a.memory.held.log.isEmpty then none
  else some { request, message, recoveryMessage, startup, approved, completed, recovered }

def admitted (w : World) : Bool :=
  view w .a (allowPeer c keyB) && view w .b (allowPeer c keyB) && view w .b (allowPeer c keyA)

def waitingForApproval (w : World) : Bool :=
  w.a.node.conns.isEmpty && w.b.node.conns.isEmpty &&
    !(view w .a (allowPeer c keyB)) && !(view w .b (allowPeer c keyB))

def sharedSession (w : World) : Bool :=
  w.a.node.conns.any fun (cid, _) =>
    w.b.node.conns.any fun (other, _) => decide (cid = other)

def hasMessage (message : Op) (w : World) : Bool :=
  decide (w.b.memory.held.db.ops message.id = some message)

def goal (message : Op) (w : World) : Prop :=
  admitted w = true ∧ sharedSession w = true ∧ hasMessage message w = true ∧ w.unhandledDrops = 0

instance (message : Op) (w : World) : Decidable (goal message w) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- All concrete native premises are checked before applying the theorem.
There is no assumed Scene.Good, fair schedule, successful delivery or session.
The prefix must not have ignored an implicit socket-close effect. Its infinite
continuation is a node-interpreter fairness proof, not a TCP refinement. -/
def certificate (s : Scenario) :=
  if h : goal s.recoveryMessage (trace setup initial s.recovered) then
    some (PLift.up (successful_fair_extension setup initial s.recovered (goal s.recoveryMessage) h))
  else none

theorem infiniteScheduler : (fairRun setup initial).Fair := fairRun_fair setup initial

def main : IO UInt32 := do
  let t ← Tests.Checks.new
  let some s := scenario | t.ok "native bootstrap fixture constructs" false; t.finish "production-bootstrap"
  let before := trace setup initial s.startup
  t.ok "actual bare handshake carries the join request before approval"
    (decide (before.a.memory.held.db.ops s.request.id = some s.request))
  t.ok "approval withheld: no session and no admission"
    (waitingForApproval before)
  let withheld := trace setup before (drive 150)
  t.ok "more fair service cannot substitute for user approval"
    (waitingForApproval withheld)
  let offline := trace setup (trace setup initial s.approved) (noDelivery 120)
  t.ok "ticks without network delivery do not complete bootstrap" (!sharedSession offline)
  let completed := trace setup initial s.completed
  t.ok "native signatures, Noise and sync produce mutual admission" (admitted completed)
  t.ok "actual established facts open one shared session" (sharedSession completed)
  t.ok "post bytes reach the joiner through sealed session frames" (hasMessage s.message completed)
  let closed := step setup completed .close
  t.ok "transport loss purges both sessions" (closed.a.node.conns.isEmpty && closed.b.node.conns.isEmpty)
  t.ok "admission obligation survives transport loss" (admitted closed)
  let recovered := trace setup initial s.recovered
  t.ok "ticks redial from retained membership and restore shared session" (sharedSession recovered)
  t.ok "recovery uses a new session id"
    (recovered.a.node.conns.all fun (cid, _) => !completed.a.node.conns.any (fun p => decide (p.1 = cid)))
  t.ok "application bytes survive reconnect" (hasMessage s.message recovered)
  t.ok "new sealed post traverses the replacement session" (hasMessage s.recoveryMessage recovered)
  t.ok "recovery post was absent before transport loss" (!(hasMessage s.recoveryMessage completed))
  t.ok "finite prefix ignores no implicit socket-close effects" (recovered.unhandledDrops == 0)
  t.ok "finite native premises construct an infinite fair continuation certificate" (certificate s).isSome
  let unmodeledClose := recovered.run setup .a recovered.net
    (fun n => pure (n, { drop := [c] }))
  t.ok "unmodeled socket-close effect is recorded and rejects success"
    (unmodeledClose.unhandledDrops == 1 && !(decide (goal s.recoveryMessage unmodeledClose)))
  let absent := post c c alice content "This message was never sent.".toUTF8 2 2
  t.ok "unsent message rejects the certificate" (!(certificate { s with recoveryMessage := absent }).isSome)
  t.ok "withheld approval rejects the certificate" (!(certificate { s with recovered := s.startup }).isSome)
  t.finish "production-bootstrap"

end Vacuity.ProductionBootstrap
