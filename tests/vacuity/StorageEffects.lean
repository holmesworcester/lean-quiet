import ops.connection.StorageEffects
import tests.vacuity.ProductionBootstrap

/- Synthetic Alice/Bob identities and messages; native signatures, Noise,
AEAD and the complete production Node handlers. Not captured user data. -/
namespace Vacuity.StorageEffects
open Engine Engine.Sync Community Connection.Execution Vacuity.ProductionBootstrap

def finished (s : Scenario) := trace setup initial s.completed

theorem source_reachable (s : Scenario) :
    ((finished s).b.memory.held).Reachable Connection.Execution.family :=
  (empty_trace_store setup (entropy "alice") (entropy "bob") s.completed .b).1

theorem source_settled (s : Scenario) : (finished s).b.memory.held.db.queue = [] :=
  (empty_trace_store setup (entropy "alice") (entropy "bob") s.completed .b).2

/-- Checks the native membership and shared scope before applying the full
handler theorem. Reachability and initial settling come from the exact
production event prefix, not from native assumptions. -/
def eventCertificate (s : Scenario) (input : Node.Input) :=
  let p := (finished s).b
  if ho : p.memory.held.db.ops s.message.id = some s.message then
    if hs : (Connection.Execution.family.room s.message).isSome then
      some (PLift.up (And.intro
        (production_step_retains setup .b p.node input (finished s).now p.memory ho hs)
        (And.intro
          (production_step_reachable setup .b p.node input (finished s).now p.memory (source_reachable s))
          (production_step_settled setup .b p.node input (finished s).now p.memory
            (source_reachable s) (source_settled s)))))
    else none
  else none

def isValid (s : Memory) (o : Op) : Bool :=
  match s.held.db.status o.id with
  | some (.valid (.inl (.message ..))) => true
  | _ => false

def main : IO UInt32 := do
  let t ← Tests.Checks.new
  let some scene := scenario | t.ok "native production scenario constructs" false; t.finish "storage-effects"
  let w := finished scene
  let p := w.b
  let some (cid, _) := p.node.conns.head? |
    t.ok "fixture has a production session" false; t.finish "storage-effects"
  let sealed := (Connection.sealFor Connection.sodium cid
    (Codec.encode [scene.recoveryMessage.bytes]) : M (Option ByteArray)) w.a.memory
  let some sealedBytes := sealed.1 |
    t.ok "actual sender hook seals new message" false; t.finish "storage-effects"
  let frameInput := Node.Input.frame (setup.addr .a) (tagged sealedTag sealedBytes)
  let written := p.node.step (setup.sync .b) (.write [scene.recoveryMessage]) w.now p.memory
  let framed := p.node.step (setup.sync .b) frameInput w.now p.memory
  let ticked := p.node.step (setup.sync .b) .tick w.now p.memory
  let closed := p.node.step (setup.sync .b) (.close (setup.addr .a)) w.now p.memory
  let malformed := p.node.step (setup.sync .b) (.frame (setup.addr .a) (tagged sealedTag "bad".toUTF8)) w.now p.memory
  t.ok "fixture starts with valid shared message and no replacement post"
    (isValid p.memory scene.message && (p.memory.held.db.ops scene.recoveryMessage.id).isNone)
  t.ok "sender sealing advances actual entropy cursor"
    (sealed.2.cursor == w.a.memory.cursor + 1)
  for (label, input) in [("write", Node.Input.write [scene.recoveryMessage]),
      ("frame", frameInput), ("tick", .tick), ("close", .close (setup.addr .a))] do
    t.ok s!"{label}: native premises apply full handler retention and settling"
      (eventCertificate scene input).isSome
  t.ok "actual write stores and validates new shared message"
    (written.2.held.db.ops scene.recoveryMessage.id == some scene.recoveryMessage &&
      isValid written.2 scene.recoveryMessage)
  t.ok "actual sealed frame stores and validates new shared message"
    (framed.2.held.db.ops scene.recoveryMessage.id == some scene.recoveryMessage &&
      isValid framed.2 scene.recoveryMessage)
  t.ok "all full handlers retain old shared bytes and finish validation"
    ([written.2, framed.2, ticked.2, closed.2, malformed.2].all fun s =>
      s.held.db.ops scene.message.id == some scene.message && s.held.db.queue.isEmpty)
  t.ok "close actually purges session secrets and connection operations"
    (!closed.1.2.purged.isEmpty && (closed.2.held.db.ops cid).isNone && closed.1.1.conns.isEmpty)
  t.ok "close keeps shared message valid while local connection disappears"
    (isValid closed.2 scene.message)
  let directlyPurged := (Turn.purge Connection.Execution.family [scene.message.id] true : M Unit) p.memory
  t.ok "even explicitly naming a shared message in purge retains and revalidates it"
    (directlyPurged.2.held.db.ops scene.message.id == some scene.message &&
      isValid directlyPurged.2 scene.message && directlyPurged.2.held.db.queue.isEmpty)
  t.ok "malformed frame cannot insert the absent new message"
    ((malformed.2.held.db.ops scene.recoveryMessage.id).isNone)
  let absentScene := { scene with message := scene.recoveryMessage }
  t.ok "unheld-operation premise rejects the retention certificate"
    (!(eventCertificate absentScene .tick).isSome)
  t.finish "full production node storage effects"

end Vacuity.StorageEffects
