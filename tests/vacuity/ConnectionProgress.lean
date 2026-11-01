import tests.vacuity.IdentityConnection
import ops.connection.Progress
import ops.connection.ProgressTape

/- Native sodium computations discharge each finite premise before applying
the positive validator laws. These are generated test users and messages,
not a capture of a deployed community, and not a universal crypto proof. -/
namespace Vacuity.ConnectionProgress
open Engine Engine.Sync Codec Tests Connection Connection.Progress
open Vacuity.Identity
open Vacuity.IdentityConnection
set_option linter.defProp false

def address := "127.0.0.1:7447".toUTF8

def exchange : Option (Exchange sodium) := do
  let payload := encode (c, address, [requestB.bytes])
  let (st, m1) ← Noise.write1 sodium.suite prologue staticB eB pkA payload
  let (sr, m2) ← Noise.write2 sodium.suite st eA pkB (sodium.suite.pub eB) .empty
  let (si, _) ← Noise.read2 sodium.suite st staticB eB m2
  pure ⟨staticB, staticA, eB, eA, c, address, [requestB.bytes], st, m1, sr, m2, si⟩

def correct (x : Exchange sodium) : Option (PLift x.Correct) :=
  if h : sodium.suite.pub x.responder ≠ sodium.suite.pub x.initiator ∧
      Noise.write1 sodium.suite prologue x.initiator x.ephemeralI
        (sodium.suite.pub x.responder) x.payload = some (x.state, x.message1) ∧
      Noise.read1 sodium.suite prologue x.responder (sodium.suite.pub x.initiator)
        x.message1 = some (x.state, sodium.suite.pub x.ephemeralI, x.payload) ∧
      Noise.sent1 sodium.suite prologue x.initiator x.ephemeralI
        (sodium.suite.pub x.responder) x.message1 = some (x.state, x.payload) ∧
      Noise.write2 sodium.suite x.state x.ephemeralR (sodium.suite.pub x.initiator)
        (sodium.suite.pub x.ephemeralI) .empty = some (x.sessionR, x.message2) ∧
      Noise.read2 sodium.suite x.state x.initiator x.ephemeralI
        x.message2 = some (x.sessionI, .empty) then
    some ⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩⟩
  else none

def requestConstructed (x : Exchange sodium) := do
  let ⟨h⟩ ← correct x
  pure (PLift.up (x.request_constructed h))

def replyConstructed (x : Exchange sodium) := do
  let ⟨h⟩ ← correct x
  pure (PLift.up (x.answer_constructed h))

def requestAccepts (x : Exchange sodium) := do
  let ⟨h⟩ ← correct x
  if hl : (sodium.suite.pub x.responder).size = 32 ∧
      (sodium.suite.pub x.initiator).size = 32 ∧ 48 ≤ x.message1.size then
    pure (PLift.up (x.request_accepts h hl.1 hl.2.1 hl.2.2))
  else none

def replyAccepts (x : Exchange sodium) :=
  if hl : 48 ≤ x.message2.size then some (PLift.up (x.reply_accepts hl)) else none

def openedAccepts (x : Exchange sodium) := do
  let ⟨h⟩ ← correct x
  pure (PLift.up (x.opened_accepts h endpointA.id))

def responderAccepts (x : Exchange sodium) := do
  let ⟨h⟩ ← correct x
  pure (PLift.up (x.responder_accepts h (Eph.op x.ephemeralR x.connection.id).id endpointA.id))

def initiatorAccepts (x : Exchange sodium) := do
  let ⟨h⟩ ← correct x
  pure (PLift.up (x.initiator_accepts h (Eph.op x.ephemeralI x.request.id).id
    (Community.endpoint x.initiator).id))

def answerReady (s : IdentityConnection.Session) :=
  let db := run (awaitingOps s)
  let eps := [(pkA, staticA, endpointA.id)]
  if h : ((count connection.byRequest [s.req.id] : Model F Nat).run db).1 = 0 ∧
      db.ops s.req.id = some s.req ∧
      (decode s.req.body : Option Body) = some (.request pkA pkB s.m1) ∧
      eps.find? (fun p => decide (p.1 = pkA)) = some (pkA, staticA, endpointA.id) ∧
      ((trusts c pkA pkB).liftL : View F Bool).eval db = true ∧
      ((arrivedFrom s.req.id : Model F (Option B)).run db).1 = some address ∧
      Reply.op sodium s.req.id staticA pkB s.m1 ((Fresh.fresh : Model F B).run db).1 = some s.reply then
    some (PLift.up (answer_ready sodium db eps s.req.id c pkB pkA pkB s.m1 staticA
      endpointA.id address s.req s.reply h.1 h.2.1 h.2.2.1 h.2.2.2.1
      h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2))
  else none

def reactReady (s : IdentityConnection.Session) := do
  let ⟨ha⟩ ← answerReady s
  let db := run (awaitingOps s)
  if he : ((endpoints : Model F (List (B × B × Id))).run db).1 = [(pkA, staticA, endpointA.id)] then
    if hm : (((rows opened.all [] : Model F (List (Id × Fact))).run db).1).any
        (fun row => decide (row = ((opened s).id, Fact.opened s.req.id c pkB address [requestB.bytes]))) = true then
      let ho : s.reply ∈ ((answerOne sodium ((endpoints : Model F (List (B × B × Id))).run db).1
          s.req.id c pkB : Model F (List Op)).run db).1 := by
        rw [he, ha]
        exact List.mem_cons_self ..
      pure (PLift.up (react_contains_answer freshPure fam sodium db s.reply (opened s).id
        s.req.id c pkB address [requestB.bytes] (by
          obtain ⟨row, hr, he⟩ := List.any_eq_true.mp hm
          exact (of_decide_eq_true he) ▸ hr) ho))
    else none
  else none

def memory (s : IdentityConnection.Session) (cursor : Nat) : Execution.Memory := {
  held := { log := awaitingOps s, db := run (awaitingOps s) }
  entropy := fun n => sha256 s!"connection-progress/entropy/{n}".toUTF8
  cursor }

def tapeReady (s : IdentityConnection.Session) (cursor : Nat) :=
  let mem := memory s cursor
  let eps : List (B × B × Id) := [(pkA, staticA, endpointA.id)]
  let reply := Reply.op sodium s.req.id staticA pkB s.m1 (mem.entropy mem.cursor)
  let co := reply.getD (mkOp [] .opened)
  if hc : reply = some co then
    if h : (Engine.eval mem.held.db (connection.byRequest.query [s.req.id] (limit := some 0))).total = 0 ∧
        mem.held.db.ops s.req.id = some s.req ∧
        (decode s.req.body : Option Body) = some (.request pkA pkB s.m1) ∧
        eps.find? (fun p => decide (p.1 = pkA)) = some (pkA, staticA, endpointA.id) ∧
        ((trusts c pkA pkB).liftL : View F Bool).eval mem.held.db = true ∧
        ((arrivedFrom s.req.id : Model F (Option B)).run mem.held.db).1 = some address then
      some (PLift.up (ProgressTape.answer_ready sodium mem eps s.req.id c pkB pkA pkB s.m1
        staticA endpointA.id address s.req co h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2 hc))
    else none
  else none

def tapeReads (s : IdentityConnection.Session) :=
  let mem := memory s 3
  if h : (Engine.eval mem.held.db (request.byTo.query [pkA] (limit := some 0))).total = 1 ∧
      mem.held.db.ops s.req.id = some s.req ∧
      ((trusts c pkA pkB).liftL : View F Bool).eval mem.held.db = true ∧
      ((arrivedFrom s.req.id : Model F (Option B)).run mem.held.db).1 = some address then
    let hc : (count request.byTo [pkA] : Execution.M Nat) mem = (1, mem) := by
      rw [ProgressTape.run_count, h.1]
    let hg : (Store.getOp s.req.id : Execution.M (Option Op)) mem = (some s.req, mem) := by
      rw [ProgressTape.run_get, h.2.1]
    let hv : (((trusts c pkA pkB).liftL : View F Bool).run : Execution.M Bool) mem = (true, mem) := by
      rw [ProgressTape.run_view, h.2.2.1]
    let ha : (arrivedFrom s.req.id : Execution.M (Option B)) mem = (some address, mem) := by
      rw [ProgressTape.run_arrivedFrom, h.2.2.2]
    some (PLift.up (And.intro hc (And.intro hg (And.intro hv ha))))
  else none

def main : IO UInt32 := do
  let t ← Checks.new
  let some x := exchange | IO.eprintln "Native handshake construction failed"; return 1
  let some s := session | IO.eprintln "Native approved-request fixture failed"; return 1
  for (label, ok) in [
      ("primitive equations checked", (correct x).isSome),
      ("actual request constructed", (requestConstructed x).isSome),
      ("actual reply constructed", (replyConstructed x).isSome),
      ("request structural validator accepts", (requestAccepts x).isSome),
      ("reply structural validator accepts", (replyAccepts x).isSome),
      ("opened validator accepts", (openedAccepts x).isSome),
      ("responder established validator accepts", (responderAccepts x).isSome),
      ("initiator established validator accepts", (initiatorAccepts x).isSome),
      ("approved stored request actually produces four operations", (answerReady s).isSome),
      ("production react includes the constructed answer", (reactReady s).isSome)] do
    t.ok label ok
  t.ok "both ends derive matching session keys" (x.sessionI.h == x.sessionR.h &&
    x.sessionI.send.k == x.sessionR.recv.k && x.sessionI.recv.k == x.sessionR.send.k)
  t.ok "altered request fails the premise certificate"
    ((correct { x with message1 := x.message1 ++ "tamper".toUTF8 }).isNone)
  t.ok "altered reply fails the premise certificate"
    ((correct { x with message2 := x.message2 ++ "tamper".toUTF8 }).isNone)
  t.ok "wrong responder ephemeral fails the premise certificate"
    ((correct { x with ephemeralR := sha256 "wrong ephemeral".toUTF8 }).isNone)
  t.ok "identical participants fail the premise certificate"
    ((correct { x with responder := x.initiator }).isNone)
  t.ok "truncated reply fails its structural premise"
    ((replyAccepts { x with message2 := .empty }).isNone)
  t.ok "answer consumes the current entropy-tape draw" ((tapeReady s 3).isSome)
  t.ok "answer theorem applies after earlier draws" ((tapeReady s 4).isSome)
  t.ok "entropy interpreter reads actual stored request, trust and arrival" ((tapeReads s).isSome)
  let first := (answerOne sodium [(pkA, staticA, endpointA.id)] s.req.id c pkB : Execution.M (List Op))
  let (a, next) := first (memory s 3)
  let (b, last) := first next
  t.ok "successive answers advance entropy and have distinct connection ids"
    (next.cursor == 4 && last.cursor == 5 && a.length == 4 && b.length == 4 &&
      (a.head?.map Op.id) != (b.head?.map Op.id))
  t.finish "positive connection progress (native crypto and checked store premises)"

end Vacuity.ConnectionProgress
