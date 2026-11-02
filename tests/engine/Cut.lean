/-
The causal cut on SQLite with real Ed25519: a removed member cannot
readmit its own node, by its own approval, by a fork of its approval
chain, or through a fresh user it admits; those it approved before the
removal stay; a current member's approval lets a device in. The trust
rule's views only (app/community/Commands.lean), not their laws, so the
negative controls (tests/engine/cut_negative.py) can mutate the views
and run this.
-/
import tests.engine.Checks
import engine.core.Sqlite
import app.community.Commands

open Engine Community Tests

namespace CutCheck

def C := ed25519

/-- A test device's node key: each device is its own node. -/
def keyOf (d : Device) : Key := cryptoSeal.pub (Bytes.digest ("test node ".toUTF8 ++ d.pk))

def isValid (x : Id) : SqlM Fact Bool := do
  return match ← Store.getStatus x with | some (.valid _) => true | _ => false

def allow (c : Id) (d : Device) : SqlM Fact Bool := (allowPeer c (keyOf d)).run

/-- Device d asks to join through an invitation issued as `issuerAdm`
by `by_`, naming node key `key`: the invitation and the request. -/
def ask (c issuerAdm : Id) (by_ d : Device) (key : Key) (tag : String) : Op × Op :=
  let b := Device.named ("cut-bearer-" ++ tag)
  let inv := invite c issuerAdm by_ b.pk false
  (inv, request c inv.id d key b.sk)

end CutCheck

open CutCheck in
def main (args : List String) : IO UInt32 := do
  let dir := args.headD "out/cut"
  IO.FS.createDirAll dir
  for f in ["a.db", "a.db-wal", "a.db-shm", "b.db", "b.db-wal", "b.db-shm"] do
    if ← System.FilePath.pathExists (dir ++ "/" ++ f) then IO.FS.removeFile (dir ++ "/" ++ f)
  let t ← Checks.new
  let fam := family C
  let db ← Db.openAt (dir ++ "/a.db")
  let run {α} (m : SqlM Fact α) : IO α := m.run db
  let recv (ops : List Op) : IO Unit := run (receive fam ops)
  let write (w : Write) : IO Unit := recv w.ops

  let alice := Device.named "cut-alice"
  let bob := Device.named "cut-bob"
  let dave := Device.named "cut-dave"
  let erin := Device.named "cut-erin"
  let bobAgain := Device.named "cut-bob-again"
  let bobFork := Device.named "cut-bob-fork"
  let sybil := Device.named "cut-sybil"
  let bobVia := Device.named "cut-bob-via"

  -- Alice founds; Bob joins, approved by Alice's intent.
  let r := root alice (keyOf alice) .empty  -- no posts: no content key id
  let c := r.id
  let (invB, reqB) := ask c c alice bob (keyOf bob) "b"
  recv [r, invB, reqB]
  write (← run ((approveReq c reqB.id c alice).run))
  let joinB ← run ((admission.byDevice.read [c, bob.pk] (limit := some 1)).run)
  let some ((_, admB), _) := joinB.rows.head? | do t.ok "bob is admitted" false; return 1
  t.ok "bob is let in" (← run (allow c bob))

  -- Bob approves Dave, then Erin: one chain, through Bob's intent.
  let (invD, reqD) := ask c admB bob dave (keyOf dave) "d"
  recv [invD, reqD]
  write (← run ((approveReq c reqD.id admB bob).run))
  let (invE, reqE) := ask c admB bob erin (keyOf erin) "e"
  recv [invE, reqE]
  write (← run ((approveReq c reqE.id admB bob).run))
  t.ok "dave is let in" (← run (allow c dave))
  t.ok "erin is let in" (← run (allow c erin))
  let chain ← run ((approval.byDev.read [c, bob.pk]).run)
  t.ok "bob's approvals are one chain: places 0 and 1"
    ((chain.rows.filterMap fun (_, f) => match f with | .ofApproval a => some a.n | _ => none) == [1, 0])
  let some ((_, head), .ofApproval headF) := chain.rows.head? | do t.ok "bob has a chain head" false; return 1
  let upB := headF.up

  -- Alice removes Bob, through her intent: its cut is Bob's chain head.
  let wrm ← run ((removeMember c reqB.id alice).run)
  t.ok "the removal cites bob's chain head" (wrm.ops.map (·.reqs.getLast?) == [some head])
  write wrm
  t.ok "bob is refused" (!(← run (allow c bob)))
  t.ok "no cascade: dave, approved by bob inside the cut, is still let in" (← run (allow c dave))
  t.ok "no cascade: erin, approved by bob inside the cut, is still let in" (← run (allow c erin))

  -- Bob, removed, approves a fresh device on his own node, continuing his
  -- chain past the head: Valid, and admits no one.
  let (invR, reqR) := ask c admB bob bobAgain (keyOf bob) "r"
  let okR := approve c reqR.id admB bob (some upB) (some head)
  let joinR := admit c reqR.id okR.id
  recv [invR, reqR, okR, joinR]
  t.ok "bob's own approval is Valid" (← run (isValid okR.id))
  t.ok "and so is the admission it gives" (← run (isValid joinR.id))
  t.ok "self-readmission refused: bob's own approval does not let his node in" (!(← run (allow c bob)))

  -- Equivocation: Bob forks his chain at place 0, inside the cut by its
  -- number, not by its hash.
  let (invF, reqF) := ask c admB bob bobFork (keyOf bob) "f"
  let okF := approve c reqF.id admB bob (some upB)
  let joinF := admit c reqF.id okF.id
  recv [invF, reqF, okF, joinF]
  t.ok "bob's fork is Valid" (← run (isValid okF.id))
  t.ok "equivocation refused: a fork at a place inside the cut does not readmit" (!(← run (allow c bob)))

  -- Two steps: Bob admits a fresh user, who approves Bob's node.
  let (invS, reqS) := ask c admB bob sybil (keyOf sybil) "s"
  let okS := approve c reqS.id admB bob (some upB) (some okR.id)
  let joinS := admit c reqS.id okS.id
  let (invV, reqV) := ask c joinS.id sybil bobVia (keyOf bob) "v"
  let okV := approve c reqV.id joinS.id sybil (some okS.id)
  let joinV := admit c reqV.id okV.id
  recv [invS, reqS, okS, joinS, invV, reqV, okV, joinV]
  t.ok "the fresh user's approval is Valid" (← run (isValid okV.id))
  t.ok "two-step readmission refused: a user bob admitted after his removal does not let his node in"
    (!(← run (allow c bob)))
  t.ok "and that user is refused too" (!(← run (allow c sybil)))

  -- A current member's approval: Alice approves the fresh user.
  write (← run ((approveReq c reqS.id c alice).run))
  t.ok "a current member's fresh approval lets the fresh user in" (← run (allow c sybil))
  t.ok "and bob's node stays refused" (!(← run (allow c bob)))

  -- Order: the same ops, reversed, on another database: the same trust.
  let all ← run (dumpOps (F := Fact))
  let db2 ← Db.openAt (dir ++ "/b.db")
  (receive fam all.reverse).run db2
  let ds := [alice, bob, dave, erin, sybil, bobAgain]
  let v1 ← ds.mapM fun d => run (allow c d)
  let v2 ← ds.mapM fun d => (allow c d).run db2
  t.ok "the same trust verdicts in reverse arrival order" (v1 == v2)
  t.finish "cut"
