import engine.wire.NodeUniqueLaws
import app.Proofs
import engine.sync.Witnesses

/- Synthetic Unit-family session labels make kernel computation possible.
These witnesses exercise the actual Node handlers, not Noise correctness.
The named native suite separately supplies signed/Noise/SQLite/TCP sessions. -/
namespace Vacuity.NodeUnique
open Engine Engine.Sync Engine.Sync.NodeUnique

private instance : LawfulMonad (HeldM Unit) :=
  inferInstanceAs (LawfulMonad (StateM (Held Unit)))

def room : Id := "unique-room".toUTF8
def cid : Id := "authenticated-session-fixture".toUTF8
def addr : ByteArray := "127.0.0.1:43111".toUTF8
def fam : Family Unit := oneRoom room
def sync : Sync Unit (HeldM Unit) :=
  { fam, cfg := {}, deferredRetries := true,
    hooks := {
      rooms := fun _ => pure [.sync room]
      established := pure [(cid, addr, true), (cid, addr, true)]
      sealFor := fun _ _ => pure none
      openFrame := fun _ => pure none } }
def fresh : Node := Node.boot fam [] 0

theorem boot : Valid fresh := boot_valid fam [] 0

def opened : Node := ((fresh.open sync cid addr true 0) {}).1.1

theorem opening : Valid opened := Ensures.state (open_valid sync fresh cid addr true 0 boot) {}
theorem nonempty : opened.conns.map Prod.fst = [cid] := rfl

def reopened : Node := ((opened.open sync cid addr false 1) {}).1.1

theorem replacing : Valid reopened := Ensures.state (open_valid sync opened cid addr false 1 opening) {}
theorem still_one : reopened.conns.map Prod.fst = [cid] := by decide +kernel

def swept : Node := ((reopened.sweepAll sync [cid] {}) {}).1.1

theorem sweeping : Valid swept := Ensures.state (sweepAll_valid sync reopened [cid] {} replacing) {}
theorem queued : swept.retryOrder = [cid] := by decide +kernel

theorem every_input (input : Node.Input) (now : Nat) :
    Valid ((swept.step sync input now) {}).1.1 :=
  Ensures.state (step_valid sync swept input now sweeping) {}

def first : Node := ((fresh.step sync .tick 0) {}).1.1
def second : Node := ((first.step sync .tick 0) {}).1.1

theorem first_unique : Valid first := Ensures.state (step_valid sync fresh .tick 0 boot) {}
theorem second_unique : Valid second := Ensures.state (step_valid sync first .tick 0 first_unique) {}
theorem first_nonempty : first.conns.map Prod.fst = [cid] := by decide +kernel
theorem second_queued : second.retryOrder = [cid] := by decide +kernel
theorem second_nonempty : second.conns.map Prod.fst = [cid] := by decide +kernel

/-- An infinite actual-handler execution after two boot/timer steps. Hostile
empty frames keep arriving. Safety needs no fairness or successful delivery. -/
def nodes : Nat → Node
  | 0 => second
  | n+1 => (((nodes n).step sync (.frame addr .empty) 0) {}).1.1

theorem ignored_frame (n : Node) : ((n.step sync (.frame addr .empty) 0) {}).1.1 = n := rfl

theorem infinite_unique (i : Nat) : Valid (nodes i) := by
  induction i with
  | zero => exact second_unique
  | succ i ih => exact Ensures.state (step_valid sync (nodes i) (.frame addr .empty) 0 ih) {}

theorem always_nonempty (i : Nat) : (nodes i).conns.map Prod.fst = [cid] := by
  induction i with
  | zero => exact second_nonempty
  | succ i ih => change _ = [cid]; rw [nodes, ignored_frame]; exact ih

theorem native_return_factorization (db : Db) :
    Ensures (((Node.boot Connection.Execution.family [] 0).step
      ({ fam := Connection.Execution.family, cfg := {}, hooks := {
          rooms := fun _ => pure [.sync room]
          sealFor := fun _ _ => pure none
          openFrame := fun _ => pure none } } : Sync Connection.F (SqlM Connection.F))
      .tick 0).run db) (fun r => Valid r.1) :=
  sql_step_valid _ db _ .tick 0 (boot_valid Connection.Execution.family [] 0)

/-- The production advancing-entropy interpreter also uses the theorem.
This closed witness allows arbitrary schedules and both peers. -/
theorem production_prefix (actions : List Connection.Execution.Action)
    (target : Connection.Execution.Side) :
    Valid ((Connection.Execution.trace { addr := fun _ => addr }
      (Connection.Execution.empty (fun _ => .empty) (fun _ => .empty)) actions).peer target).node :=
  Connection.Execution.empty_trace_unique _ _ _ actions target

theorem production_run (i : Nat) (target : Connection.Execution.Side) :
    Valid (((Connection.Execution.fairRun { addr := fun _ => addr }
      (Connection.Execution.empty (fun _ => .empty) (fun _ => .empty))).state i).peer target).node :=
  Connection.Execution.Run.unique _ i target

#print axioms every_input
#print axioms infinite_unique
#print axioms native_return_factorization
#print axioms production_prefix
#print axioms production_run
end Vacuity.NodeUnique
