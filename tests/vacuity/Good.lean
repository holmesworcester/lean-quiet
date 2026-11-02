import engine.world.Send
import tests.engine.Checks

/-! A concrete plain World for the good-world laws: two nodes on the
one-room Unit family, from empty stores, with no attacker. Alice writes
two synthetic messages, then Bob writes the same two in the opposite
order, then the nodes' clocks tick forever. Every act is legal (all at
time 0), so the run is an execution of `Plain.Run`, and each law below is
applied to it: in the kernel where its premise is the run, and natively
where it also takes premises about op ids (SHA-256, decided by running
it). Synthetic fixture; the running node on a held store, not the
Community family, sealed frames or the handshake. -/
namespace Vacuity.Good
open Engine Engine.Sync Engine.World Tests

def room : Id := "vacuity/community/alice-bob".toUTF8
def hello : Op := Op.make 1 [] "Alice: hello Bob".toUTF8
def reply : Op := Op.make 1 [] "Bob: hello Alice".toUTF8

/-- Two plain nodes showing the room on every session. -/
def world : Plain Unit where
  fam := oneRoom room
  n := 2
  addr i := if i = 0 then "10.0.0.1:7000".toUTF8 else "10.0.0.2:7000".toUTF8
  rooms _ _ := [room]

def alice : Fin world.n := ⟨0, by decide⟩
def bob : Fin world.n := ⟨1, by decide⟩

/-- The same two ops written in opposite orders, then ticks: all at time 0. -/
def act : Nat → Act world.n
  | 0 => .write alice [hello, reply] 0
  | 1 => .write bob [reply, hello] 0
  | k + 2 => .tick (if k % 2 = 0 then alice else bob) 0

theorem now_zero : ∀ k, (worlds world.setup world.start act k).now = 0
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | _ + 3 => rfl

/-- The run is legal at every step. -/
def run : world.Run where
  act := act
  legal k := by
    have h := now_zero k
    match k with
    | 0 => exact ⟨Nat.le_of_eq h, trivial⟩
    | 1 => exact ⟨Nat.le_of_eq h, trivial⟩
    | _ + 2 => exact Nat.le_of_eq h

/-! ## Kernel witnesses: laws whose premise is the run -/

theorem good : ∀ k, world.Good (run.world k) := Plain.good_always run

/-- Alice's write moves her store only by turns and purges. -/
theorem writeMoves : Moves world.fam ((run.world 0).box alice) ((run.world 1).box alice) :=
  Plain.moves_always run 0 alice

theorem owes : ∀ k i cid c, ((run.world k).node i).conn? cid = some c → OwesQueued c :=
  Plain.owes_queued_start run

theorem covers : ∀ k i, IxCovers world.fam ((run.world k).node i) ((run.world k).box i) :=
  Plain.ix_covers_start run

theorem bounded : ∀ k i cid c, ((run.world k).node i).conn? cid = some c → c.owed.length ≤ world.cfg.maxKnown :=
  Plain.owed_bounded_start run

theorem managed : ∀ k i, ((run.world k).node i).managed = [] :=
  Plain.managed_nil run fun _ => rfl

/-! ## The pieces, over the run -/

theorem oqPieces : Pieces world.setup alice (fun n _ => NodeOQ n) := Plain.oq_pieces alice
theorem ixPieces : Pieces world.setup alice (IxInv world.fam) := Plain.ix_pieces alice
theorem boundedPieces : Pieces world.setup alice (fun n _ => NodeBounded world.cfg.maxKnown n) :=
  Plain.bounded_pieces alice
theorem managedPieces : Pieces world.setup alice (fun n _ => n.managed = []) := Plain.managed_pieces alice

/-- Bob's node after Alice's write, every entry point at it: what its
sessions owe stays queued. -/
theorem tickKeeps : Ok world.setup (fun n _ => NodeOQ n)
    (world.setup.run (((run.world 1).node bob).onTick (world.setup.sync bob) 0) ((run.world 1).box bob)) :=
  onTick_keeps Plain.lawful (Plain.oq_pieces bob) _ 0 _ (Plain.good_node run 1 bob).owes

theorem frameKeeps : Ok world.setup (fun n _ => NodeOQ n)
    (world.setup.run (((run.world 1).node bob).onFrame (world.setup.sync bob) (world.addr alice) hello.bytes 0)
      ((run.world 1).box bob)) :=
  onFrame_keeps Plain.lawful (Plain.oq_pieces bob) _ _ _ 0 _ (Plain.good_node run 1 bob).owes

theorem writeKeeps : Ok world.setup (fun n _ => NodeOQ n)
    (world.setup.run (((run.world 1).node bob).onWrite (world.setup.sync bob) [reply, hello] 0) ((run.world 1).box bob)) :=
  onWrite_keeps Plain.lawful (Plain.oq_pieces bob) _ _ 0 _ (Plain.good_node run 1 bob).owes

theorem closeKeeps : Ok world.setup (fun n _ => NodeOQ n)
    (world.setup.run (((run.world 1).node bob).onClose (world.setup.sync bob) (world.addr alice) 0) ((run.world 1).box bob)) :=
  onClose_keeps Plain.lawful (Plain.oq_pieces bob) _ _ 0 _ (Plain.good_node run 1 bob).owes

/-- The negative control, at the fixture's room and op. -/
theorem mutantUnindexed : ¬ Pieces (dialMutant room hello) ⟨0, Nat.zero_lt_one⟩ (IxInv (oneRoom room)) :=
  dial_mutant_unindexed room hello

/-! ## Runtime witnesses: the ops' ids are decided by running SHA-256 -/

def aliceBox : Held Unit := (run.world 2).box alice
def bobBox : Held Unit := (run.world 2).box bob

instance (L : List Op) : Decidable (Distinct L) := by unfold Distinct; infer_instance

theorem same_of_mem {A B : List Op} (h : ∀ o ∈ A ++ B, (o ∈ A ↔ o ∈ B)) : ∀ o, o ∈ A ↔ o ∈ B := by
  intro o
  by_cases hm : o ∈ A ++ B
  · exact h o hm
  · rw [List.mem_append, not_or] at hm
    exact ⟨fun h' => absurd h' hm.1, fun h' => absurd h' hm.2⟩

/-- Alice and Bob received the same two ops in opposite orders, with
distinct ids: they agree on every verdict. -/
def agreeing : Option (PLift (aliceBox.db.status = bobBox.db.status)) :=
  if hd : Distinct (aliceBox.log ++ bobBox.log) then
    if hs : ∀ o ∈ aliceBox.log ++ bobBox.log, (o ∈ aliceBox.log ↔ o ∈ bobBox.log) then
      some ⟨Plain.agree run 2 2 alice bob hd (same_of_mem hs)⟩
    else none
  else none

/-- Alice's verdict on Bob's reply, stored after her write, is the spec's
over her stored ops. -/
def replySpec : Option (PLift (∃ v, Spec world.fam aliceBox.db.ops reply.id v)) :=
  match h : aliceBox.db.status reply.id with
  | some v => some ⟨⟨v, (Plain.verdicts_spec run 2 alice reply.id v).1 h⟩⟩
  | none => none

def main : IO UInt32 := do
  let t ← Checks.new
  t.ok "both nodes hold both ops" (aliceBox.log.length == 2 && bobBox.log.length == 2)
  t.ok "the two nodes received them in opposite orders" (aliceBox.log != bobBox.log)
  t.ok "the two ops have distinct ids" (hello.id != reply.id)
  t.ok "same ops in opposite orders agree on every verdict" agreeing.isSome
  t.ok "alice's stored verdict on bob's reply is the spec's" replySpec.isSome
  t.ok "both stores decided both ops" ((aliceBox.db.status hello.id).isSome && (bobBox.db.status reply.id).isSome)
  return ← t.finish "good vacuity"

end Vacuity.Good
