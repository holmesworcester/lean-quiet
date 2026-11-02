import engine.world.Send
import tests.engine.Checks

/-! A concrete plain World for the good-world laws: two nodes on the
one-room Unit family, from empty stores, with no attacker. Alice writes
two synthetic messages, then Bob writes the same two in the opposite
order, then the nodes' clocks tick forever. Every act is legal (all at
time 0), so the run is an execution of `Plain.Run`, and each law below is
applied to it: in the kernel where its premise is the run, and natively
where it also takes premises about op ids (SHA-256, decided by running
it). The urgent laws run on the same World over a family whose every op
is urgent, as membership is (`urgentWorld`), where their closure premise
holds of every op; and on a mixed family (`mixedWorld`) where one kind
is urgent: Alice's backlog of `drainCap + 1` replies waits on a message
she writes later, so the write that brings it leaves a reply queued
behind the cap while the urgent grant in that same write is decided, its
closure checked natively (`closed_of_check`), and the next tick decides
the rest. Synthetic fixture; the running node on a held store, not the
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

/-- The same World on a family whose every op is urgent. -/
def urgentWorld : Plain Unit := { world with fam := { oneRoom room with urgent := fun _ => true } }

theorem urgent_now_zero : ∀ k, (worlds urgentWorld.setup urgentWorld.start act k).now = 0
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | _ + 3 => rfl

def urgentRun : urgentWorld.Run where
  act := act
  legal k := by
    have h := urgent_now_zero k
    match k with
    | 0 => exact ⟨Nat.le_of_eq h, trivial⟩
    | 1 => exact ⟨Nat.le_of_eq h, trivial⟩
    | _ + 2 => exact Nat.le_of_eq h

/-- Every op's closure is all urgent on the urgent family. -/
theorem all_urgent (s : DB Unit) (x : Id) : UrgentClosed urgentWorld.fam s x := fun _ _ _ _ => rfl

/-! ### The mixed family: urgent grants, content behind the cap -/

/-- Kind 2 is urgent (admission-like); kind 1 is content. -/
def mixedWorld : Plain Unit := { world with fam := { oneRoom room with urgent := fun o => o.kind == 2 } }

def admit : Op := Op.make 2 [] "Alice admits Bob".toUTF8
def grant : Op := Op.make 2 [admit.id] "Alice grants Bob, citing his admission".toUTF8
/-- The message the replies answer, written after them. -/
def anchor : Op := Op.make 1 [] "Alice: the thread's first message".toUTF8
/-- One more reply than a turn drains. -/
def backlog : List Op :=
  (List.range (drainCap + 1)).map fun i => Op.make 1 [anchor.id] s!"Alice: reply {i}".toUTF8

/-- Alice writes the admission and the replies (which wait on the anchor),
then the anchor and the grant, then the clocks tick. -/
def mixedAct : Nat → Act world.n
  | 0 => .write alice (admit :: backlog) 0
  | 1 => .write alice [anchor, grant] 0
  | k + 2 => .tick (if k % 2 = 0 then alice else bob) 0

theorem mixed_now_zero : ∀ k, (worlds mixedWorld.setup mixedWorld.start mixedAct k).now = 0
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | _ + 3 => rfl

def mixedRun : mixedWorld.Run where
  act := mixedAct
  legal k := by
    have h := mixed_now_zero k
    match k with
    | 0 => exact ⟨Nat.le_of_eq h, trivial⟩
    | 1 => exact ⟨Nat.le_of_eq h, trivial⟩
    | _ + 2 => exact Nat.le_of_eq h

/-- Every listed id's stored op is urgent and requires only listed ids. -/
def closedIn {F : Type} (fam : Family F) (s : DB F) (S : List Id) : Bool :=
  S.all fun y => match s.ops y with
    | none => true
    | some o => urgentOf fam o && o.reqs.all (has S)

/-- **A checked closure is all urgent**: the list holds x's whole stored
closure, and every op in it is urgent. -/
theorem closed_of_check {F : Type} {fam : Family F} {s : DB F} {S : List Id} (h : closedIn fam s S = true)
    {x : Id} (hx : x ∈ S) : UrgentClosed fam s x := by
  have hS : ∀ y ∈ S, ∀ o, s.ops y = some o → urgentOf fam o = true ∧ ∀ r ∈ o.reqs, r ∈ S := by
    intro y hy o ho
    have := List.all_eq_true.1 h y hy
    simp only [ho, Bool.and_eq_true, List.all_eq_true] at this
    exact ⟨this.1, fun r hr => (has_iff S r).1 (this.2 r hr)⟩
  have hreach : ∀ y, Engine.Sync.Reach s.ops x y → y ∈ S := by
    intro y hy
    induction hy with
    | refl => exact hx
    | step _ ho hr ih => exact (hS _ ih _ ho).2 _ hr
  intro y o hy ho
  exact (hS y (hreach y hy) o ho).1

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
distinct ids: they agree on every op both decided. -/
def agreeing : Option (PLift (∃ v w, aliceBox.db.status hello.id = some v ∧
    bobBox.db.status hello.id = some w ∧ v = w)) :=
  if hd : Distinct (aliceBox.log ++ bobBox.log) then
    if hs : ∀ o ∈ aliceBox.log ++ bobBox.log, (o ∈ aliceBox.log ↔ o ∈ bobBox.log) then
      match h1 : aliceBox.db.status hello.id, h2 : bobBox.db.status hello.id with
      | some v, some w => some ⟨v, w, rfl, rfl, Plain.agree_decided run 2 2 alice bob hd (same_of_mem hs) h1 h2⟩
      | _, _ => none
    else none
  else none

/-- Alice's verdict on Bob's reply, stored after her write, is the spec's
over her stored ops. -/
def replySpec : Option (PLift (∃ v, Spec world.fam aliceBox.db.ops reply.id v)) :=
  match h : aliceBox.db.status reply.id with
  | some v => some ⟨⟨v, Plain.verdicts_sound run 2 alice reply.id v h⟩⟩
  | none => none

def urgentAlice : Held Unit := (urgentRun.world 2).box alice
def urgentBob : Held Unit := (urgentRun.world 2).box bob

/-- On the urgent family the same two nodes agree on each op's verdict,
decided or not. -/
def urgentAgreeing : Option (PLift (urgentAlice.db.status hello.id = urgentBob.db.status hello.id)) :=
  if hd : Distinct (urgentAlice.log ++ urgentBob.log) then
    if hs : ∀ o ∈ urgentAlice.log ++ urgentBob.log, (o ∈ urgentAlice.log ↔ o ∈ urgentBob.log) then
      some ⟨Plain.agree urgentRun 2 2 alice bob hd (same_of_mem hs) (all_urgent _ _)⟩
    else none
  else none

/-- On the urgent family, Alice's verdict on Bob's reply is exactly the
spec's. -/
def urgentReplySpec : Option (PLift (∃ v, urgentAlice.db.status reply.id = some v ∧
    Spec urgentWorld.fam urgentAlice.db.ops reply.id v)) :=
  match h : urgentAlice.db.status reply.id with
  | some v => some ⟨⟨v, rfl, (Plain.verdicts_spec urgentRun 2 alice (all_urgent _ _) v).1 h⟩⟩
  | none => none

def mixedAlice : Held Unit := (mixedRun.world 2).box alice
def mixedTicked : Held Unit := (mixedRun.world 3).box alice

/-- A reply Alice still has queued, undecided, after the write that
brought its anchor. -/
def queuedReply : Option Op :=
  backlog.find? fun o => has mixedAlice.db.queue o.id && (mixedAlice.db.status o.id).isNone

/-- The grant's stored closure, the grant and the admission, is all
urgent: checked by running `closedIn`. -/
def grantClosed : Option (PLift (UrgentClosed mixedWorld.fam mixedAlice.db grant.id)) :=
  if h : closedIn mixedWorld.fam mixedAlice.db [grant.id, admit.id] = true then
    some ⟨closed_of_check h (List.mem_cons_self ..)⟩
  else none

theorem mixedInv : Inv mixedWorld.fam mixedAlice.db :=
  let ⟨_, hr, _⟩ := (Plain.good_node mixedRun 2 alice).store
  reach_inv hr

theorem mixedSettled : UrgentSettled mixedWorld.fam mixedAlice.db :=
  (Plain.good_node mixedRun 2 alice).waiting.settled

/-- With a reply still queued, the grant's stored verdict is the spec's
(`verdicts_spec` at the node). -/
def grantSpec : Option (PLift (∃ v, mixedAlice.db.status grant.id = some v ∧
    Spec mixedWorld.fam mixedAlice.db.ops grant.id v)) :=
  match grantClosed with
  | some ⟨hc⟩ =>
    match h : mixedAlice.db.status grant.id with
    | some v => some ⟨⟨v, rfl, (Plain.verdicts_spec mixedRun 2 alice hc v).1 h⟩⟩
    | none => none
  | none => none

/-- With a reply still queued, the grant is Valid exactly as the spec
says (`urgent_valid_iff` on the store's `Inv` and settled urgent work). -/
def grantValid : Option (PLift (mixedAlice.db.status grant.id = some (.valid ()) ∧
    Spec mixedWorld.fam mixedAlice.db.ops grant.id (.valid ()))) :=
  match grantClosed with
  | some ⟨hc⟩ =>
    match h : mixedAlice.db.status grant.id with
    | some (.valid ()) => some ⟨rfl, (urgent_valid_iff mixedInv mixedSettled hc ()).1 h⟩
    | _ => none
  | none => none

def main : IO UInt32 := do
  let t ← Checks.new
  t.ok "both nodes hold both ops" (aliceBox.log.length == 2 && bobBox.log.length == 2)
  t.ok "the two nodes received them in opposite orders" (aliceBox.log != bobBox.log)
  t.ok "the two ops have distinct ids" (hello.id != reply.id)
  t.ok "same ops in opposite orders agree on every op both decided" agreeing.isSome
  t.ok "alice's stored verdict on bob's reply is the spec's" replySpec.isSome
  t.ok "both stores decided both ops" ((aliceBox.db.status hello.id).isSome && (bobBox.db.status reply.id).isSome)
  t.ok "urgent family: same ops in opposite orders agree on an urgent op" urgentAgreeing.isSome
  t.ok "urgent family: alice's verdict on bob's reply is exactly the spec's" urgentReplySpec.isSome
  t.ok "urgent family: both stores decided both ops"
    ((urgentAlice.db.status hello.id).isSome && (urgentBob.db.status reply.id).isSome)
  t.ok "mixed family: a reply is still queued and undecided after the anchor's write" queuedReply.isSome
  t.ok "mixed family: the grant's stored closure is all urgent (checked)" grantClosed.isSome
  t.ok "mixed family: with a reply queued, the grant's verdict is the spec's" grantSpec.isSome
  t.ok "mixed family: with a reply queued, the grant is Valid as the spec says" grantValid.isSome
  t.ok "mixed family: the next tick decides every reply"
    (backlog.all fun o => (mixedTicked.db.status o.id).isSome)
  return ← t.finish "good vacuity"

end Vacuity.Good
