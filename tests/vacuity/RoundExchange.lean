import ops.sync.RoundRun
import tests.engine.Checks

namespace Vacuity.RoundExchange
open Engine Engine.Sync Engine.Sync.RoundRun Tests
attribute [local instance] byteArray_lawfulBEq
set_option maxRecDepth 4096

-- Synthetic index entries: three different stored-message identifiers.
-- The native certificate uses the production SHA256 implementation.
def room : Id := "round-exchange-room".toUTF8
def alice : Id := "alice-history-message-00000000001".toUTF8
def bob1 : Id := "bob-history-message-000000000001".toUTF8
def bob2 : Id := "bob-history-message-000000000002".toUTF8
def xs : List Item := [(⟨1, 1⟩, alice)]
def ys : List Item := [(⟨2, 2⟩, bob1), (⟨3, 3⟩, bob2)]
def ix : Index := { rooms := [(room, xs)] }
def iy : Index := { rooms := [(room, ys)] }
def cfg : Config := { params := { leaf := 1, fan := 2 }, maxKnown := 8, maxIds := 1 }
def times (n : Nat) : Nat := n * 10
def first := initial cfg room ix iy 0
def states := execute cfg room 1 times first

theorem runs : Run cfg room 1 times states := execute_runs cfg room 1 times first
theorem ready : Ready room 1 xs ys (states 0) := initial_ready ..
theorem sortedX : Sorted Prod.fst xs := by unfold Sorted xs; decide
theorem sortedY : Sorted Prod.fst ys := by unfold Sorted ys; decide
theorem named : Named Prod.fst Prod.snd (xs ++ ys) := by
  simp [Named, xs, ys]
  decide

theorem withinX : within Prod.fst fullRange xs = xs := by decide
theorem withinY : within Prod.fst fullRange ys = ys := by decide

theorem startsFingerprint : (states 0).pending =
    [.fp fullRange 2 (lbl Prod.fst Prod.snd sha256 ys)] := by
  change (initial cfg room ix iy 0).pending = _
  rw [initial_claim]
  change [opening Prod.fst Prod.snd sha256 cfg.params ys fullRange] = _
  simp only [opening, withinY]
  simp [cfg, fp, ys]

-- Count mismatch (1 versus 2) forces an id reply, independently of hashes.
theorem firstReply : (states 1).pending = [.ids fullRange [alice]] := by
  rw [runs 0, successor cfg room 1 (times 0) xs ys _ ready (by rw [startsFingerprint]; simp)]
  simp only [outputs, startsFingerprint, List.flatMap_cons, List.flatMap_nil, List.append_nil, answer, withinX]
  simp [cfg, fp, xs, nextClaims]

theorem readyOne : Ready room 1 ys xs (states 1) := by
  rw [runs 0]
  apply ready_next cfg room 1 (times 0) xs ys _ ready (by rw [startsFingerprint]; simp)
  rw [← runs 0, firstReply]
  simp

theorem secondReply : (states 2).pending = [] := by
  rw [show 2 = 1 + 1 from rfl, runs 1,
    successor cfg room 1 (times 1) ys xs _ readyOne (by rw [firstReply]; simp)]
  simp [outputs, firstReply, answer, nextClaims]

theorem laterEmpty (n : Nat) : (states (n + 2)).pending = [] := by
  simpa [Nat.add_comm] using run_empty cfg room 1 times states runs 2 secondReply n

theorem bounded (t : Nat) : (states t).receiving.Bounded cfg ∧ (states t).waiting.Bounded cfg :=
  run_bounded cfg room 1 times states runs
    (by simp [states, execute, first, initial, Conn.start, Conn.beginRound, Conn.Bounded, cfg]) t

theorem capacity (t : Nat) : Capacity cfg room 1 (states t) := by
  cases t with
  | zero =>
    rw [Capacity, ready.2.2.2.2.1]
    have asks : (states 0).receiving.asked = ∅ := rfl
    simp only [asks, outputs, startsFingerprint, List.flatMap_cons, List.flatMap_nil, List.append_nil, answer, withinX]
    simp [fp, cfg, xs, roundWants]
  | succ t =>
    cases t with
    | zero =>
      rw [Capacity, readyOne.2.2.2.2.1]
      have asks : (states 1).receiving.asked = ∅ := rfl
      simp only [asks, outputs, firstReply, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        answer, withinY, roundWants, List.flatMap_cons, List.flatMap_nil, List.nil_append, List.append_nil,
        Std.HashSet.size_empty, Nat.zero_add]
      exact Nat.le_trans (List.length_filter_le _ _) (by decide)
    | succ n =>
      have empty := laterEmpty n
      change (states (n + 2)).receiving.asked.size +
        (roundWants (outputs cfg ((states (n + 2)).receiving.snap (states (n + 2)).index room 1)
          (states (n + 2)).pending)).length ≤ cfg.maxKnown
      simp only [empty, outputs, List.flatMap_nil, roundWants, List.length_nil, Nat.add_zero]
      exact (bounded (n + 2)).1.2

theorem ranks : ∀ cl ∈ (states 0).pending, rank xs ys cl ≤ 7 := by
  rw [startsFingerprint]
  intro cl hc
  obtain rfl := List.mem_singleton.mp hc
  decide

theorem emptyAsks : (states 0).receiving.asked = ∅ ∧ (states 0).waiting.asked = ∅ :=
  initial_asks ..

theorem terminates : ∃ j, j ≤ 8 ∧ (states j).pending = [] := by
  obtain ⟨j, _, hj, hdone⟩ := RoundRun.terminates cfg room 1 times states runs 7 0 xs ys ready sortedX sortedY ranks
  exact ⟨j, by omega, hdone⟩

-- Checking all possible filtered snapshots proves Sound for every range.
-- No global injectivity or collision-resistance axiom is introduced.
def exchangeCertificate :=
  if checked : collisionCheck (hashInputs xs ++ hashInputs ys) = true then
    if pending : alice ∈ (states 2).waiting.asked then
      let sound := sound_of_check xs ys checked
      let result := conn_runs_exchange cfg room 1 7 times states xs ys runs capacity (by decide)
        ready sortedX sortedY named sound emptyAsks.1 emptyAsks.2 ranks
      have member : opening Prod.fst Prod.snd sha256 cfg.params ys fullRange ∈ (states 0).pending := by
        change _ ∈ (initial cfg room ix iy 0).pending
        rw [initial_claim]
        exact List.mem_singleton_self _
      have honest := opening_honest (key := Prod.fst) (ident := Prod.snd) (h := sha256) (P := cfg.params) ys fullRange
      have enough : (within Prod.fst fullRange xs).length + (within Prod.fst fullRange ys).length < 4 := by decide
      let exactIds := exchange_complete (P := cfg.params) 4 xs ys fullRange _ sortedX sortedY named sound honest enough
      have aliceMissing := (exactIds alice).1.mpr (by decide)
      have bobMissing := (exactIds bob1).2.mpr (by decide)
      have bobMissing2 := (exactIds bob2).2.mpr (by decide)
      let announces := result.2 _ member fullRange honest 4 enough
      let aliceWire := announces alice (Or.inl aliceMissing)
      let bobWire := announces bob1 (Or.inr bobMissing)
      let bobWire2 := announces bob2 (Or.inr bobMissing2)
      let earlierWant := pending_source cfg room 1 times states runs (by decide) emptyAsks.1 emptyAsks.2
        2 alice (Or.inr pending)
      some (PLift.up (And.intro result.1 (And.intro aliceWire (And.intro bobWire (And.intro bobWire2 earlierWant)))))
    else none
  else none

def main : IO UInt32 := do
  let t ← Checks.new
  t.ok "finite native SHA check discharges every range fingerprint premise" exchangeCertificate.isSome
  t.ok "opening uses a real fingerprint over two messages"
    (match (states 0).pending with | [.fp _ 2 _] => true | _ => false)
  t.ok "count mismatch causes actual fingerprint-to-id transition"
    (match (states 1).pending with | [.ids _ [i]] => i == alice | _ => false)
  t.ok "both message sets reach a terminal claim batch" ((states 2).pending.isEmpty)
  t.ok "terminal batches remain empty through later delivered steps" ((states 10).pending.isEmpty)
  t.ok "a later pending ask has an earlier actual wire witness" ((states 2).waiting.asked.contains alice)
  let sent := ((states 1).result cfg room 1 (times 1)).send
  t.ok "actual wire holds both Bob messages in separate bounded chunks"
    (sent.any (fun o => o.bytes == (Msg.hold room [bob1]).op.bytes) &&
      sent.any (fun o => o.bytes == (Msg.hold room [bob2]).op.bytes))
  t.ok "actual wire requests Alice's missing message"
    (sent.any fun o => o.bytes == (Msg.want [alice]).op.bytes)
  t.ok "a constant hash fails the finite collision checker"
    (!collisionCheckWith (fun _ => .empty) (hashInputs xs ++ hashInputs ys))
  let capped := ((states 1).result { cfg with maxKnown := 0 } room 1 (times 1)).send
  t.ok "zero ask capacity prevents the request and violates the positive premise"
    (!(capped.any fun o => o.bytes == (Msg.want [alice]).op.bytes))
  t.finish "round exchange: real handler transitions and finite SHA premises"

end Vacuity.RoundExchange
