import engine.sync.RoundRun
import engine.sync.NewestLaws
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
-- The responder reads ix at even steps, the dialer iy at odd ones.
def ixs (n : Nat) : Index := if n % 2 = 0 then ix else iy
def first := initial cfg room ix iy 0
def states := execute cfg room 1 times ixs first

theorem runs : Exec cfg room 1 times ixs states := execute_runs cfg room 1 times ixs first
theorem run : Run cfg room 1 times states := exec_runs cfg room 1 times ixs states runs
theorem ready : Both room 1 (states 0) := initial_ready ..
theorem current : Current room 1 states := exec_current cfg room 1 times ixs states runs ready
theorem sortedX : Sorted Prod.fst xs := by unfold Sorted xs; decide
theorem sortedY : Sorted Prod.fst ys := by unfold Sorted ys; decide
theorem named : Named Prod.fst Prod.snd (xs ++ ys) := by
  simp [Named, xs, ys]
  decide

-- Both ends are full (floor 0): every step's set is the room's items.
theorem full (t : Nat) : Full (states t).receiving ∧ Full (states t).waiting :=
  exec_full cfg room 1 times ixs states runs
    (by simp [states, execute, first, initial, Full, Conn.start, Conn.due, Conn.roundedAt, Conn.retake,
      Conn.beginRound]) t

theorem itemsAt (n : Nat) : (states n).items cfg room 1 = if n % 2 = 0 then xs else ys := by
  rw [items_full _ _ _ _ (full n).1]
  cases n with
  | zero => rfl
  | succ n =>
    change (ixs (n + 1)).items room = _
    unfold ixs
    split <;> rfl

theorem itemsX (t : Nat) : (states (2 * t)).items cfg room 1 = xs := by
  rw [itemsAt, if_pos (by omega)]
theorem itemsY (t : Nat) : (states (2 * t + 1)).items cfg room 1 = ys := by
  rw [itemsAt, if_neg (by omega)]

theorem items0 : (states 0).items cfg room 1 = xs := by simpa using itemsX 0
theorem items1 : (states 1).items cfg room 1 = ys := by simpa using itemsY 0

-- The messages claim times; the structure range (time 0) is empty on both sides.
theorem withinX : within Prod.fst timedRange xs = xs := by decide
theorem withinY : within Prod.fst timedRange ys = ys := by decide
theorem structX : within Prod.fst structureRange xs = [] := by decide
theorem structY : within Prod.fst structureRange ys = [] := by decide

-- The opening: the structure range first (no ids there), then the messages.
theorem startsFingerprint : (states 0).pending =
    [.ids structureRange [], .fp timedRange 2 (lbl Prod.fst Prod.snd sha256 ys)] := by
  change (initial cfg room ix iy 0).pending = _
  rw [initial_claim]
  change [opening Prod.fst Prod.snd sha256 cfg.params ys structureRange,
    opening Prod.fst Prod.snd sha256 cfg.params ys timedRange] = _
  simp only [opening, withinY, structY]
  simp [cfg, fp, ys]

-- Count mismatch (1 versus 2) forces an id reply, independently of hashes.
theorem firstReply : (states 1).pending = [.ids timedRange [alice]] := by
  rw [next_pending cfg room 1 times states run current 0 (by rw [startsFingerprint]; simp), items0]
  simp only [outputs, startsFingerprint, List.flatMap_cons, List.flatMap_nil, List.append_nil, answer, withinX,
    structX]
  simp [cfg, fp, xs, nextClaims]

theorem secondReply : (states 2).pending = [] := by
  rw [next_pending cfg room 1 times states run current 1 (by rw [firstReply]; simp), items1]
  simp [outputs, firstReply, answer, nextClaims, withinY]

theorem laterEmpty (n : Nat) : (states (n + 2)).pending = [] := by
  simpa [Nat.add_comm] using run_empty cfg room 1 times ixs states runs 2 secondReply n

theorem bounded (t : Nat) : (states t).receiving.Bounded cfg ∧ (states t).waiting.Bounded cfg :=
  run_bounded cfg room 1 times ixs states runs
    (by simp [states, execute, first, initial, Conn.start, Conn.due, Conn.roundedAt, Conn.beginRound,
      Conn.Bounded, cfg]) t

theorem capacity (t : Nat) : Capacity cfg room 1 (states t) := by
  cases t with
  | zero =>
    rw [Capacity, items0]
    have asks : (states 0).receiving.asked = ∅ := rfl
    simp only [asks, outputs, startsFingerprint, List.flatMap_cons, List.flatMap_nil, List.append_nil, answer, withinX,
      structX]
    simp [fp, cfg, xs, roundWants]
  | succ t =>
    cases t with
    | zero =>
      rw [Capacity, items1]
      have asks : (states 1).receiving.asked = ∅ := rfl
      simp only [asks, outputs, firstReply, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        answer, roundWants, List.flatMap_cons, List.flatMap_nil, List.nil_append, List.append_nil,
        Std.HashSet.size_empty, Nat.zero_add]
      simp only [withinY]
      exact Nat.le_trans (List.length_filter_le _ _) (by decide)
    | succ n =>
      have empty := laterEmpty n
      change (states (n + 2)).receiving.asked.size +
        (roundWants (outputs cfg ((states (n + 2)).items cfg room 1) (states (n + 2)).pending)).length ≤ cfg.maxKnown
      simp only [empty, outputs, List.flatMap_nil, roundWants, List.length_nil, Nat.add_zero]
      exact (bounded (n + 2)).1.2

theorem ranks : ∀ cl ∈ (states 0).pending, rankIn (xs ++ ys) cl ≤ 7 := by
  rw [startsFingerprint]
  intro cl hc
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> decide

theorem emptyAsks : (states 0).receiving.asked = ∅ ∧ (states 0).waiting.asked = ∅ :=
  initial_asks ..

theorem terminates : ∃ j, j ≤ 8 ∧ (states j).pending = [] := by
  have sub : ∀ t, ∀ a ∈ (states t).items cfg room 1, a ∈ xs ++ ys := by
    intro t a ha; rw [itemsAt] at ha
    split at ha
    · exact List.mem_append_left _ ha
    · exact List.mem_append_right _ ha
  have sorted : ∀ t, Sorted Prod.fst ((states t).items cfg room 1) := by
    intro t; rw [itemsAt]; split
    · exact sortedX
    · exact sortedY
  obtain ⟨j, _, hj, hdone⟩ := RoundRun.terminates cfg room 1 times states run current (xs ++ ys) sub sorted 7 0 ranks
  exact ⟨j, by omega, hdone⟩

-- Checking all possible filtered snapshots proves Sound for every range.
-- No global injectivity or collision-resistance axiom is introduced.
def exchangeCertificate :=
  if checked : collisionCheck (hashInputs xs ++ hashInputs ys) = true then
    if pending : alice ∈ (states 2).waiting.asked then
      let sound := sound_of_check xs ys checked
      let result := conn_runs_exchange cfg room 1 7 times ixs states xs ys runs capacity (by decide)
        ready itemsX itemsY sortedX sortedY named sound emptyAsks.1 emptyAsks.2 ranks
      have member : opening Prod.fst Prod.snd sha256 cfg.params ys timedRange ∈ (states 0).pending := by
        change _ ∈ (initial cfg room ix iy 0).pending
        rw [initial_claim]
        exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
      have honest := opening_honest (key := Prod.fst) (ident := Prod.snd) (h := sha256) (P := cfg.params) ys timedRange
      have enough : (within Prod.fst timedRange xs).length + (within Prod.fst timedRange ys).length < 4 := by decide
      let exactIds := exchange_complete (P := cfg.params) 4 xs ys timedRange _ sortedX sortedY named sound honest enough
      have aliceMissing := (exactIds alice).1.mpr (by decide)
      have bobMissing := (exactIds bob1).2.mpr (by decide)
      have bobMissing2 := (exactIds bob2).2.mpr (by decide)
      let announces := result.2 _ member timedRange honest 4 enough
      let aliceWire := announces alice (Or.inl aliceMissing)
      let bobWire := announces bob1 (Or.inr bobMissing)
      let bobWire2 := announces bob2 (Or.inr bobMissing2)
      let earlierWant := pending_source cfg room 1 times ixs states runs (by decide) emptyAsks.1 emptyAsks.2
        2 alice (Or.inr pending)
      some (PLift.up (And.intro result.1 (And.intro aliceWire (And.intro bobWire (And.intro bobWire2 earlierWant)))))
    else none
  else none

-- Newest first on the fixture's items: answering Alice's ids claim, Bob's
-- two messages are offered newest first; the opening's answer likewise.
set_option linter.defProp false in
def newestAnswer := answer_newest_first (key := Prod.fst) (ident := Prod.snd) (h := sha256)
  (P := cfg.params) ys sortedY (.ids timedRange [alice])
set_option linter.defProp false in
def windowFirst := window_first 100
set_option linter.defProp false in
def newestHaves := newest_first (key := Prod.fst) (ident := Prod.snd) (h := sha256) (P := cfg.params)
  ys sortedY ((window 0).map (opening Prod.fst Prod.snd sha256 cfg.params xs))
  (by simpa [List.map_map, Function.comp_def, opening_range] using (window_first 0).1)
  (by intro c hc; obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hc; rw [opening_range]; exact (window_first 0).2 w hw)
set_option linter.defProp false in
def openingNewest := opening_newest_first (key := Prod.fst) (ident := Prod.snd) (h := sha256)
  (P := cfg.params) ys xs sortedY 0

def main : IO UInt32 := do
  let t ← Checks.new
  t.ok "finite native SHA check discharges every range fingerprint premise" exchangeCertificate.isSome
  t.ok "opening claims the structure range first, then a real fingerprint over two messages"
    (match (states 0).pending with | [.ids q [], .fp _ 2 _] => q == structureRange | _ => false)
  t.ok "count mismatch causes actual fingerprint-to-id transition"
    (match (states 1).pending with | [.ids _ [i]] => i == alice | _ => false)
  t.ok "Bob's haves answer Alice's ids claim newest first"
    ((answer Prod.fst Prod.snd sha256 cfg.params ys (.ids timedRange [alice])).flatMap holdIds == [bob2, bob1])
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
