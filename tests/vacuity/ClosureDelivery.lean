import engine.sync.ClosureDelivery
import tests.vacuity.IdentityTrust

/- Synthetic signed Alice/Bob community, not captured private user data.
The same actual service and Node.put operations appear in both the infinite
certificate and the finite executable regression. -/
namespace Vacuity.ClosureDelivery
open Engine Engine.Sync Community Tests Vacuity.Identity Vacuity.IdentityTrust
set_option linter.defProp false
attribute [local instance] byteArray_lawfulBEq

def fam := family ed25519
def cfg : Config := {}
def source : Held Fact := { log := before, db := run before }
def sync : Sync Fact (HeldM Fact) := {
  fam := fam
  hooks := {
    rooms := fun _ => pure []
    sealFor := fun _ _ => pure none
    openFrame := fun _ => pure none } }

def base : Conn := {
  dialer := false
  rooms := [c]
  floor := 0 }
def index := Index.ofOps fam before
def initial : Conn := (base.onWant cfg index (before.reverse.map Op.id)).conn

theorem want_rooms (conn : Conn) (ids : List Id) :
    (conn.onWant cfg index ids).conn.rooms = conn.rooms := by
  unfold Conn.onWant
  split <;> rfl

/-- Every third service poll has no room. New requests join forever. -/
def room (n : Nat) : Nat := if n % 3 = 0 then 0 else 1
def priorities : List Id := [renamed.id]
def moreWants : List Id := [r.id, renamed.id]
def sender : Nat → Conn
  | 0 => initial
  | n + 1 =>
    let out := (((sender n).serveOwed fam cfg (room n) priorities : HeldM Fact _) source).1.1
    (out.onWant cfg index moreWants).conn

def service : ServiceRun fam cfg := {
  store := fun _ => source
  conn := sender
  room := room
  first := fun _ => priorities
  added := fun n =>
    let out := (((sender n).serveOwed fam cfg (room n) priorities : HeldM Fact _) source).1.1
    (out.onWant cfg index moreWants).conn.owed.drop out.owed.length
  next := fun n => by
    let out := (((sender n).serveOwed fam cfg (room n) priorities : HeldM Fact _) source).1.1
    obtain ⟨added, he⟩ := onWant_order cfg index out moreWants
    change (out.onWant cfg index moreWants).conn.owed =
      out.owed ++ (out.onWant cfg index moreWants).conn.owed.drop out.owed.length
    rw [he]
    simp }

theorem sender_rooms (n : Nat) : (sender n).rooms = [c] := by
  induction n with
  | zero => exact want_rooms base _
  | succ n ih =>
    simp only [sender, want_rooms, serveOwed_eq]
    exact ih

theorem room_recurs : ∀ N, ∃ n ≥ N, 0 < room n := by
  intro N
  refine ⟨3 * N + 1, by omega, ?_⟩
  simp [room, Nat.add_mod]

/-- What the receiver takes in at step n: the last two polls' sends, the
older reversed (out of order and repeated). -/
def incoming (n : Nat) : List Op := (service.emitted (n - 1)).reverse ++ service.emitted n

/-- Odd steps are a tick's idle turn; even ones receive. -/
def idleAt (n : Nat) : Bool := n % 2 == 1

def receiver : Nat → Node × Held Fact
  | 0 => (Node.boot fam [] 0, {})
  | n + 1 =>
    if idleAt n then ((receiver n).1, ((Turn.turn fam [] : HeldM Fact Unit) (receiver n).2).2)
    else
      let result := ((receiver n).1.put sync (incoming n) false (receiver n).2)
      (result.1.1, result.2)

theorem emitted_source (n : Nat) : service.emitted n ⊆ before := by
  intro o he
  obtain ⟨_, i, _, hi⟩ := serveOwed_shown fam cfg (sender n) (room n) priorities source o
    (List.mem_append.mp he)
  exact (reach_stored (runReach before) i o hi).1

theorem incoming_source (n : Nat) : incoming n ⊆ before := by
  intro o ho
  rcases List.mem_append.mp ho with h | h
  · exact emitted_source _ (List.mem_reverse.mp h)
  · exact emitted_source n h

theorem receiver_succ (n : Nat) : receiver (n + 1) =
    if idleAt n then ((receiver n).1, ((Turn.turn fam [] : HeldM Fact Unit) (receiver n).2).2)
    else (((receiver n).1.put sync (incoming n) false (receiver n).2).1.1,
      ((receiver n).1.put sync (incoming n) false (receiver n).2).2) := rfl

theorem receiver_put (n : Nat) (hi : idleAt n = false) :
    (receiver (n + 1)).2 = ((receiver n).1.put sync (incoming n) false (receiver n).2).2 := by
  rw [receiver_succ, hi]; rfl

theorem receiver_idle (n : Nat) (hi : idleAt n = true) :
    (receiver (n + 1)).2 = ((Turn.turn fam [] : HeldM Fact Unit) (receiver n).2).2 := by
  rw [receiver_succ, hi]; rfl

theorem receiver_log (n : Nat) : (receiver n).2.log ⊆ before := by
  induction n with
  | zero => simp [receiver]
  | succ n ih =>
    intro o ho
    cases hi : idleAt n
    · rw [receiver_put n hi] at ho
      have h := write_log_subset sync (receiver n).1 (receiver n).2 (intake fam false (incoming n)) ho
      rcases List.mem_append.mp h with h | h
      · exact ih h
      · exact incoming_source n (intake_sub fam h)
    · rw [receiver_idle n hi] at ho
      have : o ∈ (receiver n).2.log ++ [] := ho
      exact ih (by simpa using this)

def receiving (hd : Distinct before) : ReceiverRun sync := {
  node := fun n => (receiver n).1
  store := fun n => (receiver n).2
  input := incoming
  idle := idleAt
  next := fun n => by
    show (receiver (n + 1)).2 = _
    cases hi : idleAt n
    · rw [receiver_put n hi]; rfl
    · rw [receiver_idle n hi]; rfl
  initial := held_empty_reachable fam
  initialWaiting := waiting_empty
  distinct := fun n a ha b hb he =>
    hd a (List.mem_append.mp ha |>.elim (fun h => receiver_log n h) (fun h => incoming_source n h))
      b (List.mem_append.mp hb |>.elim (fun h => receiver_log n h) (fun h => incoming_source n h)) he }

/-- Ticks recur: every odd step. -/
theorem receiving_ticks (hd : Distinct before) : (receiving hd).Ticks := fun N =>
  ⟨2 * N + 1, by omega, by show idleAt (2 * N + 1) = true; simp [idleAt, Nat.add_mod]⟩

/-- Every poll's sends reach a receiving step: its own, if even, or the next. -/
theorem delivered (hd : Distinct before) (j : Nat) (o : Op) (ho : o ∈ service.emitted j) :
    ∃ k ≥ j, (receiving hd).idle k = false ∧ o ∈ (receiving hd).input k := by
  by_cases hj : j % 2 = 1
  · refine ⟨j + 1, by omega, ?_, ?_⟩
    · show idleAt (j + 1) = false; simp [idleAt]; omega
    · show o ∈ incoming (j + 1)
      exact List.mem_append_left _ (by simpa using ho)
  · refine ⟨j, Nat.le_refl _, ?_, ?_⟩
    · show idleAt j = false; simp [idleAt]; omega
    · exact List.mem_append_right _ ho

def Result : Prop := ∃ k, ∀ j ≥ k,
  (∀ o ∈ before, (receiver j).2.db.ops o.id = some o) ∧
  (receiver j).2.db.status message.id = some (.valid messageFact)

theorem convergence (hd : Distinct before)
    (available : ∀ o ∈ before, source.db.ops o.id = some o ∧ initial.shows fam o = true)
    (queued : ∀ o ∈ before, o.id ∈ initial.owed)
    (spec : Spec fam source.db.ops message.id (.valid messageFact))
    (capped : ∀ o ∈ before, o.capped = true) : Result := by
  obtain ⟨k, _, hk⟩ := closure_delivered (x := sync) (cfg := cfg) service (receiving hd) before source.db.ops message.id
    (.valid messageFact) 0 spec
    (fun i o _ ho => reach_stored (runReach before) i o ho)
    room_recurs
    (fun o ho j _ => ⟨(available o ho).1, by
      have e : (sender j).rooms = initial.rooms := (sender_rooms j).trans (want_rooms base _).symm
      exact (shows_rooms fam e o).trans (available o ho).2⟩)
    (fun o ho => Or.inr ⟨0, Nat.le_refl _, queued o ho⟩)
    (fun j _ o ho => delivered hd j o ho) capped (receiving_ticks hd)
  exact ⟨k, hk⟩

instance : Decidable (Distinct before) := by unfold Distinct; infer_instance

/-- Finite production crypto checks discharge all premises of the infinite
closure theorem. No universal native crypto contract or schedule premise is
introduced here. -/
def certificate : Option (PLift Result) :=
  if hd : Distinct before then
    if hav : before.all (fun o => decide
        (source.db.ops o.id = some o ∧ initial.shows fam o = true ∧ o.id ∈ initial.owed)) = true then
      if hs : source.db.status message.id = some (.valid messageFact) then
        if hc : before.all Op.capped = true then
          some ⟨convergence hd
            (fun o ho => let h := of_decide_eq_true (List.all_eq_true.mp hav o ho); ⟨h.1, h.2.1⟩)
            (fun o ho => (of_decide_eq_true (List.all_eq_true.mp hav o ho)).2.2)
            ((runInv before).sound _ _ hs) (fun o ho => List.all_eq_true.mp hc o ho)⟩
        else none
      else none
    else none
  else none

/-- The helper checks use the already populated signed community and a
new signed message, with old operations and retransmissions mixed in. -/
def extra := post c admission.id bob "content-key-1".toUTF8
  "The closure is complete; this message is new.".toUTF8 2 29880001
def extraFact := Fact.message c requestB.id bob.pk "content-key-1".toUTF8
  "The closure is complete; this message is new.".toUTF8 2 29880001
def jobs := [r, extra, message, extra]
def staged := [message]
def writer := Node.boot fam before 0

-- Closed kernel instances: their actual premises are list membership, not
-- successful opaque crypto calculations. Native checks below also exercise
-- the fresh write and deduplication branches on the same signed values.
theorem writeStoreWitness :
    (writer.write sync jobs source).2 =
      let absent := jobs.foldl (absentStep source.db) []
      if absent.isEmpty then source else
        ((Turn.turn fam absent.reverse : HeldM Fact Unit) source).2 :=
  write_store sync writer source jobs

theorem absentStepKeepsWitness : message ∈ absentStep source.db staged extra :=
  absentStep_keeps source.db staged message extra (by simp [staged])

theorem absentFoldKeepsWitness : message ∈ jobs.foldl (absentStep source.db) staged :=
  absentFold_keeps source.db jobs staged (by simp [staged])

-- The source witnesses deliberately select the newly added operation,
-- rather than an operation that was present in the initial accumulator.
def absentStepSourceWitness :=
  if h : extra ∈ absentStep source.db staged extra then
    some (PLift.up (absentStep_source source.db staged extra extra h))
  else none

def absentFoldSourceWitness :=
  if h : extra ∈ jobs.foldl (absentStep source.db) staged then
    some (PLift.up (absentFold_source source.db jobs staged h))
  else none

def absentFoldCoversWitness :=
  if h : source.db.ops extra.id = none then
    some (PLift.up (absentFold_covers source.db jobs staged (o := extra)
      (by simp [jobs]) h))
  else none

def main : IO UInt32 := do
  let t ← Checks.new
  t.ok "new signed message satisfies absent-step source premise" absentStepSourceWitness.isSome
  t.ok "mixed repeated input satisfies absent-fold source premise" absentFoldSourceWitness.isSome
  t.ok "new signed message satisfies absent-fold coverage premise" absentFoldCoversWitness.isSome
  t.ok "absent-step keeps existing queue and adds the new message"
    ((absentStep source.db staged extra).contains message &&
      (absentStep source.db staged extra).contains extra)
  t.ok "deduplication keeps original queue and admits one new message"
    (jobs.foldl (absentStep source.db) staged == [extra, message])
  t.ok "deduplication never invents an unrelated signed removal"
    (!(jobs.foldl (absentStep source.db) staged).contains removeB)
  let written := (writer.write sync jobs source).2
  t.ok "actual write stores and validates new message while retaining old history"
    (written.db.ops message.id == some message && written.db.ops extra.id == some extra &&
      written.db.status extra.id == some (.valid extraFact) && written.db.queue.isEmpty)
  t.ok "finite signed premises instantiate infinite closure convergence" certificate.isSome
  t.ok "zero ordinary capacity still sends hot requests"
    ([0, 3, 6].all fun n =>
      let sent := (((sender n).serveOwed fam cfg (room n) priorities : HeldM Fact _) source).1.2
      !sent.1.isEmpty && sent.2.isEmpty)
  t.ok "positive ordinary capacity serves both lanes under continuous hot requests"
    ([1, 2, 4].all fun n =>
      let sent := (((sender n).serveOwed fam cfg (room n) priorities : HeldM Fact _) source).1.2
      !sent.1.isEmpty && !sent.2.isEmpty)
  let out := receiver 24
  t.ok "all signed closure operations arrive despite stalls and tail requests"
    (before.all fun o => out.2.db.ops o.id == some o)
  t.ok "dependency closure validates Bob's actual signed message"
    (out.2.db.status message.id == some (.valid messageFact))
  t.ok "actual write turn has drained validation queue" out.2.db.queue.isEmpty
  t.ok "continuing requests keep sender queue occupied" (!(sender 24).owed.isEmpty)
  t.ok "late duplicate inputs preserve complete validated closure"
    ((receiver 36).2.db.status message.id == some (.valid messageFact))
  let early := receiver 8
  t.ok "message arrives before missing root and remains unresolved"
    (early.2.db.ops message.id == some message && early.2.db.status message.id == none)
  let withheld := (Node.boot fam [] 0).put sync (before.filter (fun o => o.id != r.id)) false ({} : Held Fact)
  t.ok "withholding root blocks dependent message validation"
    (withheld.2.db.ops message.id == some message && withheld.2.db.status message.id == none)
  let denied := { initial with rooms := [] }
  t.ok "revoked authorization emits no closure payload"
    (((((denied.serveOwed fam cfg 100000 [] : HeldM Fact _) source).1.2).2).isEmpty)
  t.ok "actual session byte decoder accepts each authorized data operation"
    (before.all fun o => (((initial.recv fam cfg {} o.bytes 0 : HeldM Fact Step) source).1.take == [o]))
  t.ok "decoder rejects data after room authorization is removed"
    (before.all fun o => (((denied.recv fam cfg {} o.bytes 0 : HeldM Fact Step) source).1.take).isEmpty)
  t.finish "closure delivery: signed runtime premises and infinite convergence"

end Vacuity.ClosureDelivery
