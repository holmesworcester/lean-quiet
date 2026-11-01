/- Production hooks with an advancing entropy tape. ReadsHeld preserves
only the Held database/history; fresh draws are allowed to change cursor. -/
import ops.connection.Execution
import engine.wire.WorldLaws

namespace Connection.Execution
open Engine Engine.Sync Codec

@[simp] theorem M.bind_apply {α β} (p : M α) (k : α → M β) (s : Memory) :
    (p >>= k) s = k (p s).1 (p s).2 := rfl
@[simp] theorem M.pure_apply {α} (a : α) (s : Memory) :
    (pure a : M α) s = (a, s) := rfl

def ReadsHeld {α} (p : M α) : Prop := ∀ s, (p s).2.held = s.held

namespace ReadsHeld
 theorem pure' {α} (a : α) : ReadsHeld (pure a : M α) := fun _ => rfl
 theorem bind' {α β} {p : M α} {k : α → M β}
     (hp : ReadsHeld p) (hk : ∀ a, ReadsHeld (k a)) : ReadsHeld (p >>= k) := by
   intro s
   exact (hk _ _).trans (hp s)
 theorem forIn' {α β} (l : List α) (b : β) {f : α → β → M (ForInStep β)}
     (hf : ∀ a b, ReadsHeld (f a b)) : ReadsHeld (forIn l b f) := by
   induction l generalizing b with
   | nil => exact pure' b
   | cons a t ih =>
     rw [List.forIn_cons]
     apply bind' (hf a b)
     intro r
     cases r with
     | done b => exact pure' b
     | yield b => exact ih b
 theorem getOp' (i : Id) : ReadsHeld (Store.getOp i : M _) := fun _ => rfl
 theorem getStatus' (i : Id) : ReadsHeld (Store.getStatus i : M _) := fun _ => rfl
 theorem fresh : ReadsHeld (Fresh.fresh : M ByteArray) := fun _ => rfl
end ReadsHeld

syntax "readsHeld" "[" term,* "]" : tactic
macro_rules
  | `(tactic| readsHeld [$ts,*]) => do
    let mut tac : Lean.TSyntax `tactic ← `(tactic| first | split | intro)
    for t in ts.getElems.reverse do
      tac ← `(tactic| first | with_reducible_and_instances apply $t | $tac:tactic)
    `(tactic| repeat' (first
      | dsimp only | with_reducible_and_instances apply ReadsHeld.bind'
      | with_reducible_and_instances apply ReadsHeld.pure' | with_reducible_and_instances apply ReadsHeld.forIn'
      | with_reducible_and_instances apply ReadsHeld.getOp' | with_reducible_and_instances apply ReadsHeld.getStatus'
      | $tac:tactic))

/-- **A view run on held data is its evaluation**, and leaves the store
as it is. -/
theorem view_held {α} (v : View F α) (h : Memory) :
    (v.run : M α) h = (v.eval h.held.db, h) := by
  induction v with
  | pure a => rfl
  | list q k ih => exact ih (Engine.eval h.held.db q)

theorem view_reads {α} (v : View F α) : ReadsHeld (v.run : M α) := fun h => by
  rw [view_held]

/-- **The rooms hook is `roomsV`, read afresh from the store**, and it
reads only. -/
theorem rooms_held (cid : Id) (h : Memory) :
    (rooms cid : M (List Room)) h = ((roomsV cid).eval h.held.db, h) :=
  view_held (roomsV cid) h

theorem list_reads (q : ListQ) : ReadsHeld (Lists.list q : M (Answer F)) := fun _ => rfl

theorem rows_reads (r : Rel Fact) (args : List B) : ReadsHeld (rows r args : M _) := by
  unfold rows; readsHeld [list_reads]

theorem count_reads (r : Rel Fact) (args : List B) : ReadsHeld (count r args : M _) := by
  unfold count; readsHeld [list_reads]

theorem endpoints_reads : ReadsHeld (endpoints : M _) := by
  unfold endpoints; readsHeld [list_reads]

theorem arrivedFrom_reads (x : Id) : ReadsHeld (arrivedFrom x : M _) := by
  unfold arrivedFrom; readsHeld [rows_reads]

theorem arrival_reads (x : Id) : ReadsHeld (arrival x : M _) := by
  unfold arrival; readsHeld [rows_reads]

/-- `sessionKeys_reads` (ops/connection/Laws.lean), as `ReadsHeld`. -/
private theorem keys_reads (cid : Id) : ReadsHeld (sessionKeys cid : M _) := by
  unfold sessionKeys; readsHeld [rows_reads]

theorem connectedTo_reads (peer : B) : ReadsHeld (connectedTo peer : M _) := by
  unfold connectedTo; readsHeld [rows_reads]

theorem helloOf_reads (K : Keys) (sk r to m1 : B) : ReadsHeld (helloOf K sk r to m1 : M _) := by
  unfold helloOf; readsHeld [rows_reads]

/-! ## react -/

theorem openEach_reads (epOp : Id) : ∀ l, ReadsHeld (openEach epOp l : M (List Op))
  | [] => ReadsHeld.pure' _
  | (_, _) :: t => by rw [openEach]; readsHeld [count_reads, openEach_reads epOp t]

theorem openAll_reads : ∀ l, ReadsHeld (openAll l : M (List Op))
  | [] => ReadsHeld.pure' _
  | (_, _, _) :: t => by rw [openAll]; readsHeld [rows_reads, openEach_reads, openAll_reads t]

theorem joinsOf_reads (fam : Family F) (c : B) : ∀ l, ReadsHeld (joinsOf fam c l : M (List Op))
  | [] => ReadsHeld.pure' _
  | _ :: t => by rw [joinsOf]; readsHeld [joinsOf_reads fam c t]

theorem deliverAll_reads (fam : Family F) : ∀ l, ReadsHeld (deliverAll fam l : M (List Op)) := by
  intro l
  induction l with
  | nil => exact ReadsHeld.pure' _
  | cons p t ih =>
    obtain ⟨x, f⟩ := p
    cases f <;> simp only [deliverAll] <;> readsHeld [joinsOf_reads, ih]

theorem answerOne_reads [Fresh (M)] (hfr : ReadsHeld (Fresh.fresh : M ByteArray))
    (K : Keys) (eps : List (B × B × Id)) (r c frm : B) :
    ReadsHeld (answerOne K eps r c frm : M (List Op)) := by
  unfold answerOne; readsHeld [count_reads, view_reads, arrivedFrom_reads, hfr]

theorem answerAll_reads [Fresh (M)] (hfr : ReadsHeld (Fresh.fresh : M ByteArray))
    (K : Keys) (eps : List (B × B × Id)) : ∀ l, ReadsHeld (answerAll K eps l : M (List Op)) := by
  intro l
  induction l with
  | nil => exact ReadsHeld.pure' _
  | cons p t ih =>
    obtain ⟨x, f⟩ := p
    cases f <;> simp only [answerAll] <;> readsHeld [answerOne_reads hfr, ih]

theorem establishConns_reads (r e epOp : Id) : ∀ l, ReadsHeld (establishConns r e epOp l : M (List Op))
  | [] => ReadsHeld.pure' _
  | (_, _) :: t => by rw [establishConns]; readsHeld [count_reads, establishConns_reads r e epOp t]

theorem establishReqs_reads (epOp : Id) : ∀ l, ReadsHeld (establishReqs epOp l : M (List Op))
  | [] => ReadsHeld.pure' _
  | (_, _) :: t => by
    rw [establishReqs]; readsHeld [rows_reads, establishConns_reads, establishReqs_reads epOp t]

theorem establishAll_reads : ∀ l, ReadsHeld (establishAll l : M (List Op))
  | [] => ReadsHeld.pure' _
  | (_, _, _) :: t => by rw [establishAll]; readsHeld [rows_reads, establishReqs_reads, establishAll_reads t]

theorem react_reads [Fresh (M)] (hfr : ReadsHeld (Fresh.fresh : M ByteArray)) (fam : Family F) (K : Keys) :
    ReadsHeld (react fam K : M (List Op)) := by
  unfold react
  readsHeld [endpoints_reads, rows_reads, openAll_reads, deliverAll_reads, answerAll_reads hfr,
    establishAll_reads]

/-! ## dial -/

theorem requestOf_reads (K : Keys) (sk inviter : B) (req : Id) :
    ∀ l, ReadsHeld (requestOf K sk inviter req l : M (Option Id)) := by
  intro l
  induction l with
  | nil => exact ReadsHeld.pure' _
  | cons p t ih =>
    obtain ⟨x, f⟩ := p
    cases f <;> simp only [requestOf] <;> readsHeld [helloOf_reads, ih]

theorem dialOne_reads [Fresh (M)] (hfr : ReadsHeld (Fresh.fresh : M ByteArray)) (K : Keys) (listen pk sk : B)
    (f : Community.Fact) : ReadsHeld (dialOne K listen pk sk f : M (List Op)) := by
  cases f <;> simp only [dialOne] <;>
    readsHeld [view_reads, list_reads, requestOf_reads, rows_reads, connectedTo_reads, count_reads, hfr]

theorem dialAll_reads [Fresh (M)] (hfr : ReadsHeld (Fresh.fresh : M ByteArray)) (K : Keys) (listen pk sk : B) :
    ∀ l, ReadsHeld (dialAll K listen pk sk l : M (List Op))
  | [] => ReadsHeld.pure' _
  | (_, _) :: t => by rw [dialAll]; readsHeld [dialOne_reads hfr, dialAll_reads hfr K listen pk sk t]

theorem dial_reads [Fresh (M)] (hfr : ReadsHeld (Fresh.fresh : M ByteArray)) (K : Keys) (listen : B) (t : Nat) :
    ReadsHeld (dial K listen t : M (List Op)) := by
  unfold dial; readsHeld [endpoints_reads, list_reads, dialAll_reads hfr]

/-! ## Sessions -/

theorem closing_reads (cid : Id) : ReadsHeld (closing cid : M (List Id)) := by
  unfold closing; readsHeld []

theorem rooms_reads (cid : Id) : ReadsHeld (rooms cid : M (List Room)) := by
  unfold rooms; exact view_reads _

theorem sessionOf_reads (f : Fact) : ReadsHeld (sessionOf f : M _) := by
  cases f <;> simp only [sessionOf] <;> readsHeld [arrival_reads]

theorem sessionsOf_reads : ∀ l, ReadsHeld (sessionsOf l : M _)
  | [] => ReadsHeld.pure' _
  | (_, _) :: t => by rw [sessionsOf]; readsHeld [sessionOf_reads, sessionsOf_reads t]

theorem allSessions_reads : ReadsHeld (allSessions : M _) := by
  unfold allSessions; readsHeld [rows_reads, sessionsOf_reads]

theorem carrying_reads : ∀ l, ReadsHeld (carrying l : M _)
  | [] => ReadsHeld.pure' _
  | _ :: t => by rw [carrying]; readsHeld [view_reads, carrying_reads t]

theorem openSessions_reads : ReadsHeld (openSessions : M _) := by
  unfold openSessions; readsHeld [allSessions_reads, carrying_reads]

theorem sessions_reads : ReadsHeld (sessions : M _) := by
  unfold sessions; readsHeld [openSessions_reads]

theorem routedSessions_reads : ReadsHeld (routedSessions : M _) := by
  unfold routedSessions; readsHeld [allSessions_reads]

/-- `retired`, as this base has it (another branch reads the
established facts themselves: redo this lemma there). -/
theorem retired_reads : ReadsHeld (retired : M (List Id)) := by
  unfold retired; readsHeld [allSessions_reads, sessions_reads, rows_reads]

theorem sealFor_reads [Fresh (M)] (hfr : ReadsHeld (Fresh.fresh : M ByteArray)) (K : Keys) (cid : Id) (p : B) :
    ReadsHeld (sealFor K cid p : M (Option B)) := by
  unfold sealFor; readsHeld [keys_reads, hfr]

theorem outbox_reads : ReadsHeld (outbox : M (List (Id × B × B))) := by
  unfold outbox; readsHeld [rows_reads]

theorem resendConns_reads (addr : B) : ∀ l, ReadsHeld (resendConns addr l : M (List Op))
  | [] => ReadsHeld.pure' _
  | (_, _) :: t => by rw [resendConns]; readsHeld [resendConns_reads addr t]

theorem onArrival_reads (via : Option Id) (addr : B) (o : Op) (at_ : Nat) :
    ReadsHeld (onArrival via addr o at_ : M (List Op)) := by
  unfold onArrival; readsHeld [count_reads, view_reads, rows_reads, resendConns_reads]

theorem openFrame_tape_reads (K : Keys) (b : B) : ReadsHeld (openFrame K b : M _) := by
  unfold openFrame; readsHeld [keys_reads]

theorem retryKey_reads (cid : Id) : ReadsHeld (retryKey cid : M (Option Id)) := by
  unfold retryKey; readsHeld [rows_reads]

/-- **The Connection family's hooks only read the store.** Run on held
data, each leaves the store as it is: what the family would store it
returns as ops for the node to write, and what it would forget it
returns as ids for the node to purge. -/
theorem hooks_reads [Fresh (M)] (hfr : ReadsHeld (Fresh.fresh : M ByteArray))
    (fam : Family F) (K : Keys) (listen : B) :
    let k := (hooks fam K listen : Hooks F (M))
    (∀ cid, ReadsHeld (k.rooms cid)) ∧ (∀ via a o t, ReadsHeld (k.recv via a o t)) ∧ ReadsHeld k.outbox ∧
    (∀ cid, ReadsHeld (k.closing cid)) ∧ ReadsHeld k.retired ∧ ReadsHeld k.react ∧ (∀ t, ReadsHeld (k.dial t)) ∧
    ReadsHeld k.established ∧ (∀ cid b, ReadsHeld (k.sealFor cid b)) ∧ (∀ b, ReadsHeld (k.openFrame b)) ∧ (∀ cid, ReadsHeld (k.retryKey cid)) :=
  ⟨rooms_reads, onArrival_reads, outbox_reads, closing_reads, retired_reads, react_reads hfr fam K,
    dial_reads hfr K listen, routedSessions_reads, sealFor_reads hfr K, openFrame_tape_reads K, retryKey_reads⟩

end Connection.Execution
