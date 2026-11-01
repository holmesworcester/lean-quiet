/-
The Connection family's hooks only read the store, on held data: each
leaves the `Held` store as it is (`Reads`). Everything they would have
stored they return as ops, which the node writes through the engine
(`Node.store`, `Node.put`), and every id they want purged they return
too (`closing`, `retired`, `outbox`), which the node purges through
`Turn.purge`. `hooks_reads` collects them.

The fresh bytes `react`, `dial` and `sealFor` draw are assumed to leave
the store as it is (`hfr`), as the OS's random bytes do on SQLite.

`view_held`: a view run on held data is its evaluation over the tables,
and reads only; so `rooms` gives `roomsV` (`rooms_held`).
-/
import ops.connection.Laws
import engine.wire.WorldLaws

namespace Connection
open Engine Engine.Sync Codec

/-- **A view run on held data is its evaluation**, and leaves the store
as it is. -/
theorem view_held {α} (v : View F α) (h : Held F) :
    (v.run : HeldM F α).run h = (v.eval h.db, h) := by
  induction v with
  | pure a => rfl
  | list q k ih => exact ih (Engine.eval h.db q)

theorem view_reads {α} (v : View F α) : Reads (v.run : HeldM F α) := fun h => by
  rw [view_held]

/-- **The rooms hook is `roomsV`, read afresh from the store**, and it
reads only. -/
theorem rooms_held (cid : Id) (h : Held F) :
    (rooms cid : HeldM F (List Room)).run h = ((roomsV cid).eval h.db, h) :=
  view_held (roomsV cid) h

theorem list_reads (q : ListQ) : Reads (Lists.list q : HeldM F (Answer F)) := fun _ => rfl

theorem rows_reads (r : Rel Fact) (args : List B) : Reads (rows r args : HeldM F _) := by
  unfold rows; keeps [list_reads]

theorem count_reads (r : Rel Fact) (args : List B) : Reads (count r args : HeldM F _) := by
  unfold count; keeps [list_reads]

theorem endpoints_reads : Reads (endpoints : HeldM F _) := by
  unfold endpoints; keeps [list_reads]

theorem arrivedFrom_reads (x : Id) : Reads (arrivedFrom x : HeldM F _) := by
  unfold arrivedFrom; keeps [rows_reads]

theorem arrival_reads (x : Id) : Reads (arrival x : HeldM F _) := by
  unfold arrival; keeps [rows_reads]

/-- `sessionKeys_reads` (ops/connection/Laws.lean), as `Reads`. -/
private theorem keys_reads (cid : Id) : Reads (sessionKeys cid : HeldM F _) := sessionKeys_reads cid

theorem connectedTo_reads (peer : B) : Reads (connectedTo peer : HeldM F _) := by
  unfold connectedTo; keeps [rows_reads]

theorem helloOf_reads (K : Keys) (sk r to m1 : B) : Reads (helloOf K sk r to m1 : HeldM F _) := by
  unfold helloOf; keeps [rows_reads]

/-! ## react -/

theorem openEach_reads (epOp : Id) : ∀ l, Reads (openEach epOp l : HeldM F (List Op))
  | [] => Reads.pure' _
  | (_, _) :: t => by rw [openEach]; keeps [count_reads, openEach_reads epOp t]

theorem openAll_reads : ∀ l, Reads (openAll l : HeldM F (List Op))
  | [] => Reads.pure' _
  | (_, _, _) :: t => by rw [openAll]; keeps [rows_reads, openEach_reads, openAll_reads t]

theorem joinsOf_reads (fam : Family F) (c : B) : ∀ l, Reads (joinsOf fam c l : HeldM F (List Op))
  | [] => Reads.pure' _
  | _ :: t => by rw [joinsOf]; keeps [joinsOf_reads fam c t]

theorem deliverAll_reads (fam : Family F) : ∀ l, Reads (deliverAll fam l : HeldM F (List Op)) := by
  intro l
  induction l with
  | nil => exact Reads.pure' _
  | cons p t ih =>
    obtain ⟨x, f⟩ := p
    cases f <;> simp only [deliverAll] <;> keeps [joinsOf_reads, ih]

theorem answerOne_reads [Fresh (HeldM F)] (hfr : Reads (Fresh.fresh : HeldM F ByteArray))
    (K : Keys) (eps : List (B × B × Id)) (r c frm : B) :
    Reads (answerOne K eps r c frm : HeldM F (List Op)) := by
  unfold answerOne; keeps [count_reads, view_reads, arrivedFrom_reads, hfr]

theorem answerAll_reads [Fresh (HeldM F)] (hfr : Reads (Fresh.fresh : HeldM F ByteArray))
    (K : Keys) (eps : List (B × B × Id)) : ∀ l, Reads (answerAll K eps l : HeldM F (List Op)) := by
  intro l
  induction l with
  | nil => exact Reads.pure' _
  | cons p t ih =>
    obtain ⟨x, f⟩ := p
    cases f <;> simp only [answerAll] <;> keeps [answerOne_reads hfr, ih]

theorem establishConns_reads (r e epOp : Id) : ∀ l, Reads (establishConns r e epOp l : HeldM F (List Op))
  | [] => Reads.pure' _
  | (_, _) :: t => by rw [establishConns]; keeps [count_reads, establishConns_reads r e epOp t]

theorem establishReqs_reads (epOp : Id) : ∀ l, Reads (establishReqs epOp l : HeldM F (List Op))
  | [] => Reads.pure' _
  | (_, _) :: t => by
    rw [establishReqs]; keeps [rows_reads, establishConns_reads, establishReqs_reads epOp t]

theorem establishAll_reads : ∀ l, Reads (establishAll l : HeldM F (List Op))
  | [] => Reads.pure' _
  | (_, _, _) :: t => by rw [establishAll]; keeps [rows_reads, establishReqs_reads, establishAll_reads t]

theorem react_reads [Fresh (HeldM F)] (hfr : Reads (Fresh.fresh : HeldM F ByteArray)) (fam : Family F) (K : Keys) :
    Reads (react fam K : HeldM F (List Op)) := by
  unfold react
  keeps [endpoints_reads, rows_reads, openAll_reads, deliverAll_reads, answerAll_reads hfr,
    establishAll_reads]

/-! ## dial -/

theorem requestOf_reads (K : Keys) (sk inviter : B) (req : Id) :
    ∀ l, Reads (requestOf K sk inviter req l : HeldM F (Option Id)) := by
  intro l
  induction l with
  | nil => exact Reads.pure' _
  | cons p t ih =>
    obtain ⟨x, f⟩ := p
    cases f <;> simp only [requestOf] <;> keeps [helloOf_reads, ih]

theorem dialOne_reads [Fresh (HeldM F)] (hfr : Reads (Fresh.fresh : HeldM F ByteArray)) (K : Keys) (listen pk sk : B)
    (f : Community.Fact) : Reads (dialOne K listen pk sk f : HeldM F (List Op)) := by
  cases f <;> simp only [dialOne] <;>
    keeps [view_reads, list_reads, requestOf_reads, rows_reads, connectedTo_reads, count_reads, hfr]

theorem dialAll_reads [Fresh (HeldM F)] (hfr : Reads (Fresh.fresh : HeldM F ByteArray)) (K : Keys) (listen pk sk : B) :
    ∀ l, Reads (dialAll K listen pk sk l : HeldM F (List Op))
  | [] => Reads.pure' _
  | (_, _) :: t => by rw [dialAll]; keeps [dialOne_reads hfr, dialAll_reads hfr K listen pk sk t]

theorem dial_reads [Fresh (HeldM F)] (hfr : Reads (Fresh.fresh : HeldM F ByteArray)) (K : Keys) (listen : B) (t : Nat) :
    Reads (dial K listen t : HeldM F (List Op)) := by
  unfold dial; keeps [endpoints_reads, list_reads, dialAll_reads hfr]

/-! ## Sessions -/

theorem closing_reads (cid : Id) : Reads (closing cid : HeldM F (List Id)) := by
  unfold closing; keeps []

theorem rooms_reads (cid : Id) : Reads (rooms cid : HeldM F (List Room)) := by
  unfold rooms; exact view_reads _

theorem sessionOf_reads (f : Fact) : Reads (sessionOf f : HeldM F _) := by
  cases f <;> simp only [sessionOf] <;> keeps [arrival_reads]

theorem sessionsOf_reads : ∀ l, Reads (sessionsOf l : HeldM F _)
  | [] => Reads.pure' _
  | (_, _) :: t => by rw [sessionsOf]; keeps [sessionOf_reads, sessionsOf_reads t]

theorem allSessions_reads : Reads (allSessions : HeldM F _) := by
  unfold allSessions; keeps [rows_reads, sessionsOf_reads]

theorem carrying_reads : ∀ l, Reads (carrying l : HeldM F _)
  | [] => Reads.pure' _
  | _ :: t => by rw [carrying]; keeps [view_reads, carrying_reads t]

theorem openSessions_reads : Reads (openSessions : HeldM F _) := by
  unfold openSessions; keeps [allSessions_reads, carrying_reads]

theorem sessions_reads : Reads (sessions : HeldM F _) := by
  unfold sessions; keeps [openSessions_reads]

theorem routedSessions_reads : Reads (routedSessions : HeldM F _) := by
  unfold routedSessions; keeps [allSessions_reads]

/-- `retired`, as this base has it (another branch reads the
established facts themselves: redo this lemma there). -/
theorem retired_reads : Reads (retired : HeldM F (List Id)) := by
  unfold retired; keeps [allSessions_reads, openSessions_reads, rows_reads]

theorem sealFor_reads [Fresh (HeldM F)] (hfr : Reads (Fresh.fresh : HeldM F ByteArray)) (K : Keys) (cid : Id) (p : B) :
    Reads (sealFor K cid p : HeldM F (Option B)) := by
  unfold sealFor; keeps [keys_reads, hfr]

theorem outbox_reads : Reads (outbox : HeldM F (List (Id × B × B))) := by
  unfold outbox; keeps [rows_reads]

theorem resendConns_reads (addr : B) : ∀ l, Reads (resendConns addr l : HeldM F (List Op))
  | [] => Reads.pure' _
  | (_, _) :: t => by rw [resendConns]; keeps [resendConns_reads addr t]

theorem onArrival_reads (via : Option Id) (addr : B) (o : Op) (at_ : Nat) :
    Reads (onArrival via addr o at_ : HeldM F (List Op)) := by
  unfold onArrival; keeps [count_reads, view_reads, rows_reads, resendConns_reads]

/-- **The Connection family's hooks only read the store.** Run on held
data, each leaves the store as it is: what the family would store it
returns as ops for the node to write, and what it would forget it
returns as ids for the node to purge. -/
theorem hooks_reads [Fresh (HeldM F)] (hfr : Reads (Fresh.fresh : HeldM F ByteArray))
    (fam : Family F) (K : Keys) (listen : B) :
    let k := (hooks fam K listen : Hooks F (HeldM F))
    (∀ cid, Reads (k.rooms cid)) ∧ (∀ via a o t, Reads (k.recv via a o t)) ∧ Reads k.outbox ∧
    (∀ cid, Reads (k.closing cid)) ∧ Reads k.retired ∧ Reads k.react ∧ (∀ t, Reads (k.dial t)) ∧
    Reads k.established ∧ (∀ cid b, Reads (k.sealFor cid b)) ∧ (∀ b, Reads (k.openFrame b)) :=
  ⟨rooms_reads, onArrival_reads, outbox_reads, closing_reads, retired_reads, react_reads hfr fam K,
    dial_reads hfr K listen, routedSessions_reads, sealFor_reads hfr K, openFrame_reads K⟩

end Connection
