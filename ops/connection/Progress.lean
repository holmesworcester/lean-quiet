/-
Positive progress through the connection code. Safety laws say that an
answer is authorized if one exists; these laws establish that a ready request
actually gets an answer and that an honest Noise exchange is accepted by the
real opened/established validators. Store/transport scheduling is separate.
-/
import ops.connection.RemovalLaws

namespace Connection.Progress
open Engine Engine.Sync Codec

/-- The actual two-message Noise computation, before the op validators run.
These are primitive cryptographic results, not assumed session/admission facts. -/
structure Exchange (K : Keys) where
  initiator : B
  responder : B
  ephemeralI : B
  ephemeralR : B
  community : Id
  address : B
  introduction : List B
  state : Noise.Sym B
  message1 : B
  sessionR : Noise.Session B
  message2 : B
  sessionI : Noise.Session B

namespace Exchange
variable {K : Keys} (x : Exchange K)

def payload : B := encode (x.community, x.address, x.introduction)
def request : Op := mkOp [] (.request (K.suite.pub x.responder) (K.suite.pub x.initiator) x.message1)
def connection : Op := mkOp [x.request.id] (.connection x.message2)

structure Correct : Prop where
  distinct : K.suite.pub x.responder ≠ K.suite.pub x.initiator
  write1 : Noise.write1 K.suite prologue x.initiator x.ephemeralI
    (K.suite.pub x.responder) x.payload = some (x.state, x.message1)
  read1 : Noise.read1 K.suite prologue x.responder (K.suite.pub x.initiator)
    x.message1 = some (x.state, K.suite.pub x.ephemeralI, x.payload)
  sent1 : Noise.sent1 K.suite prologue x.initiator x.ephemeralI
    (K.suite.pub x.responder) x.message1 = some (x.state, x.payload)
  write2 : Noise.write2 K.suite x.state x.ephemeralR (K.suite.pub x.initiator)
    (K.suite.pub x.ephemeralI) .empty = some (x.sessionR, x.message2)
  read2 : Noise.read2 K.suite x.state x.initiator x.ephemeralI
    x.message2 = some (x.sessionI, .empty)

theorem request_constructed (h : x.Correct) :
    Request.op K x.initiator (K.suite.pub x.responder) x.ephemeralI x.payload = some x.request := by
  simp [Request.op, h.write1, request]

theorem answer_constructed (h : x.Correct) :
    Reply.op K x.request.id x.responder (K.suite.pub x.initiator) x.message1 x.ephemeralR =
      some x.connection := by
  simp [Reply.op, h.read1, h.write2, connection]

/-- Wire-format premises are separate from the cryptographic equations:
Good alone does not promise key or ciphertext lengths. -/
theorem request_accepts (h : x.Correct)
    (hr : (K.suite.pub x.responder).size = 32)
    (hi : (K.suite.pub x.initiator).size = 32) (hm : 48 ≤ x.message1.size) :
    Request.check (K.suite.pub x.responder) (K.suite.pub x.initiator) x.message1 [] =
      some (.request (K.suite.pub x.responder) (K.suite.pub x.initiator) x.message1) := by
  simp [Request.check, hr, hi, h.distinct, hm]

theorem reply_accepts (hm : 48 ≤ x.message2.size) :
    Reply.check x.connection x.message2
      [.inr (.request (K.suite.pub x.responder) (K.suite.pub x.initiator) x.message1)] =
      some (.connection x.request.id x.message2) := by
  simp [Reply.check, hm, connection, mkOp, Op.make]

/-- Opening the actual request recovers its community, address and payload. -/
theorem opened_accepts (h : x.Correct) (endpoint : Id) :
    Opened.check K (Opened.op x.request.id endpoint)
      [.inr (.request (K.suite.pub x.responder) (K.suite.pub x.initiator) x.message1),
       .inl (.endpoint (K.suite.pub x.responder) x.responder)] =
      some (.opened x.request.id x.community (K.suite.pub x.initiator) x.address x.introduction) := by
  simp [Opened.check, Opened.op, h.read1, payload, decode_encode, mkOp, Op.make]

/-- The responder's local established op validates; its existence is not a
premise. This is the op answerOne writes alongside the actual reply. -/
theorem responder_accepts (h : x.Correct) (eph endpoint : Id) :
    Established.check K (Established.op x.connection.id x.request.id eph endpoint)
      [.inr (.connection x.request.id x.message2),
       .inr (.request (K.suite.pub x.responder) (K.suite.pub x.initiator) x.message1),
       .inr (.eph x.connection.id (K.suite.pub x.ephemeralR) x.ephemeralR),
       .inl (.endpoint (K.suite.pub x.responder) x.responder)] =
      some (.established x.connection.id x.community (K.suite.pub x.initiator)
        x.sessionR.h x.sessionR.send.k x.sessionR.recv.k false) := by
  simp [Established.check, Established.op, h.read1, h.write2, payload, decode_encode, mkOp, Op.make]

/-- Receiving the honest answer produces a valid local established op at
the initiator as well. The two private keys must name different nodes. -/
theorem initiator_accepts (h : x.Correct) (eph endpoint : Id) :
    Established.check K (Established.op x.connection.id x.request.id eph endpoint)
      [.inr (.connection x.request.id x.message2),
       .inr (.request (K.suite.pub x.responder) (K.suite.pub x.initiator) x.message1),
       .inr (.eph x.request.id (K.suite.pub x.ephemeralI) x.ephemeralI),
       .inl (.endpoint (K.suite.pub x.initiator) x.initiator)] =
      some (.established x.connection.id x.community (K.suite.pub x.responder)
        x.sessionI.h x.sessionI.send.k x.sessionI.recv.k true) := by
  simp [Established.check, Established.op, h.distinct.symm, h.sent1, h.read2,
    payload, decode_encode, mkOp, Op.make]

end Exchange

/-- Supported payloads and the four primitive DH results suffice to construct
an exchange accepted by both actual session validators. This does not assume
their success or a finished bootstrap. -/
theorem honest_exchange (K : Keys) (g : K.suite.Good)
    (si sr ei er c addr : B) (intro : List B)
    (hne : K.suite.pub sr ≠ K.suite.pub si)
    (hp : K.suite.ValidPayload (encode (c, addr, intro)))
    (he : K.suite.ValidPayload .empty)
    {es ss ee se : B}
    (hes : K.suite.dh ei (K.suite.pub sr) = some es)
    (hss : K.suite.dh si (K.suite.pub sr) = some ss)
    (hee : K.suite.dh er (K.suite.pub ei) = some ee)
    (hse : K.suite.dh er (K.suite.pub si) = some se) :
    ∃ x : Exchange K, x.initiator = si ∧ x.responder = sr ∧
      x.ephemeralI = ei ∧ x.ephemeralR = er ∧ x.community = c ∧
      x.address = addr ∧ x.introduction = intro ∧ x.Correct ∧
      x.sessionI.h = x.sessionR.h ∧ x.sessionI.send = x.sessionR.recv ∧
      x.sessionI.recv = x.sessionR.send := by
  obtain ⟨st, m1, h1, hr1, sessR, m2, h2, sessI, hr2, hh, hs, hr⟩ :=
    Noise.handshake_agrees g prologue si sr ei er (encode (c, addr, intro)) .empty hp he hes hss hee hse
  refine ⟨⟨si, sr, ei, er, c, addr, intro, st, m1, sessR, m2, sessI⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, hh, hs, hr⟩
  exact ⟨hne, h1, hr1, Noise.sent1_write1 g hp h1, h2, hr2⟩

section
variable [Fresh (Model F)]

theorem answerAll_contains (hfr : FreshPure) (K : Keys) (eps : List (B × B × Id))
    (s : DB F) (o : Op) (x r c frm addr : B) (hs : List B)
    (ho : o ∈ ((answerOne K eps r c frm : Model F (List Op)).run s).1) :
    ∀ rs, (x, Fact.opened r c frm addr hs) ∈ rs →
      o ∈ ((answerAll K eps rs : Model F (List Op)).run s).1 := by
  intro rs
  induction rs with
  | nil => simp
  | cons p rs ih =>
    obtain ⟨y, f⟩ := p
    intro hm
    rcases List.mem_cons.1 hm with he | hm
    · cases he
      simp only [answerAll, Model.run_bind, Model.run_pure, List.mem_append]
      exact Or.inl ho
    · have ht := ih hm
      cases f with
      | opened r' c' frm' addr' hs' =>
        simp only [answerAll, Model.run_bind, Model.run_pure, List.mem_append]
        rw [answerOne_state hfr]
        exact Or.inr ht
      | _ => exact ht

/-- A ready answer is included in the complete production reaction, even
when unrelated opened requests precede or follow it. -/
theorem react_contains_answer (hfr : FreshPure) (fam : Family F) (K : Keys)
    (s : DB F) (o : Op) (x r c frm addr : B) (hs : List B)
    (hm : (x, Fact.opened r c frm addr hs) ∈
      ((rows opened.all [] : Model F (List (Id × Fact))).run s).1)
    (ho : o ∈ ((answerOne K ((endpoints : Model F (List (B × B × Id))).run s).1
      r c frm : Model F (List Op)).run s).1) :
    o ∈ ((react fam K : Model F (List Op)).run s).1 := by
  simp only [react, Model.run_bind, Model.run_pure, List.mem_append]
  have he : ((endpoints : Model F (List (B × B × Id))).run s).2 = s := rfl
  have hr : ((rows opened.all [] : Model F (List (Id × Fact))).run s).2 = s := rfl
  rw [he, hr, openAll_state, deliverAll_state]
  exact Or.inl (Or.inr (answerAll_contains hfr K _ s o x r c frm addr hs ho _ hm))

/-- Every concrete readiness check is a read of the actual store. Under
these conditions answerOne returns the reply, both local records and courier,
so the existing safety law is accompanied by a positive progress law. -/
theorem answer_ready (K : Keys) (s : DB F) (eps : List (B × B × Id))
    (r c frm to frm' m1 sk epOp addr : B) (ro co : Op)
    (hcount : ((count connection.byRequest [r] : Model F Nat).run s).1 = 0)
    (hro : s.ops r = some ro)
    (hb : (decode ro.body : Option Body) = some (.request to frm' m1))
    (hep : eps.find? (fun p => decide (p.1 = to)) = some (to, sk, epOp))
    (ht : ((trusts c to frm).liftL : View F Bool).eval s = true)
    (ha : ((arrivedFrom r : Model F (Option B)).run s).1 = some addr)
    (hc : Reply.op K r sk frm m1 ((Fresh.fresh : Model F B).run s).1 = some co) :
    ((answerOne K eps r c frm : Model F (List Op)).run s).1 =
      [co, Eph.op ((Fresh.fresh : Model F B).run s).1 co.id,
       Established.op co.id r (Eph.op ((Fresh.fresh : Model F B).run s).1 co.id).id epOp,
       Send.op addr co] := by
  simp only [answerOne, Model.run_bind]
  rw [ite_eq_right (by simpa using hcount), Model.run_bind]
  have h0 : ((count connection.byRequest [r] : Model F Nat).run s).2 = s := rfl
  rw [h0, run_getOp, hro]
  simp only [hb, hep, Model.run_bind, run_view, ht, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, run_arrivedFrom, ha, hc]
  rfl

end
end Connection.Progress
