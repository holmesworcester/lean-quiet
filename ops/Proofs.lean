import engine.core.Project
import engine.wire.NodeLaws
import ops.Commands
import ops.community.member.invite.request.Commands
import ops.community.member.join.joining.Commands
import ops.connection.Commands
import ops.connection.Family
import ops.connection.Proofs
import ops.connection.connection.Commands
import ops.connection.connection.Proofs
import ops.connection.eph.Commands
import ops.connection.established.Commands
import ops.connection.established.Proofs
import ops.connection.opened.Proofs
import ops.connection.recv.Commands
import ops.connection.request.Commands
import ops.connection.send.Commands
import ops.connection.send.Proofs
import ops.sync.NoticeLaws

/-!
`app`: laws about the op types in this folder and below.
-/
namespace Connection
open Engine Codec

/-- **Both ends of a connection hold one session.** When a responder's
and an initiator's `established` validators both succeed over the same
request and connection, each with its own node key's secret as its
static (`to` and `frm` are those keys), they hold the same handshake
hash and community, each names the other's node key, and each one's send
key is the other's receive key. -/
theorem established_agrees (K : Keys) (G : K.suite.Good)
    {oR oI : Op} {r m2 to frm m1 ofR ofI pkR pkI f e skR skI : B}
    {cidR cR pR hR sR kR cidI cI pI hI sI kI : B}
    (hto : to = K.suite.pub skR) (hfrm : frm = K.suite.pub skI) (hne : to ≠ frm)
    (hRc : check K oR .established [.inr (.connection r m2), .inr (.request to frm m1), .inr (.eph ofR pkR f),
      .inl (.endpoint to skR)] = some (.established cidR cR pR hR sR kR false))
    (hIc : check K oI .established [.inr (.connection r m2), .inr (.request to frm m1), .inr (.eph ofI pkI e),
      .inl (.endpoint frm skI)] = some (.established cidI cI pI hI sI kI true)) :
    hR = hI ∧ cR = cI ∧ sR = kI ∧ kR = sI ∧ pR = frm ∧ pI = to := by
  simp only [check, Option.map_eq_some_iff, Fact.established, Fact.ofEstablished.injEq, exists_eq_right] at hRc hIc
  unfold Established.check at hRc hIc
  simp only [ite_true, hne.symm, ite_false, Ne] at hRc hIc
  split at hRc
  · cases hRc
  split at hIc
  · cases hIc
  subst hto hfrm
  cases h1 : Noise.read1 K.suite prologue skR (K.suite.pub skI) m1 with
  | none => simp [h1] at hRc
  | some x1 =>
    obtain ⟨st, re, p1⟩ := x1
    cases h2 : Noise.sent1 K.suite prologue skI e (K.suite.pub skR) m1 with
    | none => simp [h2] at hIc
    | some x2 =>
      obtain ⟨st', p1'⟩ := x2
      obtain ⟨rfl, rfl, rfl⟩ := Noise.sent1_read1 G h2 h1
      simp only [h1, h2, Option.bind_eq_bind, Option.bind_some] at hRc hIc
      cases h3 : (decode p1' : Option (B × B × List B)) with
      | none => simp [h3] at hRc
      | some d =>
        simp only [h3, Option.bind_some] at hRc hIc
        cases h4 : Noise.write2 K.suite st' f (K.suite.pub skI) (K.suite.pub e) ByteArray.empty with
        | none => simp [h4] at hRc
        | some w =>
          obtain ⟨sr, m2'⟩ := w
          simp only [h4, Option.bind_some] at hRc
          by_cases hm : m2' = m2
          · subst hm
            simp only [not_true_eq_false, ite_false] at hRc
            cases h5 : Noise.read2 K.suite st' skI e m2' with
            | none => simp [h5] at hIc
            | some q =>
              obtain ⟨si, pp⟩ := q
              simp only [h5, Option.bind_some, Option.some.injEq, Established.Fact.mk.injEq] at hRc hIc
              obtain ⟨hh, hs, hr⟩ := Noise.read2_write2' G h4 h5
              obtain ⟨_, rfl, rfl, rfl, rfl, rfl, -⟩ := hRc
              obtain ⟨_, rfl, rfl, rfl, rfl, rfl, -⟩ := hIc
              exact ⟨hh.symm, rfl, by rw [hr], by rw [hs], rfl, rfl⟩
          · simp [hm] at hRc
end Connection
namespace Connection
open Engine Engine.Sync

/-- **For a live member, the trust rule is `allowPeer`.** The link
clause (trust the inviter a pending join names) holds only before this
device is admitted. -/
theorem trusts_live (s : DB F) {c me peer : B}
    (h : ((Community.allowPeer c me).liftL : View F Bool).eval s = true) :
    ((trusts c me peer).liftL : View F Bool).eval s =
      ((Community.allowPeer c peer).liftL : View F Bool).eval s := by
  unfold trusts
  rw [eval_liftL_bind]
  cases hp : ((Community.allowPeer c peer).liftL : View F Bool).eval s
  · simp only [Bool.false_eq_true, ite_false]
    rw [eval_liftL_bind]
    split
    · rfl
    · rw [eval_liftL_bind, h, eval_liftL_bind]
      simp [eval_liftL_pure]
  · rfl

theorem eval_roomFor (s : DB F) (given : List Id) (c peer : B) :
    (roomFor given c peer).eval s =
      match (meV c).eval s with
      | some me =>
        if ((trusts c me peer).liftL : View F Bool).eval s then [Room.sync c]
        else ((((Community.removalsAt c peer).liftL : View F (List Id)).eval s).filter
          fun x => !has given x).map (Room.notice c)
      | none => [] := by
  unfold roomFor
  rw [View.eval_bind]
  cases (meV c).eval s with
  | none => rfl
  | some me =>
    simp only [View.eval_bind]
    cases ((trusts c me peer).liftL : View F Bool).eval s <;> simp [View.eval_bind]

theorem eval_roomsOf (s : DB F) (given : List Id) (ps : List (B × B)) :
    (roomsOf given ps).eval s = ps.flatMap fun (c, peer) => (roomFor given c peer).eval s := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨c, peer⟩ := p
    simp only [roomsOf, View.eval_bind, View.eval_pure, List.flatMap_cons, ih]

/-- A room cid carries, with the (community, peer) pair it is for. -/
theorem mem_roomsV (s : DB F) {cid : Id} {rm : Room} (h : rm ∈ (roomsV cid).eval s) :
    ∃ c peer, peer ∈ peersOf (Engine.eval s (established.byConn.query [cid])) ∧ c ∈ heldV.eval s ∧
      rm ∈ (roomFor ((givenOn cid).eval s) c peer).eval s := by
  simp only [roomsV, View.eval_bind, View.eval_read, eval_roomsOf, List.mem_flatMap] at h
  obtain ⟨⟨c, peer⟩, hp, hm⟩ := h
  obtain ⟨peer', hpeer, hp⟩ := hp
  rw [List.mem_map] at hp
  obtain ⟨c', hheld, he⟩ := hp
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨c', peer', hpeer, hheld, hm⟩
end Connection
namespace Connection
open Engine Engine.Sync Codec

/-- **A removed member's connection carries only notices
(`rooms_removed`).** If this node is a live member of c and the trust
rule refuses every peer cid names in c, cid carries no synced room c,
and each notice of c it carries is of a removal owed to the peer. -/
theorem rooms_removed (s : DB F) {cid c : B} (hl : LiveIn s c) (hr : Refused s cid c) :
    ∀ rm ∈ (roomsV cid).eval s, match rm with
      | .sync r => r ≠ c
      | .notice r x => r = c → Owed s cid c x := by
  intro rm hm
  obtain ⟨c', peer, hpeer, _, hm⟩ := mem_roomsV s hm
  rw [eval_roomFor] at hm
  cases hme : (meV c').eval s with
  | none => simp only [hme, List.not_mem_nil] at hm
  | some me =>
    cases ht : ((trusts c' me peer).liftL : View F Bool).eval s
    · simp only [hme, ht, Bool.false_eq_true, ite_false, List.mem_map, List.mem_filter] at hm
      obtain ⟨x, ⟨hx, _⟩, rfl⟩ := hm
      intro hc; subst hc
      exact ⟨peer, hpeer, hx⟩
    · simp only [hme, ht, ite_true, List.mem_singleton] at hm
      subst hm
      intro hc; subst hc
      rw [trusts_live s (hl me hme), hr peer hpeer] at ht
      cases ht

/-- **The session keeps its other communities (`rooms_complete`).** A
connection carries, synced, every community c this node holds and is
in whose peer the trust rule takes. -/
theorem rooms_complete (s : DB F) {cid c me peer : B} (hm : (meV c).eval s = some me)
    (hp : peer ∈ peersOf (Engine.eval s (established.byConn.query [cid]))) (hh : c ∈ heldV.eval s)
    (ht : ((trusts c me peer).liftL : View F Bool).eval s = true) :
    Room.sync c ∈ (roomsV cid).eval s := by
  simp only [roomsV, View.eval_bind, View.eval_read, eval_roomsOf, List.mem_flatMap]
  refine ⟨(c, peer), ?_, ?_⟩
  · exact ⟨peer, hp, List.mem_map.2 ⟨c, hh, rfl⟩⟩
  · rw [eval_roomFor]; simp [hm, ht]

/-- **Nothing but the notice (`removed_gets_only_notice`).** If this
node is a live member of c and the trust rule refuses every peer cid
names in c, then on the connection as each step reads it afresh
(`Node.refresh`: `carry` of `roomsV`): opening says hello only; and of
community c, a frame received, ops just stored (`filedGive`) and the
clock (`tickGive`) send only sync wire ops and stored ops in the
requirement closure of a removal owed to the peer. A frame received
hands the writer nothing of c. -/
theorem removed_gets_only_notice (fam : Family F) (cfg : Config) (ix : Index) (s : DB F) (cid c : B)
    (conn : Conn) (bytes : B) (ids : List Id) (now floor : Nat) (dialer : Bool)
    (hl : LiveIn s c) (hr : Refused s cid c) :
    let k := conn.carry ((roomsV cid).eval s)
    (∀ rs, ∀ o ∈ (Conn.open dialer rs floor now).send, isWire o.kind = true) ∧
    (∀ o ∈ ((Conn.recv fam cfg ix k bytes now : Model F Step).run s).1.send,
      NoticeOnly fam s cid c o) ∧
    (∀ o ∈ ((Conn.recv fam cfg ix k bytes now : Model F Step).run s).1.take, fam.room o ≠ some c) ∧
    (∀ o ∈ ((Conn.filedGive fam cfg k ids : Model F Step).run s).1.send, NoticeOnly fam s cid c o) ∧
    (∀ o ∈ ((Conn.tickGive fam cfg ix k now : Model F Step).run s).1.send, NoticeOnly fam s cid c o) := by
  intro k
  have hrm := rooms_removed s hl hr
  -- an op k may show is of a synced room, so not of c
  have hshow : ∀ o, k.shows fam o = true → fam.room o ≠ some c := by
    intro o ho hc
    simp only [Conn.shows, hc] at ho
    have := hrm _ (mem_syncs ((Engine.has_iff _ _).1 ho))
    exact this rfl
  -- a notice op of k is of another room, or of an owed removal of c
  have hnote : ∀ o, NoticeOp fam s k o → NoticeOnly fam s cid c o := by
    rintro o ⟨r, x, hm, _, y, hy, hroom, hreach⟩
    by_cases hrc : r = c
    · subst hrc
      exact Or.inr (Or.inr ⟨x, hrm _ (mem_notices hm) rfl, y, hy, hreach⟩)
    · exact Or.inr (Or.inl (by rw [hroom]; exact fun h => hrc (Option.some.inj h)))
  refine ⟨fun rs o ho => ?_, fun o ho => ?_, fun o ho => ?_, fun o ho => ?_, fun o ho => ?_⟩
  · simp only [Conn.open, List.mem_singleton] at ho
    subst ho; exact msg_wire _
  · rcases recv_send fam cfg ix k bytes now s o ho with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (hshow o h))
  · exact hshow o (recv_take fam cfg ix k bytes now s o ho).2
  · rcases (notice_send fam cfg ix s k ids now _ (List.mem_cons_self ..)).1 o ho with h | h
    · exact Or.inl h
    · exact hnote o h
  · rcases (notice_send fam cfg ix s k ids now _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))).1 o ho
      with h | h
    · exact Or.inl h
    · exact hnote o h

/-- A connection carries nothing once, for every community this node
is in, the trust rule refuses its peer and every removal owed to it is
given on it. -/
theorem roomsV_nil (s : DB F) {cid : B}
    (h : ∀ c me, (meV c).eval s = some me →
      LiveIn s c ∧ Refused s cid c ∧ ∀ x, Owed s cid c x → x ∈ (givenOn cid).eval s) :
    (roomsV cid).eval s = [] := by
  apply List.eq_nil_iff_forall_not_mem.2
  intro rm hm
  obtain ⟨c, peer, hpeer, _, hm⟩ := mem_roomsV s hm
  rw [eval_roomFor] at hm
  cases hme : (meV c).eval s with
  | none => simp only [hme, List.not_mem_nil] at hm
  | some me =>
    obtain ⟨hl, hr, hg⟩ := h c me hme
    have ht : ((trusts c me peer).liftL : View F Bool).eval s = false := by
      rw [trusts_live s (hl me hme), hr peer hpeer]
    simp only [hme, ht, Bool.false_eq_true, ite_false, List.mem_map, List.mem_filter] at hm
    obtain ⟨x, ⟨hx, hn⟩, _⟩ := hm
    rw [has_of_mem (hg x ⟨peer, hpeer, hx⟩)] at hn
    cases hn

theorem carrying_mem : ∀ (es : List (Id × B × Bool × B × Nat)) (s : DB F) (e : Id × B × Bool × B × Nat),
    (e ∈ ((carrying es : Model F _).run s).1 ↔ e ∈ es ∧ (roomsV e.1).eval s ≠ []) ∧
      ((carrying es : Model F _).run s).2 = s
  | [], _, _ => by simp [carrying]
  | x :: t, s, e => by
    simp only [carrying, Model.run_bind, Model.run_pure]
    rw [View.run_model]
    obtain ⟨ih, hs⟩ := carrying_mem t s e
    refine ⟨?_, hs⟩
    by_cases hx : ((roomsV x.1).eval s).isEmpty = true
    · rw [if_pos hx, ih]
      constructor
      · rintro ⟨hm, hn⟩; exact ⟨List.mem_cons_of_mem _ hm, hn⟩
      · rintro ⟨hm, hn⟩
        rcases List.mem_cons.1 hm with rfl | hm
        · exact absurd (List.isEmpty_iff.1 hx) hn
        · exact ⟨hm, hn⟩
    · rw [if_neg hx, List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨hm, hn⟩)
        · exact ⟨List.mem_cons_self .., fun h => hx (List.isEmpty_iff.2 h)⟩
        · exact ⟨List.mem_cons_of_mem _ hm, hn⟩
      · rintro ⟨hm, hn⟩
        rcases List.mem_cons.1 hm with rfl | hm
        · exact Or.inl rfl
        · exact Or.inr ⟨hm, hn⟩

/-- **Notice, then cut (`notice_then_cut`).** If, for every community c
this node is in, it is a live member, the trust rule refuses cid's peer,
and every removal owed to the peer is given on cid (`conn.given`), then
cid carries nothing, `sessions` does not list it,
and `retired` names it if it is an established session: the node closes
it, and `closing` purges its ops. A session that still carries another
community stays open (`rooms_complete`). -/
theorem notice_then_cut (s : DB F) {cid : B}
    (h : ∀ c me, (meV c).eval s = some me →
      LiveIn s c ∧ Refused s cid c ∧ ∀ x, Owed s cid c x → x ∈ (givenOn cid).eval s) :
    (roomsV cid).eval s = [] ∧
    (∀ e ∈ ((sessions : Model F _).run s).1, e.1 ≠ cid) ∧
    ((∃ e ∈ ((allSessions : Model F _).run s).1, e.1 = cid) →
      cid ∈ ((retired : Model F _).run s).1) := by
  have hnil := roomsV_nil s h
  -- what is open: kept sessions that carry something, read at s
  have hopen : ∀ e, e ∈ ((openSessions : Model F _).run s).1 → e.1 ≠ cid := by
    intro e he
    simp only [openSessions, Model.run_bind, Model.run_pure] at he
    rw [allSessions_state] at he
    obtain ⟨_, hn⟩ := ((carrying_mem _ s e).1).1 he
    intro hc; rw [hc] at hn; exact hn hnil
  refine ⟨hnil, ?_, ?_⟩
  · intro e he
    simp only [sessions, Model.run_bind, Model.run_pure, List.mem_map] at he
    obtain ⟨⟨cid', p, dialer, a, t⟩, ho, rfl⟩ := he
    exact hopen _ ho
  · rintro ⟨e, he, rfl⟩
    simp only [retired, Model.run_bind, Model.run_pure]
    rw [allSessions_state]
    rw [List.mem_filterMap]
    refine ⟨e, he, ?_⟩
    have : (((openSessions : Model F _).run s).1.any fun x => decide (x.1 = e.1)) = false := by
      rw [List.any_eq_false]
      intro x hx hb
      exact hopen x hx (of_decide_eq_true hb)
    rw [this]; rfl

/-- **A responder opens with its node's key (`opened_endpoint`).** An
`opened` checks out only citing the request and an endpoint fact whose
key is the request's addressee; message 1 is read with that endpoint's
secret as the responder's static and the request's sender key as the
initiator's. -/
theorem opened_endpoint (K : Keys) {o : Op} {fs : List F} {r c frm addr : B} {hs : List B}
    (h : check K o .opened fs = some (.opened r c frm addr hs)) :
    ∃ to m1 pk sk, fs = [.inr (.request to frm m1), .inl (.endpoint pk sk)] ∧ pk = to ∧
      (Noise.read1 K.suite prologue sk frm m1).isSome := by
  obtain ⟨q, e, a, rfl, ha, hfa⟩ := check_opened h
  simp only [Fact.opened, Fact.ofOpened.injEq] at hfa
  subst hfa
  obtain ⟨to, frm', m1⟩ := q
  obtain ⟨pk, sk⟩ := e
  simp only [Opened.check] at ha
  split at ha
  · cases ha
  · rename_i hpk
    split at ha
    · rename_i x hr
      split at ha
      · simp only [Option.some.injEq, Opened.Fact.mk.injEq] at ha
        obtain ⟨_, _, rfl, _, _⟩ := ha
        exact ⟨to, m1, pk, sk, rfl, Decidable.of_not_not hpk, by rw [hr]; rfl⟩
      · cases ha
    · cases ha

/-- **A session is between two nodes' keys (`established_endpoint`).**
An `established` checks out only citing the connection, the request,
this side's ephemeral and an endpoint fact (pk, sk). The responder's
endpoint is the request's addressee and its peer the sender; the
initiator's is the sender and its peer the addressee; each side runs
its half of KK with sk as its static and the peer's key as the remote
static. Device keys never enter the handshake. -/
theorem established_endpoint (K : Keys) {o : Op} {fs : List F} {cid c peer h sk' rk : B}
    {dialer : Bool} (hc : check K o .established fs = some (.established cid c peer h sk' rk dialer)) :
    ∃ r m2 to frm m1 ofE pkE esk pk sk,
      fs = [.inr (.connection r m2), .inr (.request to frm m1), .inr (.eph ofE pkE esk),
        .inl (.endpoint pk sk)] ∧
      ((dialer = false ∧ pk = to ∧ peer = frm ∧ (Noise.read1 K.suite prologue sk frm m1).isSome) ∨
       (dialer = true ∧ pk = frm ∧ peer = to ∧ (Noise.sent1 K.suite prologue sk esk to m1).isSome)) := by
  obtain ⟨cn, rq, ep, en, a, rfl, ha, hfa⟩ := check_established hc
  simp only [Fact.established, Fact.ofEstablished.injEq] at hfa
  subst hfa
  obtain ⟨r, m2⟩ := cn; obtain ⟨to, frm, m1⟩ := rq; obtain ⟨ofE, pkE, esk⟩ := ep; obtain ⟨pk, sk⟩ := en
  clear hc
  have hc := ha
  simp only [Established.check] at hc
  · refine ⟨r, m2, to, frm, m1, ofE, pkE, esk, pk, sk, rfl, ?_⟩
    try simp only at hc
    split at hc
    · cases hc
    · split at hc
      · rename_i hto
        left
        cases h1 : Noise.read1 K.suite prologue sk frm m1 with
        | none => simp [h1] at hc
        | some x =>
          obtain ⟨st, re, p1⟩ := x
          simp only [h1, Option.bind_eq_bind, Option.bind_some] at hc
          cases h3 : (decode p1 : Option (B × B × List B)) with
          | none => simp [h3] at hc
          | some d =>
            simp only [h3, Option.bind_some] at hc
            cases h4 : Noise.write2 K.suite st esk frm re .empty with
            | none => simp [h4] at hc
            | some w =>
              simp only [h4, Option.bind_some] at hc
              split at hc
              · cases hc
              · simp only [Option.some.injEq, Established.Fact.mk.injEq] at hc
                obtain ⟨_, _, rfl, _, _, _, rfl⟩ := hc
                exact ⟨rfl, hto, rfl, rfl⟩
      · split at hc
        · rename_i _ hfrm
          right
          cases h1 : Noise.sent1 K.suite prologue sk esk to m1 with
          | none => simp [h1] at hc
          | some x =>
            obtain ⟨st, p1⟩ := x
            simp only [h1, Option.bind_eq_bind, Option.bind_some] at hc
            cases h3 : (decode p1 : Option (B × B × List B)) with
            | none => simp [h3] at hc
            | some d =>
              simp only [h3, Option.bind_some] at hc
              cases h5 : Noise.read2 K.suite st sk esk m2 with
              | none => simp [h5] at hc
              | some q =>
                simp only [h5, Option.bind_some, Option.some.injEq, Established.Fact.mk.injEq] at hc
                obtain ⟨_, _, rfl, _, _, _, rfl⟩ := hc
                exact ⟨rfl, hfrm, rfl, rfl⟩
        · cases hc
end Connection
namespace Connection
open Engine Engine.Sync Codec
section
variable [fr : Fresh (Model F)]

/-- What `answerOne` writes: nothing, or, for a request it trusts, the
connection (a reply to r) and three local ops. -/
theorem answerOne_out (K : Keys) (eps : List (B × B × Id)) (r c frm : B) (s : DB F) :
    ((answerOne K eps r c frm : Model F (List Op)).run s).1 = [] ∨
      ∃ ro to frm' m1 sk epOp f co addr, s.ops r = some ro ∧
        (decode ro.body : Option Body) = some (.request to frm' m1) ∧
        ((trusts c to frm).liftL : View F Bool).eval s = true ∧
        Reply.op K r sk frm m1 f = some co ∧
        ((answerOne K eps r c frm : Model F (List Op)).run s).1 =
          [co, Eph.op f co.id, Established.op co.id r (Eph.op f co.id).id epOp, Send.op addr co] := by
  simp only [answerOne, Model.run_bind]
  by_cases h0 : ((count connection.byRequest [r] : Model F Nat).run s).1 ≠ 0
  · left; rw [if_pos h0]; rfl
  rw [if_neg h0, Model.run_bind]
  have hs0 : ((count connection.byRequest [r] : Model F Nat).run s).2 = s := rfl
  rw [hs0, run_getOp]
  cases hro : s.ops r with
  | none => left; rfl
  | some ro =>
    simp only
    cases hb : (decode ro.body : Option Body) with
    | none => left; rfl
    | some b =>
      cases b with
      | ofRequest x =>
        obtain ⟨to, frm', m1⟩ := x
        simp only
        cases hf : eps.find? (fun x => decide (x.1 = to)) with
        | none => left; rfl
        | some x =>
          obtain ⟨_, sk, epOp⟩ := x
          simp only [Model.run_bind, run_view]
          by_cases hok : ((trusts c to frm).liftL : View F Bool).eval s = true
          · rw [if_neg (by simp [hok]), Model.run_bind, run_arrivedFrom]
            cases ha : ((arrivedFrom r : Model F (Option B)).run s).1 with
            | none => left; simp only [ha]; rfl
            | some addr =>
              simp only [ha, Model.run_bind]
              cases hco : Reply.op K r sk frm m1 ((Fresh.fresh : Model F B).run s).1 with
              | none => left; simp only [hco]; rfl
              | some co =>
                right
                refine ⟨ro, to, frm', m1, sk, epOp, _, co, addr, rfl, hb, hok, hco, ?_⟩
                simp only [hco]; rfl
          · left; rw [if_pos (by simpa using hok)]; rfl
      | _ => left; rfl

theorem answerAll_conn (K : Keys) (eps : List (B × B × Id)) : ∀ (rs : List (Id × Fact)) (s : DB F),
    ∀ o ∈ ((answerAll K eps rs : Model F (List Op)).run s).1, ConnOp o
  | [], _, _, h => by cases h
  | (x, f) :: t, s, o, h => by
    cases f with
    | ofOpened x =>
      obtain ⟨r, c, frm, _, _⟩ := x
      simp only [answerAll, Model.run_bind, Model.run_pure, List.mem_append] at h
      rcases h with h | h
      · rcases answerOne_out K eps r c frm s with he | ⟨_, _, _, _, _, _, _, co, _, _, _, _, hco, he⟩
        · rw [he] at h; cases h
        · rw [he] at h
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl | rfl | rfl
          · exact reply_conn hco
          all_goals exact ⟨_, _, rfl⟩
      · exact answerAll_conn K eps t _ o h
    | _ => exact answerAll_conn K eps t s o h

theorem joinsOf_join (fam : Family F) (c : B) : ∀ (hs : List B) (s : DB F),
    ∀ o ∈ ((joinsOf fam c hs : Model F (List Op)).run s).1, o.bytes ∈ hs ∧ joinOf c o = true
  | [], _, _, h => by cases h
  | b :: t, s, o, h => by
    simp only [joinsOf, Model.run_bind] at h
    have ih := joinsOf_join fam c t s
    split at h
    · have := ih o h; exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩
    · rename_i o' hd
      by_cases hj : (joinOf c o' && decide (fam.scope o' = .shared c)) = true
      · rw [if_pos hj] at h
        simp only [Model.run_bind, Model.run_pure] at h
        by_cases hn : ((Store.getOp (F := F) o'.id : Model F (Option Op)).run
            ((joinsOf fam c t : Model F (List Op)).run s).2).1.isNone = true
        · rw [if_pos hn] at h
          rcases List.mem_cons.1 h with rfl | h
          · simp only [Bool.and_eq_true] at hj
            exact ⟨by rw [show o.bytes = b from Codec.encode_decode hd]; exact List.mem_cons_self .., hj.1⟩
          · have := ih o h; exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩
        · rw [if_neg hn] at h
          have := ih o h; exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩
      · rw [if_neg hj] at h
        simp only [Model.run_pure] at h
        have := ih o h; exact ⟨List.mem_cons_of_mem _ this.1, this.2⟩

theorem deliverAll_join (fam : Family F) : ∀ (rs : List (Id × Fact)) (s : DB F),
    ∀ o ∈ ((deliverAll fam rs : Model F (List Op)).run s).1,
      ∃ x r c frm addr hs, (x, Fact.opened r c frm addr hs) ∈ rs ∧ o.bytes ∈ hs ∧ joinOf c o = true
  | [], _, _, h => by cases h
  | (x, f) :: t, s, o, h => by
    cases f with
    | ofOpened x =>
      obtain ⟨r, c, frm, addr, hs⟩ := x
      simp only [deliverAll, Model.run_bind, Model.run_pure, List.mem_append] at h
      rcases h with h | h
      · obtain ⟨hb, hj⟩ := joinsOf_join fam c hs s o h
        exact ⟨x, r, c, frm, addr, hs, List.mem_cons_self .., hb, hj⟩
      · obtain ⟨x', r', c', frm', addr', hs', hm, hb, hj⟩ := deliverAll_join fam t _ o h
        exact ⟨x', r', c', frm', addr', hs', List.mem_cons_of_mem _ hm, hb, hj⟩
    | _ =>
      obtain ⟨x', r', c', frm', addr', hs', hm, hb, hj⟩ := deliverAll_join fam t s o h
      exact ⟨x', r', c', frm', addr', hs', List.mem_cons_of_mem _ hm, hb, hj⟩

theorem joinOf_request {c : B} {o : Op} (h : joinOf c o = true) :
    o.reqs.head? = some c ∧ ∃ d e cs bs, (decode o.body : Option Community.Body) = some (.request d e cs bs) := by
  unfold joinOf at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hc, _⟩, hb⟩ := h
  refine ⟨hc, ?_⟩
  split at hb
  · rename_i d e cs bs hd; exact ⟨d, e, cs, bs, hd⟩
  · cases hb

/-- **The bare path takes only a join (`bare_takes_only_join`).** Every
shared op `react` writes is a join request of community c carried in
the hello of a request opened here for c, whether or not the trust rule
takes its initiator. Everything else of a hello is left on the wire: a
removed member's node, or anyone who knows c's id, pushes nothing else
into a member's store without a session. -/
theorem bare_takes_only_join (C : Community.Crypto) (K : Keys) (s : DB F) (o : Op)
    (ho : o ∈ ((react (node C K) K : Model F (List Op)).run s).1)
    (hs : ((node C K).room o).isSome = true) :
    ∃ r c frm addr hs d e cs bs,
      (.inr (.opened r c frm addr hs)) ∈ (Engine.eval s (opened.all.query [])).rows.map (·.2) ∧
      o.bytes ∈ hs ∧ o.reqs.head? = some c ∧
      (decode o.body : Option Community.Body) = some (.request d e cs bs) := by
  simp only [react, Model.run_bind, run_rows, Model.run_pure, List.mem_append] at ho
  have notConn : ∀ {o}, ConnOp o → ((node C K).room o).isSome = false := fun h => by
    rw [room_connOp C K h]; rfl
  rcases ho with ((ho | ho) | ho) | ho
  · exact absurd hs (by rw [notConn (openAll_conn _ _ o ho)]; simp)
  · obtain ⟨x, r, c, frm, addr, hs', hm, hb, hj⟩ := deliverAll_join _ _ _ o ho
    obtain ⟨hc, d, e, cs, bs, hd⟩ := joinOf_request hj
    refine ⟨r, c, frm, addr, hs', d, e, cs, bs, ?_, hb, hc, hd⟩
    rw [List.mem_map] at hm
    obtain ⟨⟨⟨p, x'⟩, g⟩, hg, he⟩ := hm
    simp only [Prod.mk.injEq] at he
    obtain ⟨_, rfl⟩ := he
    simp only [Answer.rights, List.mem_filterMap] at hg
    obtain ⟨⟨p', f⟩, hrow, hf⟩ := hg
    rw [List.mem_map]
    refine ⟨(p', f), hrow, ?_⟩
    cases f with
    | inl _ => simp at hf
    | inr y => simp only [Option.some.injEq, Prod.mk.injEq] at hf; obtain ⟨_, rfl⟩ := hf; rfl
  · exact absurd hs (by rw [notConn (answerAll_conn K _ _ _ o ho)]; simp)
  · exact absurd hs (by rw [notConn (establishAll_conn _ _ o ho)]; simp)

theorem answerOne_state (hfr : FreshPure) (K : Keys) (eps : List (B × B × Id)) (r c frm : B)
    (s : DB F) : ((answerOne K eps r c frm : Model F (List Op)).run s).2 = s := by
  simp only [answerOne, Model.run_bind]
  by_cases h0 : ((count connection.byRequest [r] : Model F Nat).run s).1 ≠ 0
  · rw [if_pos h0]; rfl
  rw [if_neg h0, Model.run_bind]
  have hs0 : ((count connection.byRequest [r] : Model F Nat).run s).2 = s := rfl
  rw [hs0, run_getOp]
  cases hro : s.ops r with
  | none => rfl
  | some ro =>
    simp only
    cases hb : (decode ro.body : Option Body) with
    | none => rfl
    | some b =>
      cases b with
      | ofRequest x =>
        obtain ⟨to, frm', m1⟩ := x
        simp only
        cases hf : eps.find? (fun x => decide (x.1 = to)) with
        | none => rfl
        | some x =>
          obtain ⟨_, sk, epOp⟩ := x
          simp only [Model.run_bind, run_view]
          by_cases hok : ((trusts c to frm).liftL : View F Bool).eval s = true
          · rw [if_neg (by simp [hok]), Model.run_bind, run_arrivedFrom]
            cases ha : ((arrivedFrom r : Model F (Option B)).run s).1 with
            | none => simp only [ha]; rfl
            | some addr =>
              simp only [ha, Model.run_bind]
              cases hco : Reply.op K r sk frm m1 ((Fresh.fresh : Model F B).run s).1 with
              | none => simp only [hco]; exact hfr s
              | some co => simp only [hco]; exact hfr s
          · rw [if_pos (by simpa using hok)]; rfl
      | _ => rfl

theorem answerAll_trusted (hfr : FreshPure) (K : Keys) (eps : List (B × B × Id)) :
    ∀ (rs : List (Id × Fact)) (s : DB F), ∀ o ∈ ((answerAll K eps rs : Model F (List Op)).run s).1,
      ∀ m2, (decode o.body : Option Body) = some (.connection m2) →
      ∃ x r c frm addr hs ro to frm' m1, (x, Fact.opened r c frm addr hs) ∈ rs ∧ o.reqs = [r] ∧
        s.ops r = some ro ∧ (decode ro.body : Option Body) = some (.request to frm' m1) ∧
        ((trusts c to frm).liftL : View F Bool).eval s = true
  | [], _, _, h, _, _ => by cases h
  | (x, f) :: t, s, o, h, m2, hb => by
    cases f with
    | ofOpened x =>
      obtain ⟨r, c, frm, addr, hs⟩ := x
      simp only [answerAll, Model.run_bind, Model.run_pure, List.mem_append] at h
      rcases h with h | h
      · rcases answerOne_out K eps r c frm s with he | ⟨ro, to, frm', m1, _, _, _, co, _, hro, hrb, hok, hco, he⟩
        · rw [he] at h; cases h
        · rw [he] at h
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          rcases h with rfl | rfl | rfl | rfl
          · exact ⟨x, r, c, frm, addr, hs, ro, to, frm', m1, List.mem_cons_self .., (reply_reqs hco).1,
              hro, hrb, hok⟩
          all_goals (simp only [Eph.op, Established.op, Send.op, body_conn] at hb; cases hb)
      · rw [answerOne_state hfr] at h
        obtain ⟨x', r', c', frm', addr', hs', ro, to, frm'', m1, hm, hr⟩ :=
          answerAll_trusted hfr K eps t s o h m2 hb
        exact ⟨x', r', c', frm', addr', hs', ro, to, frm'', m1, List.mem_cons_of_mem _ hm, hr⟩
    | _ =>
      obtain ⟨x', r', c', frm', addr', hs', ro, to, frm'', m1, hm, hr⟩ :=
        answerAll_trusted hfr K eps t s o h m2 hb
      exact ⟨x', r', c', frm', addr', hs', ro, to, frm'', m1, List.mem_cons_of_mem _ hm, hr⟩

theorem joinsOf_state (fam : Family F) (c : B) : ∀ (hs : List B) (s : DB F),
    ((joinsOf fam c hs : Model F (List Op)).run s).2 = s
  | [], _ => rfl
  | b :: t, s => by
    simp only [joinsOf, Model.run_bind]
    have ih := joinsOf_state fam c t s
    split
    · simp only [Model.run_pure]; exact ih
    · split
      · simp only [Model.run_bind, Model.run_pure]; exact ih
      · simp only [Model.run_pure]; exact ih

theorem deliverAll_state (fam : Family F) : ∀ (rs : List (Id × Fact)) (s : DB F),
    ((deliverAll fam rs : Model F (List Op)).run s).2 = s
  | [], _ => rfl
  | (_, f) :: t, s => by
    cases f with
    | ofOpened x =>
      obtain ⟨r, c, frm, addr, hs⟩ := x
      simp only [deliverAll, Model.run_bind, Model.run_pure]
      rw [deliverAll_state fam t, joinsOf_state]
    | _ => exact deliverAll_state fam t s

/-- A join request is no Connection op: its body's first byte is
Community's request tag, which no Connection body has. -/
theorem joinOf_not_conn {c : B} {o : Op} (h : joinOf c o = true) (m2 : B) :
    (decode o.body : Option Body) ≠ some (.connection m2) := by
  obtain ⟨_, d, e, cs, bs, hd⟩ := joinOf_request h
  intro hc
  have h1 := Codec.encode_decode hd
  have h2 := Codec.encode_decode hc
  rw [← h2] at h1
  have h3 := congrArg (fun b : ByteArray => b.data.toList.head?) h1
  simp [Codec.encode, Codec.enc, Body.enc, Community.Body.enc] at h3

/-- **An answer only to the trusted (`answer_trusted`).** Every
connection op `react` writes (on the model, with fresh bytes that leave
the store as it is) answers a stored request r, opened here for
community c from key frm, addressed to `to`, where the trust rule takes
frm for c with `to` as this node: lean-net's "no connection before
approval", and after removal, no new session for a removed member's
node. -/
theorem answer_trusted (C : Community.Crypto) (K : Keys) (hfr : FreshPure) (s : DB F) (o : Op) (m2 : B)
    (ho : o ∈ ((react (node C K) K : Model F (List Op)).run s).1)
    (hb : (decode o.body : Option Body) = some (.connection m2)) :
    ∃ r ro to frm' m1 c frm addr hs, o.reqs = [r] ∧ s.ops r = some ro ∧
      (decode ro.body : Option Body) = some (.request to frm' m1) ∧
      (.inr (.opened r c frm addr hs)) ∈ (Engine.eval s (opened.all.query [])).rows.map (·.2) ∧
      ((trusts c to frm).liftL : View F Bool).eval s = true := by
  simp only [react, Model.run_bind, run_rows, Model.run_pure, List.mem_append] at ho
  have hse : ((endpoints : Model F (List (B × B × Id))).run s).2 = s := rfl
  rw [hse, openAll_state, deliverAll_state] at ho
  rcases ho with ((ho | ho) | ho) | ho
  · rw [openAll_body _ _ o ho] at hb; cases hb
  · obtain ⟨_, _, c, _, _, _, _, _, hj⟩ := deliverAll_join _ _ _ o ho
    exact absurd hb (joinOf_not_conn hj m2)
  · obtain ⟨x, r, c, frm, addr, hs, ro, to, frm', m1, hm, hr, hro, hrb, hok⟩ :=
      answerAll_trusted hfr K _ _ s o ho m2 hb
    refine ⟨r, ro, to, frm', m1, c, frm, addr, hs, hr, hro, hrb, ?_, hok⟩
    rw [List.mem_map] at hm
    obtain ⟨⟨⟨p, x'⟩, g⟩, hg, he⟩ := hm
    simp only [Prod.mk.injEq] at he
    obtain ⟨_, rfl⟩ := he
    simp only [Answer.rights, List.mem_filterMap] at hg
    obtain ⟨⟨p', f⟩, hrow, hf⟩ := hg
    rw [List.mem_map]
    refine ⟨(p', f), hrow, ?_⟩
    cases f with
    | inl _ => simp at hf
    | inr y => simp only [Option.some.injEq, Prod.mk.injEq] at hf; obtain ⟨_, rfl⟩ := hf; rfl
  · rw [establishAll_body _ _ o ho] at hb; cases hb

theorem resendConns_send (addr : B) : ∀ (rs : List (Id × Fact)) (s : DB F),
    ∀ q ∈ ((resendConns addr rs : Model F (List Op)).run s).1, ∃ co, q = Send.op addr co
  | [], _, _, h => by cases h
  | (cid, _) :: t, s, q, h => by
    simp only [resendConns, Model.run_bind, Model.run_pure] at h
    split at h
    · rcases List.mem_cons.1 h with rfl | h
      · exact ⟨_, rfl⟩
      · exact resendConns_send addr t _ q h
    · exact resendConns_send addr t _ q h

/-- **A re-sent answer only to the trusted (`resend_trusted`).** A
request arriving again, bare, gets its answer re-sent (a courier) only
if it was opened here for community c from key frm and the trust rule
still takes frm for c, with this node's key the request's addressee: a
removed member's node replaying its request gets nothing. -/
theorem resend_trusted (s : DB F) (addr : B) (o : Op) (at_ : Nat) (q : Op) (a : B)
    (hq : q ∈ ((onArrival none addr o at_ : Model F (List Op)).run s).1)
    (hb : (decode q.body : Option Body) = some (.send a)) :
    ∃ to frm' m1 r c frm addr' hs, (decode o.body : Option Body) = some (.request to frm' m1) ∧
      (.inr (.opened r c frm addr' hs)) ∈
        (Engine.eval s (opened.byRequest.query [o.id])).rows.map (·.2) ∧
      ((trusts c to frm).liftL : View F Bool).eval s = true := by
  have hfirst : ∀ (n : Nat), (q ∈ (if n = 0 then [Recv.op o.id none addr at_] else [])) ∨
      q ∈ ((Community.receiptFor o).liftL : View F (List Op)).eval s → False := by
    intro n hm
    rcases hm with hm | hm
    · split at hm
      · rw [List.mem_singleton] at hm; subst hm
        unfold Recv.op at hb; rw [body_conn] at hb; cases hb
      · cases hm
    · obtain ⟨j, rfl⟩ := receiptFor_receipts s o hm
      exact receipt_not_send _ _ _ hb
  simp only [onArrival, Model.run_bind, run_view, Option.isSome_none, Bool.false_eq_true, ite_false] at hq
  have hs0 : ((count recv.byOp [o.id] : Model F Nat).run s).2 = s := rfl
  rw [hs0] at hq
  split at hq
  · rename_i to frm' m1 hd
    simp only [Model.run_bind, run_rows] at hq
    split at hq
    · rename_i x r c frm addr' hs hhead
      simp only [Model.run_bind, run_view] at hq
      by_cases hok : ((trusts c to frm).liftL : View F Bool).eval s = true
      · rw [if_neg (by simp [hok])] at hq
        simp only [Model.run_bind, run_rows, Model.run_pure, List.mem_append] at hq
        rcases hq with hq | hq
        · exact (hfirst _ hq).elim
        · refine ⟨to, frm', m1, r, c, frm, addr', hs, hd, ?_, hok⟩
          have hm := List.mem_of_mem_head? hhead
          rw [List.mem_map] at hm
          obtain ⟨⟨⟨p, x'⟩, g⟩, hg, he⟩ := hm
          simp only [Prod.mk.injEq] at he
          obtain ⟨_, rfl⟩ := he
          simp only [Answer.rights, List.mem_filterMap] at hg
          obtain ⟨⟨p', f⟩, hrow, hf⟩ := hg
          rw [List.mem_map]
          refine ⟨(p', f), hrow, ?_⟩
          cases f with
          | inl _ => simp at hf
          | inr y => simp only [Option.some.injEq, Prod.mk.injEq] at hf; obtain ⟨_, rfl⟩ := hf; rfl
      · rw [if_pos (by simpa using hok)] at hq
        simp only [Model.run_pure, List.mem_append] at hq
        exact (hfirst _ hq).elim
    · simp only [Model.run_pure, List.mem_append] at hq
      exact (hfirst _ hq).elim
  · simp only [Model.run_pure, List.mem_append] at hq
    exact (hfirst _ hq).elim

/-- `dialOne` sends a courier to the hint when it does not skip. -/
theorem dialOne_sends (K : Keys) (listen pk sk : B) (s : DB F) {c inviter hint : B} {hs : List B}
    {req : Id} {nm d : B} {n : Nat} {a : Id} {waiting : Bool}
    (hm : ((Community.mine c).liftL : View F _).eval s = some (d, a))
    (hw : waiting = decide ((Engine.eval s (Community.admission.byDevice.query [c, d]
      (limit := some 0))).total = 0))
    (hskip : waiting = false → ((connectedTo inviter : Model F Bool).run s).1 = false)
    (hu : Unanswered K listen s pk sk c inviter req waiting) :
    ∃ ro, Send.op hint ro ∈
      ((dialOne K listen pk sk (.joining c inviter (hint :: hs) req nm d n) : Model F (List Op)).run s).1 := by
  simp only [dialOne, List.head?_cons, Model.run_bind]
  rw [run_view, hm]
  simp only [ne_eq, not_true_eq_false, ite_false, Model.run_bind]
  have hl : ((Lists.list (m := Model F) (Community.admission.byDevice.query [c, d] (limit := some 0)) :
      Model F (Answer F)).run s) =
      (Engine.eval s (Community.admission.byDevice.query [c, d] (limit := some 0)), s) := rfl
  rw [hl]
  simp only [Model.run_bind, run_rows]
  rw [requestOf_state]
  unfold Unanswered at hu
  rw [run_rows] at hu
  generalize ((requestOf K sk inviter req _ : Model F (Option Id)).run s).1 = r? at hu ⊢
  cases hwt : waiting
  · -- admitted: dialed while not connected
    have hz : ¬ (Engine.eval s (Community.admission.byDevice.query [c, d] (limit := some 0))).total = 0 := by
      intro h; rw [hwt, h] at hw; cases hw
    rw [if_pos hz, Model.run_bind]
    have hc := hskip hwt
    have hcs : ((connectedTo inviter : Model F Bool).run s).2 = s := rfl
    rw [hcs, hc]
    simp only [Bool.false_eq_true, ite_false]
    cases r? with
    | some r =>
      obtain ⟨_, ho⟩ := hu
      simp only [Model.run_bind, run_getOp, Model.run_pure]
      obtain ⟨ro, hro⟩ := Option.isSome_iff_exists.1 ho
      rw [hro]; exact ⟨ro, List.mem_singleton_self _⟩
    | none =>
      obtain ⟨jr, hjr, hop⟩ := hu
      simp only [Model.run_bind, run_getOp]
      rw [hjr]
      obtain ⟨ro, hro⟩ := Option.isSome_iff_exists.1 (hop ((Fresh.fresh : Model F B).run s).1)
      simp only [Model.run_bind, Model.run_pure]
      rw [hro]
      exact ⟨ro, by simp⟩
  · -- waiting: sent until answered
    have hz : (Engine.eval s (Community.admission.byDevice.query [c, d] (limit := some 0))).total = 0 := by
      rw [hwt] at hw; exact of_decide_eq_true hw.symm
    rw [if_neg (fun h => h hz)]
    cases r? with
    | some r =>
      obtain ⟨hn, ho⟩ := hu
      simp only [Model.run_bind, Model.run_pure]
      have hc : ((count connection.byRequest [r] : Model F Nat).run s).1 = 0 := hn hwt
      have hcs : ((count connection.byRequest [r] : Model F Nat).run s).2 = s := rfl
      rw [hcs, hc]
      simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ite_false, Model.run_bind,
        run_getOp, Model.run_pure]
      obtain ⟨ro, hro⟩ := Option.isSome_iff_exists.1 ho
      rw [hro]; exact ⟨ro, List.mem_singleton_self _⟩
    | none =>
      obtain ⟨jr, hjr, hop⟩ := hu
      simp only [Model.run_pure, Bool.false_eq_true, ite_false, Model.run_bind, run_getOp]
      rw [hjr]
      obtain ⟨ro, hro⟩ := Option.isSome_iff_exists.1 (hop ((Fresh.fresh : Model F B).run s).1)
      simp only [Model.run_bind, Model.run_pure]
      rw [hro]
      exact ⟨ro, by simp⟩

theorem dialOne_state (hfr : FreshPure) (K : Keys) (listen pk sk : B) (f : Community.Fact) (s : DB F) :
    ((dialOne K listen pk sk f : Model F (List Op)).run s).2 = s := by
  cases f with
  | ofJoining x =>
    obtain ⟨c, inviter, hints, req, nm, d, n⟩ := x
    cases hints with
    | nil => rfl
    | cons hint hs =>
      simp only [dialOne, List.head?_cons, Model.run_bind]
      rw [run_view]
      cases hm : ((Community.mine c).liftL : View F _).eval s with
      | none => rfl
      | some da =>
        obtain ⟨me, a⟩ := da
        by_cases hme : me = d
        · subst hme
          simp only [ne_eq, not_true_eq_false, ite_false, Model.run_bind]
          have hl : ((Lists.list (m := Model F) (Community.admission.byDevice.query [c, me]
              (limit := some 0)) : Model F (Answer F)).run s).2 = s := rfl
          rw [hl, run_rows]
          simp only [Model.run_bind]
          rw [requestOf_state]
          generalize ((requestOf K sk inviter req _ : Model F (Option Id)).run s).1 = r?
          generalize ((Lists.list (m := Model F) (Community.admission.byDevice.query [c, me]
              (limit := some 0)) : Model F (Answer F)).run s).1 = adm
          by_cases hz : adm.total ≠ 0
          · rw [if_pos hz, Model.run_bind]
            have hcs : ((connectedTo inviter : Model F Bool).run s).2 = s := rfl
            rw [hcs]
            cases hb : ((connectedTo inviter : Model F Bool).run s).1
            · simp only [Bool.false_eq_true, ite_false]
              cases r? with
              | some r => simp only [Model.run_bind, run_getOp, Model.run_pure]
              | none =>
                simp only [Model.run_bind, run_getOp]
                cases hj : s.ops req with
                | none => rfl
                | some jr => simp only [Model.run_bind, Model.run_pure]; exact hfr s
            · rfl
          · rw [if_neg hz]
            cases r? with
            | some r =>
              simp only [Model.run_bind, Model.run_pure]
              have hcs : ((count connection.byRequest [r] : Model F Nat).run s).2 = s := rfl
              rw [hcs]
              by_cases hn : ((count connection.byRequest [r] : Model F Nat).run s).1 ≠ 0
              · simp only [hn, decide_true, ite_true]; rfl
              · simp only [hn, decide_false, Bool.false_eq_true, ite_false, Model.run_bind, run_getOp,
                  Model.run_pure]
            | none =>
              simp only [Model.run_pure, Bool.false_eq_true, ite_false, Model.run_bind, run_getOp]
              cases hj : s.ops req with
              | none => rfl
              | some jr => simp only [Model.run_bind, Model.run_pure]; exact hfr s
        · simp only [ne_eq, hme, not_false_eq_true, ite_true, Model.run_pure]
  | _ => rfl

theorem dialAll_mem (hfr : FreshPure) (K : Keys) (listen pk sk : B) :
    ∀ (rows : List (Pos × Community.Fact)) (s : DB F) (p : Pos) (f : Community.Fact) (o : Op),
      (p, f) ∈ rows → o ∈ ((dialOne K listen pk sk f : Model F (List Op)).run s).1 →
      o ∈ ((dialAll K listen pk sk rows : Model F (List Op)).run s).1
  | [], _, _, _, _, h, _ => by cases h
  | (q, g) :: rest, s, p, f, o, hm, ho => by
    simp only [dialAll, Model.run_bind, Model.run_pure, List.mem_append]
    rcases List.mem_cons.1 hm with he | hm
    · simp only [Prod.mk.injEq] at he
      obtain ⟨_, rfl⟩ := he
      exact Or.inl ho
    · rw [dialOne_state hfr]
      exact Or.inr (dialAll_mem hfr K listen pk sk rest s p f o hm ho)

/-- **A pending join is sent until it is answered (`rejoin_dials`).** On
a node with a key, a pending join of this node's own entry for c, whose
device is not admitted here, is sent on a tick, to the link's first
hint, while no connection answers its request: beside an open session
or not, so a node removed from c that shares another community with the
inviter dials its rejoin too. -/
theorem rejoin_dials (K : Keys) (listen : B) (now : Nat) (hfr : FreshPure) (s : DB F)
    {pk sk : B} {x : Id} {more : List (B × B × Id)}
    (hk : ((endpoints : Model F _).run s).1 = (pk, sk, x) :: more)
    {p : Pos} {c inviter hint : B} {hs : List B} {req : Id} {nm d : B} {n : Nat} {a : Id}
    (hj : (p, Community.Fact.joining c inviter (hint :: hs) req nm d n) ∈
      (Engine.eval s (Community.joining.all.query [])).lefts)
    (hm : ((Community.mine c).liftL : View F _).eval s = some (d, a))
    (hna : (Engine.eval s (Community.admission.byDevice.query [c, d] (limit := some 0))).total = 0)
    (hu : Unanswered K listen s pk sk c inviter req true) :
    ∃ ro, Send.op hint ro ∈ ((dial K listen now : Model F (List Op)).run s).1 := by
  obtain ⟨ro, hro⟩ := dialOne_sends (hint := hint) (hs := hs) (nm := nm) (n := n) K listen pk sk s hm
    (by simp [hna]) (fun h => by cases h) hu
  refine ⟨ro, ?_⟩
  simp only [dial, Model.run_bind]
  have hs0 : ((endpoints : Model F _).run s).2 = s := rfl
  rw [hk, hs0]
  simp only [List.head?_cons, Model.run_bind]
  exact dialAll_mem hfr K listen pk sk _ s p _ _ hj hro

/-- **A dropped session is dialed again (`reconnect_dials`).** A pending
join of this node's own entry whose device is admitted is sent while no
session to the inviter is open. -/
theorem reconnect_dials (K : Keys) (listen : B) (now : Nat) (hfr : FreshPure) (s : DB F)
    {pk sk : B} {x : Id} {more : List (B × B × Id)}
    (hk : ((endpoints : Model F _).run s).1 = (pk, sk, x) :: more)
    {p : Pos} {c inviter hint : B} {hs : List B} {req : Id} {nm d : B} {n : Nat} {a : Id}
    (hj : (p, Community.Fact.joining c inviter (hint :: hs) req nm d n) ∈
      (Engine.eval s (Community.joining.all.query [])).lefts)
    (hm : ((Community.mine c).liftL : View F _).eval s = some (d, a))
    (had : (Engine.eval s (Community.admission.byDevice.query [c, d] (limit := some 0))).total ≠ 0)
    (hc : ((connectedTo inviter : Model F Bool).run s).1 = false)
    (hu : Unanswered K listen s pk sk c inviter req false) :
    ∃ ro, Send.op hint ro ∈ ((dial K listen now : Model F (List Op)).run s).1 := by
  obtain ⟨ro, hro⟩ := dialOne_sends (hint := hint) (hs := hs) (nm := nm) (n := n) K listen pk sk s hm
    (by simp [had]) (fun _ => hc) hu
  refine ⟨ro, ?_⟩
  simp only [dial, Model.run_bind]
  have hs0 : ((endpoints : Model F _).run s).2 = s := rfl
  rw [hk, hs0]
  simp only [List.head?_cons, Model.run_bind]
  exact dialAll_mem hfr K listen pk sk _ s p _ _ hj hro
end
end Connection
namespace Connection
open Engine
variable {C : Community.Crypto} {K : Keys} {s : DB F}
open Community (Admitted Removed)

/-- Admitted among the node's Community ops: by a Valid admission in the
node's own verdicts. -/
theorem admitted_node (h : Inv (node C K) s) (hq : s.queue = []) {c u : Id} {d e : Community.Key} :
    Admitted C (community C s).ops c u d e ↔ ∃ x, s.status x = some (.valid (.inl (.admission c u d e))) :=
  exists_congr fun x => (sum_project_node h hq).2.2.2.1 x _

/-- Removed among the node's Community ops: by a Valid removal in the
node's own verdicts. -/
theorem removed_node (h : Inv (node C K) s) (hq : s.queue = []) {c u : Id} :
    Removed C (community C s).ops c u ↔ ∃ x r, s.status x = some (.valid (.inl (.removal c u r))) :=
  exists_congr fun x => exists_congr fun _ => (sum_project_node h hq).2.2.2.1 x _
end Connection
namespace Connection
open Engine Engine.Sync

/-- **A room is carried synced only if trusted.** If connection cid
carries room c synced, this node holds c and is in it as its key `me`,
one of cid's established facts names a peer key, and the trust rule
takes it. -/
theorem rooms_trusted (s : DB F) {cid c : Id} (h : Room.sync c ∈ (roomsV cid).eval s) :
    ∃ peer me, peer ∈ peersOf (Engine.eval s (established.byConn.query [cid])) ∧
      c ∈ heldV.eval s ∧
      (meV c).eval s = some me ∧ ((trusts c me peer).liftL : View F Bool).eval s = true := by
  obtain ⟨c', peer, hpeer, hheld, hm⟩ := mem_roomsV s h
  rw [eval_roomFor] at hm
  cases hme : (meV c').eval s with
  | none => simp only [hme, List.not_mem_nil] at hm
  | some me =>
    cases ht : ((trusts c' me peer).liftL : View F Bool).eval s
    · simp only [hme, ht, Bool.false_eq_true, ite_false, List.mem_map] at hm
      obtain ⟨_, _, hn⟩ := hm; cases hn
    · simp only [hme, ht, ite_true, List.mem_singleton, Room.sync.injEq] at hm
      subst hm
      exact ⟨peer, me, hpeer, hheld, hme, ht⟩

/-- **A live member's connection carries no synced room whose peer
`allowPeer` refuses.** If this node is a live member of c, and
`allowPeer` refuses, for c, every peer key cid's established facts name,
then cid carries no room c synced: no step of it sends an op of c by
sync or takes one (`recv_send`, `recv_take`). It may carry c's notices
(`rooms_removed`). -/
theorem rooms_cut (s : DB F) {cid c : Id}
    (hme : ∀ me, (meV c).eval s = some me →
      ((Community.allowPeer c me).liftL : View F Bool).eval s = true)
    (hpeer : ∀ peer ∈ peersOf (Engine.eval s (established.byConn.query [cid])),
      ((Community.allowPeer c peer).liftL : View F Bool).eval s = false) :
    Room.sync c ∉ (roomsV cid).eval s := by
  intro h
  obtain ⟨peer, me, hp, _, hm, ht⟩ := rooms_trusted s h
  rw [trusts_live s (hme me hm), hpeer peer hp] at ht
  cases ht
end Connection
namespace Connection
open Engine
variable {C : Community.Crypto} {K : Keys} {s : DB F}
open Community (Admitted Removed)

/-- **A removal ends a live session's sync, in the running node.** At
rest, if this node is let into c (a device admitted under its key is
live), and each peer connection cid's established facts name in c has
only devices admitted into a removed user u, then cid carries no sync
room of c: no step of it sends an op of c or takes one (`recv_send`,
`recv_take`). -/
theorem rooms_cut_node (h : Inv (node C K) s) (hq : s.queue = []) {cid c : Id}
    (hme : ∀ me, (meV c).eval s = some me →
      ∃ u d, Admitted C (community C s).ops c u d me ∧ Community.Live C (community C s).ops c d)
    (hpeer : ∀ peer ∈ peersOf (Engine.eval s (established.byConn.query [cid])),
      ∃ u, Removed C (community C s).ops c u ∧
        ∀ u' d, Admitted C (community C s).ops c u' d peer → ∃ e', Admitted C (community C s).ops c u d e') :
    Engine.Sync.Room.sync c ∉ (roomsV cid).eval s :=
  rooms_cut s (fun me hm => (connect_iff_node h hq c me).2 (hme me hm)) fun peer hp =>
    let ⟨_, hr, only⟩ := hpeer peer hp
    removal_cuts_off_node h hq hr only
end Connection
namespace Connection
open Engine Engine.Sync

/-- The hook runs the view: on the model, `rooms` gives `roomsV`, its
synced rooms and its notices, and reads only. -/
theorem rooms_model (s : DB F) (cid : Id) :
    ((rooms cid : Model F (List Room))).run s = ((roomsV cid).eval s, s) := by
  unfold rooms
  exact View.run_model _ s

end Connection
