import engine.core.Project
import engine.wire.NodeLaws
import app.Commands
import app.community.member.invite.request.Commands
import app.community.member.join.joining.Commands
import app.connection.Commands
import app.connection.Family
import app.connection.Proofs
import app.connection.connection.Commands
import app.connection.connection.Proofs
import app.connection.eph.Commands
import app.connection.established.Commands
import app.connection.established.Proofs
import app.connection.opened.Proofs
import app.connection.recv.Commands
import app.connection.request.Commands
import app.connection.send.Commands
import app.connection.send.Proofs
import engine.sync.NoticeLaws
import app.Screen
import engine.renderer.Cue
import app.connection.given.Commands
import app.connection.opened.Commands
import engine.core.FIFO

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

section

/-
Laws at the app's call sites: an unmounted state's reads and writes are
pure no-ops; a callback from an earlier mount cannot execute even after
remount; checkpoints restore the page and anchor read by the app. Geometry
is quantified over every fitting viewport, including a changed keyboard.
-/

namespace LifecycleLaws
open App Engine Data

/-- No query is run on behalf of an unmounted page. -/
theorem unmount_read (s : St) (scope : Component.Scope) (q : Reader.Want) :
    (App.query scope q).run (unmountState s) = pure (none, unmountState s) := by rfl

/-- No write is submitted on behalf of an unmounted page. -/
theorem unmount_write (s : St) (w : Community.Write) :
    (App.writeAll w).run (unmountState s) = pure (false, unmountState s) := by rfl

/-- No old callback can read, paint or write after the page is remounted. -/
theorem old_callback (s : St) (action : M α) :
    (App.owned s.life.lease action).run { unmountState s with life := s.life.unmount.mount } =
      pure (none, { unmountState s with life := s.life.unmount.mount }) := by
  change (Lifecycle.owned s.life.unmount.mount s.life.lease action).run _ = _
  rw [Lifecycle.old_quiet]
  rfl

/-- The serialized op restores the page and anchor that the app saves.
This states the round trip at the call sites, not just for an arbitrary
codec; the native SQLite read/commit is tested separately. -/
theorem restore_page_anchor (s : St) :
    (Lifecycle.restore (Codec.encode (checkpoint s))).map (fun cp =>
      (PageId.ofCode cp.2.1, cp.2.2.2.1, cp.2.2.2.2.1)) =
    some (s.page, ((checkpointAnchor s).getD (.empty, 0)).1, ((checkpointAnchor s).getD (.empty, 0)).2) := by
  rw [Lifecycle.restore_checkpoint]
  by_cases h : s.me.acc.isEmpty <;> simp [checkpoint, stashDraft, h, page_round]

/-- The actual restore function returns the saved page and anchor. Real
anchors are op ids, which are nonempty; no saved anchor is also allowed. -/
theorem apply_page_anchor (s target : St)
    (valid : ∀ x off, checkpointAnchor s = some (x, off) → x.isEmpty = false) :
    (applyCheckpoint target (checkpoint s)).page = s.page ∧
    (applyCheckpoint target (checkpoint s)).mark = checkpointAnchor s := by
  cases ha : checkpointAnchor s with
  | none =>
    by_cases h : s.me.acc.isEmpty <;>
      simp [applyCheckpoint, St.withNav, Nav.go_page, checkpoint, stashDraft, useDraft, h, ha, page_round] <;> rfl
  | some a =>
    rcases a with ⟨x, off⟩
    have hx := valid x off ha
    by_cases h : s.me.acc.isEmpty <;>
      simp [applyCheckpoint, St.withNav, Nav.go_page, checkpoint, stashDraft, useDraft, h, ha, hx, page_round]

/-- Both placement and page hit inversion hold at every fitting size,
without a portrait, DPI or keyboard-height restriction. -/
theorem viewport_geometry (g : Geometry.Geom) (fits : g.Fits) (over bf bn r y : Nat) :
    Geometry.Seam.place g over bf bn r = Geometry.Seam.home g bn (Geometry.Seam.frameRow g over bf r) ∧
    Geometry.Seam.tapRow g y = (y : Int) - g.top :=
  ⟨Geometry.placed_row g fits over bf bn r, Geometry.pinned_tap g fits y⟩

/-- A fitting viewport with a visible keyboard exists. -/
theorem viewport_possible : (Geometry.Geom.mk 1280 24 300 80 100).Fits := by
  unfold Geometry.Geom.Fits; decide

end LifecycleLaws

end

section

/-
The app's navigation laws, over the running code: App.openSt, backSt and
switchSt, which openPage, back and switchToAcc run (and onPageAct's
channel, join, Stop waiting and removal steps through Nav too).

- `back_open`: **back goes back.** Back after opening a page that is
  neither shown nor under it gives the state before, but for what back
  always clears: the page's one-line field, refusal and viewport initialization. The composer's
  draft is unchanged. The switcher's render-only backdrop cache is retained
  from the opened page.
- `back_root`: at a root, back keeps the page and the state.
- `back_switch`: after a switch, any number of backs stays on the new
  community's home: back never reaches the community before.
- `draft_open`, `draft_back`: no navigation step changes the composer's
  draft, its selection or its photos.
- `inv_open`, `inv_back`, `inv_switch`: no page is twice in the page and
  its stack; so (`depth`) after any open, fewer than 18 backs reach a root.
-/

namespace NavLaws
open App

theorem nav_open (p : PageId) (s : St) : (openSt p s).nav = Nav.go p s.nav := rfl

theorem nav_back (s : St) : (backSt s).nav = Nav.back s.nav := rfl

theorem nav_switch (a : Engine.Id) (s : St) : (switchSt a s).nav = Nav.reset PageId.home := rfl

/-- **Back goes back.** -/
theorem back_open (p : PageId) (s : St) (hp : p ≠ s.page) (hs : p ∉ s.backStack) :
    backSt (openSt p s) = { s with field := "", refusal := none, pageKey := none, pageScrollStarted := false, switcherBackdrop := (openSt p s).switcherBackdrop } := by
  have h := Nav.back_go p s.nav hp hs
  unfold backSt
  rw [nav_open, h]
  simp only [openSt, St.withNav, St.nav]

/-- **Back at a root keeps the page.** -/
theorem back_root (s : St) (h : s.backStack = []) :
    backSt s = { s with field := "", refusal := none, pageKey := none, pageScrollStarted := false } := by
  have hb := Nav.back_root s.nav h
  unfold backSt
  rw [hb]
  rfl

theorem backs_root (k : Nat) (s : St) (h : s.backStack = []) :
    (Nat.repeat backSt k s).nav = s.nav := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show (backSt (Nat.repeat backSt k s)).nav = s.nav
    rw [nav_back, ih]
    exact Nav.back_root s.nav h

/-- **A switch is a root.** However many times back is pressed after a
switch, the page is the new community's home, with nothing under it. -/
theorem back_switch (k : Nat) (a : Engine.Id) (s : St) :
    (Nat.repeat backSt k (switchSt a s)).nav = Nav.reset PageId.home :=
  (backs_root k (switchSt a s) rfl).trans (nav_switch a s)

/-- **Opening a page keeps the draft.** -/
theorem draft_open (p : PageId) (s : St) :
    (openSt p s).text = s.text ∧ (openSt p s).sel = s.sel ∧ (openSt p s).chips = s.chips :=
  ⟨rfl, rfl, rfl⟩

/-- **Back keeps the draft.** -/
theorem draft_back (s : St) :
    (backSt s).text = s.text ∧ (backSt s).sel = s.sel ∧ (backSt s).chips = s.chips :=
  ⟨rfl, rfl, rfl⟩

theorem inv_open (p : PageId) (s : St) (h : Nav.Inv s.nav) : Nav.Inv (openSt p s).nav :=
  Nav.go_inv p s.nav h

theorem inv_back (s : St) (h : Nav.Inv s.nav) : Nav.Inv (backSt s).nav :=
  Nav.back_inv s.nav h

theorem inv_switch (a : Engine.Id) (s : St) : Nav.Inv (switchSt a s).nav := by
  rw [nav_switch]; exact Nav.reset_inv _

theorem all_pages (p : PageId) : p ∈ PageId.all := by
  cases p <;> simp [PageId.all]

/-- **Back reaches a root** in fewer than 19 steps (there are 19 pages):
opening a page never stacks more. -/
theorem depth (p : PageId) (s : St) (h : Nav.Inv s.nav) : (openSt p s).backStack.length < PageId.all.length :=
  Nav.depth PageId.all all_pages (openSt p s).nav (inv_open p s h)

end NavLaws

end

section

/-
What a removed person's device shows, over the running code
(Kinds.Accepted.listed, newlyGone, landing; App.forgetEntry), once the
removal is in its store (the engine's last notice delivers it):

- `listed_iff`: a community is listed exactly when this device's entry in
  it is not removed (A1); the entry's data stays in the store;
- `told_once`: a removal is announced once: after its notice, the same
  removal is never new again (A2); and `not_replayed`: a removal already
  in the store at launch is not announced;
- `landing_listed`: the app lands on a listed entry, or on none (Get
  started) (A5);
- `forget_clears`: nothing the app holds names the forgotten entry: no
  invite link of it, no pasted link to its community, and, if it was
  current, no composer text or photos (A4).
-/

namespace RemovedLaws
open Kinds.Accepted

/-- **Listed exactly when not removed.** -/
theorem listed_iff (ms : Array Me) (m : Me) : m ∈ listed ms ↔ m ∈ ms ∧ m.removed = false := by
  simp [listed, Array.mem_filter]

theorem any_eq (l : List Engine.Id) (x : Engine.Id) : l.any (fun y => decide (y = x)) = true ↔ x ∈ l := by
  simp [List.any_eq_true]

/-- **Told once.** Once the newly removed entries are added to what has
been told, none of them (and nothing else) is new again. -/
theorem told_once (seen : List Engine.Id) (ms : Array Me) :
    newlyGone ((newlyGone seen ms).map (·.acc) ++ seen) ms = [] := by
  apply List.eq_nil_iff_forall_not_mem.2
  intro m hm
  simp only [newlyGone, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true', any_eq] at hm
  obtain ⟨hmem, hrm, hnot⟩ := hm
  have hin : m ∈ newlyGone seen ms := by
    simp only [newlyGone, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨hmem, hrm, ?_⟩
    cases h : seen.any (fun y => decide (y = m.acc)) with
    | false => rfl
    | true => exact absurd (List.mem_append_right _ ((any_eq seen m.acc).1 h)) (by
        intro h'; rw [Bool.eq_false_iff] at hnot; exact hnot ((any_eq _ _).2 h'))
  have : m.acc ∈ (newlyGone seen ms).map (·.acc) ++ seen := List.mem_append_left _ (List.mem_map_of_mem hin)
  rw [Bool.eq_false_iff] at hnot
  exact hnot ((any_eq _ _).2 this)

/-- **Not replayed.** What was already removed at launch is told. -/
theorem not_replayed (ms : Array Me) :
    newlyGone ((ms.toList.filter (·.removed)).map (·.acc)) ms = [] := by
  apply List.eq_nil_iff_forall_not_mem.2
  intro m hm
  simp only [newlyGone, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true', any_eq] at hm
  obtain ⟨hmem, hrm, hnot⟩ := hm
  rw [Bool.eq_false_iff] at hnot
  exact hnot ((any_eq _ _).2 (List.mem_map_of_mem (List.mem_filter.2 ⟨hmem, hrm⟩)))

/-- **The app lands on a listed entry, or on none.** -/
theorem landing_listed (cs : Array Me) (cur : Engine.Id) (m : Me) (h : landing cs cur = some m) : m ∈ cs := by
  unfold landing select at h
  cases hs : cs.find? (fun m => decide (m.acc = cur)) with
  | some x =>
    rw [hs] at h; simp at h; subst h; exact Array.mem_of_find?_eq_some hs
  | none =>
    rw [hs] at h; simp at h
    exact Array.mem_of_getElem? h

/-- **Nothing is left of the forgotten entry.** -/
theorem forget_clears (s : App.St) (a c : Engine.Id) :
    ((App.forgetEntry s a c).links.all (·.1 != a)) = true ∧
    ((App.forgetEntry s a c).invite.map (·.community == c)) ≠ some true ∧
    (s.me.acc == a → (App.forgetEntry s a c).text = "" ∧ (App.forgetEntry s a c).chips = #[]) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [App.forgetEntry, List.all_filter]
  · simp only [App.forgetEntry]
    split <;> rename_i h
    · simp
    · intro h'; exact h (by rw [h']; rfl)
  · intro h; simp [App.forgetEntry, h]

end RemovedLaws

end

section

/-
Re-layout laws about the app's report handler, not a parallel state.
The old five-word protocol uses the most recent IME event; an extended
report supplies it directly. Row invalidation is tested with App.step.
-/

namespace App

theorem screenChanged_size (sc : Array UInt32) (now : Nat) (s : St) :
    (screenChanged sc now s).W =
      (Safe.content { SafeFrame.report sc s.imeH with ime := {} }).w ∧
    (screenChanged sc now s).Hs = (SafeFrame.report sc s.imeH).h := by
  simp [screenChanged]

theorem screenChanged_insets (sc : Array UInt32) (now : Nat) (s : St) :
    (screenChanged sc now s).window = SafeFrame.report sc s.imeH ∧
    (screenChanged sc now s).imeH = (SafeFrame.report sc s.imeH).ime.bottom ∧
    (screenChanged sc now s).insetTop =
      (Safe.content { SafeFrame.report sc s.imeH with ime := {} }).y := by
  simp [screenChanged]

end App

end

section

/-
Theme laws over the running app's transition and the renderer's colour
resolver. Layout ownership and later occlusion are separate obligations:
text must still be visible, and copied layers must keep their pixels.
-/

namespace ThemeLaws
open App Paint

/-- No row, image, sheet cell, page or chrome from the old theme remains
reachable after the transition, including their asynchronous tasks. -/
theorem cleared (s : St) (t : Theme.State) :
    (themed s t).rows = {} ∧ (themed s t).imgs = {} ∧
    (themed s t).gridRows = {} ∧ (themed s t).pageNow = none ∧
    (themed s t).pageKey = none ∧ (themed s t).chromeKey = "" ∧
    (themed s t).topBmp.rows = #[] ∧ (themed s t).botBmp.rows = #[] := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The new background and every painter's palette input agree with the
new effective theme, regardless of the previous cache contents. -/
theorem palette (s : St) (t : Theme.State) :
    (themed s t).dim.theme = Theme.effective t ∧
    (themed s t).bgRow = solid (Palette.color (Theme.effective t) (if s.wide then .panel else .bg)) s.W := ⟨rfl, rfl⟩

/-- Theme changes preserve the content and layout inputs. -/
theorem content (s : St) (t : Theme.State) :
    (themed s t).me = s.me ∧ (themed s t).ids = s.ids ∧
    (themed s t).text = s.text ∧ (themed s t).W = s.W ∧
    (themed s t).dim.dpi = s.dim.dpi ∧ (themed s t).dim.cell = s.dim.cell :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The glyph painter's actual colour selector meets 4.5:1 against the
composited pixel below, for every possible RGB background. -/
theorem text (wanted : Color) (row : ByteArray) (x : Nat) :
    Contrast.meets (textColor wanted row x) (getPx row x) := Contrast.ink_meets _ _

end ThemeLaws

end

section

/-
Executions of the production node and connection hooks. Unlike Sync.World,
sessions open through Noise and the actual connection reactions; frames use
the native AEAD and rooms are read from the store. The store is Held, whose
interpreter is explicit, and entropy is an input tape. SQLite, the OS entropy
source and TCP are tested separately by JoinFair, not silently identified with
this interpreter. No direct Node.connect or plaintext session hook is used.
-/

namespace Connection.Execution
open Engine Engine.Sync Community

inductive Side where
  | a | b
  deriving DecidableEq, Inhabited

structure Memory where
  held : Held F := {}
  /-- An input, not a claim that deterministic fixtures are secure randomness. -/
  entropy : Nat → ByteArray
  cursor : Nat := 0

def M (α : Type) := Memory → α × Memory

instance : Monad M where
  pure a := fun s => (a, s)
  bind x f := fun s => let (a, s') := x s; f a s'

def lift {α : Type} (x : HeldM F α) : M α := fun s =>
  let (a, h) := x s.held
  (a, { s with held := h })

instance : Store F M where
  getOp x := lift (Store.getOp x)
  putOp o := lift (Store.putOp o)
  getStatus x := lift (Store.getStatus x)
  setStatus x v := lift (Store.setStatus x v)
  addWait x y := lift (Store.addWait x y)
  waiters x := lift (Store.waiters x)
  clearWaiters x := lift (Store.clearWaiters x)
  push x := lift (Store.push x)
  pop := lift Store.pop
  index k x := lift (Store.index k x)
  lookup k := lift (Store.lookup k)

instance : Lists F M where
  list q := lift (Lists.list q)

instance : Turn F M where
  turn fam ops := lift (Turn.turn fam ops)
  purge fam ids scrub := lift (Turn.purge fam ids scrub)

instance : Fresh M where
  fresh := fun s => (s.entropy s.cursor, { s with cursor := s.cursor + 1 })

def family : Family F := Connection.node ed25519 sodium

structure Peer where
  node : Engine.Sync.Node
  memory : Memory

structure Packet where
  src : ByteArray
  dst : ByteArray
  bytes : ByteArray
  deriving DecidableEq

structure World where
  a : Peer
  b : Peer
  net : List Packet := []
  now : Nat := 0
  /-- Socket-close requests whose external transport effect this interpreter
  has not modeled. Finite native success certificates require this to stay
  zero. The infinite fairness theorem alone does not assert that it does. -/
  unhandledDrops : Nat := 0

structure Setup where
  addr : Side → ByteArray
  cfg : Config := { every := 30000, askTime := 20000 }
  /-- Flow-control input, in the same form the runner supplies to Sync. -/
  room : Side → ByteArray → Option Nat := fun _ _ => none

def Setup.sync (S : Setup) (side : Side) : Sync F M :=
  { fam := family, cfg := S.cfg, hooks := Connection.hooks family sodium (S.addr side),
    room := S.room side }

def World.peer (w : World) : Side → Peer
  | .a => w.a
  | .b => w.b

def World.set (w : World) : Side → Peer → World
  | .a, p => { w with a := p }
  | .b, p => { w with b := p }

def packets (S : Setup) (side : Side) (e : Effects) : List Packet :=
  e.send.map fun (addr, bytes) => ⟨S.addr side, addr, bytes⟩

def World.run (S : Setup) (w : World) (side : Side) (queue : List Packet)
    (f : Engine.Sync.Node → M (Engine.Sync.Node × Effects))
    (transportClosed : Bool := false) : World :=
  let p := w.peer side
  let ((n, e), memory) := f p.node p.memory
  { w.set side ⟨n, memory⟩ with
    net := queue ++ packets S side e
    unhandledDrops := w.unhandledDrops + (if transportClosed then 0 else e.drop.length) }

/-- Environment actions. Close discards buffered transport frames and notifies
both actual nodes; surviving join/admission ops must drive any redial. -/
inductive Action where
  | tick (side : Side)
  | write (side : Side) (ops : List Op)
  | deliver
  | close
  | drop
  | idle

/-- Deliver only the FIFO head. An address outside this two-node environment
has no receiver; it is discarded explicitly rather than sent to the wrong node. -/
def World.deliver (S : Setup) (w : World) : World :=
  match w.net with
  | [] => w
  | p :: rest =>
    if p.dst = S.addr .a then
      w.run S .a rest fun n => n.onFrame (S.sync .a) p.src p.bytes w.now
    else if p.dst = S.addr .b then
      w.run S .b rest fun n => n.onFrame (S.sync .b) p.src p.bytes w.now
    else { w with net := rest }

/-- One completed iteration. Time advances even when queues are empty.
This is simulated time, not a promise about OS scheduling or I/O duration. -/
def step (S : Setup) (w : World) (a : Action) : World :=
  let w' := match a with
    | .tick s => w.run S s w.net fun n => n.onTick (S.sync s) w.now
    | .write s ops => w.run S s w.net fun n => n.onWrite (S.sync s) ops w.now
    | .deliver => w.deliver S
    | .close =>
      -- This explicit environment action already closes both sides and
      -- discards buffered frames. Earlier unhandled effects stay recorded.
      let a := w.run S .a [] (fun n => n.onClose (S.sync .a) (S.addr .b) w.now) true
      a.run S .b a.net (fun n => n.onClose (S.sync .b) (S.addr .a) w.now) true
    | .drop => { w with net := w.net.tail }
    | .idle => w
  { w' with now := w.now + 1 }

def trace (S : Setup) (w : World) : List Action → World
  | [] => w
  | a :: rest => trace S (step S w a) rest

/-- A fair tail: both nodes tick, and the FIFO head is offered to its real
destination each cycle. Approval is an explicit local write in the prefix. -/
def schedule (i : Nat) : Action :=
  if i % 3 = 0 then .tick .a else if i % 3 = 1 then .tick .b else .deliver

def states (S : Setup) (initial : World) : Nat → World
  | 0 => initial
  | n + 1 => step S (states S initial n) (schedule n)

def dequeued (w : World) : Action → Option Packet
  | .deliver => w.net.head?
  | _ => none

structure Run (S : Setup) (initial : World) where
  state : Nat → World
  action : Nat → Action
  zero : state 0 = initial
  next : ∀ i, state (i + 1) = step S (state i) (action i)

def fairRun (S : Setup) (initial : World) : Run S initial :=
  ⟨states S initial, schedule, rfl, fun _ => rfl⟩

/-- Scheduler/transport fairness in this explicit two-node interpreter. A
queued packet reaches its addressed handler if that address is one of the
two peers. This says nothing about whether that handler accepts its bytes. -/
def Run.Fair {S initial} (r : Run S initial) : Prop :=
  (∀ N, ∃ i ≥ N, r.action i = .tick .a) ∧
  (∀ N, ∃ i ≥ N, r.action i = .tick .b) ∧
  (∀ n p, p ∈ (r.state n).net → ∃ i ≥ n, dequeued (r.state i) (r.action i) = some p) ∧
  (∀ i, (r.state i).now = initial.now + i)

def empty (ea eb : Nat → ByteArray) : World :=
  { a := ⟨Engine.Sync.Node.boot family [] 0, { entropy := ea }⟩,
    b := ⟨Engine.Sync.Node.boot family [] 0, { entropy := eb }⟩ }

end Connection.Execution

end

section

namespace Connection.Execution
open Engine Engine.Sync

theorem run_queue (S : Setup) (w : World) (s : Side) (q : List Packet)
    (f : Engine.Sync.Node → M (Engine.Sync.Node × Effects)) :
    ∃ added, (w.run S s q f).net = q ++ added := by
  exact ⟨_, rfl⟩

theorem deliver_queue (S : Setup) (w : World) :
    Net.FIFO.Advance w.net (w.deliver S).net w.net.head? := by
  unfold World.deliver
  cases h : w.net with
  | nil => simpa [h] using (Net.FIFO.Advance.append ([] : List Packet) [])
  | cons p rest =>
    simp only [List.head?_cons]
    split
    · obtain ⟨added, he⟩ := run_queue S w .a rest _
      rw [he]; exact .pop p rest added
    · split
      · obtain ⟨added, he⟩ := run_queue S w .b rest _
        rw [he]; exact .pop p rest added
      · simpa using (Net.FIFO.Advance.pop p rest [])

theorem schedule_queue (S : Setup) (w : World) (i : Nat) :
    Net.FIFO.Advance w.net (step S w (schedule i)).net (dequeued w (schedule i)) := by
  unfold schedule
  split
  · let f := fun n : Engine.Sync.Node => n.onTick (S.sync .a) w.now
    have eqn : (step S w (.tick .a)).net = (w.run S .a w.net f).net := by simp only [step]; rfl
    rw [eqn]
    obtain ⟨added, he⟩ := run_queue S w .a w.net f
    rw [he]
    exact Net.FIFO.Advance.append w.net added
  · split
    · let f := fun n : Engine.Sync.Node => n.onTick (S.sync .b) w.now
      have eqn : (step S w (.tick .b)).net = (w.run S .b w.net f).net := by simp only [step]; rfl
      rw [eqn]
      obtain ⟨added, he⟩ := run_queue S w .b w.net f
      rw [he]
      exact Net.FIFO.Advance.append w.net added
    · exact deliver_queue S w

theorem fairRun_fair (S : Setup) (initial : World) : (fairRun S initial).Fair := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro N
    refine ⟨3 * N, by omega, ?_⟩
    simp [fairRun, schedule]
  · intro N
    refine ⟨3 * N + 1, by omega, ?_⟩
    simp [fairRun, schedule]
  · intro n p hp
    apply Net.FIFO.eventually_delivered
      (fun i => (states S initial i).net)
      (fun i => dequeued (states S initial i) (schedule i))
      (fun i => schedule_queue S (states S initial i) i) ?_ hp
    intro N
    refine ⟨3 * N + 2, by omega, ?_⟩
    intro hn
    simp only [schedule, Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.zero_mul,
      Nat.zero_mod, Nat.reduceMod, Nat.zero_add, show ¬(2 : Nat) = 0 from by decide,
      show ¬(2 : Nat) = 1 from by decide, ↓reduceIte, dequeued]
    cases he : (states S initial (3 * N + 2)).net with
    | nil => exact False.elim (hn he)
    | cons p rest => rfl
  · intro i
    change (states S initial i).now = _
    induction i with
    | zero => simp [states]
    | succ i ih => simpa [states, step, ih, Nat.add_assoc]

/-- Prefix a real transition; no state is reset or invented at the join. -/
def Run.cons {S initial} (a : Action) (r : Run S (step S initial a)) : Run S initial where
  state
    | 0 => initial
    | i + 1 => r.state i
  action
    | 0 => a
    | i + 1 => r.action i
  zero := rfl
  next i := by cases i with
    | zero => exact r.zero
    | succ i => exact r.next i

def prepend (S : Setup) (initial : World) (actions : List Action)
    (r : Run S (trace S initial actions)) : Run S initial :=
  match actions with
  | [] => r
  | a :: rest => Run.cons a (prepend S (step S initial a) rest r)

theorem prepend_state (S : Setup) (initial : World) (actions : List Action)
    (r : Run S (trace S initial actions)) (i : Nat) :
    (prepend S initial actions r).state (actions.length + i) = r.state i := by
  induction actions generalizing initial with
  | nil => simp [prepend]
  | cons a rest ih =>
    simpa only [List.length_cons, Nat.add_right_comm, prepend, Run.cons] using
      ih (step S initial a) r

theorem prepend_action (S : Setup) (initial : World) (actions : List Action)
    (r : Run S (trace S initial actions)) (i : Nat) :
    (prepend S initial actions r).action (actions.length + i) = r.action i := by
  induction actions generalizing initial with
  | nil => simp [prepend]
  | cons a rest ih =>
    simpa only [List.length_cons, Nat.add_right_comm, prepend, Run.cons] using
      ih (step S initial a) r

/-- A finite execution with delays/drops/closes can be followed by an infinite
fair suffix through the production node. The goal is checked on the finite
prefix, not assumed as a scheduler property. This is existence of a successful
prefix with a fair node-interpreter continuation, not convergence of every
fair execution or a guarantee that future socket-close effects are modeled. -/
theorem successful_fair_extension (S : Setup) (initial : World) (actions : List Action)
    (Goal : World → Prop) (success : Goal (trace S initial actions)) :
    ∃ r : Run S initial,
      Goal (r.state actions.length) ∧
      ∃ tail : Run S (trace S initial actions), tail.Fair ∧
        (∀ i, r.state (actions.length + i) = tail.state i) ∧
        (∀ i, r.action (actions.length + i) = tail.action i) := by
  let tail := fairRun S (trace S initial actions)
  refine ⟨prepend S initial actions tail, ?_, tail, fairRun_fair S _,
    prepend_state S initial actions tail, prepend_action S initial actions tail⟩
  have h := prepend_state S initial actions tail 0
  simpa only [Nat.add_zero, tail.zero] using h ▸ success

end Connection.Execution

end
