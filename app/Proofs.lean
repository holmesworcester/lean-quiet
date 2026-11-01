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
import engine.wire.WorldLaws
import engine.sync.StoreEvolution
import engine.sync.SimLaws
import engine.wire.Loop
import engine.wire.EgressLaws
import engine.sync.SharedLog
import engine.wire.CloseLaws
import engine.wire.NodeUniqueLaws

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
open Engine Engine.Sync

/-- **Both ends of a running connection hold one session**
(`established_agrees` at the running keys, `sodium`): the suite's
correctness is the crypto trust file's (`Noise.suite_good`), so no
premise about the suite is left but the crates'. -/
theorem established_agrees_sodium (t : Trust.NativeCrypto)
    {oR oI : Op} {r m2 to frm m1 ofR ofI pkR pkI f e skR skI : B}
    {cidR cR pR hR sR kR cidI cI pI hI sI kI : B}
    (hto : to = sodium.suite.pub skR) (hfrm : frm = sodium.suite.pub skI) (hne : to ≠ frm)
    (hRc : check sodium oR .established [.inr (.connection r m2), .inr (.request to frm m1),
      .inr (.eph ofR pkR f), .inl (.endpoint to skR)] = some (.established cidR cR pR hR sR kR false))
    (hIc : check sodium oI .established [.inr (.connection r m2), .inr (.request to frm m1),
      .inr (.eph ofI pkI e), .inl (.endpoint frm skI)] = some (.established cidI cI pI hI sI kI true)) :
    hR = hI ∧ cR = cI ∧ sR = kI ∧ kR = sI ∧ pR = frm ∧ pI = to :=
  established_agrees sodium (Noise.suite_good t) hto hfrm hne hRc hIc

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

theorem openSessions_state (s : DB F) :
    ((openSessions : Model F (List (Id × B × Bool × B × Nat))).run s).2 = s := by
  simp only [openSessions, Model.run_bind]
  rw [allSessions_state]
  exact (carrying_mem _ s ((.empty, .empty, false, .empty, 0))).2

/-- A session `sessionOf` places is an established fact's, under its id. -/
theorem sessionOf_some (f : Fact) (s : DB F) {e : Id × B × Bool × B × Nat}
    (h : ((sessionOf f : Model F _).run s).1 = some e) :
    ∃ c p hh sk rk d, f = .established e.1 c p hh sk rk d := by
  match f, h with
  | .established cid c peer hh sk rk dialer, h =>
    cases dialer <;>
    · simp only [sessionOf, Bool.false_eq_true, ite_false, ite_true, Model.run_bind, Model.run_pure] at h
      generalize ((arrival _ : Model F (Option (B × Nat))).run _).1 = a at h
      cases a with
      | none => cases h
      | some at_ =>
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        exact ⟨_, _, _, _, _, _, rfl⟩
  | .ofEph _, h | .ofRequest _, h | .ofOpened _, h | .ofConnection _, h
  | .ofSend _, h | .ofRecv _, h | .ofGiven _, h => cases h

theorem mem_sessionsOf : ∀ (rs : List (Id × Fact)) (s : DB F) (e : Id × B × Bool × B × Nat),
    e ∈ ((sessionsOf rs : Model F (List (Id × B × Bool × B × Nat))).run s).1 →
      ∃ y c p hh sk rk d, (y, Fact.established e.1 c p hh sk rk d) ∈ rs
  | [], _, _, h => by cases h
  | (y, f) :: t, s, e, h => by
    simp only [sessionsOf, Model.run_bind, Model.run_pure] at h
    rw [sessionOf_state] at h
    cases hf : ((sessionOf f : Model F _).run s).1 with
    | none =>
      rw [hf] at h
      obtain ⟨y', c, p, hh, sk, rk, d, hm⟩ := mem_sessionsOf t s e h
      exact ⟨y', c, p, hh, sk, rk, d, List.mem_cons_of_mem _ hm⟩
    | some e' =>
      rw [hf] at h
      rcases List.mem_cons.1 h with rfl | h
      · obtain ⟨c, p, hh, sk, rk, d, rfl⟩ := sessionOf_some f s hf
        exact ⟨y, c, p, hh, sk, rk, d, List.mem_cons_self ..⟩
      · obtain ⟨y', c, p, hh, sk, rk, d, hm⟩ := mem_sessionsOf t s e h
        exact ⟨y', c, p, hh, sk, rk, d, List.mem_cons_of_mem _ hm⟩

/-- Every session `allSessions` places is an established fact the store
lists. -/
theorem allSessions_established (s : DB F) {e : Id × B × Bool × B × Nat}
    (he : e ∈ ((allSessions : Model F (List (Id × B × Bool × B × Nat))).run s).1) :
    ∃ y c p hh sk rk d, (y, Fact.established e.1 c p hh sk rk d) ∈ ((rows established.all [] : Model F _).run s).1 := by
  simp only [allSessions, Model.run_bind, Model.run_pure, List.mem_reverse] at he
  exact mem_sessionsOf _ s e he

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
    obtain ⟨y, c, p, hh, sk, rk, d, hy⟩ := allSessions_established s he
    simp only [retired, Model.run_bind, Model.run_pure]
    rw [openSessions_state, List.mem_filterMap]
    refine ⟨_, hy, ?_⟩
    have : (((openSessions : Model F _).run s).1.any fun x => decide (x.1 = e.1)) = false := by
      rw [List.any_eq_false]
      intro x hx hb
      exact hopen x hx (of_decide_eq_true hb)
    simp only [this, Bool.false_eq_true, ite_false]

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

/-- `dialOne` sends the same request to every listed hint on each retry. -/
theorem dialOne_sends_mem (K : Keys) (listen pk sk : B) (s : DB F) {c inviter hint target : B} {hs : List B}
    {req : Id} {nm d : B} {n : Nat} {a : Id} {waiting : Bool}
    (hm : ((Community.mine c).liftL : View F _).eval s = some (d, a))
    (hw : waiting = decide ((Engine.eval s (Community.admission.byDevice.query [c, d]
      (limit := some 0))).total = 0))
    (hskip : waiting = false → ((connectedTo inviter : Model F Bool).run s).1 = false)
    (hu : Unanswered K listen s pk sk c inviter req waiting)
    (ht : target ∈ hint :: hs) :
    ∃ ro, Send.op target ro ∈
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
      rw [hro]; exact ⟨ro, List.mem_map_of_mem ht⟩
    | none =>
      obtain ⟨jr, hjr, hop⟩ := hu
      simp only [Model.run_bind, run_getOp]
      rw [hjr]
      obtain ⟨ro, hro⟩ := Option.isSome_iff_exists.1 (hop ((Fresh.fresh : Model F B).run s).1)
      simp only [Model.run_bind, Model.run_pure]
      rw [hro]
      exact ⟨ro, List.mem_append_right _ (List.mem_map_of_mem ht)⟩
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
      rw [hro]; exact ⟨ro, List.mem_map_of_mem ht⟩
    | none =>
      obtain ⟨jr, hjr, hop⟩ := hu
      simp only [Model.run_pure, Bool.false_eq_true, ite_false, Model.run_bind, run_getOp]
      rw [hjr]
      obtain ⟨ro, hro⟩ := Option.isSome_iff_exists.1 (hop ((Fresh.fresh : Model F B).run s).1)
      simp only [Model.run_bind, Model.run_pure]
      rw [hro]
      exact ⟨ro, List.mem_append_right _ (List.mem_map_of_mem ht)⟩

/-- The former first-hint guarantee is a special case of all-hint retry. -/
theorem dialOne_sends (K : Keys) (listen pk sk : B) (s : DB F) {c inviter hint : B} {hs : List B}
    {req : Id} {nm d : B} {n : Nat} {a : Id} {waiting : Bool}
    (hm : ((Community.mine c).liftL : View F _).eval s = some (d, a))
    (hw : waiting = decide ((Engine.eval s (Community.admission.byDevice.query [c, d]
      (limit := some 0))).total = 0))
    (hskip : waiting = false → ((connectedTo inviter : Model F Bool).run s).1 = false)
    (hu : Unanswered K listen s pk sk c inviter req waiting) :
    ∃ ro, Send.op hint ro ∈
      ((dialOne K listen pk sk (.joining c inviter (hint :: hs) req nm d n) : Model F (List Op)).run s).1 :=
  dialOne_sends_mem K listen pk sk s hm hw hskip hu (by simp)

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

/-- Every retry-eligible tick covers every advertised hint, independently
of the timestamp residues at which ticks happen. Transport admission is a
separate bounded FIFO obligation; this law does not assume a hint succeeds. -/
theorem rejoin_dials_each (K : Keys) (listen : B) (now : Nat) (hfr : FreshPure) (s : DB F)
    {pk sk : B} {x : Id} {more : List (B × B × Id)}
    (hk : ((endpoints : Model F _).run s).1 = (pk, sk, x) :: more)
    {p : Pos} {c inviter hint target : B} {hs : List B} {req : Id} {nm d : B} {n : Nat} {a : Id}
    (hj : (p, Community.Fact.joining c inviter (hint :: hs) req nm d n) ∈
      (Engine.eval s (Community.joining.all.query [])).lefts)
    (hm : ((Community.mine c).liftL : View F _).eval s = some (d, a))
    (hna : (Engine.eval s (Community.admission.byDevice.query [c, d] (limit := some 0))).total = 0)
    (hu : Unanswered K listen s pk sk c inviter req true)
    (ht : target ∈ hint :: hs) :
    ∃ ro, Send.op target ro ∈ ((dial K listen now : Model F (List Op)).run s).1 := by
  obtain ⟨ro, hro⟩ := dialOne_sends_mem K listen pk sk s hm (by simp [hna]) (fun h => by cases h) hu ht
  refine ⟨ro, ?_⟩
  simp only [dial, Model.run_bind]
  have hs0 : ((endpoints : Model F _).run s).2 = s := rfl
  rw [hk, hs0]
  simp only [List.head?_cons, Model.run_bind]
  exact dialAll_mem hfr K listen pk sk _ s p _ _ hj hro

theorem reconnect_dials_each (K : Keys) (listen : B) (now : Nat) (hfr : FreshPure) (s : DB F)
    {pk sk : B} {x : Id} {more : List (B × B × Id)}
    (hk : ((endpoints : Model F _).run s).1 = (pk, sk, x) :: more)
    {p : Pos} {c inviter hint target : B} {hs : List B} {req : Id} {nm d : B} {n : Nat} {a : Id}
    (hj : (p, Community.Fact.joining c inviter (hint :: hs) req nm d n) ∈
      (Engine.eval s (Community.joining.all.query [])).lefts)
    (hm : ((Community.mine c).liftL : View F _).eval s = some (d, a))
    (had : (Engine.eval s (Community.admission.byDevice.query [c, d] (limit := some 0))).total ≠ 0)
    (hc : ((connectedTo inviter : Model F Bool).run s).1 = false)
    (hu : Unanswered K listen s pk sk c inviter req false)
    (ht : target ∈ hint :: hs) :
    ∃ ro, Send.op target ro ∈ ((dial K listen now : Model F (List Op)).run s).1 := by
  obtain ⟨ro, hro⟩ := dialOne_sends_mem K listen pk sk s hm (by simp [had]) (fun _ => hc) hu ht
  refine ⟨ro, ?_⟩
  simp only [dial, Model.run_bind]
  have hs0 : ((endpoints : Model F _).run s).2 = s := rfl
  rw [hk, hs0]
  simp only [List.head?_cons, Model.run_bind]
  exact dialAll_mem hfr K listen pk sk _ s p _ _ hj hro
end
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
  draft is unchanged, and so is all else but the pending presentation
  obligations, which leaving chat cancels. `back_open_all` is the same
  for the switcher too, whose opening also composes the backdrop drawn
  behind it; `open_keeps_backdrop`: opening any other page keeps that
  backdrop.
- `shipped_back_open_fails`: the negative control, `openSt` as 566e566
  shipped it (opening any page emptied the switcher's backdrop), breaks
  `back_open`. This law caught it: see docs/CAUGHT.md.
- `back_root`: at a root, back keeps the page; non-chat presentation demand is cleared.
- `back_switch`: after a switch, any number of backs stays on the new
  community's home: back never reaches the community before.
- `draft_open`, `draft_back`: no navigation step changes the composer's
  draft, its selection or its photos.
- `inv_open`, `inv_back`, `inv_switch`: no page is twice in the page and
  its stack; so (`depth`) after any open, fewer backs than there are
  pages reach a root.
-/

namespace NavLaws
open App

theorem nav_open (p : PageId) (s : St) : (openSt p s).nav = Nav.go p s.nav := rfl

theorem nav_back (s : St) : (backSt s).nav = Nav.back s.nav := rfl

theorem nav_switch (a : Engine.Id) (s : St) : (switchSt a s).nav = Nav.reset PageId.home := rfl

/-- Back after opening any page, the switcher included: the state before,
but for what back clears and the backdrop opening the switcher composes
(drawn only on the switcher). Both navigation calls revoke the old editor
epoch. -/
theorem back_open_all (p : PageId) (s : St) (hp : p ≠ s.page) (hs : p ∉ s.backStack) :
    backSt (openSt p s) =
      { s with
        editorEpoch := s.editorEpoch + 1 + 1, field := "", refusal := none, pageKey := none, pageScrollStarted := false,
        switcherBackdrop := (openSt p s).switcherBackdrop, ownSends := {}, presenting := none } := by
  have h := Nav.back_go p s.nav hp hs
  unfold backSt
  rw [nav_open, h]
  -- Name the backdrop, so neither `rfl` nor `simp` unfolds the switcher's composition.
  generalize hb : (openSt p s).switcherBackdrop = b
  have ho : openSt p s = { s.withNav (Nav.go p s.nav) with
      refusal := none, pageKey := none, pageScrollStarted := false, switcherBackdrop := b } := by
    rw [← hb]; rfl
  rw [ho]
  simp only [St.withNav, St.nav, Nav.go_page]
  by_cases hc : s.page = .chat
  · have hn : p ≠ .chat := by simpa [hc] using hp
    simp [hc, hn]
  · simp [hc]

/-- Opening any page but the switcher keeps the switcher's backdrop. -/
theorem open_keeps_backdrop (p : PageId) (s : St) (hw : p ≠ .switcher) :
    (openSt p s).switcherBackdrop = s.switcherBackdrop := by
  have hne : (p == PageId.switcher) = false := by simpa using hw
  simp only [openSt, hne]
  rfl

/-- **Back goes back.** -/
theorem back_open (p : PageId) (s : St) (hp : p ≠ s.page) (hs : p ∉ s.backStack) (hw : p ≠ .switcher) :
    backSt (openSt p s) = { s with editorEpoch := s.editorEpoch + 1 + 1, field := "", refusal := none, pageKey := none, pageScrollStarted := false, ownSends := {}, presenting := none } := by
  rw [back_open_all p s hp hs, open_keeps_backdrop p s hw]

/-- **Back at a root keeps the page**, while revoking the old editor epoch. -/
theorem back_root (s : St) (h : s.backStack = []) :
    backSt s = { s with
      editorEpoch := s.editorEpoch + 1, field := "", refusal := none, pageKey := none, pageScrollStarted := false,
      ownSends := if s.page == .chat then s.ownSends else {},
      presenting := if s.page == .chat then s.presenting else none } := by
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

/-- k presses of back are k Nav backs. -/
theorem backs_nav (k : Nat) (s : St) : (Nat.repeat backSt k s).nav = Nat.repeat Nav.back k s.nav := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show (backSt (Nat.repeat backSt k s)).nav = Nav.back (Nat.repeat Nav.back k s.nav)
    rw [nav_back, ih]

/-- **Back reaches a root** in fewer presses than there are pages
(`PageId.all`): after any open, the stack is shorter than that, and
pressing back once per stacked page leaves none under the shown one. -/
theorem depth (p : PageId) (s : St) (h : Nav.Inv s.nav) :
    (openSt p s).backStack.length < PageId.all.length ∧
      (Nat.repeat backSt (openSt p s).backStack.length (openSt p s)).backStack = [] := by
  obtain ⟨h1, h2⟩ := Nav.depth PageId.all all_pages (openSt p s).nav (inv_open p s h)
  refine ⟨h1, ?_⟩
  show (Nat.repeat backSt _ (openSt p s)).nav.stack = []
  rw [backs_nav]; exact h2

/-! ## Negative control: `openSt` as 566e566 shipped it

Opening any page but the switcher emptied the switcher's backdrop, so
switcher → gear (or Join, Create, Add members) → back drew the switcher
over the plain background instead of the dimmed screen behind it.
`back_open` stopped proving (its `rfl` timed out trying to equate the
composed backdrop with the old one), which is how it was found. Kept so
the law stays able to tell. -/

/-- `openSt` at 566e566. A mutant: nothing runs it. -/
def openStShipped (p : PageId) (s : St) : St :=
  let backdrop := if p == .switcher then
    match s.lastDisplay with
    | some (words, rows, top, bot) => Surface.compose words s.Hs s.bgRow rows top bot
    | none => #[]
    else #[]
  { s.withNav (Nav.go p s.nav) with
    refusal := none, pageKey := none, pageScrollStarted := false, switcherBackdrop := backdrop }

/-- The shipped `openSt` breaks `back_open` from every state that holds a
switcher backdrop, whichever other page is opened. -/
theorem shipped_back_open_fails (p : PageId) (s : St) (hw : p ≠ .switcher)
    (hb : s.switcherBackdrop ≠ #[]) :
    backSt (openStShipped p s) ≠
      { s with editorEpoch := s.editorEpoch + 1 + 1, field := "", refusal := none, pageKey := none, pageScrollStarted := false, ownSends := {}, presenting := none } := by
  intro h
  have h2 := congrArg St.switcherBackdrop h
  have hne : (p == PageId.switcher) = false := by simpa using hw
  simp only [backSt, openStShipped, hne, St.withNav] at h2
  exact hb h2.symm

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

/-- `textColor`, the ink the glyph painter picks for `wanted` over a
ground row, meets 4.5:1 against that row's pixel at x, for every RGB
ground. This is the selector only, not the painted pixel: a stroke with
`exactInk` keeps its ink and skips it, a stroke with a non-empty `under`
row is blended over `under` while its ink was chosen against `ground`,
and antialiased coverage blends the ink with what is below
(`Stroke.color`). None of those is covered here. -/
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
  /-- Durable per-peer retry metadata, kept across disposable sessions. -/
  retries : Id → Option Sweep := fun _ => none

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
  dependents x := lift (Store.dependents x)
  undecide x := lift (Store.undecide x)
  deleteOp x := lift (Store.deleteOp x)
  countOps := lift Store.countOps

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
  { fam := family
    cfg := S.cfg
    hooks := Connection.hooks family sodium (S.addr side)
    room := S.room side
    catalog := some {
      ceiling := lift (Catalog.held family).ceiling
      read := fun seq => lift ((Catalog.held family).read seq) }
    retryStore := some {
      load := fun peer s => ((s.retries peer).getD {}, s)
      save := fun peer cursor s => ((), { s with retries := fun p => if p = peer then some cursor else s.retries p }) } }

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

section

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

/-- `sessionKeys_reads` (app/connection/Proofs.lean), as `Reads`. -/
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

theorem retryKey_reads (cid : Id) : Reads (retryKey cid : HeldM F (Option Id)) := by
  unfold retryKey; keeps [rows_reads]

/-- **The Connection family's hooks only read the store.** Run on held
data, each leaves the store as it is: what the family would store it
returns as ops for the node to write, and what it would forget it
returns as ids for the node to purge. -/
theorem hooks_reads [Fresh (HeldM F)] (hfr : Reads (Fresh.fresh : HeldM F ByteArray))
    (fam : Family F) (K : Keys) (listen : B) :
    let k := (hooks fam K listen : Hooks F (HeldM F))
    (∀ cid, Reads (k.rooms cid)) ∧ (∀ via a o t, Reads (k.recv via a o t)) ∧ Reads k.outbox ∧
    (∀ cid, Reads (k.closing cid)) ∧ Reads k.retired ∧ Reads k.react ∧ (∀ t, Reads (k.dial t)) ∧
    Reads k.established ∧ (∀ cid b, Reads (k.sealFor cid b)) ∧ (∀ b, Reads (k.openFrame b)) ∧ (∀ cid, Reads (k.retryKey cid)) :=
  ⟨rooms_reads, onArrival_reads, outbox_reads, closing_reads, retired_reads, react_reads hfr fam K,
    dial_reads hfr K listen, sessions_reads, sealFor_reads hfr K, openFrame_reads K, retryKey_reads⟩

end Connection

end

section

/- Production hooks with an advancing entropy tape. ReadsHeld preserves
only the Held database/history; fresh draws are allowed to change cursor. -/

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

/-- `sessionKeys_reads` (app/connection/Proofs.lean), as `ReadsHeld`. -/
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

/-- `retired`, as this base has it (another branch reads the
established facts themselves: redo this lemma there). -/
theorem retired_reads : ReadsHeld (retired : M (List Id)) := by
  unfold retired; readsHeld [allSessions_reads, openSessions_reads, rows_reads]

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
    dial_reads hfr K listen, sessions_reads, sealFor_reads hfr K, openFrame_tape_reads K, retryKey_reads⟩

end Connection.Execution

end

section

/-
Positive progress through the connection code. Safety laws say that an
answer is authorized if one exists; these laws establish that a ready request
actually gets an answer and that an honest Noise exchange is accepted by the
real opened/established validators. Store/transport scheduling is separate.
-/

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
    Request.check ⟨(K.suite.pub x.responder), (K.suite.pub x.initiator), x.message1⟩ =
      some ⟨(K.suite.pub x.responder), (K.suite.pub x.initiator), x.message1⟩ := by
  simp [Request.check, hr, hi, h.distinct, hm]

theorem reply_accepts (hm : 48 ≤ x.message2.size) :
    Reply.check x.connection ⟨x.message2⟩ ⟨(K.suite.pub x.responder), (K.suite.pub x.initiator), x.message1⟩ =
      some ⟨x.request.id, x.message2⟩ := by
  simp [Reply.check, hm, connection, mkOp, Op.make]

/-- Opening the actual request recovers its community, address and payload. -/
theorem opened_accepts (h : x.Correct) (endpoint : Id) :
    Opened.check K (Opened.op x.request.id endpoint) {} ⟨(K.suite.pub x.responder), (K.suite.pub x.initiator), x.message1⟩
      ⟨(K.suite.pub x.responder), x.responder⟩ =
      some ⟨x.request.id, x.community, (K.suite.pub x.initiator), x.address, x.introduction⟩ := by
  simp [Opened.check, Opened.op, h.read1, payload, decode_encode, mkOp, Op.make]

/-- The responder's local established op validates; its existence is not a
premise. This is the op answerOne writes alongside the actual reply. -/
theorem responder_accepts (h : x.Correct) (eph endpoint : Id) :
    Established.check K (Established.op x.connection.id x.request.id eph endpoint) {}
      ⟨x.request.id, x.message2⟩ ⟨(K.suite.pub x.responder), (K.suite.pub x.initiator), x.message1⟩
      ⟨x.connection.id, K.suite.pub x.ephemeralR, x.ephemeralR⟩ ⟨(K.suite.pub x.responder), x.responder⟩ =
      some ⟨x.connection.id, x.community, (K.suite.pub x.initiator),
        x.sessionR.h, x.sessionR.send.k, x.sessionR.recv.k, false⟩ := by
  simp [Established.check, Established.op, h.read1, h.write2, payload, decode_encode, mkOp, Op.make]

/-- Receiving the honest answer produces a valid local established op at
the initiator as well. The two private keys must name different nodes. -/
theorem initiator_accepts (h : x.Correct) (eph endpoint : Id) :
    Established.check K (Established.op x.connection.id x.request.id eph endpoint) {}
      ⟨x.request.id, x.message2⟩ ⟨(K.suite.pub x.responder), (K.suite.pub x.initiator), x.message1⟩
      ⟨x.request.id, K.suite.pub x.ephemeralI, x.ephemeralI⟩ ⟨(K.suite.pub x.initiator), x.initiator⟩ =
      some ⟨x.connection.id, x.community, (K.suite.pub x.responder),
        x.sessionI.h, x.sessionI.send.k, x.sessionI.recv.k, true⟩ := by
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
      | ofOpened _ =>
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

end

section

/- The positive answer law with the production interpreter's advancing
entropy tape. This does not rely on FreshPure or repeat a secret whenever
the database is unchanged. Native entropy remains an external input. -/
namespace Connection.ProgressTape
open Engine Engine.Sync Codec Execution

theorem run_bind (a : M α) (f : α → M β) (s : Memory) :
    (a >>= f) s = f (a s).1 (a s).2 := rfl

theorem run_count (r : Rel Fact) (args : List B) (s : Memory) :
    (count r args : M Nat) s = ((Engine.eval s.held.db (r.query args (limit := some 0))).total, s) := rfl

theorem run_get (id : Id) (s : Memory) :
    (Store.getOp id : M (Option Op)) s = (s.held.db.ops id, s) := rfl

theorem run_view (v : View F α) (s : Memory) :
    (v.run : M α) s = (v.eval s.held.db, s) := by
  induction v with
  | pure a => rfl
  | list q k ih => exact ih (Engine.eval s.held.db q)

theorem run_arrivedFrom (id : Id) (s : Memory) :
    (arrivedFrom id : M (Option B)) s =
      (((arrivedFrom id : Model F (Option B)).run s.held.db).1, s) := rfl

theorem run_fresh (s : Memory) :
    (Fresh.fresh : M B) s = (s.entropy s.cursor, { s with cursor := s.cursor + 1 }) := rfl

/-- The actual answer handler consumes exactly its next entropy input and
constructs the answer from that value. All earlier and later tape values
are arbitrary. Store readiness is checked before that draw. -/
theorem answer_ready (K : Keys) (s : Memory) (eps : List (B × B × Id))
    (r c frm to frm' m1 sk epOp addr : B) (ro co : Op)
    (hcount : (Engine.eval s.held.db (connection.byRequest.query [r] (limit := some 0))).total = 0)
    (hro : s.held.db.ops r = some ro)
    (hb : (decode ro.body : Option Body) = some (.request to frm' m1))
    (hep : eps.find? (fun p => decide (p.1 = to)) = some (to, sk, epOp))
    (ht : ((trusts c to frm).liftL : View F Bool).eval s.held.db = true)
    (ha : ((arrivedFrom r : Model F (Option B)).run s.held.db).1 = some addr)
    (hc : Reply.op K r sk frm m1 (s.entropy s.cursor) = some co) :
    (answerOne K eps r c frm : M (List Op)) s =
      ([co, Eph.op (s.entropy s.cursor) co.id,
        Established.op co.id r (Eph.op (s.entropy s.cursor) co.id).id epOp,
        Send.op addr co], { s with cursor := s.cursor + 1 }) := by
  simp only [answerOne, run_bind, run_count, hcount, ne_eq, not_true_eq_false, ↓reduceIte,
    run_get, hro, hb, hep, run_view, ht, Bool.not_true, Bool.false_eq_true,
    run_arrivedFrom, ha]
  simp only [run_fresh, hc]
  rfl

end Connection.ProgressTape

end

section

/- Store effects of the actual Node event handlers, including production
hooks with advancing entropy, reactions, courier purges and session closes. -/

namespace Connection.Execution
open Engine Engine.Sync

/-- Only the store is constrained. In particular, entropy state can advance. -/
def GoesM (fam : Family F) {α} (p : M α) : Prop :=
  ∀ s, Moves fam s.held (p s).2.held

theorem ReadsHeld.goes {fam : Family F} {α} {p : M α} (h : ReadsHeld p) : GoesM fam p :=
  fun s => Moves.of_eq (h s).symm

namespace GoesM
theorem pure' (fam : Family F) {α} (a : α) : GoesM fam (pure a : M α) := fun _ => .refl _
theorem bind' {fam : Family F} {α β} {p : M α} {k : α → M β}
    (hp : GoesM fam p) (hk : ∀ a, GoesM fam (k a)) : GoesM fam (p >>= k) :=
  fun s => (hp s).trans (hk _ _)
theorem forIn' {fam : Family F} {α β} (l : List α) (b : β)
    {f : α → β → M (ForInStep β)} (hf : ∀ a b, GoesM fam (f a b)) :
    GoesM fam (forIn l b f) := by
  induction l generalizing b with
  | nil => exact pure' fam b
  | cons a t ih =>
    rw [List.forIn_cons]
    apply bind' (hf a b)
    intro r
    cases r with
    | done b => exact pure' fam b
    | yield b => exact ih b
theorem getOp' (fam : Family F) (i : Id) : GoesM fam (Store.getOp i : M _) :=
  (ReadsHeld.getOp' i).goes
theorem getStatus' (fam : Family F) (i : Id) : GoesM fam (Store.getStatus i : M _) :=
  (ReadsHeld.getStatus' i).goes
theorem turn' (fam : Family F) (ops : List Op) : GoesM fam (Turn.turn fam ops : M Unit) :=
  fun _ => .single (.turn _ _)
theorem purge' (fam : Family F) (ids : List Id) (scrub : Bool) :
    GoesM fam (Turn.purge fam ids scrub : M Unit) := fun _ => .single (.purge ids scrub _)
end GoesM

syntax "goesTape" "[" term,* "]" : tactic
macro_rules
  | `(tactic| goesTape [$ts,*]) => do
    let mut tac : Lean.TSyntax `tactic ← `(tactic| first | split | intro)
    for t in ts.getElems.reverse do
      tac ← `(tactic| first | with_reducible_and_instances apply $t | $tac:tactic)
    `(tactic| repeat' (first
      | dsimp only | with_reducible_and_instances apply GoesM.bind'
      | with_reducible_and_instances apply GoesM.pure' | with_reducible_and_instances apply GoesM.forIn'
      | with_reducible_and_instances apply GoesM.getOp' | with_reducible_and_instances apply GoesM.getStatus'
      | with_reducible_and_instances apply GoesM.turn' | with_reducible_and_instances apply GoesM.purge'
      | $tac:tactic))

namespace NodeTape

structure ReadOnly (x : Sync F M) : Prop where
  rooms : ∀ cid, ReadsHeld (x.hooks.rooms cid)
  recv : ∀ via a o t, ReadsHeld (x.hooks.recv via a o t)
  outbox : ReadsHeld x.hooks.outbox
  closing : ∀ cid, ReadsHeld (x.hooks.closing cid)
  retired : ReadsHeld x.hooks.retired
  react : ReadsHeld x.hooks.react
  dial : ∀ t, ReadsHeld (x.hooks.dial t)
  established : ReadsHeld x.hooks.established
  sealFor : ∀ cid b, ReadsHeld (x.hooks.sealFor cid b)
  openFrame : ∀ b, ReadsHeld (x.hooks.openFrame b)
  catalog : ∀ cat, x.catalog = some cat → ReadsHeld cat.ceiling ∧ ∀ i, ReadsHeld (cat.read i)
  retryKey : ∀ cid, ReadsHeld (x.hooks.retryKey cid)
  retryStore : ∀ store, x.retryStore = some store →
    (∀ peer, ReadsHeld (store.load peer)) ∧ (∀ peer cursor, ReadsHeld (store.save peer cursor))

/-- Discharges every hook premise for the actual advancing-tape interpreter. -/
theorem production_readOnly (S : Setup) (side : Side) : ReadOnly (S.sync side) := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11⟩ :=
    hooks_reads ReadsHeld.fresh family sodium (S.addr side)
  refine ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10, ?_, h11, ?_⟩
  · intro cat hcat
    cases hcat
    exact ⟨fun _ => rfl, fun _ _ => rfl⟩
  · intro store hstore
    cases hstore
    exact ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem ReadOnly.afterActs {x : Sync F M} (hr : ReadOnly x) (n : Engine.Sync.Node) (out : Acts) :
    ReadOnly (n.afterActs x out) :=
  ⟨hr.rooms, hr.recv, hr.outbox, hr.closing, hr.retired, hr.react, hr.dial,
    hr.established, hr.sealFor, hr.openFrame, hr.catalog, hr.retryKey, hr.retryStore⟩

theorem sweep_reads (cat : Catalog M) (hc : ReadsHeld cat.ceiling)
    (hr : ∀ i, ReadsHeld (cat.read i)) (cursor : Sweep) (shows : Op → Bool) (room : Nat) :
    ReadsHeld (Sweep.run (F := F) cat cursor shows room) := by
  unfold Sweep.run
  readsHeld [hc, hr]

theorem read_program {α} (p : Read α) : ReadsHeld (p.run (Store.getOp (F := F)) : M α) := by
  induction p with
  | done a => exact ReadsHeld.pure' a
  | get i next ih => exact ReadsHeld.bind' (ReadsHeld.getOp' i) ih

variable (fam : Family F) (cfg : Config)

theorem holdsIn_reads (r i : Id) : ReadsHeld (holdsIn fam r i : M Bool) := by
  unfold holdsIn; readsHeld []
theorem onHold_reads (c : Conn) (r : Id) (ids : List Id) :
    ReadsHeld (c.onHold fam cfg r ids : M Step) := by
  unfold Conn.onHold; readsHeld [holdsIn_reads]
theorem filed_reads (c : Conn) (ids : List Id) : ReadsHeld (c.filed fam cfg ids : M Step) := by
  unfold Conn.filed; readsHeld []
theorem closure_reads (r : Id) (fuel : Nat) : ∀ todo seen,
    ReadsHeld (closureOps fam r fuel todo seen : M (List Op)) := by
  induction fuel with
  | zero => intro todo seen; rw [closureOps_zero]; exact ReadsHeld.pure' _
  | succ n ih =>
    intro todo
    induction todo with
    | nil => intro seen; rw [closureOps_nil]; exact ReadsHeld.pure' _
    | cons y rest ihr =>
      intro seen
      rw [closureOps_cons]
      split
      · exact ihr seen
      · refine ReadsHeld.bind' (ReadsHeld.getOp' y) fun oo => ?_
        cases oo with
        | none => exact ih _ _
        | some o =>
          dsimp only
          split
          · exact ReadsHeld.bind' (ih _ _) fun _ => ReadsHeld.pure' _
          · exact ih _ _
theorem give_reads : ∀ (l : List (Id × Id)) (c : Conn), ReadsHeld (c.give fam cfg l : M Step)
  | [], _ => ReadsHeld.pure' _
  | (r,x) :: rest, c => by
    unfold Conn.give
    split
    · exact give_reads rest c
    · exact ReadsHeld.bind' (closure_reads fam r _ _ _) fun _ =>
        ReadsHeld.bind' (give_reads rest _) fun _ => ReadsHeld.pure' _
theorem filedGive_reads (c : Conn) (ids : List Id) : ReadsHeld (c.filedGive fam cfg ids : M Step) := by
  unfold Conn.filedGive Conn.notify; readsHeld [give_reads, filed_reads]
theorem walkN_reads : ∀ budget (c : Conn) offer,
    ReadsHeld (c.walkN fam cfg offer budget : M (Conn × List (Id × Id)))
  | 0, _, _ => ReadsHeld.pure' _
  | budget + 1, c, offer => by
    unfold Conn.walkN
    readsHeld [walkN_reads budget]
theorem tickGive_reads (ix : Index) (c : Conn) (now : Nat) :
    ReadsHeld (c.tickGive fam cfg ix now : M Step) := by
  unfold Conn.tickGive Conn.notify Conn.tick Conn.work Conn.walk
  readsHeld [give_reads, walkN_reads]
theorem recv_reads (ix : Index) (c : Conn) (bytes : ByteArray) (now : Nat) :
    ReadsHeld (Conn.recv fam cfg ix c bytes now : M Step) := by
  unfold Conn.recv; readsHeld [onHold_reads]
theorem serveOwed_reads (c : Conn) (budget : Nat) (first : List Id) :
    ReadsHeld (c.serveOwed fam cfg budget first : M (Conn × List Op × List Op)) := by
  unfold Conn.serveOwed; readsHeld [read_program]

variable {fam cfg}
variable (x : Sync F M) (hr : ReadOnly x)

theorem write_goes (n : Engine.Sync.Node) (ops : List Op) : GoesM x.fam (n.write x ops) := by
  unfold Node.write; goesTape []
theorem put_goes (n : Engine.Sync.Node) (ops : List Op) (mine : Bool) : GoesM x.fam (n.put x ops mine) :=
  write_goes x n _
theorem recordGiven_goes (n : Engine.Sync.Node) (st : List (Id × Id)) : GoesM x.fam (n.recordGiven x st) := by
  unfold Node.recordGiven; goesTape [put_goes]
include hr

theorem refresh_reads (cid : Id) (c : Conn) : ReadsHeld (Node.refresh x cid c) := by
  unfold Node.refresh; readsHeld [hr.rooms]
theorem fanout_goes (n : Engine.Sync.Node) (ids : List Id) : GoesM x.fam (n.fanout x ids) := by
  unfold Node.fanout
  goesTape [fun cid c => (refresh_reads x hr cid c).goes,
    fun c ids => (filedGive_reads x.fam x.cfg c ids).goes, recordGiven_goes]
theorem store_goes (n : Engine.Sync.Node) (ops : List Op) (mine : Bool) : GoesM x.fam (n.store x ops mine) := by
  unfold Node.store
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  goesTape [put_goes, fanout_goes x hr, hr.react.goes]
theorem open_goes (n : Engine.Sync.Node) (cid : Id) (addr : ByteArray) (dialer : Bool) (now : Nat) :
    GoesM x.fam (n.open x cid addr dialer now) := by
  unfold Node.open; goesTape [fun cid => (hr.rooms cid).goes]
theorem follow_goes (n : Engine.Sync.Node) (now : Nat) : GoesM x.fam (n.follow x now) := by
  unfold Node.follow; goesTape [hr.established.goes, open_goes x hr]
omit hr in
theorem effectsPurge_goes (ids : List Id) (scrub : Bool) : GoesM x.fam (Effects.purge x ids scrub) := by
  unfold Effects.purge; goesTape []
theorem flush_goes (n : Engine.Sync.Node) (out : Acts) : GoesM x.fam (n.flush x out) := by
  unfold Node.flush; goesTape [hr.outbox.goes, effectsPurge_goes]
theorem seal_goes (n : Engine.Sync.Node) (out : Acts) : GoesM x.fam (n.seal x out) := by
  unfold Node.seal; goesTape [fun cid b => (hr.sealFor cid b).goes]
theorem sealRetries_goes (n : Engine.Sync.Node) (retries : List RetryOffer) :
    GoesM x.fam (n.sealRetries x retries) := by
  unfold Node.sealRetries; goesTape [seal_goes x hr]
theorem endSession_goes (cid : Id) : GoesM x.fam (Node.endSession x cid) := by
  unfold Node.endSession; goesTape [fun cid => (hr.closing cid).goes, effectsPurge_goes]
theorem finish_goes (n : Engine.Sync.Node) (out : Acts) (now : Nat) : GoesM x.fam (n.finish x out now) := by
  unfold Node.finish
  goesTape [follow_goes x hr, flush_goes x hr, hr.retired.goes, seal_goes x hr,
    sealRetries_goes x hr, endSession_goes x hr]
theorem onClose_goes (n : Engine.Sync.Node) (addr : ByteArray) (now : Nat) : GoesM x.fam (n.onClose x addr now) := by
  unfold Node.onClose; goesTape [finish_goes x hr]
theorem apply_goes (n : Engine.Sync.Node) (cid : Id) (st : Step) (now : Nat) :
    GoesM x.fam (n.apply x cid st now) := by
  unfold Node.apply
  goesTape [recordGiven_goes, store_goes x hr, fun via a o t => (hr.recv via a o t).goes]
theorem serve_goes (n : Engine.Sync.Node) (cid : Id) (now : Nat) : GoesM x.fam (n.serveOwed x cid now) := by
  unfold Node.serveOwed
  goesTape [fun cid c => (refresh_reads x hr cid c).goes,
    fun c budget first => (serveOwed_reads x.fam x.cfg c budget first).goes]
theorem sweep_goes (n : Engine.Sync.Node) (cid : Id) : GoesM x.fam (n.sweep x cid) := by
  cases hcat : x.catalog with
  | none => simp only [Node.sweep, hcat]; exact GoesM.pure' x.fam _
  | some cat =>
    obtain ⟨hc, hrd⟩ := hr.catalog cat hcat
    cases hs : x.retryStore with
    | none =>
      simp only [Node.sweep, hcat, hs]
      goesTape [fun cid c => (refresh_reads x hr cid c).goes,
        fun cid => (hr.retryKey cid).goes,
        fun cursor shows room => (sweep_reads cat hc hrd cursor shows room).goes]
    | some store =>
      obtain ⟨hl, hsave⟩ := hr.retryStore store hs
      simp only [Node.sweep, hcat, hs]
      goesTape [fun cid c => (refresh_reads x hr cid c).goes,
        fun cid => (hr.retryKey cid).goes, fun peer => (hl peer).goes,
        fun peer cursor => (hsave peer cursor).goes,
        fun cursor shows room => (sweep_reads cat hc hrd cursor shows room).goes]

theorem sweep_afterActs_goes (n : Engine.Sync.Node) (out : Acts) (cid : Id) :
    GoesM x.fam (n.sweep (n.afterActs x out) cid) :=
  sweep_goes (n.afterActs x out) (hr.afterActs n out) n cid

theorem serve_afterActs_goes (n : Engine.Sync.Node) (out : Acts) (cid : Id) (now : Nat) :
    GoesM x.fam (n.serveOwed (n.afterActs x out) cid now) :=
  serve_goes (n.afterActs x out) (hr.afterActs n out) n cid now

theorem onSealed_goes (n : Engine.Sync.Node) (addr : ByteArray) (opened : Option (Id × ByteArray)) (now : Nat) :
    GoesM x.fam (n.onSealed x addr opened now) := by
  unfold Node.onSealed
  goesTape [fun cid c => (refresh_reads x hr cid c).goes,
    fun ix c bytes now => (recv_reads x.fam x.cfg ix c bytes now).goes,
    apply_goes x hr, serve_goes x hr, finish_goes x hr]
theorem onFrame_goes (n : Engine.Sync.Node) (addr bytes : ByteArray) (now : Nat) :
    GoesM x.fam (n.onFrame x addr bytes now) := by
  unfold Node.onFrame
  goesTape [write_goes, store_goes x hr, fun via a o t => (hr.recv via a o t).goes,
    finish_goes x hr, fun b => (hr.openFrame b).goes, onSealed_goes x hr]
theorem onTick_goes (n : Engine.Sync.Node) (now : Nat) : GoesM x.fam (n.onTick x now) := by
  unfold Node.onTick Node.onTickReserved Node.onTickDirect Node.sweepAll
  goesTape [fun t => (hr.dial t).goes, store_goes x hr,
    fun cid c => (refresh_reads x hr cid c).goes,
    fun ix c now => (tickGive_reads x.fam x.cfg ix c now).goes,
    apply_goes x hr,
    sweep_goes x hr, sweep_afterActs_goes x hr,
    serve_afterActs_goes x hr,
    finish_goes x hr]
theorem onWrite_goes (n : Engine.Sync.Node) (ops : List Op) (now : Nat) : GoesM x.fam (n.onWrite x ops now) := by
  unfold Node.onWrite; goesTape [store_goes x hr, finish_goes x hr]

/-- Every full event handler uses only actual turn/purge effects, including
the hooks' reactions and the common finish path. -/
theorem step_goes (n : Engine.Sync.Node) (input : Node.Input) (now : Nat) :
    GoesM x.fam (n.step x input now) := by
  cases input with
  | write ops => exact onWrite_goes x hr n ops now
  | frame addr bytes => exact onFrame_goes x hr n addr bytes now
  | tick => exact onTick_goes x hr n now
  | close addr => exact onClose_goes x hr n addr now

end NodeTape

/-- Production hooks, the actual dispatch, every input, arbitrary entropy. -/
theorem production_step_moves (S : Setup) (side : Side) (n : Engine.Sync.Node)
    (input : Node.Input) (now : Nat) (s : Memory) :
    Moves family s.held ((n.step (S.sync side) input now) s).2.held :=
  NodeTape.step_goes (S.sync side) (NodeTape.production_readOnly S side) n input now s

theorem production_step_retains (S : Setup) (side : Side) (n : Engine.Sync.Node)
    (input : Node.Input) (now : Nat) (s : Memory) {i : Id} {o : Op}
    (ho : s.held.db.ops i = some o) (hs : (family.room o).isSome) :
    ((n.step (S.sync side) input now) s).2.held.db.ops i = some o :=
  (production_step_moves S side n input now s).shared_retained ho hs

theorem production_step_reachable (S : Setup) (side : Side) (n : Engine.Sync.Node)
    (input : Node.Input) (now : Nat) (s : Memory) (hr : s.held.Reachable family) :
    (((n.step (S.sync side) input now) s).2.held).Reachable family :=
  (production_step_moves S side n input now s).store_reachable hr

/-- Finite settling of this call's validation queue, not a uniform bound on
work per event: the proven runtime budget depends on stored history size. -/
theorem production_step_settled (S : Setup) (side : Side) (n : Engine.Sync.Node)
    (input : Node.Input) (now : Nat) (s : Memory)
    (hr : s.held.Reachable family) (hq : s.held.db.queue = []) :
    ((n.step (S.sync side) input now) s).2.held.db.queue = [] :=
  (production_step_moves S side n input now s).store_settled hr hq

theorem world_run_moves (S : Setup) (w : World) (side target : Side) (queue : List Packet)
    (f : Engine.Sync.Node → M (Engine.Sync.Node × Effects)) (closed : Bool)
    (hf : ∀ n s, Moves family s.held (f n s).2.held) :
    Moves family (w.peer target).memory.held
      ((w.run S side queue f closed).peer target).memory.held := by
  cases side <;> cases target
  · exact hf _ _
  · exact .refl _
  · exact .refl _
  · exact hf _ _

/-- Every environment action, including delivery, drops and two-sided close,
preserves the exact per-peer primitive-store transition relation. -/
theorem world_step_moves (S : Setup) (w : World) (a : Action) (target : Side) :
    Moves family (w.peer target).memory.held ((step S w a).peer target).memory.held := by
  have hp : ∀ (w : World) (side : Side) (queue : List Packet) (input : Node.Input) (closed : Bool),
      Moves family (w.peer target).memory.held
        ((w.run S side queue (fun n => n.step (S.sync side) input w.now) closed).peer target).memory.held :=
    fun w side queue input closed => world_run_moves S w side target queue _ closed
      (fun n s => production_step_moves S side n input w.now s)
  have time : ∀ w' : World, ({ w' with now := w.now + 1 }.peer target).memory.held =
      (w'.peer target).memory.held := by intro w'; cases target <;> rfl
  unfold step
  rw [time]
  cases a with
  | tick side => exact hp w side w.net .tick false
  | write side ops => exact hp w side w.net (.write ops) false
  | idle => exact .refl _
  | drop => cases target <;> exact .refl _
  | close =>
    have ha := world_run_moves S w .a target []
      (fun n => n.onClose (S.sync .a) (S.addr .b) w.now) true
      (NodeTape.onClose_goes (S.sync .a) (NodeTape.production_readOnly S .a) · (S.addr .b) w.now)
    let wa := w.run S .a [] (fun n => n.onClose (S.sync .a) (S.addr .b) w.now) true
    have hb := world_run_moves S wa .b target wa.net
      (fun n => n.onClose (S.sync .b) (S.addr .a) w.now) true
      (NodeTape.onClose_goes (S.sync .b) (NodeTape.production_readOnly S .b) · (S.addr .a) w.now)
    exact ha.trans hb
  | deliver =>
    cases hnet : w.net with
    | nil => simpa only [World.deliver, hnet] using (Moves.refl (fam := family) (w.peer target).memory.held)
    | cons p rest =>
      by_cases ha : p.dst = S.addr .a
      · simpa only [World.deliver, hnet, ite_eq_left ha, Node.step] using hp w .a rest (.frame p.src p.bytes) false
      · by_cases hb : p.dst = S.addr .b
        · simpa only [World.deliver, hnet, ite_eq_right ha, ite_eq_left hb, Node.step] using hp w .b rest (.frame p.src p.bytes) false
        · simp only [World.deliver, hnet, ite_eq_right ha, ite_eq_right hb]
          cases target <;> exact .refl _

theorem world_trace_moves (S : Setup) (w : World) (actions : List Action) (target : Side) :
    Moves family (w.peer target).memory.held
      ((trace S w actions).peer target).memory.held := by
  induction actions generalizing w with
  | nil => exact .refl _
  | cons a rest ih => exact (world_step_moves S w a target).trans (ih (step S w a))

/-- Arbitrary full production-event prefixes remain reachable and settled.
The schedule need not be fair; entropy can differ at every fresh draw. -/
theorem empty_trace_store (S : Setup) (ea eb : Nat → ByteArray)
    (actions : List Action) (target : Side) :
    let h := ((trace S (empty ea eb) actions).peer target).memory.held
    h.Reachable family ∧ h.db.queue = [] := by
  have hm := world_trace_moves S (empty ea eb) actions target
  have he : ((empty ea eb).peer target).memory.held = ({} : Held F) := by cases target <;> rfl
  rw [he] at hm
  exact ⟨hm.store_reachable (held_empty_reachable family),
    hm.store_settled (held_empty_reachable family) rfl⟩

/-- The byte-retention statement applies to every execution, not only a
chosen fair schedule. It does not claim an invalid op becomes valid. -/
theorem Run.shared_retained {S initial} (r : Run S initial) (target : Side)
    {n k : Nat} (hnk : n ≤ k) {i : Id} {o : Op}
    (ho : ((r.state n).peer target).memory.held.db.ops i = some o)
    (hs : (family.room o).isSome) :
    ((r.state k).peer target).memory.held.db.ops i = some o := by
  induction hnk with
  | refl => exact ho
  | @step k _ ih =>
    rw [r.next k]
    exact (world_step_moves S (r.state k) (r.action k) target).shared_retained ih hs

end Connection.Execution

end

section

/-
**A removal reaches a live session**, over the node's entry points
(`Node.onFrame`, `onTick`, `onWrite`, `onClose`), run on held data with
the Connection family's own hooks.

`entry_fresh` (engine/wire/EgressLaws.lean): every payload an entry point
seals for a session is an op a connection step sent at a store on the
way, on the session's connection as that store gave its rooms. Here the
hooks are the family's (`hooks`), which only read (`hooks_reads`), and
whose rooms are `roomsV` read afresh (`rooms_held`). Each step, run on
held data, answers as on the model's tables (engine/sync/SimLaws.lean), so
the per-step law `removed_gets_only_notice` (and `serveOwed_shown` for a
session's queue) applies at that store: there, if this node is live in c
and the trust rule refuses the peer, the op is a sync wire op, an op of
another community, or in the requirement closure of a removal owed to
the peer (`sent_mayGo`).

So `removal_reaches_session`: once a removal is stored, every later step
on the session reads it, and nothing of c but the removal's notice goes
out, whatever entry point runs. The fresh bytes the hooks draw are
assumed to leave the store as it is (`hfr`), as the OS's do.
-/

namespace Connection
open Engine Engine.Sync Codec

/-- The family's hooks only read, so the node's laws of hooks that only
read hold of them. -/
theorem hooks_readOnly [Fresh (HeldM F)] (hfr : Reads (Fresh.fresh : HeldM F ByteArray))
    (x : Sync F (HeldM F)) (K : Keys) (listen : B) (hx : x.hooks = hooks x.fam K listen)
    (hc : ∀ cat, x.catalog = some cat → Reads cat.ceiling ∧ ∀ i, Reads (cat.read i))
    (hs : ∀ store, x.retryStore = some store →
      (∀ peer, Reads (store.load peer)) ∧ (∀ peer cursor, Reads (store.save peer cursor))) : ReadOnly x := by
  obtain ⟨fam, cfg, hk, room, catalog, retryStore, retryRoom, deferredRetries, tickReady⟩ := x
  simp only at hx
  subst hx
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hooks_reads hfr fam K listen
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, hc, h11, hs⟩

/-- What may go out on session cid at store h, as of community c: if
this node is live in c and the trust rule refuses cid's peer, only a sync
wire op, an op of another community, or an op in the requirement
closure of a removal owed to the peer (`NoticeOnly`). -/
def MayGo (fam : Family F) (h : Held F) (cid c : B) (o : Op) : Prop :=
  LiveIn h.db c → Refused h.db cid c → NoticeOnly fam h.db cid c o

/-- **Each fresh step's send may go** (`sent_mayGo`): every op a
connection step sends, run where the node runs it, on the connection as
the store gives its rooms, is one `MayGo` allows at that store. -/
theorem sent_mayGo [Fresh (HeldM F)] (x : Sync F (HeldM F)) (K : Keys) (listen : B) (hx : x.hooks = hooks x.fam K listen)
    {h : Held F} {cid : Id} {o : Op} (hs : Sent x h cid o) (c : B) : MayGo x.fam h cid c o := by
  intro hl hr
  have hR : ((x.hooks.rooms cid).run h).1 = (roomsV cid).eval h.db := by
    simp only [hx, hooks, rooms_held]
  have hrm := rooms_removed h.db hl hr
  rcases hs with ⟨conn, ix, bytes, now, ho⟩ | ⟨conn, ids, ho⟩ | ⟨conn, ix, now, ho⟩ |
      ⟨conn, budget, first, ho⟩ | ⟨dialer, floor, now, ho⟩ | ⟨conn, cat, cursor, room, _, ho⟩
  · rw [hR, recv_held] at ho
    exact (removed_gets_only_notice x.fam x.cfg ix h.db cid c conn bytes [] now 0 false hl hr).2.1 o ho
  · rw [hR, filedGive_held] at ho
    exact (removed_gets_only_notice x.fam x.cfg {} h.db cid c conn .empty ids 0 0 false hl hr).2.2.2.1 o ho
  · rw [hR, tickGive_held] at ho
    exact (removed_gets_only_notice x.fam x.cfg ix h.db cid c conn .empty [] now 0 false hl hr).2.2.2.2 o ho
  · rw [hR] at ho
    have hsh := (serveOwed_shown x.fam x.cfg (conn.carry ((roomsV cid).eval h.db)) budget first h o ho).1
    refine Or.inr (Or.inl fun hc => ?_)
    simp only [Conn.shows, hc] at hsh
    exact hrm _ (mem_syncs ((Engine.has_iff _ _).1 hsh)) rfl
  · simp only [Conn.open, List.mem_singleton] at ho
    subst ho
    exact Or.inl (msg_wire _)
  · have hsh := sweep_shown cat cursor _ room h ho
    rw [hR] at hsh
    refine Or.inr (Or.inl fun hc => ?_)
    simp only [Conn.shows, hc] at hsh
    exact hrm _ (mem_syncs ((Engine.has_iff _ _).1 hsh)) rfl

/-- **A removal reaches a live session** (`removal_reaches_session`).
Run with the Connection family's hooks, whatever entry point the node
runs (a frame, the clock, a write, a socket closing), from any store:
it changes the store only by write turns and purges, and every frame it
sends is a bare op or a bundle sealed for one session cid, each of whose
payloads is an op that, at the store a connection step sent it from,
`MayGo` allows for every community: where this node is live in c and the
trust rule refuses cid's peer, only a sync wire op, an op of another
community, or one in the requirement closure of a removal owed to the
peer. -/
theorem removal_reaches_session [Fresh (HeldM F)] (hfr : Reads (Fresh.fresh : HeldM F ByteArray))
    (x : Sync F (HeldM F)) (K : Keys) (listen : B) (hx : x.hooks = hooks x.fam K listen)
    (hc : ∀ cat, x.catalog = some cat → Reads cat.ceiling ∧ ∀ i, Reads (cat.read i))
    (hs : ∀ store, x.retryStore = some store →
      (∀ peer, Reads (store.load peer)) ∧ (∀ peer cursor, Reads (store.save peer cursor)))
    {E : Engine.Sync.Node → HeldM F (Engine.Sync.Node × Effects)} (hE : Entry x E)
    (n : Engine.Sync.Node) (h : Held F) :
    Moves x.fam h ((E n).run h).2 ∧
      FramesBy x (fun h' cid o => ∀ c, MayGo x.fam h' cid c o) h ((E n).run h).2 ((E n).run h).1.2 := by
  obtain ⟨m, ok⟩ := entry_fresh (hooks_readOnly hfr x K listen hx hc hs) hE n h
  exact ⟨m, ok.mono fun _ _ _ hs c => sent_mayGo x K listen hx hs c⟩

end Connection

end

section

/- Actual local writes commit shared operation bytes before the handler returns.
The representation compatibility premises avoid assuming hash injectivity. -/

namespace Connection.Execution
open Engine Engine.Sync

theorem M.getOp_apply (i : Id) (s : Memory) :
    (Store.getOp i : M _) s = (s.held.db.ops i, s) := rfl

theorem M.forIn_reads {α β} (l : List α) (b : β) (f : α → β → M (ForInStep β))
    (g : β → α → β) (s : Memory) (hf : ∀ a b, f a b s = (.yield (g b a), s)) :
    forIn l b f s = (l.foldl g b, s) := by
  induction l generalizing b with
  | nil => rfl
  | cons a t ih => rw [List.forIn_cons, M.bind_apply, hf]; exact ih _

/-- This is the same deduplicating writer, interpreted with entropy/retry
metadata alongside Held. The writer itself changes neither metadata field. -/
theorem write_store_tape (x : Sync F M) (n : Engine.Sync.Node) (s : Memory) (ops : List Op) :
    (n.write x ops s).2.held =
      (n.write ({ fam := x.fam, hooks := { rooms := fun _ => pure [], sealFor := plainSeal, openFrame := plainOpen } } : Sync F (HeldM F)) ops s.held).2 := by
  rw [write_store]
  unfold Node.write
  simp only [M.bind_apply]
  rw [M.forIn_reads (g := absentStep s.held.db)]
  · dsimp only
    generalize ops.foldl (absentStep s.held.db) [] = absent
    split
    · rfl
    · simp only [M.bind_apply]
      rw [M.forIn_reads (g := fileStep x.fam ((Turn.turn x.fam absent.reverse : M Unit) s).2.held.db)]
      · rfl
      · intro a b
        rw [M.bind_apply, M.getOp_apply]
        unfold fileStep
        split <;> rfl
  · intro a b
    unfold absentStep
    split
    · rw [M.bind_apply, M.getOp_apply]
      split <;> rfl
    · rfl

theorem write_receives (x : Sync F M) (n : Engine.Sync.Node) (s : Memory) (ops : List Op)
    (hi : Inv x.fam s.held.db) {o : Op} (ho : o ∈ ops)
    (sameInput : ∀ p ∈ ops, p.id = o.id → p = o)
    (sameStore : ∀ p, s.held.db.ops o.id = some p → p = o) :
    (n.write x ops s).2.held.db.ops o.id = some o := by
  rw [write_store_tape]
  exact write_takes _ n s.held ops hi ho sameInput sameStore

theorem write_log_agrees_tape (x : Sync F M) (n : Engine.Sync.Node) (s : Memory) (ops : List Op)
    (hi : Inv x.fam s.held.db) (ha : s.held.LogAgrees) : (n.write x ops s).2.held.LogAgrees := by
  rw [write_store_tape]
  exact write_log_agrees _ n s.held ops hi ha

/-- Once a shared operation is committed, all ordinary runtime effects
in a continuation retain it, including reactions and session purges. -/
theorem committed_bind {α β} (fam : Family F) (p : M α) (k : α → M β) (s : Memory)
    {o : Op} (ho : (p s).2.held.db.ops o.id = some o) (hs : (fam.room o).isSome)
    (hk : ∀ a, GoesM fam (k a)) : ((p >>= k) s).2.held.db.ops o.id = some o :=
  (hk _ _).shared_retained ho hs

/-- The complete Node.store continuation retains the operation it just
committed, including all sixteen possible actual reaction rounds. -/
theorem store_receives (x : Sync F M) (hr : NodeTape.ReadOnly x)
    (n : Engine.Sync.Node) (s : Memory) (ops : List Op)
    (hi : Inv x.fam s.held.db) {o : Op} (ho : o ∈ ops) (hs : (x.fam.room o).isSome)
    (sameInput : ∀ p ∈ ops, p.id = o.id → p = o)
    (sameStore : ∀ p, s.held.db.ops o.id = some p → p = o) :
    (n.store x ops true s).2.held.db.ops o.id = some o := by
  have hp : (n.put x ops true s).2.held.db.ops o.id = some o := by
    simpa only [Node.put, intake, ite_true] using write_receives x n s ops hi ho sameInput sameStore
  unfold Node.store
  apply committed_bind x.fam _ _ s hp hs
  intro r
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  goesTape [NodeTape.fanout_goes x hr, NodeTape.put_goes, hr.react.goes]

/-- A local write has committed every compatible shared input before
Node.onWrite returns. This is a completed-handler bound, not a wall-clock
bound or a claim that absent prerequisites already exist. -/
theorem onWrite_receives (x : Sync F M) (hr : NodeTape.ReadOnly x)
    (n : Engine.Sync.Node) (s : Memory) (ops : List Op) (now : Nat)
    (hi : Inv x.fam s.held.db) {o : Op} (ho : o ∈ ops) (hs : (x.fam.room o).isSome)
    (sameInput : ∀ p ∈ ops, p.id = o.id → p = o)
    (sameStore : ∀ p, s.held.db.ops o.id = some p → p = o) :
    (n.onWrite x ops now s).2.held.db.ops o.id = some o := by
  unfold Node.onWrite
  exact committed_bind x.fam _ _ s
    (store_receives x hr n s ops hi ho hs sameInput sameStore) hs
    (fun _ => NodeTape.finish_goes x hr _ _ _)

theorem production_write_receives (S : Setup) (side : Side) (n : Engine.Sync.Node)
    (s : Memory) (ops : List Op) (now : Nat) (hi : Inv family s.held.db)
    {o : Op} (ho : o ∈ ops) (hs : (family.room o).isSome)
    (sameInput : ∀ p ∈ ops, p.id = o.id → p = o)
    (sameStore : ∀ p, s.held.db.ops o.id = some p → p = o) :
    (n.step (S.sync side) (.write ops) now s).2.held.db.ops o.id = some o := by
  simpa only [Node.step] using
    (onWrite_receives (S.sync side) (NodeTape.production_readOnly S side) n s ops now hi ho hs sameInput sameStore)

end Connection.Execution

end

section

/- Stable catalog positions through the actual runtime handlers. Writes
append new shared bytes; purges remove only local history entries. -/

namespace Connection.Execution
open Engine Engine.Sync

/-- Prefix order, not merely set inclusion, is the catalog cursor invariant. -/
def HistoryStep (fam : Family F) (a b : Held F) : Prop :=
  a.Reachable fam → a.LogAgrees →
    b.Reachable fam ∧ b.LogAgrees ∧ ∃ tail, Catalog.shared fam b = Catalog.shared fam a ++ tail

namespace HistoryStep
 theorem refl {fam : Family F} (h : Held F) : HistoryStep fam h h :=
   fun hr ha => ⟨hr, ha, [], by simp⟩
 theorem trans {fam : Family F} {a b c : Held F} (h1 : HistoryStep fam a b) (h2 : HistoryStep fam b c) :
     HistoryStep fam a c := by
   intro hr ha
   obtain ⟨hrb, hab, tail, he⟩ := h1 hr ha
   obtain ⟨hrc, hac, rest, he'⟩ := h2 hrb hab
   exact ⟨hrc, hac, tail ++ rest, by rw [he', he, List.append_assoc]⟩

 /-- Exact point lookups below an already captured high-water mark survive
 every full handler, including local-secret purge and concurrent appends. -/
 theorem catalog_read {fam : Family F} {a b : Held F} (step : HistoryStep fam a b)
     (hr : a.Reachable fam) (ha : a.LogAgrees) {seq : Nat}
     (positive : 0 < seq) (below : seq ≤ (Catalog.shared fam a).length) :
     ((Catalog.held fam).read seq b).1 = ((Catalog.held fam).read seq a).1 := by
   obtain ⟨_, _, tail, he⟩ := step hr ha
   simp only [Catalog.held, he]
   rw [List.getElem?_append_left (by omega)]

 theorem ceiling_mono {fam : Family F} {a b : Held F} (step : HistoryStep fam a b)
     (hr : a.Reachable fam) (ha : a.LogAgrees) :
     ((Catalog.held fam).ceiling a).1 ≤ ((Catalog.held fam).ceiling b).1 := by
   obtain ⟨_, _, tail, he⟩ := step hr ha
   simp only [Catalog.held, he, List.length_append]
   omega
end HistoryStep

def HistoryM (fam : Family F) {α} (p : M α) : Prop :=
  ∀ s, HistoryStep fam s.held (p s).2.held

theorem ReadsHeld.history {fam : Family F} {α} {p : M α} (hp : ReadsHeld p) : HistoryM fam p := by
  intro s hr ha
  rw [hp s]
  exact ⟨hr, ha, [], by simp⟩

namespace HistoryM
 theorem pure' (fam : Family F) {α} (a : α) : HistoryM fam (pure a : M α) :=
   (ReadsHeld.pure' a).history
 theorem bind' {fam : Family F} {α β} {p : M α} {k : α → M β}
     (hp : HistoryM fam p) (hk : ∀ a, HistoryM fam (k a)) : HistoryM fam (p >>= k) := by
   intro s hr ha
   obtain ⟨hr', ha', tail, he⟩ := hp s hr ha
   obtain ⟨hr'', ha'', rest, he'⟩ := hk (p s).1 (p s).2 hr' ha'
   exact ⟨hr'', ha'', tail ++ rest, by rw [M.bind_apply, he', he, List.append_assoc]⟩
 theorem forIn' {fam : Family F} {α β} (l : List α) (b : β)
     {f : α → β → M (ForInStep β)} (hf : ∀ a b, HistoryM fam (f a b)) :
     HistoryM fam (forIn l b f) := by
   induction l generalizing b with
   | nil => exact pure' fam b
   | cons a t ih =>
     rw [List.forIn_cons]
     apply bind' (hf a b)
     intro r
     cases r with
     | done b => exact pure' fam b
     | yield b => exact ih b
 theorem getOp' (fam : Family F) (i : Id) : HistoryM fam (Store.getOp i : M _) :=
   (ReadsHeld.getOp' i).history
 theorem getStatus' (fam : Family F) (i : Id) : HistoryM fam (Store.getStatus i : M _) :=
   (ReadsHeld.getStatus' i).history
 theorem purge' (fam : Family F) (ids : List Id) (scrub : Bool) :
     HistoryM fam (Turn.purge fam ids scrub : M Unit) := by
   intro s hr ha
   exact ⟨purge_reachable fam ids scrub s.held hr, purge_log_agrees fam s.held ids scrub ha,
     [], by
       change Catalog.shared fam ((Turn.purge fam ids scrub : HeldM F Unit) s.held).2 = _
       simpa using shared_log_purge fam s.held ids scrub ha⟩
end HistoryM

syntax "historyTape" "[" term,* "]" : tactic
macro_rules
  | `(tactic| historyTape [$ts,*]) => do
    let mut tac : Lean.TSyntax `tactic ← `(tactic| first | split | intro)
    for t in ts.getElems.reverse do
      tac ← `(tactic| first | with_reducible_and_instances apply $t | $tac:tactic)
    `(tactic| repeat' (first
      | dsimp only | with_reducible_and_instances apply HistoryM.bind'
      | with_reducible_and_instances apply HistoryM.pure' | with_reducible_and_instances apply HistoryM.forIn'
      | with_reducible_and_instances apply HistoryM.getOp' | with_reducible_and_instances apply HistoryM.getStatus'
      | with_reducible_and_instances apply HistoryM.purge'
      | $tac:tactic))

namespace NodeHistory
open NodeTape
variable (x : Sync F M) (hr : ReadOnly x)

theorem write_history (n : Engine.Sync.Node) (ops : List Op) : HistoryM x.fam (n.write x ops) := by
  intro s hr ha
  obtain ⟨history, reach, _⟩ := hr
  have hi := reach_inv reach
  refine ⟨(NodeTape.write_goes x n ops s).store_reachable ⟨history, reach, by assumption⟩,
    write_log_agrees_tape x n s ops hi ha, ?_⟩
  rw [write_store_tape, write_store]
  dsimp only
  split
  · exact ⟨[], by simp⟩
  · exact ⟨_, shared_log_turn _ _ _⟩

theorem put_history (n : Engine.Sync.Node) (ops : List Op) (mine : Bool) : HistoryM x.fam (n.put x ops mine) :=
  write_history x n _
theorem recordGiven_history (n : Engine.Sync.Node) (st : List (Id × Id)) : HistoryM x.fam (n.recordGiven x st) := by
  unfold Node.recordGiven; historyTape [put_history]
include hr

theorem refresh_reads (cid : Id) (c : Conn) : ReadsHeld (Node.refresh x cid c) := by
  unfold Node.refresh; readsHeld [hr.rooms]
theorem fanout_history (n : Engine.Sync.Node) (ids : List Id) : HistoryM x.fam (n.fanout x ids) := by
  unfold Node.fanout
  historyTape [fun cid c => (refresh_reads x hr cid c).history,
    fun c ids => (NodeTape.filedGive_reads x.fam x.cfg c ids).history, recordGiven_history]
theorem store_history (n : Engine.Sync.Node) (ops : List Op) (mine : Bool) : HistoryM x.fam (n.store x ops mine) := by
  unfold Node.store
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  historyTape [put_history, fanout_history x hr, hr.react.history]
theorem open_history (n : Engine.Sync.Node) (cid : Id) (addr : ByteArray) (dialer : Bool) (now : Nat) :
    HistoryM x.fam (n.open x cid addr dialer now) := by
  unfold Node.open; historyTape [fun cid => (hr.rooms cid).history]
theorem follow_history (n : Engine.Sync.Node) (now : Nat) : HistoryM x.fam (n.follow x now) := by
  unfold Node.follow; historyTape [hr.established.history, open_history x hr]
omit hr in
theorem effectsPurge_history (ids : List Id) (scrub : Bool) : HistoryM x.fam (Effects.purge x ids scrub) := by
  unfold Effects.purge; historyTape []
theorem flush_history (n : Engine.Sync.Node) (out : Acts) : HistoryM x.fam (n.flush x out) := by
  unfold Node.flush; historyTape [hr.outbox.history, effectsPurge_history]
theorem seal_history (n : Engine.Sync.Node) (out : Acts) : HistoryM x.fam (n.seal x out) := by
  unfold Node.seal; historyTape [fun cid b => (hr.sealFor cid b).history]
theorem sealRetries_history (n : Engine.Sync.Node) (retries : List RetryOffer) :
    HistoryM x.fam (n.sealRetries x retries) := by
  unfold Node.sealRetries; historyTape [seal_history x hr]
theorem endSession_history (cid : Id) : HistoryM x.fam (Node.endSession x cid) := by
  unfold Node.endSession; historyTape [fun cid => (hr.closing cid).history, effectsPurge_history]
theorem finish_history (n : Engine.Sync.Node) (out : Acts) (now : Nat) : HistoryM x.fam (n.finish x out now) := by
  unfold Node.finish
  historyTape [follow_history x hr, flush_history x hr, hr.retired.history, seal_history x hr,
    sealRetries_history x hr, endSession_history x hr]
theorem onClose_history (n : Engine.Sync.Node) (addr : ByteArray) (now : Nat) : HistoryM x.fam (n.onClose x addr now) := by
  unfold Node.onClose; historyTape [finish_history x hr]
theorem apply_history (n : Engine.Sync.Node) (cid : Id) (st : Step) (now : Nat) :
    HistoryM x.fam (n.apply x cid st now) := by
  unfold Node.apply
  historyTape [recordGiven_history, store_history x hr, fun via a o t => (hr.recv via a o t).history]
theorem serve_history (n : Engine.Sync.Node) (cid : Id) (now : Nat) : HistoryM x.fam (n.serveOwed x cid now) := by
  unfold Node.serveOwed
  historyTape [fun cid c => (refresh_reads x hr cid c).history,
    fun c budget first => (NodeTape.serveOwed_reads x.fam x.cfg c budget first).history]
theorem sweep_history (n : Engine.Sync.Node) (cid : Id) : HistoryM x.fam (n.sweep x cid) := by
  cases hcat : x.catalog with
  | none => simp only [Node.sweep, hcat]; exact HistoryM.pure' x.fam _
  | some cat =>
    obtain ⟨hc, hrd⟩ := hr.catalog cat hcat
    cases hs : x.retryStore with
    | none =>
      simp only [Node.sweep, hcat, hs]
      historyTape [fun cid c => (refresh_reads x hr cid c).history,
        fun cid => (hr.retryKey cid).history,
        fun cursor shows room => (NodeTape.sweep_reads cat hc hrd cursor shows room).history]
    | some store =>
      obtain ⟨hl, hsave⟩ := hr.retryStore store hs
      simp only [Node.sweep, hcat, hs]
      historyTape [fun cid c => (refresh_reads x hr cid c).history,
        fun cid => (hr.retryKey cid).history, fun peer => (hl peer).history,
        fun peer cursor => (hsave peer cursor).history,
        fun cursor shows room => (NodeTape.sweep_reads cat hc hrd cursor shows room).history]

theorem sweep_afterActs_history (n : Engine.Sync.Node) (out : Acts) (cid : Id) :
    HistoryM x.fam (n.sweep (n.afterActs x out) cid) :=
  sweep_history (n.afterActs x out) (hr.afterActs n out) n cid

theorem serve_afterActs_history (n : Engine.Sync.Node) (out : Acts) (cid : Id) (now : Nat) :
    HistoryM x.fam (n.serveOwed (n.afterActs x out) cid now) :=
  serve_history (n.afterActs x out) (hr.afterActs n out) n cid now

theorem onSealed_history (n : Engine.Sync.Node) (addr : ByteArray) (opened : Option (Id × ByteArray)) (now : Nat) :
    HistoryM x.fam (n.onSealed x addr opened now) := by
  unfold Node.onSealed
  historyTape [fun cid c => (refresh_reads x hr cid c).history,
    fun ix c bytes now => (NodeTape.recv_reads x.fam x.cfg ix c bytes now).history,
    apply_history x hr, serve_history x hr, finish_history x hr]
theorem onFrame_history (n : Engine.Sync.Node) (addr bytes : ByteArray) (now : Nat) :
    HistoryM x.fam (n.onFrame x addr bytes now) := by
  unfold Node.onFrame
  historyTape [write_history, store_history x hr, fun via a o t => (hr.recv via a o t).history,
    finish_history x hr, fun b => (hr.openFrame b).history, onSealed_history x hr]
theorem onTick_history (n : Engine.Sync.Node) (now : Nat) : HistoryM x.fam (n.onTick x now) := by
  unfold Node.onTick Node.onTickReserved Node.onTickDirect Node.sweepAll
  historyTape [fun t => (hr.dial t).history, store_history x hr,
    fun cid c => (refresh_reads x hr cid c).history,
    fun ix c now => (NodeTape.tickGive_reads x.fam x.cfg ix c now).history,
    apply_history x hr,
    sweep_history x hr, sweep_afterActs_history x hr,
    serve_afterActs_history x hr,
    finish_history x hr]
theorem onWrite_history (n : Engine.Sync.Node) (ops : List Op) (now : Nat) : HistoryM x.fam (n.onWrite x ops now) := by
  unfold Node.onWrite; historyTape [store_history x hr, finish_history x hr]

/-- Every full event handler uses only actual turn/purge effects, including
the hooks' reactions and the common finish path. -/
theorem step_history (n : Engine.Sync.Node) (input : Node.Input) (now : Nat) :
    HistoryM x.fam (n.step x input now) := by
  cases input with
  | write ops => exact onWrite_history x hr n ops now
  | frame addr bytes => exact onFrame_history x hr n addr bytes now
  | tick => exact onTick_history x hr n now
  | close addr => exact onClose_history x hr n addr now

end NodeHistory

/-- Every production event preserves shared catalog positions, while allowing
new shared writes and local/session purges in the same event. -/
theorem production_step_history (S : Setup) (side : Side) (n : Engine.Sync.Node)
    (input : Node.Input) (now : Nat) (s : Memory) :
    HistoryStep family s.held ((n.step (S.sync side) input now) s).2.held :=
  NodeHistory.step_history (S.sync side) (NodeTape.production_readOnly S side) n input now s

theorem world_run_history (S : Setup) (w : World) (side target : Side) (queue : List Packet)
    (f : Engine.Sync.Node → M (Engine.Sync.Node × Effects)) (closed : Bool)
    (hf : ∀ n s, HistoryStep family s.held (f n s).2.held) :
    HistoryStep family (w.peer target).memory.held
      ((w.run S side queue f closed).peer target).memory.held := by
  cases side <;> cases target
  · exact hf _ _
  · exact .refl _
  · exact .refl _
  · exact hf _ _

/-- Every environment action, including delivery, drops and two-sided close,
preserves each peer's reachable, agreeing, append-only shared history. -/
theorem world_step_history (S : Setup) (w : World) (a : Action) (target : Side) :
    HistoryStep family (w.peer target).memory.held ((step S w a).peer target).memory.held := by
  have hp : ∀ (w : World) (side : Side) (queue : List Packet) (input : Node.Input) (closed : Bool),
      HistoryStep family (w.peer target).memory.held
        ((w.run S side queue (fun n => n.step (S.sync side) input w.now) closed).peer target).memory.held :=
    fun w side queue input closed => world_run_history S w side target queue _ closed
      (fun n s => production_step_history S side n input w.now s)
  have time : ∀ w' : World, ({ w' with now := w.now + 1 }.peer target).memory.held =
      (w'.peer target).memory.held := by intro w'; cases target <;> rfl
  unfold step
  rw [time]
  cases a with
  | tick side => exact hp w side w.net .tick false
  | write side ops => exact hp w side w.net (.write ops) false
  | idle => exact .refl _
  | drop => cases target <;> exact .refl _
  | close =>
    have ha := world_run_history S w .a target []
      (fun n => n.onClose (S.sync .a) (S.addr .b) w.now) true
      (NodeHistory.onClose_history (S.sync .a) (NodeTape.production_readOnly S .a) · (S.addr .b) w.now)
    let wa := w.run S .a [] (fun n => n.onClose (S.sync .a) (S.addr .b) w.now) true
    have hb := world_run_history S wa .b target wa.net
      (fun n => n.onClose (S.sync .b) (S.addr .a) w.now) true
      (NodeHistory.onClose_history (S.sync .b) (NodeTape.production_readOnly S .b) · (S.addr .a) w.now)
    exact ha.trans hb
  | deliver =>
    cases hnet : w.net with
    | nil => simpa only [World.deliver, hnet] using (HistoryStep.refl (fam := family) (w.peer target).memory.held)
    | cons p rest =>
      by_cases ha : p.dst = S.addr .a
      · simpa only [World.deliver, hnet, ite_eq_left ha, Node.step] using hp w .a rest (.frame p.src p.bytes) false
      · by_cases hb : p.dst = S.addr .b
        · simpa only [World.deliver, hnet, ite_eq_right ha, ite_eq_left hb, Node.step] using hp w .b rest (.frame p.src p.bytes) false
        · simp only [World.deliver, hnet, ite_eq_right ha, ite_eq_right hb]
          cases target <;> exact .refl _

theorem world_trace_history (S : Setup) (w : World) (actions : List Action) (target : Side) :
    HistoryStep family (w.peer target).memory.held
      ((trace S w actions).peer target).memory.held := by
  induction actions generalizing w with
  | nil => exact .refl _
  | cons a rest ih => exact (world_step_history S w a target).trans (ih (step S w a))


/-- Starting empty, arbitrary actual event prefixes have a collision-safe
shared history. No fairness or quiescence assumption is needed. -/
theorem empty_trace_history (S : Setup) (ea eb : Nat → ByteArray)
    (actions : List Action) (target : Side) :
    let h := ((trace S (empty ea eb) actions).peer target).memory.held
    h.Reachable family ∧ h.LogAgrees := by
  have hm := world_trace_history S (empty ea eb) actions target
  have he : ((empty ea eb).peer target).memory.held = ({} : Held F) := by cases target <;> rfl
  rw [he] at hm
  have h := hm (held_empty_reachable family) empty_log_agrees
  exact ⟨h.1, h.2.1⟩

/-- Catalog positions are stable across every finite interval of the actual
execution relation. This permits unbounded append traffic and reconnects. -/
theorem Run.history {S initial} (r : Run S initial) (target : Side)
    {n k : Nat} (hnk : n ≤ k) :
    HistoryStep family ((r.state n).peer target).memory.held
      ((r.state k).peer target).memory.held := by
  induction hnk with
  | refl => exact .refl _
  | @step k _ ih =>
    rw [r.next k]
    exact ih.trans (world_step_history S (r.state k) (r.action k) target)

end Connection.Execution

end

section

/-
A closed session's keys are gone from the store (README, "A closed
session's keys cannot be recovered"; docs/CAUGHT.md, fs-erase).

**The statement, broadened.** A session's key material is its two
ephemeral secrets (each side holds its own: an `eph` op, drawn for the
request on the dialer's side and for the connection on the answerer's)
and its two transport keys (the `established` fact). In the store they
sit in two places: the `eph` op's bytes, and the verdicts (`status`) of
the `eph` and `established` ops, whose facts carry the secret and the
keys. No other table holds them: the index, the journal (`filings`) and
the counts hold relation keys, sort keys and ids, and a connection
fact's keys and sort key name only ids (`secret_unfiled`). So
`KeyRow s hs y`: row y of store s holds key material of one of the
handshakes `hs` names (an `eph` op citing one, as bytes or as a Valid
verdict; an `established` verdict naming one). `Forgets s hs`: no row
does.

Proven, over the running code:
- `purge_forgets`: the running purge (`purge`, which is `purgeS` on the
  model's tables, `run_purge`), then judging, leaves no key row of the
  handshakes it was given, whatever else the store holds. Any key row
  cites one of them, so the purge's walk reaches it, and it is local.
- `close_forgets`: so the close step every session end runs
  (`Node.endSession`, `close_purges`) with the family's `closing` leaves
  no key row of the connection or of the request it answers: neither
  side's ephemeral, nor the transport keys. `closing` names the
  connection even once it is gone (it named nothing before fs-erase),
  so a key row that cites a connection the store no longer holds cannot
  outlive the close either.
- `retired_complete`: every established session the store holds is
  kept open (`sessions`) or retired (`retired`), and `close_purges`
  ends every retired one. So no established session sits in the store
  with neither: every way a session stops being open ends it.
  `retired_open`: an open session is never retired.
- `forget_stays`: a later purge brings no key row back.

Caught (a negative control, `shipped_retired_misses`): `retired` as it
shipped (`retiredShipped`) read `allSessions`, which places a session
by its handshake's arrival record. A dialer that crashed between the
two writes of `onFrame` (the connection stored, its arrival record not)
established the session at its next write, and that session was
neither open nor retired: its keys and its ephemeral stayed in the store
for good, and `connectedTo` kept the dialer from dialing again.
tests/engine/ConnectionCheck.lean reproduces it on SQLite.

Assumed: the store model (`Model.run`, which since the purge bridge
covers the purge's reads and deletes too), and the README's trusted
item that a row SQLite deleted, with `secure_delete` on, then `VACUUM`
and the WAL truncated, leaves no recoverable byte (tests/engine/Purge.lean
reads the files raw). With both, a closed session's ephemerals are not
on this node's disk, which is `kk_forward_secret`'s premise. That last
step, from the store's bytes to the symbolic model's names, is read, not
proven.

What this does not say (README): an initiator holds its ephemeral while
its request waits for an answer, and a responder may have answered and
closed meanwhile (the answer lost); while the request waits, that
session's keys follow from the initiator's store and the static keys.
That needs the initiator to know of a session it never heard of, so it
is out of reach of any store law.
-/

namespace Connection
open Engine Engine.Sync

/-! ## Where key material sits -/

/-- Row y of store s holds key material of one of the handshakes `hs`
names: an ephemeral drawn for one of them (an `eph` op citing it, or its
Valid fact), or the transport keys of a session one of them names (an
`established` fact). -/
def KeyRow (s : DB F) (hs : List Id) (y : Id) : Prop :=
  (∃ o, s.ops y = some o ∧ o.kind = 32 ∧ ∃ r ∈ o.reqs, r ∈ hs) ∨
  (∃ of pk sk, s.status y = some (.valid (.inr (.eph of pk sk))) ∧ of ∈ hs) ∨
  (∃ c c' p hh sk rk d, s.status y = some (.valid (.inr (.established c c' p hh sk rk d))) ∧ c ∈ hs)

/-- No row of s holds key material of the handshakes `hs`. -/
def Forgets (s : DB F) (hs : List Id) : Prop := ∀ y, ¬ KeyRow s hs y

/-- **No secret is filed.** The keys a connection fact is filed under,
and its sort key, name only ids: so the index, its counts and the
journal (`filings`), which copy them, hold no ephemeral and no
transport key. -/
theorem secret_unfiled (of pk sk c c' p hh sk' rk : B) (d : Bool) :
    keys (.eph of pk sk) = [eph.byOf.key [of]] ∧ sortOf (.eph of pk sk) = .empty ∧
    keys (.established c c' p hh sk' rk d) = [established.all.key [], established.byConn.key [c]] ∧
    sortOf (.established c c' p hh sk' rk d) = .empty := by
  refine ⟨?_, rfl, ?_, rfl⟩ <;> rfl

/-! ## A key fact is an op's own -/

theorem allValid_length {sts : List (Option (Verdict F))} {fs : List F} (h : allValid sts = some fs) :
    fs.length = sts.length := by
  induction sts generalizing fs with
  | nil => cases h; rfl
  | cons st t ih =>
    match st, h with
    | some (.valid f), h =>
      simp only [allValid] at h
      cases ht : allValid t with
      | none => rw [ht] at h; cases h
      | some fs' =>
        rw [ht] at h; cases h
        simp [ih ht]

/-- A Valid verdict of the node's is its validator's answer on the op's
requirements' facts. -/
theorem valid_op {C : Community.Crypto} {K : Keys} {s : DB F} (hi : Inv (node C K) s) {y : Id} {g : Fact}
    (hy : s.status y = some (.valid (.inr g))) :
    ∃ o fs, s.ops y = some o ∧ fs.length = o.reqs.length ∧ validate K o fs = some g := by
  obtain ⟨n, hn⟩ := hi.sound y _ hy
  cases n with
  | zero => cases hn
  | succ n =>
    simp only [specAt] at hn
    cases ho : s.ops y with
    | none => rw [ho] at hn; cases hn
    | some o =>
      rw [ho] at hn
      simp only [judge] at hn
      split at hn
      · cases hn
      · split at hn
        · rename_i fs hfs
          refine ⟨o, fs, rfl, by rw [allValid_length hfs, List.length_map], ?_⟩
          split at hn
          · rename_i f hf
            simp only [Option.some.injEq, Verdict.valid.injEq] at hn
            subst hn
            simp only [node, Family.sum] at hf
            split at hf
            · change Option.map Sum.inr (validate K o fs) = _ at hf
              cases hv : validate K o fs with
              | none => rw [hv] at hf; cases hf
              | some g' =>
                rw [hv] at hf
                simp only [Option.map_some, Option.some.injEq, Sum.inr.injEq] at hf
                rw [hf]
            · cases hl : lefts fs with
              | none => rw [hl] at hf; cases hf
              | some xs =>
                rw [hl] at hf
                cases hv : (Community.family C).validate o xs with
                | none => simp [hv] at hf
                | some g' => simp [hv] at hf
          · cases hn
        · cases hn

/-- An `eph` op's fact names the op it cites. -/
theorem eph_check {K : Keys} {o : Op} {b : Eph.Body} {g : Eph.Fact} (h : Eph.check K o b = some g) :
    g.of = o.reqs.headD .empty := by
  obtain ⟨sk⟩ := b
  by_cases hc : sk.size = 32
  · simp only [Eph.check, hc, ite_true, Option.some.injEq] at h
    subst h; rfl
  · simp [Eph.check, hc] at h

/-- An `established` op's fact names the op it cites first. -/
theorem established_check {K : Keys} {o : Op} {b : Established.Body} {cn rq ep en} {g : Established.Fact}
    (h : Established.check K o b cn rq ep en = some g) : g.cid = o.reqs.headD .empty := by
  obtain ⟨r, m2⟩ := cn
  obtain ⟨to, frm, m1⟩ := rq
  obtain ⟨_, _, esk⟩ := ep
  obtain ⟨pk, sk⟩ := en
  simp only [Established.check] at h
  split at h
  · cases h
  · split at h
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨st, re, p1⟩, -, ⟨c, a, os⟩, -, ⟨sr, m2'⟩, -, h⟩ := h
      split at h
      · cases h
      · cases h; rfl
    · split at h
      · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨⟨st, p1⟩, -, ⟨c, a, os⟩, -, ⟨si, x⟩, -, h⟩ := h
        cases h; rfl
      · cases h

/-- **An ephemeral's fact names the op it cites, and is an `eph` op's.** -/
theorem validate_eph {K : Keys} {o : Op} {fs : List F} {of pk sk : B}
    (h : validate K o fs = some (.eph of pk sk)) :
    o.kind = 32 ∧ fs.length = 1 ∧ of = o.reqs.headD .empty := by
  unfold validate at h
  split at h
  · rename_i b hb
    split at h
    · rename_i hk
      unfold check at h
      split at h
      all_goals first
        | (obtain ⟨a, -, ha⟩ := Option.map_eq_some_iff.1 h; cases ha; done)
        | (cases h; done)
        | skip
      obtain ⟨a, ha, he⟩ := Option.map_eq_some_iff.1 h
      cases he
      exact ⟨hk.symm, rfl, eph_check ha⟩
    · cases h
  · cases h

/-- **A session's keys are its `established` op's**, which cites the
connection they name. -/
theorem validate_established {K : Keys} {o : Op} {fs : List F} {c c' p hh sk rk : B} {d : Bool}
    (h : validate K o fs = some (.established c c' p hh sk rk d)) :
    o.kind = 36 ∧ fs.length = 4 ∧ c = o.reqs.headD .empty := by
  unfold validate at h
  split at h
  · rename_i b hb
    split at h
    · rename_i hk
      unfold check at h
      split at h
      all_goals first
        | (obtain ⟨a, -, ha⟩ := Option.map_eq_some_iff.1 h; cases ha; done)
        | (cases h; done)
        | skip
      obtain ⟨a, ha, he⟩ := Option.map_eq_some_iff.1 h
      cases he
      exact ⟨hk.symm, rfl, established_check ha⟩
    · cases h
  · cases h

theorem headD_mem {l : List Id} (h : l ≠ []) : l.headD .empty ∈ l := by
  cases l with
  | nil => exact absurd rfl h
  | cons a t => exact List.mem_cons_self ..

/-- Connection ops of kinds 32–39 other than the two handshake messages
are local: in the node's family their room is none. -/
theorem room_local {C : Community.Crypto} {K : Keys} {o : Op} (hk : o.kind = 32 ∨ o.kind = 36) :
    (node C K).room o = none := by
  have ho : owns o.kind = true := by rcases hk with hk | hk <;> rw [hk] <;> rfl
  have hs : ¬ (o.kind = 33 ∨ o.kind = 35) := by rcases hk with hk | hk <;> rw [hk] <;> decide
  simp only [Family.room, node, Family.sum, family, ho, ite_true, scopeOf, hs, ite_false]

/-- Every key row is a stored local op that cites one of `hs`. -/
theorem keyRow_op {C : Community.Crypto} {K : Keys} {s : DB F} (hi : Inv (node C K) s) {hs : List Id} {y : Id}
    (h : KeyRow s hs y) :
    ∃ o, s.ops y = some o ∧ (node C K).room o = none ∧ ∃ r ∈ o.reqs, r ∈ hs := by
  rcases h with ⟨o, ho, hk, r, hr, hrs⟩ | ⟨of, pk, sk, hy, hof⟩ | ⟨c, c', p, hh, sk, rk, d, hy, hc⟩
  · exact ⟨o, ho, room_local (.inl hk), r, hr, hrs⟩
  · obtain ⟨o, fs, ho, hl, hv⟩ := valid_op hi hy
    obtain ⟨hk, h1, rfl⟩ := validate_eph hv
    have hne : o.reqs ≠ [] := by intro he; rw [he] at hl; rw [hl] at h1; cases h1
    exact ⟨o, ho, room_local (.inl hk), _, headD_mem hne, hof⟩
  · obtain ⟨o, fs, ho, hl, hv⟩ := valid_op hi hy
    obtain ⟨hk, h4, rfl⟩ := validate_established hv
    have hne : o.reqs ≠ [] := by intro he; rw [he] at hl; rw [hl] at h4; cases h4
    exact ⟨o, ho, room_local (.inr hk), _, headD_mem hne, hc⟩

/-! ## The purge forgets -/

theorem inv_drainS {fam : Family F} {s : DB F} (h : Inv fam s) : ∀ n, Inv fam (drainS fam n s)
  | 0 => h
  | n + 1 => by
    unfold drainS
    split
    · exact inv_step h
    · exact inv_drainS (inv_step h) n

/-- No stored conn or local op cites one of `hs`: what a purge of `hs`
leaves, and more than the key rows (the `opened`, the couriers, the
arrival records, the notices given). -/
def Uncited (s : DB F) (fam : Family F) (hs : List Id) : Prop :=
  ∀ y o, s.ops y = some o → fam.room o = none → ∀ r ∈ o.reqs, r ∉ hs

/-- With the tables' invariant, a store where nothing local cites `hs`
holds no key row of them. -/
theorem forgets_of_uncited {C : Community.Crypto} {K : Keys} {s : DB F} (hi : Inv (node C K) s)
    {hs : List Id} (hu : Uncited s (node C K) hs) : Forgets s hs := by
  intro y hy
  obtain ⟨o, ho, hl, r, hr, hrs⟩ := keyRow_op hi hy
  exact hu y o ho hl r hr hrs

/-- The running purge of `hs` (`purgeS`, which the running `purge` is:
`run_purge`), then any judging, leaves no conn or local op that cites
one of `hs`: the purge's walk reaches every op that cites one. -/
theorem purge_uncited {fam : Family F} {s : DB F} (hi : Inv fam s) (hs : List Id) (n : Nat) :
    Uncited (drainS fam n (purgeS fam hs s)) fam hs := by
  intro y o ho hl r hr hrs
  rw [drainS_ops] at ho
  have hnot : y ∉ purgeSet fam s hs := fun hm => by rw [purgeS_ops_mem s hs hm] at ho; cases ho
  rw [purgeS_ops_not s hs hnot] at ho
  have hst : y ∈ s.stored := (hi.stored y).2 (by rw [ho]; rfl)
  have hc : y ∈ closeUp s hs := closeUp_closed s hs hst ho hr (closeUp_sub s hs hrs)
  exact hnot (mem_purgeSet_iff.2 ⟨hc, o, ho, hl⟩)

/-- **What a purge leaves uncited stays so** through any later purge: a
purge deletes, and judging writes no op. -/
theorem uncited_stays {fam : Family F} {s : DB F} {hs : List Id} (hu : Uncited s fam hs)
    (ids : List Id) (n : Nat) : Uncited (drainS fam n (purgeS fam ids s)) fam hs := by
  intro y o ho hl r hr hrs
  rw [drainS_ops] at ho
  have hnot : y ∉ purgeSet fam s ids := fun hm => by rw [purgeS_ops_mem s ids hm] at ho; cases ho
  rw [purgeS_ops_not s ids hnot] at ho
  exact hu y o ho hl r hr hrs

/-- **The running purge forgets the handshakes it is given.** After the
purge of `hs` and any judging, no row holds an ephemeral drawn for one
of `hs`, nor the keys of a session one of them names. -/
theorem purge_forgets {C : Community.Crypto} {K : Keys} {s : DB F} (hi : Inv (node C K) s) (hs : List Id)
    (n : Nat) : Forgets (drainS (node C K) n (purgeS (node C K) hs s)) hs :=
  forgets_of_uncited (inv_drainS (purge_inv hi hs) n) (purge_uncited hi hs n)

/-- **Forgotten stays forgotten**: once nothing local cites `hs`, no
later purge brings a key row of them back. -/
theorem forget_stays {C : Community.Crypto} {K : Keys} {s : DB F} (hi : Inv (node C K) s) {hs : List Id}
    (hu : Uncited s (node C K) hs) (ids : List Id) (n : Nat) :
    Forgets (drainS (node C K) n (purgeS (node C K) ids s)) hs :=
  forgets_of_uncited (inv_drainS (purge_inv hi ids) n) (uncited_stays hu ids n)

/-! ## The close step forgets -/

/-- What `closing` names, on held data: the connection, and the
requirements of the connection op if the store holds it (the request
it answers). -/
theorem closing_apply (cid : Id) (h : Held F) :
    (closing cid : HeldM F (List Id)) h = (cid :: ((h.db.ops cid).map (·.reqs)).getD [], h) := by
  unfold closing
  simp only [HeldM.bind_apply, HeldM.getOp_apply]
  cases h.db.ops cid <;> rfl

/-- **A closed session's keys are gone from its node's store.** The
close step every session end runs (`Node.endSession`: a drop on
silence, a lost socket, a retirement, a session that left
`established`; `close_purges`), with the family's `closing`, from any
state that keeps the tables' invariant: afterwards no stored conn or
local op cites the connection or the request it answers (`Uncited`),
so no row holds this side's ephemeral for the session (drawn for the
request on the dialer's side, for the connection on the answerer's),
in its bytes or its verdict, nor the session's transport keys
(`Forgets`). -/
theorem close_forgets {C : Community.Crypto} {K : Keys} (x : Sync F (HeldM F)) (hf : x.fam = node C K)
    (hc : x.hooks.closing = closing) (h : Held F) (hi : Inv x.fam h.db) (cid : Id) :
    let hs := cid :: ((h.db.ops cid).map (·.reqs)).getD []
    let h' := ((Node.endSession x cid : HeldM F Effects) h).2
    Uncited h'.db x.fam hs ∧ Forgets h'.db hs := by
  intro hs h'
  have he : h' = ((Turn.purge x.fam hs true : HeldM F Unit) h).2 := by
    show ((Node.endSession x cid : HeldM F Effects) h).2 = _
    rw [endSession_purges, HeldM.bind_apply, hc, closing_apply]
    rfl
  rw [he, purge_apply]
  simp only [hf] at hi ⊢
  exact ⟨purge_uncited hi hs _, purge_forgets hi hs _⟩

/-! ## Every session not kept open is retired -/

/-- **Every established session is kept open or retired** (`retired`):
an established fact the store lists names a session `sessions` lists,
or one `retired` names, which the node then closes and purges
(`close_purges`, `close_forgets`). -/
theorem retired_complete (s : DB F) {y cid c p hh sk rk : B} {d : Bool}
    (hy : (y, Fact.established cid c p hh sk rk d) ∈ ((rows established.all [] : Model F _).run s).1) :
    (∃ e ∈ ((sessions : Model F _).run s).1, e.1 = cid) ∨ cid ∈ ((retired : Model F _).run s).1 := by
  simp only [sessions, retired, Model.run_bind, Model.run_pure, openSessions_state]
  by_cases ho : ((openSessions : Model F (List (Id × B × Bool × B × Nat))).run s).1.any
      (fun e => decide (e.1 = cid)) = true
  · left
    obtain ⟨e, he, hd⟩ := List.any_eq_true.1 ho
    exact ⟨_, List.mem_map_of_mem he, of_decide_eq_true hd⟩
  · right
    rw [List.mem_filterMap]
    exact ⟨_, hy, by simp only [ho, Bool.false_eq_true, ite_false]⟩

/-- **No open session is retired.** -/
theorem retired_open (s : DB F) {cid : B} (hr : cid ∈ ((retired : Model F _).run s).1) :
    ∀ e ∈ ((sessions : Model F _).run s).1, e.1 ≠ cid := by
  simp only [sessions, retired, Model.run_bind, Model.run_pure, openSessions_state, List.mem_map,
    List.mem_filterMap] at hr ⊢
  rintro _ ⟨e, he, rfl⟩ hec
  obtain ⟨⟨_, f⟩, -, hf⟩ := hr
  cases f
  case ofEstablished g =>
    obtain ⟨c, c', p, hh, sk, rk, d⟩ := g
    simp only at hf
    split at hf
    · cases hf
    · rename_i hn
      simp only [Option.some.injEq] at hf
      subst hf
      exact hn (List.any_eq_true.2 ⟨e, he, decide_eq_true hec⟩)
  all_goals cases hf

/-- **Caught: `retired` as shipped left a session with neither.** With
an established fact for cid on the dialer's side and no arrival record
of the connection (a crash between `onFrame`'s two writes), the shipped
`retiredShipped` does not name cid, and `sessions` does not list it: the
node never closes it, so its keys and its ephemeral stay in the store.
`retired_complete` is false of it. -/
theorem shipped_retired_misses (s : DB F) {y cid c p hh sk rk : B}
    (hr : ((rows established.all [] : Model F _).run s).1 = [(y, .established cid c p hh sk rk true)])
    (ha : ((rows recv.byOp [cid] : Model F _).run s).1 = []) :
    (y, Fact.established cid c p hh sk rk true) ∈ ((rows established.all [] : Model F _).run s).1 ∧
      ¬ ((∃ e ∈ ((sessions : Model F _).run s).1, e.1 = cid) ∨
        cid ∈ ((retiredShipped : Model F _).run s).1) := by
  have hs2 : ((rows established.all [] : Model F _).run s).2 = s := by rw [run_rows]
  have hall : ((allSessions : Model F (List (Id × B × Bool × B × Nat))).run s).1 = [] := by
    simp only [allSessions, Model.run_bind, Model.run_pure]
    rw [hr, hs2]
    simp only [sessionsOf, sessionOf, ite_true, Model.run_bind, Model.run_pure, arrival]
    rw [ha]
    rfl
  have hopen : ((openSessions : Model F (List (Id × B × Bool × B × Nat))).run s).1 = [] := by
    simp only [openSessions, Model.run_bind, Model.run_pure]
    rw [allSessions_state, hall]
    rfl
  refine ⟨by rw [hr]; exact List.mem_singleton_self _, ?_⟩
  rintro (⟨e, he, -⟩ | hm)
  · simp only [sessions, Model.run_bind, Model.run_pure, hopen, List.map_nil, List.not_mem_nil] at he
  · simp only [retiredShipped, Model.run_bind, Model.run_pure, allSessions_state, hall,
      List.filterMap_nil, List.not_mem_nil] at hm

end Connection

end

/-! ## Node IDs stay unique in every production execution
(engine/wire/NodeUniqueLaws.lean, over the World interpreter). -/
section
namespace Connection.Execution
open Engine Engine.Sync
open Engine.Sync.NodeUnique

private instance : LawfulMonad M := inferInstanceAs (LawfulMonad (StateM Memory))

/-- Arbitrary production hooks/entropy and the actual entry-point dispatch.
No read-only, fairness, admission or uniqueness assumption about hook output. -/
theorem production_step_unique (S : Setup) (side : Side) (n : Engine.Sync.Node)
    (input : Node.Input) (now : Nat) (s : Memory) (h : Valid n) :
    Valid ((n.step (S.sync side) input now) s).1.1 :=
  Ensures.state (step_valid (S.sync side) n input now h) s

private theorem world_run_unique (S : Setup) (w : World) (side : Side) (queue : List Packet)
    (f : Engine.Sync.Node → M (Engine.Sync.Node × Effects)) (closed : Bool)
    (hf : ∀ n s, Valid n → Valid (f n s).1.1)
    (hw : ∀ side, Valid (w.peer side).node) :
    ∀ target, Valid ((w.run S side queue f closed).peer target).node := by
  intro target
  cases side <;> cases target
  · exact hf _ _ (hw .a)
  · exact hw .b
  · exact hw .a
  · exact hf _ _ (hw .b)

/-- Reuses the existing production World transition, including two-sided
transport close, delivery, dropped frames, writes, ticks and idle actions. -/
theorem world_step_unique (S : Setup) (w : World) (a : Action)
    (hw : ∀ side, Valid (w.peer side).node) :
    ∀ target, Valid ((step S w a).peer target).node := by
  have hp : ∀ (w : World) (side : Side) (queue : List Packet) (input : Node.Input) (closed : Bool),
      (∀ s, Valid (w.peer s).node) →
      ∀ target, Valid ((w.run S side queue
        (fun n => n.step (S.sync side) input w.now) closed).peer target).node :=
    fun w side queue input closed h => world_run_unique S w side queue _ closed
      (fun n s hn => production_step_unique S side n input w.now s hn) h
  intro target
  have time : ∀ w' : World, ({ w' with now := w.now + 1 }.peer target).node =
      (w'.peer target).node := by intro w'; cases target <;> rfl
  unfold step
  rw [time]
  cases a with
  | tick side => exact hp w side w.net .tick false hw target
  | write side ops => exact hp w side w.net (.write ops) false hw target
  | idle => exact hw target
  | drop => cases target with
    | a => exact hw .a
    | b => exact hw .b
  | close =>
    have ha := hp w .a [] (.close (S.addr .b)) true hw
    let wa := w.run S .a [] (fun n => n.onClose (S.sync .a) (S.addr .b) w.now) true
    exact world_run_unique S wa .b wa.net _ true
      (fun n s hn => production_step_unique S .b n (.close (S.addr .a)) w.now s hn) ha target
  | deliver =>
    cases hnet : w.net with
    | nil => simpa only [World.deliver, hnet] using hw target
    | cons p rest =>
      by_cases ha : p.dst = S.addr .a
      · simpa only [World.deliver, hnet, ite_eq_left ha, Node.step] using
          hp w .a rest (.frame p.src p.bytes) false hw target
      · by_cases hb : p.dst = S.addr .b
        · simpa only [World.deliver, hnet, ite_eq_right ha, ite_eq_left hb, Node.step] using
            hp w .b rest (.frame p.src p.bytes) false hw target
        · simp only [World.deliver, hnet, ite_eq_right ha, ite_eq_right hb]
          cases target with
          | a => exact hw .a
          | b => exact hw .b

theorem world_trace_unique (S : Setup) (w : World) (actions : List Action)
    (hw : ∀ side, Valid (w.peer side).node) :
    ∀ target, Valid ((trace S w actions).peer target).node := by
  induction actions generalizing w with
  | nil => exact hw
  | cons a rest ih => exact ih (step S w a) (world_step_unique S w a hw)

/-- Every finite execution from the actual boot has unique live IDs and retry
order. The schedule, entropy, user writes and packet drops are arbitrary. -/
theorem empty_trace_unique (S : Setup) (ea eb : Nat → ByteArray)
    (actions : List Action) (target : Side) :
    Valid ((trace S (empty ea eb) actions).peer target).node :=
  world_trace_unique S (empty ea eb) actions (fun side => by
    cases side <;> exact boot_valid family [] 0) target

/-- Every position in an arbitrary infinite production-interpreter execution;
fairness is irrelevant to this invariant and is not a premise. -/
theorem Run.unique {S : Setup} {ea eb : Nat → ByteArray}
    (r : Run S (empty ea eb)) (i : Nat) (target : Side) :
    Valid ((r.state i).peer target).node := by
  induction i generalizing target with
  | zero => rw [r.zero]; cases target <;> exact boot_valid family [] 0
  | succ i ih =>
    rw [r.next]
    exact world_step_unique S (r.state i) (r.action i) (fun side => ih side) target

end Connection.Execution

end

section

/-
Get started's layout laws, over the functions the page runs
(`Pages.startTop`, `startGeom`, `startRow`, `startTaps`, `getStarted`,
in app/community/Screen.lean):

- `start_phone`, `start_below_bar`: on phones and narrow windows the
  column starts right under the 60 px bar, and never under the bar.
- `start_centred`: from 45rem, when it fits, the column is centred in
  the window below the bar, to a quarter CSS pixel.
- `start_column_inside`: the column (and so the card and its rows) is
  inside the window.
- `start_rows_in_card`, `start_rows_apart`: each row's box is inside the
  card's 1 px edges, and each row ends where the next row's divider
  starts, at every density: every edge is snapped on its own.
- `getStarted_taps`, `startTaps_rows`: the page's taps are exactly the
  rows' boxes, each with its own row's action; the painter draws row i
  in `startRow dm g i` too, so a tap hits what is drawn.
-/

namespace Pages
open Paint Text Font Row

theorem q_mono (dm : Dim) {a b : Nat} (h : a ≤ b) : dm.q a ≤ dm.q b :=
  Nat.div_le_div_right (Nat.add_le_add_right (Nat.mul_le_mul_right _ h) _)

/-- The page's top (the stage's 56 px bar band) is a snapped edge too. -/
theorem px56_q (dm : Dim) : dm.px 56 = dm.q 224 := by
  simp only [Row.Dim.px, Row.Dim.q]; omega

/-- **Phones top-anchor.** Below 45rem the column starts under the bar. -/
theorem start_phone (stage4 lines : Nat) : startTop false stage4 lines = 240 := by
  simp [startTop]

/-- **Never under the bar.** -/
theorem start_below_bar (wide : Bool) (stage4 lines : Nat) : 240 ≤ startTop wide stage4 lines := by
  unfold startTop; split <;> omega

/-- **Desktops centre.** From 45rem, when the column fits, the space
between the bar and the column and the space under the column differ by
at most a quarter CSS pixel. -/
theorem start_centred (stage4 lines : Nat) (h : 240 + startBody lines ≤ stage4) :
    startTop true stage4 lines - 240 ≤ stage4 - (startTop true stage4 lines + startBody lines) ∧
    stage4 - (startTop true stage4 lines + startBody lines) ≤ startTop true stage4 lines - 240 + 1 := by
  simp only [startTop, h, Bool.true_and, decide_true, if_true]
  omega

/-- **The column is inside the window** (once the window fits its two
16 px gutters). -/
theorem start_column_inside (dm : Dim) (W stage lines : Nat) (h : 2 * dm.px 16 ≤ min W (dm.px 384)) :
    (startGeom dm W stage lines).col + (startGeom dm W stage lines).colW ≤ W := by
  have := Nat.min_le_left W (dm.px 384)
  simp only [startGeom]
  omega

/-- **Rows sit inside the card**, between its 1 px top and bottom edges. -/
theorem start_rows_in_card (dm : Dim) (W stage lines i : Nat) (hi : i < 3) :
    let g := startGeom dm W stage lines
    dm.q (g.card4 + 4) - dm.px 56 ≤ (startRow dm g i).y ∧
    (startRow dm g i).y + (startRow dm g i).h ≤ dm.q (g.card4 + 588) - dm.px 56 := by
  intro g
  have hb : 240 ≤ g.top4 := start_below_bar _ _ _
  simp only [startRow, px56_q]
  have h1 := q_mono dm (show 224 ≤ g.card4 + 4 + 196 * i by simp only [Start.card4]; omega)
  have h2 := q_mono dm (Nat.le_add_right (g.card4 + 4 + 196 * i) 192)
  have h3 := q_mono dm (show g.card4 + 4 ≤ g.card4 + 4 + 196 * i by omega)
  have h4 := q_mono dm (show g.card4 + 4 + 196 * i + 192 ≤ g.card4 + 588 by omega)
  omega

/-- **Rows don't overlap**: row i ends where row i+1's divider begins,
for any card below the page's top. -/
theorem start_rows_apart (dm : Dim) (g : Start) (i : Nat) (hg : 224 ≤ g.card4) :
    (startRow dm g i).y + (startRow dm g i).h ≤ (startDivider dm g (i + 1)).1 ∧
    (startDivider dm g (i + 1)).2 = (startRow dm g (i + 1)).y := by
  simp only [startRow, startDivider, px56_q]
  have h1 := q_mono dm (show 224 ≤ g.card4 + 4 + 196 * i by omega)
  have h2 := q_mono dm (Nat.le_add_right (g.card4 + 4 + 196 * i) 192)
  have e1 : g.card4 + 196 * (i + 1) = g.card4 + 4 + 196 * i + 192 := by omega
  have e2 : g.card4 + 4 + 196 * i + 192 + 4 = g.card4 + 4 + 196 * (i + 1) := by omega
  rw [e1, e2]
  exact ⟨by omega, rfl⟩

/-- **Taps are the drawn rows.** Get started's taps are `startTaps` of
its own geometry. -/
theorem getStarted_taps {α : Type} [BEq α] [Inert α] (onJoin onCreate onDevices : α)
    (f : Font) (dm : Dim) (W h stage : Nat) :
    (getStarted onJoin onCreate onDevices f dm W h stage).taps =
      startTaps dm (startOf f dm W stage).1 (startRows onJoin onCreate onDevices) := rfl

/-- Row i's tap is row i's box with row i's action. -/
theorem startTaps_rows {α : Type} (dm : Dim) (g : Start) (rows : Array (String × String × α)) (i : Nat)
    (hi : i < rows.size) :
    (startTaps dm g rows)[i]? = some (startRow dm g i, (rows[i]).2.2) := by
  simp [startTaps, hi]

end Pages

end
