/-
What a removed member's node sees, and whose keys a handshake runs on:
the Connection family's side of docs/REMOVAL.md, over the views and
validators the node runs.

Proven:
- E3 `opened_endpoint`, `established_endpoint`: the handshake's statics
  are the two nodes' keys: a side's static is the secret of the endpoint
  op its `opened` or `established` cites, the peer's is the request's
  other key. `meV_node`: the trust rule's "me" is this node's key.
- E2 on the bare wire: `bare_takes_only_join` (the only shared op
  `react` takes from a hello is a join request of the hello's community,
  trusted or not: a removed member's node, or anyone who knows c's id,
  pushes nothing else into a member's store without a session);
  `answer_trusted` and `resend_trusted` (`react` answers, and
  `onArrival` re-sends an answer, only for a request whose initiator the
  trust rule takes). On the model, `react`'s fresh bytes leave the store
  as it is (`FreshPure`), as the model's do.

Stated (`_stmt`), to be proven with the Node and Conn step (typed rooms
in `Hooks.rooms`; docs/REMOVAL.md, Status). Read over the node's store
(`DB F`, Community and Connection composed), as `rooms_cut` is; each
connection step the node runs is a `Conn` step on the connection
`Node.refresh` leaves, `c.carry ((roomsV cid).eval s)` on the model
(then `carry` becomes `setRooms`, and the `rooms` hook gives rooms with
notices). A session is one per peer key
and carries a room for every community this node holds.
- E2 `rooms_removed_stmt`: when this node is a live member of c and the
  trust rule refuses the peer, the connection carries no synced room c,
  only notices of removals the peer's key is owed.
- `rooms_complete_stmt`: and it still carries every community whose
  peer the trust rule takes: a removal in c drops c's room and adds the
  notice, and leaves the session's other communities as they were.
- E2 `removed_gets_only_notice_stmt`: so every op a connection step
  sends of c is a sync wire op or in the requirement closure of such a
  removal, and nothing of c is taken.
- E1 `notice_then_cut_stmt`: once, for every community this node
  holds, the peer is refused and every removal owed is given on the
  connection, it carries nothing; `sessions` drops it and `retired`
  names it, so the node closes it and purges its ops.
-/
import ops.connection.Intents
import ops.connection.RoomLaws
import ops.sync.NoticeLaws

namespace Connection
open Engine Engine.Sync Codec

/-! ## Read over the node's store -/

/-- The peer keys connection cid's established facts name. -/
def peersAt (s : DB F) (cid : Id) : List B :=
  peersOf (Engine.eval s (established.byConn.query [cid]))

/-- This node is a live member of c, as the trust rule reads it. -/
def LiveIn (s : DB F) (c : B) : Prop :=
  ∀ me, (meV c).eval s = some me → ((Community.allowPeer c me).liftL : View F Bool).eval s = true

/-- The trust rule refuses, for c, every peer key connection cid names:
once the removal is held, a removed member's node. -/
def Refused (s : DB F) (cid c : B) : Prop :=
  ∀ peer ∈ peersAt s cid, ((Community.allowPeer c peer).liftL : View F Bool).eval s = false

/-- Removal x of community c is owed to connection cid's peer: a removal
of a user admitted under the peer's key, read from the lists. -/
def Owed (s : DB F) (cid c x : B) : Prop :=
  ∃ peer ∈ peersAt s cid, x ∈ ((Community.removalsAt c peer).liftL : View F (List Id)).eval s

/-- What may go out of community c on cid: a sync wire op, an op of
another room, or an op in the requirement closure, in c, of a removal
owed to the peer. -/
def NoticeOnly (fam : Family F) (s : DB F) (cid c : B) (o : Op) : Prop :=
  isWire o.kind = true ∨ fam.room o ≠ some c ∨ ∃ x, Owed s cid c x ∧ ReachIn fam s.ops c x o.id

theorem run_rows (r : Rel Fact) (args : List B) (s : DB F) :
    ((rows r args : Model F _).run s) =
      ((Engine.eval s (r.query args)).rights.map fun ((_, x), f) => (x, f), s) := rfl

theorem run_count (r : Rel Fact) (args : List B) (s : DB F) :
    ((count r args : Model F _).run s) =
      ((Engine.eval s (r.query args (limit := some 0))).total, s) := rfl

theorem run_view {α : Type} (v : View F α) (s : DB F) : (v.run : Model F α).run s = (v.eval s, s) :=
  View.run_model v s

theorem has_of_mem {l : List Id} {x : Id} (h : x ∈ l) : has l x = true := by
  induction l with
  | nil => cases h
  | cons y t ih =>
    unfold has
    by_cases hy : y = x
    · simp [hy]
    · rw [if_neg hy]
      rcases List.mem_cons.1 h with h | h
      · exact absurd h.symm hy
      · exact ih h

/-! ## E2: nothing but the notice -/

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
    (hp : peer ∈ peersAt s cid) (hh : c ∈ heldV.eval s)
    (ht : ((trusts c me peer).liftL : View F Bool).eval s = true) :
    Room.sync c ∈ (roomsV cid).eval s := by
  simp only [roomsV, View.eval_bind, View.eval_read, eval_roomsOf, List.mem_flatMap]
  refine ⟨(c, peer), ?_, ?_⟩
  · exact ⟨peer, hp, List.mem_map.2 ⟨c, hh, rfl⟩⟩
  · rw [eval_roomFor]; simp [hm, ht]

/-- **Nothing but the notice (`removed_gets_only_notice`).** Under the
same premises, on the connection as each step reads it afresh: opening
says hello only; and of community c, a frame received, ops just stored
(`filed`) and the clock (`tick`) send only sync wire ops and ops in the
requirement closure of a removal owed to the peer. A frame received
hands the writer nothing of c. (With the Node and Conn step: then
`carry` is `setRooms`, and `filed` and `tick` give notices.) -/
def removed_gets_only_notice_stmt : Prop :=
  ∀ (fam : Family F) (cfg : Config) (ix : Index) (s : DB F) (cid c : B) (conn : Conn)
    (bytes : B) (ids : List Id) (now floor : Nat) (dialer : Bool),
    LiveIn s c → Refused s cid c →
    let k := conn.carry ((roomsV cid).eval s)
    (∀ rs, ∀ o ∈ (Conn.open dialer rs floor now).send, isWire o.kind = true) ∧
    (∀ o ∈ ((Conn.recv fam cfg ix k bytes now : Model F Step).run s).1.send,
      NoticeOnly fam s cid c o) ∧
    (∀ o ∈ ((Conn.recv fam cfg ix k bytes now : Model F Step).run s).1.take, fam.room o ≠ some c) ∧
    (∀ o ∈ ((Conn.filed fam cfg k ids : Model F Step).run s).1.send, NoticeOnly fam s cid c o) ∧
    (∀ o ∈ ((Conn.tick fam cfg ix k now : Model F Step).run s).1.send, NoticeOnly fam s cid c o)

/-! ## E1: then the cut -/

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

theorem sessionOf_state (f : Fact) (s : DB F) : ((sessionOf f : Model F _).run s).2 = s := by
  cases f with
  | established cid c peer h sk rk dialer =>
    simp only [sessionOf, Model.run_bind, Model.run_pure]
    cases dialer
    · simp only [Bool.false_eq_true, ite_false, Model.run_bind, run_getOp, Model.run_pure]; rfl
    · rfl
  | _ => rfl

theorem sessionsOf_state : ∀ (rs : List (Id × Fact)) (s : DB F),
    ((sessionsOf rs : Model F (List (Id × B × Bool × B × Nat))).run s).2 = s
  | [], _ => rfl
  | (_, f) :: t, s => by
    simp only [sessionsOf, Model.run_bind, Model.run_pure]
    rw [sessionsOf_state t, sessionOf_state]

theorem allSessions_state (s : DB F) :
    ((allSessions : Model F (List (Id × B × Bool × B × Nat))).run s).2 = s := by
  simp only [allSessions, Model.run_bind, run_rows, Model.run_pure]
  exact sessionsOf_state _ s

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
and every removal owed to the peer is settled on cid (given:
`conn.settled`), then cid carries nothing, `sessions` does not list it,
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

/-! ## E2 on the bare wire -/

/-! ## E3: the handshake runs on the nodes' keys -/

/-- **A responder opens with its node's key (`opened_endpoint`).** An
`opened` checks out only citing the request and an endpoint fact whose
key is the request's addressee; message 1 is read with that endpoint's
secret as the responder's static and the request's sender key as the
initiator's. -/
theorem opened_endpoint (K : Keys) {o : Op} {fs : List F} {r c frm addr : B} {hs : List B}
    (h : Opened.check K o fs = some (.opened r c frm addr hs)) :
    ∃ to m1 pk sk, fs = [.inr (.request to frm m1), .inl (.endpoint pk sk)] ∧ pk = to ∧
      (Noise.read1 K.suite prologue sk frm m1).isSome := by
  unfold Opened.check at h
  split at h
  · rename_i to frm' m1 pk sk
    split at h
    · cases h
    · rename_i hpk
      split at h
      · rename_i x hr
        split at h
        · simp only [Option.some.injEq, Fact.opened.injEq] at h
          obtain ⟨_, _, rfl, _, _⟩ := h
          exact ⟨to, m1, pk, sk, rfl, Decidable.of_not_not hpk, by rw [hr]; rfl⟩
        · cases h
      · cases h
  · cases h

/-- **A session is between two nodes' keys (`established_endpoint`).**
An `established` checks out only citing the connection, the request,
this side's ephemeral and an endpoint fact (pk, sk). The responder's
endpoint is the request's addressee and its peer the sender; the
initiator's is the sender and its peer the addressee; each side runs
its half of KK with sk as its static and the peer's key as the remote
static. Device keys never enter the handshake. -/
theorem established_endpoint (K : Keys) {o : Op} {fs : List F} {cid c peer h sk' rk : B}
    {dialer : Bool} (hc : Established.check K o fs = some (.established cid c peer h sk' rk dialer)) :
    ∃ r m2 to frm m1 ofE pkE esk pk sk,
      fs = [.inr (.connection r m2), .inr (.request to frm m1), .inr (.eph ofE pkE esk),
        .inl (.endpoint pk sk)] ∧
      ((dialer = false ∧ pk = to ∧ peer = frm ∧ (Noise.read1 K.suite prologue sk frm m1).isSome) ∨
       (dialer = true ∧ pk = frm ∧ peer = to ∧ (Noise.sent1 K.suite prologue sk esk to m1).isSome)) := by
  unfold Established.check at hc
  split at hc
  · rename_i r m2 to frm m1 ofE pkE esk pk sk
    refine ⟨r, m2, to, frm, m1, ofE, pkE, esk, pk, sk, rfl, ?_⟩
    simp only at hc
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
              · simp only [Option.some.injEq, Fact.established.injEq] at hc
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
                simp only [h5, Option.bind_some, Option.some.injEq, Fact.established.injEq] at hc
                obtain ⟨_, _, rfl, _, _, _, rfl⟩ := hc
                exact ⟨rfl, hfrm, rfl, rfl⟩
        · cases hc
  · cases hc

/-- **"Me" is this node's key (`meV_node`).** The node is in c as its
key: `meV c` is this node's endpoint key, and only while `Community.mine`
names a device of c whose secret it holds. -/
theorem meV_node (s : DB F) {c me : B} (h : (meV c).eval s = some me) :
    (∃ sk, ((Community.nodeKey).liftL : View F _).eval s = some (me, sk)) ∧
    ∃ d a, ((Community.mine c).liftL : View F _).eval s = some (d, a) := by
  unfold meV at h
  rw [View.eval_bind] at h
  cases hm : ((Community.mine c).liftL : View F _).eval s with
  | none => rw [hm] at h; cases h
  | some da =>
    rw [hm] at h
    simp only [View.eval_bind, View.eval_pure] at h
    obtain ⟨⟨pk, sk⟩, hk, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨⟨sk, hk⟩, da.1, da.2, rfl⟩

/-! ## E2 on the bare wire -/

section
variable [fr : Fresh (Model F)]

/-- An op of the Connection family: what open, answer and establish
write. -/
def ConnOp (o : Op) : Prop := ∃ (reqs : List Id) (b : Body), o = mkOp reqs b

/-- **Connection ops are not shared**: in the node's family their room
is none, so sync never offers them. -/
theorem room_connOp (C : Community.Crypto) (K : Keys) {o : Op} (h : ConnOp o) :
    (node C K).room o = none := by
  obtain ⟨reqs, b, rfl⟩ := h
  have hk : (mkOp reqs b).kind = b.kind := rfl
  have ho : owns b.kind = true := by cases b <;> rfl
  simp only [Family.room, node, Family.sum, family, hk, ho, ite_true, scopeOf]
  by_cases hb : b.kind = 33 ∨ b.kind = 35 <;> simp [hb]


theorem openEach_conn (epOp : Id) : ∀ (rs : List (Id × Fact)) (s : DB F),
    ∀ o ∈ ((openEach epOp rs : Model F (List Op)).run s).1, ConnOp o
  | [], _, _, h => by cases h
  | (r, _) :: t, s, o, h => by
    simp only [openEach, Model.run_bind, Model.run_pure] at h
    by_cases hz : ((count opened.byRequest [r] : Model F Nat).run s).1 = 0
    · rw [if_pos hz] at h
      rcases List.mem_cons.1 h with rfl | h
      · exact ⟨_, _, rfl⟩
      · exact openEach_conn epOp t s o h
    · rw [if_neg hz] at h
      exact openEach_conn epOp t s o h

theorem openAll_conn : ∀ (eps : List (B × B × Id)) (s : DB F),
    ∀ o ∈ ((openAll eps : Model F (List Op)).run s).1, ConnOp o
  | [], _, _, h => by cases h
  | (pk, _, epOp) :: t, s, o, h => by
    simp only [openAll, Model.run_bind, run_rows, Model.run_pure, List.mem_append] at h
    rcases h with h | h
    · exact openEach_conn epOp _ s o h
    · exact openAll_conn t _ o h

theorem reply_conn {K : Keys} {r sk frm m1 f : B} {co : Op} (h : Reply.op K r sk frm m1 f = some co) :
    ConnOp co := by
  unfold Reply.op at h
  simp only [Option.bind_eq_bind] at h
  cases h1 : Noise.read1 K.suite prologue sk frm m1 with
  | none => simp [h1] at h
  | some x =>
    obtain ⟨st, re, _⟩ := x
    simp only [h1, Option.bind_some] at h
    cases h2 : Noise.write2 K.suite st f frm re .empty with
    | none => simp [h2] at h
    | some y =>
      simp only [h2, Option.bind_some, Option.some.injEq, pure] at h
      exact ⟨_, _, h.symm⟩

theorem run_arrivedFrom (x : Id) (s : DB F) : ((arrivedFrom x : Model F (Option B)).run s).2 = s := rfl

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
      | request to frm' m1 =>
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
    | opened r c frm _ _ =>
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

theorem establishConns_conn (r e epOp : Id) : ∀ (rs : List (Id × Fact)) (s : DB F),
    ∀ o ∈ ((establishConns r e epOp rs : Model F (List Op)).run s).1, ConnOp o
  | [], _, _, h => by cases h
  | (cid, _) :: t, s, o, h => by
    simp only [establishConns, Model.run_bind, Model.run_pure] at h
    by_cases hz : ((count established.byConn [cid] : Model F Nat).run s).1 = 0
    · rw [if_pos hz] at h
      rcases List.mem_cons.1 h with rfl | h
      · exact ⟨_, _, rfl⟩
      · exact establishConns_conn r e epOp t s o h
    · rw [if_neg hz] at h
      exact establishConns_conn r e epOp t s o h

theorem establishReqs_conn (epOp : Id) : ∀ (rs : List (Id × Fact)) (s : DB F),
    ∀ o ∈ ((establishReqs epOp rs : Model F (List Op)).run s).1, ConnOp o
  | [], _, _, h => by cases h
  | (r, _) :: t, s, o, h => by
    simp only [establishReqs, Model.run_bind, run_rows] at h
    generalize (List.map (fun x => (x.1.snd, x.snd)) (Engine.eval s (eph.byOf.query [r])).rights) = l at h
    cases l with
    | nil =>
      simp only [Model.run_bind, Model.run_pure, List.nil_append] at h
      exact establishReqs_conn epOp t _ o h
    | cons p t' =>
      simp only [Model.run_bind, run_rows, Model.run_pure, List.mem_append] at h
      rcases h with h | h
      · exact establishConns_conn r _ epOp _ s o h
      · exact establishReqs_conn epOp t _ o h

theorem establishAll_conn : ∀ (eps : List (B × B × Id)) (s : DB F),
    ∀ o ∈ ((establishAll eps : Model F (List Op)).run s).1, ConnOp o
  | [], _, _, h => by cases h
  | (pk, _, epOp) :: t, s, o, h => by
    simp only [establishAll, Model.run_bind, run_rows, Model.run_pure, List.mem_append] at h
    rcases h with h | h
    · exact establishReqs_conn epOp _ s o h
    · exact establishAll_conn t _ o h

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
    | opened r c frm addr hs =>
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

theorem body_conn (reqs : List Id) (b : Body) : (decode (mkOp reqs b).body : Option Body) = some b :=
  Codec.decode_encode b

/-- Fresh bytes that leave the store as it is, as the model's do. -/
def FreshPure : Prop := ∀ s : DB F, ((Fresh.fresh : Model F B).run s).2 = s

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
      | request to frm' m1 =>
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

theorem reply_reqs {K : Keys} {r sk frm m1 f : B} {co : Op} (h : Reply.op K r sk frm m1 f = some co) :
    co.reqs = [r] ∧ ∃ m2, co = mkOp [r] (.connection m2) := by
  unfold Reply.op at h
  simp only [Option.bind_eq_bind] at h
  cases h1 : Noise.read1 K.suite prologue sk frm m1 with
  | none => simp [h1] at h
  | some x =>
    obtain ⟨st, re, _⟩ := x
    simp only [h1, Option.bind_some] at h
    cases h2 : Noise.write2 K.suite st f frm re .empty with
    | none => simp [h2] at h
    | some y =>
      simp only [h2, Option.bind_some, Option.some.injEq, pure] at h
      subst h; exact ⟨rfl, _, rfl⟩

theorem answerAll_trusted (hfr : FreshPure) (K : Keys) (eps : List (B × B × Id)) :
    ∀ (rs : List (Id × Fact)) (s : DB F), ∀ o ∈ ((answerAll K eps rs : Model F (List Op)).run s).1,
      ∀ m2, (decode o.body : Option Body) = some (.connection m2) →
      ∃ x r c frm addr hs ro to frm' m1, (x, Fact.opened r c frm addr hs) ∈ rs ∧ o.reqs = [r] ∧
        s.ops r = some ro ∧ (decode ro.body : Option Body) = some (.request to frm' m1) ∧
        ((trusts c to frm).liftL : View F Bool).eval s = true
  | [], _, _, h, _, _ => by cases h
  | (x, f) :: t, s, o, h, m2, hb => by
    cases f with
    | opened r c frm addr hs =>
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

theorem openEach_state (epOp : Id) : ∀ (rs : List (Id × Fact)) (s : DB F),
    ((openEach epOp rs : Model F (List Op)).run s).2 = s
  | [], _ => rfl
  | (_, _) :: t, s => by
    simp only [openEach, Model.run_bind, Model.run_pure]
    exact openEach_state epOp t _

theorem openAll_state : ∀ (eps : List (B × B × Id)) (s : DB F), ((openAll eps : Model F (List Op)).run s).2 = s
  | [], _ => rfl
  | (_, _, epOp) :: t, s => by
    simp only [openAll, Model.run_bind, Model.run_pure]
    rw [openAll_state t, openEach_state]; rfl

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
    | opened r c frm addr hs =>
      simp only [deliverAll, Model.run_bind, Model.run_pure]
      rw [deliverAll_state fam t, joinsOf_state]
    | _ => exact deliverAll_state fam t s

theorem openEach_body (epOp : Id) : ∀ (rs : List (Id × Fact)) (s : DB F),
    ∀ o ∈ ((openEach epOp rs : Model F (List Op)).run s).1, (decode o.body : Option Body) = some .opened
  | [], _, _, h => by cases h
  | (r, _) :: t, s, o, h => by
    simp only [openEach, Model.run_bind, Model.run_pure] at h
    by_cases hz : ((count opened.byRequest [r] : Model F Nat).run s).1 = 0
    · rw [if_pos hz] at h
      rcases List.mem_cons.1 h with rfl | h
      · exact body_conn _ _
      · exact openEach_body epOp t s o h
    · rw [if_neg hz] at h
      exact openEach_body epOp t s o h

theorem openAll_body : ∀ (eps : List (B × B × Id)) (s : DB F),
    ∀ o ∈ ((openAll eps : Model F (List Op)).run s).1, (decode o.body : Option Body) = some .opened
  | [], _, _, h => by cases h
  | (pk, _, epOp) :: t, s, o, h => by
    simp only [openAll, Model.run_bind, run_rows, Model.run_pure, List.mem_append] at h
    rcases h with h | h
    · exact openEach_body epOp _ s o h
    · exact openAll_body t _ o h

theorem establishConns_body (r e epOp : Id) : ∀ (rs : List (Id × Fact)) (s : DB F),
    ∀ o ∈ ((establishConns r e epOp rs : Model F (List Op)).run s).1,
      (decode o.body : Option Body) = some .established
  | [], _, _, h => by cases h
  | (cid, _) :: t, s, o, h => by
    simp only [establishConns, Model.run_bind, Model.run_pure] at h
    by_cases hz : ((count established.byConn [cid] : Model F Nat).run s).1 = 0
    · rw [if_pos hz] at h
      rcases List.mem_cons.1 h with rfl | h
      · exact body_conn _ _
      · exact establishConns_body r e epOp t s o h
    · rw [if_neg hz] at h
      exact establishConns_body r e epOp t s o h

theorem establishReqs_body (epOp : Id) : ∀ (rs : List (Id × Fact)) (s : DB F),
    ∀ o ∈ ((establishReqs epOp rs : Model F (List Op)).run s).1,
      (decode o.body : Option Body) = some .established
  | [], _, _, h => by cases h
  | (r, _) :: t, s, o, h => by
    simp only [establishReqs, Model.run_bind, run_rows] at h
    generalize (List.map (fun x => (x.1.snd, x.snd)) (Engine.eval s (eph.byOf.query [r])).rights) = l at h
    cases l with
    | nil =>
      simp only [Model.run_bind, Model.run_pure, List.nil_append] at h
      exact establishReqs_body epOp t _ o h
    | cons p t' =>
      simp only [Model.run_bind, run_rows, Model.run_pure, List.mem_append] at h
      rcases h with h | h
      · exact establishConns_body r _ epOp _ s o h
      · exact establishReqs_body epOp t _ o h

theorem establishAll_body : ∀ (eps : List (B × B × Id)) (s : DB F),
    ∀ o ∈ ((establishAll eps : Model F (List Op)).run s).1,
      (decode o.body : Option Body) = some .established
  | [], _, _, h => by cases h
  | (pk, _, epOp) :: t, s, o, h => by
    simp only [establishAll, Model.run_bind, run_rows, Model.run_pure, List.mem_append] at h
    rcases h with h | h
    · exact establishReqs_body epOp _ s o h
    · exact establishAll_body t _ o h

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
  have hfirst : ∀ (n : Nat), q ∈ (if n = 0 then [Recv.op o.id none addr at_] else []) → False := by
    intro n hm
    split at hm
    · rw [List.mem_singleton] at hm; subst hm
      unfold Recv.op at hb; rw [body_conn] at hb; cases hb
    · cases hm
  simp only [onArrival, Model.run_bind, Option.isSome_none, Bool.false_eq_true, ite_false] at hq
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
        exact (hfirst _ hq).elim
    · exact (hfirst _ hq).elim
  · exact (hfirst _ hq).elim

end

end Connection
