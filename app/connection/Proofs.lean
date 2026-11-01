import engine.core.Project
import engine.wire.NodeLaws
import app.connection.Commands
import app.connection.Family
import app.connection.eph.Commands
import app.connection.established.Commands
import app.connection.established.Proofs
import app.connection.opened.Commands
import app.connection.opened.Proofs
import app.connection.recv.Commands
import app.connection.request.Commands
import engine.sync.NoticeLaws
import app.connection.connection.Commands
import app.connection.connection.Op
import app.connection.connection.Proofs
import app.connection.connection.Validate
import app.connection.eph.Op
import app.connection.eph.Validate
import app.connection.established.Op
import app.connection.established.Validate
import app.connection.given.Commands
import app.connection.given.Op
import app.connection.given.Validate
import app.connection.opened.Op
import app.connection.opened.Validate
import app.connection.recv.Op
import app.connection.recv.Validate
import app.connection.request.Op
import app.connection.request.Validate
import app.connection.send.Commands
import app.connection.send.Op
import app.connection.send.Proofs
import app.connection.send.Validate
import engine.wire.Noise
import engine.wire.NoiseSymbolic

/-!
`connection`: laws about the op types in this folder and below.
-/
namespace Connection
open Engine Codec

/-- **Only the two handshake messages cross the bare wire.** -/
theorem wire_kinds (o : Op) (h : scopeOf o = .conn) : o.kind = 33 ∨ o.kind = 35 := by
  unfold scopeOf at h
  split at h
  · assumption
  · cases h

/-- Every other connection op is local. -/
theorem local_kinds (o : Op) (h : ¬ (o.kind = 33 ∨ o.kind = 35)) : scopeOf o = .local := by
  simp [scopeOf, h]
end Connection
namespace Connection
open Engine Codec
section
open Engine.Sync

theorem sessionKeys_reads (cid : Id) (h : Held F) : ((sessionKeys cid : HeldM F _) h).2 = h := rfl

/-- What `openFrame` does, on held data: the session the frame names,
that session's receive key, and the AEAD check under it. -/
theorem openFrame_run (K : Keys) (b : B) (h : Held F) :
    (openFrame K b : HeldM F _) h =
      ((match Frame.cid b with
        | none => none
        | some cid => match ((sessionKeys cid : HeldM F _) h).1 with
          | some (_, rk) => Frame.open K rk b
          | none => none), h) := by
  unfold openFrame
  cases Frame.cid b with
  | none => rfl
  | some cid =>
    simp only [HeldM.bind_apply]
    rw [sessionKeys_reads]
    cases ((sessionKeys cid : HeldM F _) h).1 with
    | none => rfl
    | some p => rfl

theorem openFrame_reads (K : Keys) (b : B) (h : Held F) : ((openFrame K b : HeldM F _) h).2 = h := by
  rw [openFrame_run]

/-- **A frame opens only under its session's receive key.** `openFrame`
gives a session and bytes only if the frame names that session, this
node holds its keys, and the frame's AEAD check passes under the receive
key, giving those bytes. -/
theorem openFrame_auth {K : Keys} {b : B} {h : Held F} {cid p : B}
    (ho : ((openFrame K b : HeldM F _) h).1 = some (cid, p)) :
    Frame.cid b = some cid ∧ ∃ sk rk, ((sessionKeys cid : HeldM F _) h).1 = some (sk, rk) ∧
      K.fdec rk (b.extract 33 57) (Frame.ad cid) (b.extract 57 b.size) = some p := by
  rw [openFrame_run] at ho
  simp only at ho
  cases hc : Frame.cid b with
  | none => rw [hc] at ho; cases ho
  | some c =>
    rw [hc] at ho
    simp only at ho
    cases hk : ((sessionKeys c : HeldM F _) h).1 with
    | none => rw [hk] at ho; cases ho
    | some k =>
      obtain ⟨sk, rk⟩ := k
      rw [hk] at ho
      simp only at ho
      have hc' := hc
      unfold Frame.cid at hc'
      unfold Frame.open at ho
      split at ho
      · cases ho
      · rename_i hn
        simp only [hn, ite_false, Option.some.injEq] at hc'
        subst hc'
        dsimp only at ho
        cases hf : K.fdec rk (b.extract 33 57) (Frame.ad (b.extract 1 33)) (b.extract 57 b.size) with
        | none => rw [hf] at ho; cases ho
        | some q =>
          rw [hf] at ho
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at ho
          obtain ⟨rfl, rfl⟩ := ho
          exact ⟨rfl, sk, rk, hk, hf⟩

theorem tagged_parts (t : UInt8) (f : B) :
    (tagged t f)[0]? = some t ∧ (tagged t f).extract 1 (tagged t f).size = f := by
  have h1 : (ByteArray.mk #[t]).size = 1 := rfl
  refine ⟨?_, ?_⟩
  · have e : (tagged t f)[0]? = (ByteArray.mk #[t])[0]? := by
      show (ByteArray.mk #[t] ++ f).data[0]? = (ByteArray.mk #[t]).data[0]?
      rw [ByteArray.data_append, Array.getElem?_append_left (by show 0 < 1; decide)]
    rw [e]; rfl
  · exact ByteArray.extract_append_eq_right h1.symm (ByteArray.size_append ..)

/-- **Authenticate before parsing.** A sealed frame f, as it arrives
(`tagged sealedTag f`), at a node running this family's `openFrame`:
unless f names a session this node holds keys for and passes its AEAD
check under that session's receive key, the node and its store are as
they were, and nothing is sent, stored or dropped. Nothing of f is
decoded on the way (`onFrame_sealed`: only what `openFrame` returns goes
on). -/
theorem sealed_auth (x : Sync F (HeldM F)) {K : Keys} (hx : x.hooks.openFrame = openFrame K)
    (n : Node) (addr f : B) (now : Nat) (h : Held F)
    (hbad : ∀ cid sk rk, Frame.cid f = some cid → ((sessionKeys cid : HeldM F _) h).1 = some (sk, rk) →
      K.fdec rk (f.extract 33 57) (Frame.ad cid) (f.extract 57 f.size) = none) :
    n.onFrame x addr (tagged sealedTag f) now h = ((n, {}), h) := by
  obtain ⟨h0, h1⟩ := tagged_parts sealedTag f
  apply sealed_unopened x n addr _ now h h0
  rw [h1, hx]
  cases ho : ((openFrame K f : HeldM F _) h).1 with
  | none => exact Prod.ext ho (openFrame_reads K f h)
  | some r =>
    obtain ⟨cid, p⟩ := r
    obtain ⟨hc, sk, rk, hk, hf⟩ := openFrame_auth ho
    rw [hbad cid sk rk hc hk] at hf
    cases hf
end
end Connection
namespace Connection
open Engine Engine.Sync Codec

/-- This node is a live member of c, as the trust rule reads it. -/
def LiveIn (s : DB F) (c : B) : Prop :=
  ∀ me, (meV c).eval s = some me → ((Community.allowPeer c me).liftL : View F Bool).eval s = true

/-- What may go out of community c on cid: a sync wire op, an op of
another room, or an op in the requirement closure, in c, of a removal
owed to the peer. -/
def NoticeOnly (fam : Family F) (s : DB F) (cid c : B) (o : Op) : Prop :=
  isWire o.kind = true ∨ fam.room o ≠ some c ∨
    ∃ x, Owed s cid c x ∧ ∃ y, s.ops y = some o ∧ ReachIn fam s.ops c x y

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
end Connection
namespace Connection
open Engine Engine.Sync
section
variable {A B : Type} [SortKey (A ⊕ B)]

theorem eval_liftL_bind {α β : Type} (s : DB (A ⊕ B)) (v : View A α) (f : α → View A β) :
    ((v >>= f).liftL : View (A ⊕ B) β).eval s =
      ((f ((v.liftL : View (A ⊕ B) α).eval s)).liftL : View (A ⊕ B) β).eval s := by
  induction v with
  | pure a => rfl
  | list q k ih => exact ih _
end
end Connection
namespace Connection
open Engine Engine.Sync Codec

theorem sessionOf_state (f : Fact) (s : DB F) : ((sessionOf f : Model F _).run s).2 = s := by
  cases f with
  | ofEstablished x =>
    obtain ⟨cid, c, peer, h, sk, rk, dialer⟩ := x
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
end Connection
namespace Connection
open Engine Engine.Sync Codec
section
variable [fr : Fresh (Model F)]

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

theorem run_arrivedFrom (x : Id) (s : DB F) : ((arrivedFrom x : Model F (Option B)).run s).2 = s := rfl

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

/-- Fresh bytes that leave the store as it is, as the model's do. -/
def FreshPure : Prop := ∀ s : DB F, ((Fresh.fresh : Model F B).run s).2 = s

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

/-- What `receiptFor` writes, read in the node's store, is receipts of
the op: nothing else. -/
theorem receiptFor_receipts (s : DB F) (o : Op) {r : Op}
    (hr : r ∈ ((Community.receiptFor o).liftL : View F (List Op)).eval s) :
    ∃ j, r = Community.receipt o.id j := by
  unfold Community.receiptFor at hr
  by_cases hkind : o.kind ≠ 23
  · simp [hkind] at hr; cases hr
  simp only [hkind, ite_false] at hr
  split at hr
  · rename_i n _ _ _
    by_cases hn : n < Community.countCap
    · simp [hn] at hr; cases hr
    · simp only [hn, ite_false, Rel.read] at hr
      rw [eval_liftL_bind] at hr
      split at hr
      · cases hr
      · rw [eval_liftL_bind] at hr
        exact ⟨_, List.mem_singleton.1 hr⟩
  · cases hr

theorem helloOf_state (K : Keys) (sk r to m1 : B) (s : DB F) :
    ((helloOf K sk r to m1 : Model F _).run s).2 = s := by
  simp only [helloOf, Model.run_bind, run_rows]
  split <;> rfl

theorem requestOf_state (K : Keys) (sk inviter : B) (req : Id) :
    ∀ (rs : List (Id × Fact)) (s : DB F), ((requestOf K sk inviter req rs : Model F _).run s).2 = s
  | [], _ => rfl
  | (r, f) :: rest, s => by
    cases f with
    | ofRequest x =>
      obtain ⟨t, frm, m1⟩ := x
      simp only [requestOf, Model.run_bind]
      by_cases ht : t = inviter
      · rw [if_pos ht]
        simp only [Model.run_bind, Model.run_pure]
        rw [helloOf_state]
        split
        · rfl
        · exact requestOf_state K sk inviter req rest s
      · rw [if_neg ht]; exact requestOf_state K sk inviter req rest s
    | _ => exact requestOf_state K sk inviter req rest s

/-- What sending a pending join needs here: its request is stored (and,
while waiting, unanswered: no connection cites it); or this node holds
none, holds the join's request, and message 1 seals to the inviter's
key. -/
def Unanswered (K : Keys) (listen : B) (s : DB F) (pk sk c inviter : B) (req : Id) (waiting : Bool) : Prop :=
  -- the request a pending join is sent as, read at s
  match ((requestOf K sk inviter req ((rows request.byFrm [pk] : Model F _).run s).1 : Model F _).run s).1 with
  | some r => (waiting = true → (Engine.eval s (connection.byRequest.query [r] (limit := some 0))).total = 0) ∧
      (s.ops r).isSome
  | none => ∃ jr, s.ops req = some jr ∧ ∀ e, (Request.op K sk inviter e (hello c listen [jr])).isSome
end
end Connection
namespace Connection
open Engine
variable {C : Community.Crypto} {K : Keys} {s : DB F}
open Community (Admitted Removed)

/-- **The node lets in no node whose devices are all cut.** -/
theorem refuse_nonmember_node (h : Inv (node C K) s) (hq : s.queue = []) (c : Id) (e : Community.Key)
    (hd : ∀ u d, Admitted C (community C s).ops c u d e → Community.Cut C (community C s).ops c d) :
    ((Community.allowPeer c e).liftL : View F Bool).eval s = false := by
  rw [view_node h hq (Community.reads_allowPeer c e)]
  exact Community.refuse_nonmember (community_inv h hq) hq c e hd

/-- **Whom the node dials:** the live devices. -/
theorem members_iff_node (h : Inv (node C K) s) (hq : s.queue = []) (c : Id) (d : Community.Key) :
    d ∈ ((Community.members c).liftL : View F (List Community.Key)).eval s ↔
      Community.Live C (community C s).ops c d := by
  rw [view_node h hq (Community.reads_members c)]
  exact Community.members_iff (community_inv h hq) hq c d

/-- **Who the node seals a content key to:** the node keys of live
devices. -/
theorem recipients_iff_node (h : Inv (node C K) s) (hq : s.queue = []) (c : Id) (e : Community.Key) :
    e ∈ ((Community.recipients c).liftL : View F (List Community.Key)).eval s ↔
      ∃ u d, Admitted C (community C s).ops c u d e ∧ Community.Live C (community C s).ops c d := by
  rw [view_node h hq (Community.reads_recipients c)]
  exact Community.recipients_iff (community_inv h hq) hq c e

/-- **Every state the running node reaches settles where these laws
apply:** it keeps `Inv` (`reach_inv`), and judging empties its queue
(`drain_terminates`). -/
theorem node_settles {L : List Op} (hd : Distinct L) (hr : Reach (node C K) L s) :
    ∃ n, Inv (node C K) (drainS (node C K) n s) ∧ (drainS (node C K) n s).queue = [] :=
  let ⟨n, hn⟩ := drain_terminates hd s hr
  ⟨n, reach_inv (reach_drain hr n), hn⟩
end Connection
namespace Connection
open Engine Engine.Sync
section
variable {A B : Type} [SortKey (A ⊕ B)]

theorem eval_liftL_pure {α : Type} (s : DB (A ⊕ B)) (a : α) :
    ((Pure.pure a : View A α).liftL : View (A ⊕ B) α).eval s = a := rfl
end
end Connection
namespace Connection
open Engine
section
variable {K : Keys}

theorem seal_parts (cid sk n p : B) :
    Frame.seal K cid sk n p = ⟨#[Frame.version]⟩ ++ (cid ++ (n ++ K.fenc sk n (Frame.ad cid) p)) := by
  simp [Frame.seal, ByteArray.append_assoc]

/-- **A frame opens to what was sealed, under the matching key.** The
crypto premises concern this frame's inputs, so callers can check them
without assuming that malformed keys and nonces encrypt successfully. -/
theorem open_seal {cid sk n p : B}
    (hd : K.fdec sk n (Frame.ad cid) (K.fenc sk n (Frame.ad cid) p) = some p)
    (he : (K.fenc sk n (Frame.ad cid) p).size = p.size + 16)
    (hc : cid.size = 32) (hn : n.size = 24) :
    Frame.open K sk (Frame.seal K cid sk n p) = some (cid, p) := by
  have h1 : (⟨#[Frame.version]⟩ : B).size = 1 := rfl
  have hs : (Frame.seal K cid sk n p).size = 73 + p.size := by
    rw [seal_parts]; simp only [ByteArray.size_append, h1, hc, hn, he]; omega
  have h0 : (Frame.seal K cid sk n p).get! 0 = Frame.version := by
    rw [seal_parts]; rfl
  have hcid : (Frame.seal K cid sk n p).extract 1 33 = cid := by
    rw [seal_parts, show (33 : Nat) = 1 + 32 from rfl, show (1 : Nat) = 1 + 0 from rfl,
      ByteArray.extract_append_size_add' (by rw [h1])]
    exact ByteArray.extract_append_eq_left (by rw [hc])
  have hn' : (Frame.seal K cid sk n p).extract 33 57 = n := by
    rw [seal_parts, show (33 : Nat) = 1 + (32 + 0) from rfl, show (57 : Nat) = 1 + (32 + 24) from rfl,
      ByteArray.extract_append_size_add' (by rw [h1]), ByteArray.extract_append_size_add' (by rw [hc])]
    exact ByteArray.extract_append_eq_left (by rw [hn])
  have hct : (Frame.seal K cid sk n p).extract 57 (Frame.seal K cid sk n p).size =
      K.fenc sk n (Frame.ad cid) p := by
    rw [hs, seal_parts, show (57 : Nat) = 1 + (32 + 24) from rfl,
      show 73 + p.size = 1 + (32 + (24 + (p.size + 16))) by omega,
      ByteArray.extract_append_size_add' (by rw [h1]), ByteArray.extract_append_size_add' (by rw [hc])]
    exact ByteArray.extract_append_eq_right (by rw [hn]) (by rw [he, hn])
  unfold Frame.open
  rw [hcid, hn', hct, h0]
  simp [hd, hs]

/-- **A frame's header names the connection it was sealed for.** -/
theorem cid_seal {cid sk n p : B}
    (he : (K.fenc sk n (Frame.ad cid) p).size = p.size + 16)
    (hc : cid.size = 32) (hn : n.size = 24) :
    Frame.cid (Frame.seal K cid sk n p) = some cid := by
  have h1 : (⟨#[Frame.version]⟩ : B).size = 1 := rfl
  have hs : (Frame.seal K cid sk n p).size = 73 + p.size := by
    rw [seal_parts]; simp only [ByteArray.size_append, h1, hc, hn, he]; omega
  have h0 : (Frame.seal K cid sk n p).get! 0 = Frame.version := by rw [seal_parts]; rfl
  have hcid : (Frame.seal K cid sk n p).extract 1 33 = cid := by
    rw [seal_parts, show (33 : Nat) = 1 + 32 from rfl, show (1 : Nat) = 1 + 0 from rfl,
      ByteArray.extract_append_size_add' (by rw [h1])]
    exact ByteArray.extract_append_eq_left (by rw [hc])
  unfold Frame.cid
  rw [hcid, h0]
  simp [hs]

end
end Connection

