/-
A plain node's entry points on a held store, as terms, and the three
hops a round's leg is made of, proven of the running code over frames
of any payloads (docs/PROOFS.md, "The pilot"):

- **Closed forms.** `write_run` (Run.lean), `store_run`, `fanout_run`,
  `apply_run`, `finish_run`, and a session's frame as a fold of
  `frameStep` over its payloads (`onFrame_sealed`). A loop whose turns
  only yield is a fold (`forIn_fold`).
- **The node invariant** (`NodeOk`): the index and every snapshot name
  stored ops, no session is the family's, each op is filed under its id,
  and everything logged is stored. Every payload keeps it
  (`frameStep_ok`), grows the store, keeps the sessions and addresses,
  and only adds to what is sent.
  `reach_ok`: every node of every world the plain world reaches keeps
  it, against any attacker (every entry point, restart included).
- **The hops**, at a node with the invariant, over a whole frame:
  - `claim_wants` (H1): a claim of ids is answered with a want for each
    listed id the node lacks, in a frame to the claim's sender;
  - `want_sends` (H2): a want for an op the node holds in a room the
    session shows is answered with the op;
  - `op_taken` (H3): an op of a room the session shows is stored.

Laws that run a want or a tick take the walk's laws (`WalkLaws`) as a
premise, until a3/hostile's structural `walkN` lands.
-/
import engine.world.Plain
namespace Engine.World
open Engine Engine.Sync
variable {F : Type}

/-- A loop whose every turn yields is a fold over its state and the store. -/
theorem forIn_fold {α β} (l : List α) (f : α → β → HeldM F (ForInStep β))
    (hy : ∀ a b h, ((f a b).run h).1 = .yield ((f a b).run h).1.value) :
    ∀ b h, (forIn l b f).run h = l.foldl (fun p a => (((f a p.1).run p.2).1.value, ((f a p.1).run p.2).2)) (b, h) := by
  induction l with
  | nil => intro b h; rfl
  | cons a t ih =>
    intro b h
    rw [List.forIn_cons, HeldM.run_bind, hy a b h]
    exact ih _ _

section
variable (fam : Family F) (cfg : Config) (rms : Held F → Id → List Id)

@[simp] theorem write_nil (n : Node) (h : Held F) : (n.write (psync fam cfg rms) []).run h = ((n, []), h) := by
  rw [write_run]; rfl

@[simp] theorem settle_run (n : Node) (st : List (Id × Status)) (h : Held F) :
    (n.settle (psync fam cfg rms) st).run h = (n, h) := by
  have : (st.flatMap fun (p : Id × Status) => match p with
      | (cid, .settled r) => (psync fam cfg rms).hooks.settled cid r) = [] := by
    induction st with
    | nil => rfl
    | cons p t ih => obtain ⟨_, ⟨_⟩⟩ := p; simp at ih ⊢
  simp only [Node.settle, Node.put, this, intake, HeldM.run_bind]
  split <;> rfl

@[simp] theorem store_nil (n : Node) (mine : Bool) (h : Held F) :
    (n.store (psync fam cfg rms) [] mine).run h = ((n, {}), h) := by
  simp only [Node.store, Node.put, HeldM.run_bind]
  cases mine <;> simp [intake, write_nil]

/-- The plain family answers nothing: storing is a put, then a fanout. -/
theorem store_run (n : Node) (ops : List Op) (mine : Bool) (h : Held F) :
    (n.store (psync fam cfg rms) ops mine).run h =
      let p := (n.put (psync fam cfg rms) ops mine).run h
      if p.1.2.isEmpty then ((p.1.1, {}), p.2) else (p.1.1.fanout (psync fam cfg rms) p.1.2).run p.2 := by
  simp only [Node.store, HeldM.run_bind]
  split
  · rfl
  · simp [Std.Legacy.Range.forIn_eq_forIn_range', List.range']


theorem Keeps.run_eq {α} {p : HeldM F α} (hk : Keeps p) (h : Held F) : p.run h = ((p.run h).1, h) :=
  Prod.ext rfl (hk h)

/-- `Node.fanout`'s loop, one connection: its rooms read afresh, then the
stream's offers. -/
def fanStep (h : Held F) (ids : List Id) (st : List (Id × Conn) × Acts × List (Id × Status)) (p : Id × Conn) :
    List (Id × Conn) × Acts × List (Id × Status) :=
  let s := ((Conn.filed fam cfg (p.2.setRooms (rms h p.1)) ids : HeldM F Step).run h).1
  ((p.1, s.conn) :: st.1, st.2.1 ++ sends p.1 s.send, st.2.2 ++ s.status.map (p.1, ·))

/-- **`Node.fanout` on a held store, as a term.** -/
theorem fanout_run (n : Node) (ids : List Id) (h : Held F) :
    (n.fanout (psync fam cfg rms) ids).run h =
      (({ n with conns := (n.conns.foldl (fanStep fam cfg rms h ids) ([], {}, [])).1.reverse },
        (n.conns.foldl (fanStep fam cfg rms h ids) ([], {}, [])).2.1), h) := by
  unfold Node.fanout
  rw [HeldM.run_bind, forIn_yield _ _ (fanStep fam cfg rms h ids) h (fun p st => by
    obtain ⟨cid, c⟩ := p
    simp only [HeldM.run_bind, refresh_run, psync_fam, psync_cfg]
    rw [Keeps.run_eq (filed_keeps fam cfg _ ids) h]
    rfl)]
  simp only [HeldM.run_bind, settle_run]
  rfl

theorem Acts.append_def (a b : Acts) : a ++ b = ⟨a.send ++ b.send, a.drop ++ b.drop⟩ := rfl
@[simp] theorem Acts.append_empty (a : Acts) : a ++ ({} : Acts) = a := by
  cases a; simp [Acts.append_def]
@[simp] theorem foldl_keep {α β} (l : List α) (b : β) : l.foldl (fun b _ => b) b = b := by
  induction l <;> simp [*]

theorem seal_keeps (n : Node) (out : Acts) : Keeps (n.seal (psync fam cfg rms) out) := by
  unfold Node.seal; simp only [psync_sealFor]; keeps []

/-- An entry point's end, with no managed sessions: seal, and report. -/
theorem finish_run (n : Node) (out : Acts) (now : Nat) (h : Held F) (hm : n.managed = []) :
    (n.finish (psync fam cfg rms) out now).run h =
      (({ n with fresh := [] },
        { send := ((n.seal (psync fam cfg rms) out).run h).1, drop := out.drop, stored := n.fresh }), h) := by
  have hk := finish_grows fam cfg rms n out now h
  simp only [Node.finish, Node.follow, Node.flush, hm, psync_established, psync_outbox, psync_retired,
    psync_closing, HeldM.pure_bind, List.isEmpty_nil, ite_true, List.forIn_nil, List.append_nil,
    Bool.not_true, Bool.false_eq_true, ite_false, HeldM.run_bind, HeldM.run_pure]
  rw [Keeps.run_eq (seal_keeps fam cfg rms _ _) h]
  simp only [Acts.append_empty]
  rw [Keeps.forIn' _ _ (fun _ _ => Keeps.pure' _) h]

/-- The connections after a step on session cid: its connection replaced. -/
def setConn (n : Node) (cid : Id) (c : Conn) : Node :=
  { n with conns := n.conns.map fun p => if p.1 = cid then (cid, c) else p }

/-- **`Node.apply` on a held store**, for a step that does not drop: the
session's connection replaced, then the step's take stored. -/
theorem apply_run (n : Node) (cid : Id) (s : Step) (now : Nat) (h : Held F) (hd : s.drop = false) :
    (n.apply (psync fam cfg rms) cid s now).run h =
      (((((setConn n cid s.conn).store (psync fam cfg rms) s.take false).run h).1.1,
        sends cid s.send ++ (((setConn n cid s.conn).store (psync fam cfg rms) s.take false).run h).1.2),
        (((setConn n cid s.conn).store (psync fam cfg rms) s.take false).run h).2) := by
  unfold Node.apply
  simp only [hd, Bool.false_eq_true, ite_false, HeldM.run_bind, settle_run]
  rw [forIn_yield _ _ (fun arr _ => arr) _ (fun o arr => by simp [psync_recv])]
  simp [setConn]

end

/-! ## Frames -/

/-- A session's frame in the clear, carrying these payloads. -/
def plainFrame (cid : Id) (ps : List ByteArray) : ByteArray :=
  tagged sealedTag (Codec.encode (cid, Codec.encode ps))

theorem tagged_head (t : UInt8) (b : ByteArray) : (tagged t b)[0]? = some t := by
  have h1 : (ByteArray.mk #[t]).size = 1 := rfl
  have hs : 0 < (tagged t b).size := by simp [tagged, ByteArray.size_append, h1]; omega
  rw [getElem?_pos (tagged t b) 0 hs]
  simp only [tagged]
  rw [ByteArray.getElem_append_left (by rw [h1]; omega)]
  rfl

theorem tagged_body (t : UInt8) (b : ByteArray) : (tagged t b).extract 1 (tagged t b).size = b := by
  have h1 : (ByteArray.mk #[t]).size = 1 := rfl
  exact ByteArray.extract_append_eq_right h1.symm (by simp [tagged, ByteArray.size_append, h1])

@[simp] theorem plainFrame_head (cid : Id) (ps : List ByteArray) : (plainFrame cid ps)[0]? = some 1 :=
  tagged_head _ _

@[simp] theorem plainFrame_body (cid : Id) (ps : List ByteArray) :
    (plainFrame cid ps).extract 1 (plainFrame cid ps).size = Codec.encode (cid, Codec.encode ps) :=
  tagged_body _ _

/-- A frame in the clear reads as its session and payloads. -/
@[simp] theorem peek_plainFrame (cid : Id) (ps : List ByteArray) : plainPeek (plainFrame cid ps) = some (cid, ps) := by
  simp [plainPeek, Codec.decode_encode, sealedTag]

/-- What `plainPeek` reads is a frame in the clear. -/
theorem plainFrame_of_peek {b : ByteArray} {cid : Id} {ps : List ByteArray} (h : plainPeek b = some (cid, ps)) :
    b[0]? = some 1 ∧ ∃ bundle, Codec.decode (b.extract 1 b.size) = some (cid, bundle) ∧
      (Codec.decode bundle : Option (List ByteArray)) = some ps := by
  unfold plainPeek at h
  split at h
  · rename_i h0
    refine ⟨h0, ?_⟩
    cases e : (Codec.decode (b.extract 1 b.size) : Option (Id × ByteArray)) with
    | none => rw [e] at h; cases h
    | some q =>
      rw [e] at h
      obtain ⟨c, bd⟩ := q
      cases e2 : (Codec.decode bd : Option (List ByteArray)) with
      | none => simp [e2] at h
      | some l =>
        simp [e2] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨bd, rfl, e2⟩
  · cases h

theorem bundles_cover (max : Nat) : ∀ (l : List ByteArray), ∀ x ∈ l, ∃ g ∈ bundles max l, x ∈ g := by
  intro l
  induction l with
  | nil => intro x hx; cases hx
  | cons b rest ih =>
    intro x hx
    unfold bundles
    split
    · rename_i he
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨[x], by simp, by simp⟩
      · obtain ⟨g, hg, _⟩ := ih x hx; rw [he] at hg; cases hg
    · rename_i g gs he
      rcases List.mem_cons.1 hx with rfl | hx
      · split
        · exact ⟨x :: g, by simp, by simp⟩
        · exact ⟨[x], by simp, by simp⟩
      · obtain ⟨g', hg', hxg⟩ := ih x hx
        rw [he] at hg'
        split
        · rcases List.mem_cons.1 hg' with rfl | hg'
          · exact ⟨b :: g', by simp, List.mem_cons_of_mem _ hxg⟩
          · exact ⟨g', List.mem_cons_of_mem _ hg', hxg⟩
        · exact ⟨g', List.mem_cons_of_mem _ hg', hxg⟩

/-- The session ids a node's sends name, collected as `Node.seal` does. -/
def cidsStep (st : List (ByteArray × ByteArray) × List Id) (x : Route × ByteArray) :
    List (ByteArray × ByteArray) × List Id :=
  match x.1 with
  | .bare a => ((a, tagged bareTag x.2) :: st.1, st.2)
  | .conn cid => if (!has st.2 cid) = true then (st.1, cid :: st.2) else (st.1, st.2)

theorem cids_fold (cid : Id) : ∀ (L : List (Route × ByteArray)) st,
    ((∃ b, (Route.conn cid, b) ∈ L) ∨ cid ∈ st.2) → cid ∈ (L.foldl cidsStep st).2 := by
  intro L
  induction L with
  | nil => intro st h; rcases h with ⟨_, h⟩ | h; cases h; exact h
  | cons x L ih =>
    intro st h
    simp only [List.foldl_cons]
    apply ih
    rcases h with ⟨b, hb⟩ | h
    · rcases List.mem_cons.1 hb with rfl | hb
      · right; simp only [cidsStep]; split
        · exact List.mem_cons_self ..
        · rename_i hh; simp only [Bool.not_eq_true', Bool.not_eq_false] at hh
          exact (Engine.has_iff _ _).1 (by simpa using hh)
      · exact Or.inl ⟨b, hb⟩
    · right; simp only [cidsStep]; split <;> (try split) <;> simp [h]

theorem foldl_cons_acc {α γ} (l : List α) (g : α → γ) (b : List γ) :
    l.foldl (fun b a => g a :: b) b = (l.map g).reverse ++ b := by
  induction l generalizing b with
  | nil => rfl
  | cons a t ih => simp [ih]

/-- Session cid's payloads among a node's sends, in order. -/
def payloadsOf (out : Acts) (cid : Id) : List ByteArray :=
  out.send.filterMap fun x => match x.fst with
    | .conn c => if c = cid then some x.snd else none
    | .bare _ => none

/-- `Node.seal`'s second loop, one session: its bundles, sealed in the clear. -/
def sealStep (cfg : Config) (n : Node) (out : Acts) (sent : List (ByteArray × ByteArray)) (cid : Id) :
    List (ByteArray × ByteArray) :=
  match n.addr? cid with
  | some a => (bundles cfg.bundle (payloadsOf out cid)).foldl (fun acc g => (a, plainFrame cid g) :: acc) sent
  | none => sent

theorem seal_fold (cfg : Config) (n : Node) (out : Acts) (x : ByteArray × ByteArray) (cid : Id)
    (hx : ∀ acc, x ∈ sealStep cfg n out acc cid) :
    ∀ (L : List Id) acc, (cid ∈ L ∨ x ∈ acc) → x ∈ L.foldl (sealStep cfg n out) acc := by
  intro L
  induction L with
  | nil => intro acc h; rcases h with h | h; cases h; exact h
  | cons c L ih =>
    intro acc h
    simp only [List.foldl_cons]
    apply ih
    rcases h with h | h
    · rcases List.mem_cons.1 h with rfl | h
      · exact Or.inr (hx acc)
      · exact Or.inl h
    · right; simp only [sealStep]; split
      · rw [foldl_cons_acc]; exact List.mem_append_right _ h
      · exact h

section
variable (fam : Family F) (cfg : Config) (rms : Held F → Id → List Id)

/-- **Every payload a node sends on a session goes out in a frame** to
the session's address, sealed in the clear. -/
theorem seal_mem (n : Node) (out : Acts) (h : Held F) (cid : Id) (p a : ByteArray)
    (hp : (Route.conn cid, p) ∈ out.send) (ha : n.addr? cid = some a) :
    ∃ g, p ∈ g ∧ (a, plainFrame cid g) ∈ ((n.seal (psync fam cfg rms) out).run h).1 := by
  simp only [Node.seal, HeldM.run_bind]
  rw [forIn_yield out.send _ cidsStep h (fun x st => by
    rcases x with ⟨r, b⟩; cases r <;> simp only [cidsStep] <;> (try split) <;> rfl)]
  rw [forIn_yield _ _ (sealStep cfg n out) h (fun c sent => by
    simp only [sealStep]
    cases hc : n.addr? c with
    | none => rfl
    | some a' =>
      simp only [HeldM.run_bind]
      rw [forIn_yield _ _ (fun acc g => (a', plainFrame c g) :: acc) h (fun g acc => by
        simp [plainFrame, psync_sealFor])]
      rfl)]
  have hpl : p ∈ payloadsOf out cid := by
    simp only [payloadsOf, List.mem_filterMap]
    exact ⟨_, hp, by simp⟩
  obtain ⟨g, hg, hpg⟩ := bundles_cover cfg.bundle _ p hpl
  refine ⟨g, hpg, ?_⟩
  simp only [HeldM.run_pure, List.mem_reverse]
  refine seal_fold cfg n out _ cid (fun acc => ?_) _ _ (Or.inl (List.mem_reverse.2
    (cids_fold cid out.send ([], []) (Or.inl ⟨p, hp⟩))))
  simp only [sealStep, ha, foldl_cons_acc]
  exact List.mem_append_left _ (List.mem_reverse.2 (List.mem_map.2 ⟨g, hg, rfl⟩))


/-! ## A frame's payloads, one at a time -/

theorem foldl_ext {α β : Type} (f g : α → β → α) (H : ∀ a b, f a b = g a b) : List.foldl f = List.foldl g :=
  funext fun a => funext fun l => by
    induction l generalizing a with
    | nil => rfl
    | cons b t ih => simp only [List.foldl_cons, H a b]; exact ih _

/-- One payload of a session's frame: the connection, its rooms read
afresh, takes it, and the node applies the step. -/
def frameStep (cid : Id) (now : Nat) (st : (Node × Acts) × Held F) (b : ByteArray) : (Node × Acts) × Held F :=
  match st.1.1.conn? cid with
  | some c =>
    let s := ((Conn.recv fam cfg st.1.1.ix (c.setRooms (rms st.2 cid)) b now : HeldM F Step).run st.2).1
    let r := (st.1.1.apply (psync fam cfg rms) cid s now).run st.2
    ((r.1.1, st.1.2 ++ r.1.2), r.2)
  | none => st

/-- **A session's frame, on a held store:** its payloads one at a time
(`frameStep`), then the entry point's end. -/
theorem onFrame_sealed (hw : WalkLaws (F := F) fam cfg) (n : Node) (a b : ByteArray) (now : Nat) (h : Held F)
    (cid : Id) (bundle : ByteArray) (inner : List ByteArray) (c : Conn)
    (h0 : b[0]? = some 1) (hb : Codec.decode (b.extract 1 b.size) = some (cid, bundle))
    (hi : (Codec.decode bundle : Option (List ByteArray)) = some inner) (hc : n.conn? cid = some c) :
    (n.onFrame (psync fam cfg rms) a b now).run h =
      ((inner.foldl (frameStep fam cfg rms cid now) ((n.setAddr cid a, {}), h)).1.1.finish (psync fam cfg rms)
        (inner.foldl (frameStep fam cfg rms cid now) ((n.setAddr cid a, {}), h)).1.2 now).run
        (inner.foldl (frameStep fam cfg rms cid now) ((n.setAddr cid a, {}), h)).2 := by
  unfold Node.onFrame
  simp only [h0, psync_openFrame, HeldM.pure_bind, hb, hc, hi, HeldM.run_bind]
  rw [forIn_fold _ _ (fun b st h => by split <;> rfl)]
  rw [foldl_ext _ (frameStep fam cfg rms cid now) (fun p b => ?_)]
  unfold frameStep
  cases hcp : p.1.1.conn? cid with
  | none => rfl
  | some c' =>
    simp only [HeldM.run_bind, refresh_run, psync_fam, psync_cfg]
    rw [Keeps.run_eq (recv_keeps fam cfg hw _ _ _ _) _]
    rfl

end

/-! ## The node invariant -/

/-- `ByteArray`'s `==` is equality: the write compares ids with it. -/
theorem byteArray_lawfulBEq : LawfulBEq ByteArray where
  eq_of_beq {a b} h := ByteArray.ext (eq_of_beq (show a.data == b.data from h))
  rfl {a} := show a.data == a.data from beq_self_eq_true a.data

attribute [local instance] byteArray_lawfulBEq

/-- Every op is stored under its own id. -/
def IdsOk (h : Held F) : Prop := ∀ x o, h.db.ops x = some o → o.id = x

/-- Every logged op is stored. -/
def LogIn (h : Held F) : Prop := ∀ o ∈ h.log, Named h o.id

/-- **What every plain node keeps:** its index and snapshots name stored
ops, no session is the family's, and its store files each op under its
id and holds everything it logged. -/
structure NodeOk (n : Node) (h : Held F) : Prop where
  sub : Sub n h
  managed : n.managed = []
  ids : IdsOk h
  log : LogIn h

theorem LogIn.ext {h h' : Held F} (e : Ext h h') (hl : LogIn h) : LogIn h' := fun o ho => by
  rcases e.2 o ho with ho | ho
  · exact (hl o ho).ext e
  · exact ho

theorem ingestS_ids (o : Op) (s : DB F) (hs : ∀ x p, s.ops x = some p → p.id = x) :
    ∀ x p, (ingestS o s).ops x = some p → p.id = x := by
  intro x p hx
  unfold ingestS at hx
  split at hx
  · exact hs x p hx
  · simp only [DB.push, DB.putOp] at hx
    split at hx
    · rename_i e; cases hx; exact e.symm
    · exact hs x p hx

theorem turnH_ids (fam : Family F) (ops : List Op) (h : Held F) (hi : IdsOk h) : IdsOk (turnH fam ops h) := by
  intro x p hx
  simp only [turnH, drainS_ops] at hx
  have : ∀ (l : List Op) (s : DB F), (∀ x p, s.ops x = some p → p.id = x) →
      ∀ x p, (l.foldl (fun s o => ingestS o s) s).ops x = some p → p.id = x := by
    intro l
    induction l with
    | nil => intro s hs; exact hs
    | cons o t ih => intro s hs; exact ih _ (ingestS_ids o s hs)
  exact this ops h.db hi x p hx

section
variable (fam : Family F) (cfg : Config) (rms : Held F → Id → List Id)

/-- What a write leaves of the node: all but its index and fresh ids. -/
theorem write_node (n : Node) (ops : List Op) (h : Held F) :
    ((n.write (psync fam cfg rms) ops).run h).1.1.conns = n.conns ∧
    ((n.write (psync fam cfg rms) ops).run h).1.1.addrs = n.addrs ∧
    ((n.write (psync fam cfg rms) ops).run h).1.1.managed = n.managed := by
  rw [write_run]; dsimp only; split <;> exact ⟨rfl, rfl, rfl⟩

theorem write_store (n : Node) (ops : List Op) (h : Held F) :
    ((n.write (psync fam cfg rms) ops).run h).2 = h ∨
      ∃ l, ((n.write (psync fam cfg rms) ops).run h).2 = turnH fam l h := by
  rw [write_run]; dsimp only; split
  · exact Or.inl rfl
  · exact Or.inr ⟨_, rfl⟩

theorem write_ok (n : Node) (ops : List Op) (h : Held F) (ok : NodeOk n h) :
    NodeOk ((n.write (psync fam cfg rms) ops).run h).1.1 ((n.write (psync fam cfg rms) ops).run h).2 := by
  have e := write_grows fam cfg rms n ops h
  refine ⟨write_sub fam cfg rms n ops h ok.sub, by rw [(write_node fam cfg rms n ops h).2.2]; exact ok.managed,
    ?_, ok.log.ext e⟩
  rcases write_store fam cfg rms n ops h with hs | ⟨l, hs⟩
  · rw [hs]; exact ok.ids
  · rw [hs]; exact turnH_ids fam l h ok.ids

/-- **A write stores every op it is given** (or one under its id was there). -/
theorem write_named (n : Node) (ops : List Op) (h : Held F) : ∀ o ∈ ops,
    Named ((n.write (psync fam cfg rms) ops).run h).2 o.id := by
  intro o ho
  rw [write_run]; dsimp only
  by_cases hn : Named h o.id
  · split
    · exact hn
    · exact hn.ext (turnH_ext fam _ h)
  · have hab : ∀ (l : List Op) (acc : List Op), o ∈ l → ∃ o' ∈ l.foldl (absentStep h.db) acc, o'.id = o.id := by
      intro l
      induction l with
      | nil => intro acc h; cases h
      | cons a t ih =>
        intro acc hm
        have keep : ∀ (l : List Op) acc, (∃ o' ∈ acc, o'.id = o.id) → ∃ o' ∈ l.foldl (absentStep h.db) acc, o'.id = o.id := by
          intro l
          induction l with
          | nil => intro acc h; exact h
          | cons b t ih2 =>
            intro acc ⟨o', ho', e⟩
            apply ih2
            unfold absentStep
            split
            · exact ⟨o', List.mem_cons_of_mem _ ho', e⟩
            · exact ⟨o', ho', e⟩
        rw [List.foldl_cons]
        rcases List.mem_cons.1 hm with rfl | hm
        · apply keep
          unfold absentStep
          split
          · exact ⟨o, List.mem_cons_self .., rfl⟩
          · rename_i hc
            simp only [Bool.and_eq_true, Bool.not_eq_true', not_and] at hc
            by_cases ha : (acc.any fun x => x.id == o.id) = true
            · obtain ⟨o', ho', e⟩ := List.any_eq_true.1 ha
              exact ⟨o', ho', by simpa using e⟩
            · exfalso
              have := hc (by simpa using ha)
              apply hn
              unfold Named
              cases e : h.db.ops o.id with
              | none => rw [e] at this; simp at this
              | some _ => rfl
        · exact ih _ hm
    obtain ⟨o', ho', e⟩ := hab ops [] ho
    split
    · rename_i he; rw [List.isEmpty_iff] at he; rw [he] at ho'; cases ho'
    · rw [← e]
      show ((turnH fam _ h).db.ops o'.id).isSome = true
      simp only [turnH, drainS_ops]
      exact foldl_ingest_named _ _ o' (List.mem_reverse.2 ho')


/-- The connections a node holds, by session. -/
def cids (n : Node) : List Id := n.conns.map (·.1)

theorem conn_iff (n : Node) (cid : Id) : (∃ c, n.conn? cid = some c) ↔ cid ∈ cids n := by
  unfold Node.conn? cids
  constructor
  · rintro ⟨c, hc⟩
    cases e : n.conns.find? (fun p => Decidable.decide (p.1 = cid)) with
    | none => rw [e] at hc; cases hc
    | some p =>
      have hm := List.mem_of_find?_eq_some e
      have hp := List.find?_some e
      simp only [decide_eq_true_eq] at hp
      exact List.mem_map.2 ⟨p, hm, hp⟩
  · intro hm
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm
    cases e : n.conns.find? (fun q => Decidable.decide (q.1 = p.1)) with
    | none =>
      have := List.find?_eq_none.1 e p hp
      simp at this
    | some q => exact ⟨q.2, rfl⟩

theorem fanStep_conns (h : Held F) (ids : List Id) : ∀ (l : List (Id × Conn)) acc o st,
    (l.foldl (fanStep fam cfg rms h ids) (acc, o, st)).1 =
      (l.map fun p => (p.1, ((Conn.filed fam cfg (p.2.setRooms (rms h p.1)) ids : HeldM F Step).run h).1.conn)).reverse ++ acc := by
  intro l
  induction l with
  | nil => intro acc o st; rfl
  | cons p t ih =>
    intro acc o st
    rw [List.foldl_cons]
    simp only [fanStep]
    rw [ih]
    simp

/-- What a fanout leaves: the store, the index, the addresses and the
family's sessions, and each connection, after its stream step. -/
theorem fanout_node (n : Node) (ids : List Id) (h : Held F) :
    let r := (n.fanout (psync fam cfg rms) ids).run h
    r.2 = h ∧ r.1.1.ix = n.ix ∧ r.1.1.addrs = n.addrs ∧ r.1.1.managed = n.managed ∧
      r.1.1.conns = n.conns.map fun p =>
        (p.1, ((Conn.filed fam cfg (p.2.setRooms (rms h p.1)) ids : HeldM F Step).run h).1.conn) := by
  rw [fanout_run]
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  show (n.conns.foldl (fanStep fam cfg rms h ids) ([], {}, [])).1.reverse = _
  rw [fanStep_conns]; simp

theorem fanout_ok (n : Node) (ids : List Id) (h : Held F) (ok : NodeOk n h) :
    NodeOk ((n.fanout (psync fam cfg rms) ids).run h).1.1 ((n.fanout (psync fam cfg rms) ids).run h).2 := by
  obtain ⟨e1, e2, -, e4, e5⟩ := fanout_node fam cfg rms n ids h
  rw [e1]
  refine ⟨⟨by rw [e2]; exact ok.sub.1, ?_⟩, by rw [e4]; exact ok.managed, ok.ids, ok.log⟩
  intro p hp
  rw [e5] at hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
  intro x hx
  rw [filed_snaps] at hx
  exact (ok.sub.2 q hq).setRooms _ x hx

theorem fanout_cids (n : Node) (ids : List Id) (h : Held F) :
    cids ((n.fanout (psync fam cfg rms) ids).run h).1.1 = cids n := by
  rw [cids, (fanout_node fam cfg rms n ids h).2.2.2.2]; simp [cids]

theorem store_ok (n : Node) (ops : List Op) (mine : Bool) (h : Held F) (ok : NodeOk n h) :
    NodeOk ((n.store (psync fam cfg rms) ops mine).run h).1.1 ((n.store (psync fam cfg rms) ops mine).run h).2 := by
  rw [store_run]
  have wk := write_ok fam cfg rms n (intake fam mine ops) h ok
  simp only [Node.put, psync_fam]
  by_cases hc : ((n.write (psync fam cfg rms) (intake fam mine ops)).run h).1.2.isEmpty = true
  · simp only [hc, ↓reduceIte]; exact wk
  · simp only [hc, ↓reduceIte, Bool.false_eq_true]; exact fanout_ok fam cfg rms _ _ _ wk

/-- What a store leaves: the addresses and the sessions. -/
theorem store_node (n : Node) (ops : List Op) (mine : Bool) (h : Held F) :
    ((n.store (psync fam cfg rms) ops mine).run h).1.1.addrs = n.addrs ∧
    cids ((n.store (psync fam cfg rms) ops mine).run h).1.1 = cids n := by
  rw [store_run]
  have wn := write_node fam cfg rms n (intake fam mine ops) h
  simp only [Node.put, psync_fam]
  by_cases hc : ((n.write (psync fam cfg rms) (intake fam mine ops)).run h).1.2.isEmpty = true
  · simp only [hc, ↓reduceIte]; exact ⟨wn.2.1, by rw [cids, wn.1]; rfl⟩
  · simp only [hc, ↓reduceIte, Bool.false_eq_true]
    refine ⟨by rw [(fanout_node fam cfg rms _ _ _).2.2.1]; exact wn.2.1, ?_⟩
    rw [fanout_cids]; rw [cids, wn.1]; rfl

theorem store_grows' (n : Node) (ops : List Op) (mine : Bool) (h : Held F) :
    Ext h ((n.store (psync fam cfg rms) ops mine).run h).2 := store_grows fam cfg rms n ops mine h

theorem setConn_cids (n : Node) (cid : Id) (c : Conn) : cids (setConn n cid c) = cids n := by
  unfold setConn cids; simp only [List.map_map]
  congr 1; funext p; simp only [Function.comp_apply]; split <;> simp_all

theorem apply_ok (n : Node) (cid : Id) (s : Step) (now : Nat) (h : Held F) (ok : NodeOk n h)
    (hs : SnapsIn s.conn h) :
    NodeOk ((n.apply (psync fam cfg rms) cid s now).run h).1.1 ((n.apply (psync fam cfg rms) cid s now).run h).2 := by
  cases hd : s.drop
  · rw [apply_run fam cfg rms n cid s now h hd]
    apply store_ok
    refine ⟨⟨ok.sub.1, ?_⟩, ok.managed, ok.ids, ok.log⟩
    intro p hp
    simp only [setConn, List.mem_map] at hp
    obtain ⟨q, hq, e⟩ := hp
    split at e
    · rw [← e]; exact hs
    · rw [← e]; exact ok.sub.2 q hq
  · simp only [Node.apply, hd, ite_true, HeldM.run_pure]
    refine ⟨⟨ok.sub.1, fun p hp => ok.sub.2 p ?_⟩, ?_, ok.ids, ok.log⟩
    · simp only [Node.drop, Node.close] at hp; exact (List.mem_filter.1 hp).1
    · simp [Node.drop, Node.close, ok.managed]

end

/-! ## What a connection does with each message -/

@[simp] theorem ofOp_rbsr (c : Id) (k : Nat) (cs : List Claim) : Msg.ofOp (Msg.rbsr c k cs).op = some (.rbsr c k cs) := by
  simp [Msg.ofOp, Msg.op, Codec.decode_encode]

@[simp] theorem ofOp_want (l : List Id) : Msg.ofOp (Msg.want l).op = some (.want l) := by
  simp [Msg.ofOp, Msg.op, kRbsr, kHave, kWant]

theorem ofOp_data {o : Op} (h : isWire o.kind = false) : Msg.ofOp o = none := by
  simp [isWire, Bool.or_eq_false_iff] at h
  simp [Msg.ofOp, h.1.1, h.1.2, h.2]

theorem has_of_mem {l : List Id} {x : Id} (h : x ∈ l) : has l x = true := (Engine.has_iff l x).2 h

theorem pieceIds_cover (k : Nat) (hk : 0 < k) : ∀ (fuel : Nat) (l : List Id), l.length ≤ fuel →
    ∀ x ∈ l, ∃ p ∈ pieceIds k fuel l, x ∈ p ∧ p.length ≤ k := by
  intro fuel
  induction fuel with
  | zero => intro l hl x hx; cases l with
    | nil => cases hx
    | cons _ _ => simp at hl
  | succ f ih =>
    intro l hl x hx
    cases l with
    | nil => cases hx
    | cons a t =>
      simp only [pieceIds]
      by_cases ht : x ∈ (a :: t).take k
      · exact ⟨_, List.mem_cons_self .., ht, by simp [Nat.min_le_left]⟩
      · have hd : x ∈ (a :: t).drop k := by
          have := List.take_append_drop k (a :: t)
          rw [← this] at hx
          rcases List.mem_append.1 hx with h | h
          · exact absurd h ht
          · exact h
        obtain ⟨p, hp, hxp, hl'⟩ := ih _ (by simp at hl ⊢; omega) x hd
        exact ⟨p, List.mem_cons_of_mem _ hp, hxp, hl'⟩

/-- An id among a message's ids is in one of its chunks, of at most
`maxIds` ids. -/
theorem chunks_cover (cfg : Config) (ids : List Id) (mk : List Id → Msg) (hmax : 0 < cfg.maxIds) {x : Id}
    (hx : x ∈ ids) : ∃ l, x ∈ l ∧ l.length ≤ cfg.maxIds ∧ (mk l).op ∈ chunks cfg ids mk := by
  obtain ⟨p, hp, hxp, hl⟩ := pieceIds_cover cfg.maxIds hmax ids.length ids (Nat.le_refl _) x hx
  exact ⟨p, hxp, hl, List.mem_map.2 ⟨p, hp, rfl⟩⟩

/-- The snapshot round k of room r is answered from. -/
def snapOf (ix : Index) (c : Conn) (r : Id) (k : Nat) : List Item :=
  match c.snaps.find? fun p => Decidable.decide (p.1 = (r, k)) with
  | some (_, s) => s
  | none => ix.items r

theorem snapOf_named (ix : Index) (c : Conn) (r : Id) (k : Nat) (h : Held F) (hi : IxIn ix h) (hc : SnapsIn c h) :
    ∀ it ∈ snapOf ix c r k, Named h it.2 := by
  intro it hit
  unfold snapOf at hit
  split at hit
  · rename_i q s e
    exact hc _ (List.mem_of_find?_eq_some e) it hit
  · exact hi r it hit

/-- **A claim of ids is answered with a want for each id the snapshot
lacks.** -/
theorem onRbsr_wants (cfg : Config) (ix : Index) (c : Conn) (r : Id) (k : Nat) (rg : Range) (L : List Id)
    (now : Nat) (x : Id) (hr : r ∈ c.rooms) (hx : x ∈ L) (hmax : 0 < cfg.maxIds)
    (hs : ∀ it ∈ snapOf ix c r k, it.2 ≠ x) :
    ∃ W, x ∈ W ∧ W.length ≤ cfg.maxIds ∧ (Msg.want W).op ∈ (c.onRbsr cfg ix r k [.ids rg L] now).send := by
  have hw : x ∈ L.filter fun i => !named Prod.snd (within Prod.fst rg (snapOf ix c r k)) i := by
    refine List.mem_filter.2 ⟨hx, ?_⟩
    rw [Bool.not_eq_true']
    apply named_false.2
    intro a ha e
    exact hs a (mem_within.1 ha).1 e
  obtain ⟨W, hxW, hl, hm⟩ := chunks_cover cfg _ Msg.want hmax hw
  refine ⟨W, hxW, hl, ?_⟩
  unfold Conn.onRbsr
  simp only [has_of_mem hr, Bool.not_true, Bool.false_eq_true, ite_false, List.isEmpty_cons]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, answer, List.filterMap_cons,
    List.filterMap_nil]
  apply List.mem_cons_of_mem
  apply List.mem_append_right
  exact hm

theorem conn_mem {n : Node} {cid : Id} {c : Conn} (h : n.conn? cid = some c) : (cid, c) ∈ n.conns := by
  unfold Node.conn? at h
  cases e : n.conns.find? (fun p => Decidable.decide (p.1 = cid)) with
  | none => rw [e] at h; cases h
  | some p =>
    rw [e] at h
    have hp := List.find?_some e
    simp only [decide_eq_true_eq] at hp
    simp only [Option.map_some, Option.some.injEq] at h
    have : p = (cid, c) := Prod.ext hp h
    rw [← this]; exact List.mem_of_find?_eq_some e

theorem start_drop (cfg : Config) (ix : Index) (c : Conn) (now : Nat) : (c.start cfg ix now).drop = false := by
  unfold Conn.start; split <;> rfl

theorem onRbsr_drop (cfg : Config) (ix : Index) (c : Conn) (r : Id) (k : Nat) (cs : List Claim) (now : Nat) :
    (c.onRbsr cfg ix r k cs now).drop = false := by
  unfold Conn.onRbsr; split
  · rfl
  · dsimp only; split <;> rfl

section
variable (fam : Family F) (cfg : Config) (rms : Held F → Id → List Id)

/-- **A connection never drops on what it receives**: only its clock does. -/
theorem recv_drop (ix : Index) (c : Conn) (b : ByteArray) (now : Nat) (h : Held F) :
    ((Conn.recv fam cfg ix c b now : HeldM F Step).run h).1.drop = false := by
  unfold Conn.recv
  cases Op.decode b with
  | none => rfl
  | some o =>
    dsimp only
    cases Msg.ofOp o with
    | none => dsimp only; split <;> rfl
    | some m =>
      cases m with
      | hello f => show (Conn.finish _).drop = false; rw [Conn.finish_drop]; split
                   · exact start_drop cfg ix _ now
                   · rfl
      | rbsr r k cs => show (Conn.finish _).drop = false; rw [Conn.finish_drop]; exact onRbsr_drop cfg ix _ r k cs now
      | hold ids => simp only [HeldM.run_bind, HeldM.run_pure, Conn.finish_drop, Conn.onHold]
      | want ids =>
        simp only [HeldM.run_bind, HeldM.run_pure, Conn.finish_drop, Conn.onWant]
        split
        · rfl
        · simp only [HeldM.run_bind, HeldM.run_pure]

end

section
variable (fam : Family F) (cfg : Config) (rms : Held F → Id → List Id)

theorem recv_rbsr (ix : Index) (c : Conn) (r : Id) (k : Nat) (cs : List Claim) (now : Nat) (h : Held F) :
    ((Conn.recv fam cfg ix c (Msg.rbsr r k cs).op.bytes now : HeldM F Step).run h).1 =
      Conn.finish (({ c with heard := now } : Conn).onRbsr cfg ix r k cs now) := by
  simp [Conn.recv, Op.decode_bytes]

theorem recv_want (ix : Index) (c : Conn) (W : List Id) (now : Nat) (h : Held F) :
    ((Conn.recv fam cfg ix c (Msg.want W).op.bytes now : HeldM F Step).run h).1 =
      Conn.finish (((({ c with heard := now } : Conn).onWant fam cfg W : HeldM F Step).run h).1) := by
  simp [Conn.recv, Op.decode_bytes]

/-- A data op of the connection's rooms is taken. -/
theorem recv_data (ix : Index) (c : Conn) (o : Op) (now : Nat) (h : Held F) (hw : isWire o.kind = false)
    (hsh : c.shows fam o = true) :
    ((Conn.recv fam cfg ix c o.bytes now : HeldM F Step).run h).1 =
      Conn.finish (Step.mk { c with heard := now, asked := c.asked.erase o.id, known := c.known.insert o.id }
        [] [o] [] false) := by
  have hsh' : Conn.shows fam { c with heard := now } o = true := hsh
  simp [Conn.recv, Op.decode_bytes, ofOp_data hw, hw, hsh']

/-- **A want for a stored op the peer may see sends it.** -/
theorem onWant_sends (c : Conn) (W : List Id) (h : Held F) (x : Id) (o : Op) (r : Id) (hW : W.length ≤ cfg.maxIds)
    (hx : x ∈ W) (ho : h.db.ops x = some o) (hor : fam.room o = some r) (hr : r ∈ c.rooms) :
    o ∈ ((c.onWant fam cfg W : HeldM F Step).run h).1.send := by
  unfold Conn.onWant
  have hc : ¬ W.length > cfg.maxIds := by omega
  simp only [hc, ↓reduceIte]
  simp only [HeldM.run_bind, filterMapM_getOp, HeldM.run_pure]
  apply List.mem_append_left
  refine List.mem_filter.2 ⟨List.mem_filterMap.2 ⟨x, hx, ho⟩, ?_⟩
  simp [Conn.shows, hor, has_of_mem hr]

/-- **H1, one payload: a claim of ids is answered with a want for x**,
an id it lists that the store lacks. -/
theorem claim_step (cid : Id) (now : Nat) (st : (Node × Acts) × Held F) (ok : NodeOk st.1.1 st.2) (c : Conn)
    (hc : st.1.1.conn? cid = some c) (r : Id) (kr : Nat) (rg : Range) (L : List Id) (x : Id)
    (hr : r ∈ rms st.2 cid) (hx : x ∈ L) (hmax : 0 < cfg.maxIds) (hn : ¬ Named st.2 x) :
    ∃ W, x ∈ W ∧ W.length ≤ cfg.maxIds ∧
      (Route.conn cid, (Msg.want W).op.bytes) ∈ (frameStep fam cfg rms cid now st (Msg.rbsr r kr [.ids rg L]).op.bytes).1.2.send := by
  have hsc : SnapsIn ({ c.setRooms (rms st.2 cid) with heard := now } : Conn) st.2 :=
    (ok.sub.2 _ (conn_mem hc)).setRooms _
  obtain ⟨W, hxW, hl, hm⟩ := onRbsr_wants cfg st.1.1.ix ({ c.setRooms (rms st.2 cid) with heard := now } : Conn)
    r kr rg L now x hr hx hmax (fun it hit e => hn (e ▸ snapOf_named _ _ _ _ st.2 ok.sub.1 hsc it hit))
  refine ⟨W, hxW, hl, ?_⟩
  unfold frameStep
  rw [hc]; dsimp only
  have hd := recv_drop fam cfg st.1.1.ix (c.setRooms (rms st.2 cid)) (Msg.rbsr r kr [.ids rg L]).op.bytes now st.2
  rw [apply_run fam cfg rms _ _ _ _ _ hd, recv_rbsr]
  apply List.mem_append_right
  apply List.mem_append_left
  exact List.mem_map.2 ⟨_, hm, rfl⟩

/-- **H2, one payload: a want for x, which the store holds in a room the
session shows, sends x.** -/
theorem want_step (cid : Id) (now : Nat) (st : (Node × Acts) × Held F) (c : Conn)
    (hc : st.1.1.conn? cid = some c) (r : Id) (W : List Id) (x : Id) (o : Op)
    (hr : r ∈ rms st.2 cid) (hW : W.length ≤ cfg.maxIds) (hx : x ∈ W) (ho : st.2.db.ops x = some o)
    (hor : fam.room o = some r) :
    (Route.conn cid, o.bytes) ∈ (frameStep fam cfg rms cid now st (Msg.want W).op.bytes).1.2.send := by
  unfold frameStep
  rw [hc]; dsimp only
  have hd := recv_drop fam cfg st.1.1.ix (c.setRooms (rms st.2 cid)) (Msg.want W).op.bytes now st.2
  rw [apply_run fam cfg rms _ _ _ _ _ hd, recv_want]
  apply List.mem_append_right
  apply List.mem_append_left
  exact List.mem_map.2 ⟨o, onWant_sends fam cfg _ W st.2 x o r hW hx ho hor hr, rfl⟩

/-- Storing a shared op stores it (or one under its id was there). -/
theorem store_named (n : Node) (o : Op) (h : Held F) (hsh : fam.shared o = true) :
    Named ((n.store (psync fam cfg rms) [o] false).run h).2 o.id := by
  rw [store_run]
  have hi : intake fam false [o] = [o] := by simp [intake, hsh]
  simp only [Node.put, psync_fam, hi]
  have hn := write_named fam cfg rms n [o] h o (List.mem_singleton_self o)
  by_cases he : ((n.write (psync fam cfg rms) [o]).run h).1.2.isEmpty = true
  · simp only [he, ↓reduceIte]; exact hn
  · simp only [he, ↓reduceIte, Bool.false_eq_true]
    rw [(fanout_node fam cfg rms _ _ _).1]; exact hn

variable (hw : WalkLaws (F := F) fam cfg)
include hw

/-- **One payload keeps the node invariant**, grows the store, keeps the
sessions and addresses, and only adds to what is sent. -/
theorem frameStep_ok (cid : Id) (now : Nat) (st : (Node × Acts) × Held F) (b : ByteArray)
    (ok : NodeOk st.1.1 st.2) :
    NodeOk (frameStep fam cfg rms cid now st b).1.1 (frameStep fam cfg rms cid now st b).2 ∧
    Ext st.2 (frameStep fam cfg rms cid now st b).2 ∧
    cids (frameStep fam cfg rms cid now st b).1.1 = cids st.1.1 ∧
    (frameStep fam cfg rms cid now st b).1.1.addrs = st.1.1.addrs ∧
    ∀ y ∈ st.1.2.send, y ∈ (frameStep fam cfg rms cid now st b).1.2.send := by
  unfold frameStep
  cases hc : st.1.1.conn? cid with
  | none => exact ⟨ok, Ext.refl _, rfl, rfl, fun y hy => hy⟩
  | some c =>
    dsimp only
    have hsn := recv_snaps fam cfg hw st.1.1.ix (c.setRooms (rms st.2 cid)) b now st.2 ok.sub.1
      ((ok.sub.2 _ (conn_mem hc)).setRooms _)
    have hd := recv_drop fam cfg st.1.1.ix (c.setRooms (rms st.2 cid)) b now st.2
    refine ⟨apply_ok fam cfg rms _ _ _ _ _ ok hsn, apply_grows fam cfg rms _ _ _ _ _, ?_, ?_, ?_⟩
    · rw [apply_run fam cfg rms _ _ _ _ _ hd]
      rw [(store_node fam cfg rms _ _ _ _).2, setConn_cids]
    · rw [apply_run fam cfg rms _ _ _ _ _ hd]
      rw [(store_node fam cfg rms _ _ _ _).1]; rfl
    · intro y hy; exact List.mem_append_left _ hy

/-- Through a frame's payloads: the invariant, growth, the sessions, the
addresses, and what is sent only grows. -/
theorem frame_fold (cid : Id) (now : Nat) : ∀ (l : List ByteArray) (st : (Node × Acts) × Held F),
    NodeOk st.1.1 st.2 →
    NodeOk (l.foldl (frameStep fam cfg rms cid now) st).1.1 (l.foldl (frameStep fam cfg rms cid now) st).2 ∧
    Ext st.2 (l.foldl (frameStep fam cfg rms cid now) st).2 ∧
    cids (l.foldl (frameStep fam cfg rms cid now) st).1.1 = cids st.1.1 ∧
    (l.foldl (frameStep fam cfg rms cid now) st).1.1.addrs = st.1.1.addrs ∧
    ∀ y ∈ st.1.2.send, y ∈ (l.foldl (frameStep fam cfg rms cid now) st).1.2.send := by
  intro l
  induction l with
  | nil => intro st ok; exact ⟨ok, Ext.refl _, rfl, rfl, fun y hy => hy⟩
  | cons b t ih =>
    intro st ok
    obtain ⟨ok1, e1, c1, a1, s1⟩ := frameStep_ok fam cfg rms hw cid now st b ok
    obtain ⟨ok2, e2, c2, a2, s2⟩ := ih _ ok1
    exact ⟨ok2, e1.trans e2, c2.trans c1, a2.trans a1, fun y hy => s2 y (s1 y hy)⟩

omit hw in
/-- **H3, one payload: a data op of a room the session shows is stored.** -/
theorem op_step (cid : Id) (now : Nat) (st : (Node × Acts) × Held F) (c : Conn)
    (hc : st.1.1.conn? cid = some c) (r : Id) (o : Op) (hr : r ∈ rms st.2 cid)
    (hwire : isWire o.kind = false) (hor : fam.room o = some r) :
    Named (frameStep fam cfg rms cid now st o.bytes).2 o.id := by
  unfold frameStep
  rw [hc]; dsimp only
  have hd := recv_drop fam cfg st.1.1.ix (c.setRooms (rms st.2 cid)) o.bytes now st.2
  rw [apply_run fam cfg rms _ _ _ _ _ hd, recv_data fam cfg _ _ o now st.2 hwire
    (by simp [Conn.shows, Conn.setRooms, hor, has_of_mem hr])]
  exact store_named fam cfg rms _ o st.2 (by simp [Family.shared, hor])


end

/-! ## Hops, at a node: a whole frame -/

section
variable (fam : Family F) (cfg : Config) (rms : Held F → Id → List Id)


theorem setAddr_addr (n : Node) (cid : Id) (a : ByteArray) : (n.setAddr cid a).addr? cid = some a := by
  simp [Node.setAddr, Node.addr?]

theorem setAddr_ok (n : Node) (cid : Id) (a : ByteArray) (h : Held F) (ok : NodeOk n h) : NodeOk (n.setAddr cid a) h :=
  ⟨ok.sub, ok.managed, ok.ids, ok.log⟩

/-- A frame's payloads up to and after one of them. -/
theorem fold_at {α β : Type} (f : α → β → α) (l : List β) (b : β) (hb : b ∈ l) (st : α) :
    ∃ pre post : List β, l.foldl f st = post.foldl f (f (pre.foldl f st) b) := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hb
  exact ⟨pre, post, by simp [List.foldl_append]⟩

/-- The end of a session's frame: what it sent on the session goes out
to the frame's sender, and the store is as the payloads left it. -/
theorem frame_end (cid : Id) (now : Nat) (st : (Node × Acts) × Held F) (ok : NodeOk st.1.1 st.2) (a p : ByteArray)
    (ha : st.1.1.addr? cid = some a) (hp : (Route.conn cid, p) ∈ st.1.2.send) :
    ∃ g, p ∈ g ∧ (a, plainFrame cid g) ∈ ((st.1.1.finish (psync fam cfg rms) st.1.2 now).run st.2).1.2.send := by
  rw [finish_run fam cfg rms _ _ _ _ ok.managed]
  exact seal_mem fam cfg rms _ _ _ cid p a hp ha

theorem frame_end_store (now : Nat) (st : (Node × Acts) × Held F) (ok : NodeOk st.1.1 st.2) :
    ((st.1.1.finish (psync fam cfg rms) st.1.2 now).run st.2).2 = st.2 := by
  rw [finish_run fam cfg rms _ _ _ _ ok.managed]

end

section
variable (fam : Family F) (cfg : Config) (rms : Held F → Id → List Id) (hw : WalkLaws (F := F) fam cfg)
include hw

/-- **H1: a claim of ids, delivered, is answered with a want** for each
id it lists that the node lacks, in a frame back to the claim's sender;
or the node holds it by the frame's end. -/
theorem claim_wants (n : Node) (h : Held F) (ok : NodeOk n h) (a bytes : ByteArray) (now : Nat) (cid : Id)
    (inner : List ByteArray) (hp : plainPeek bytes = some (cid, inner)) (c : Conn) (hc : n.conn? cid = some c)
    (r : Id) (hr : ∀ h', r ∈ rms h' cid) (kr : Nat) (rg : Range) (L : List Id) (x : Id)
    (hb : (Msg.rbsr r kr [.ids rg L]).op.bytes ∈ inner) (hx : x ∈ L) (hmax : 0 < cfg.maxIds) :
    Named ((n.onFrame (psync fam cfg rms) a bytes now).run h).2 x ∨
      ∃ W g, x ∈ W ∧ W.length ≤ cfg.maxIds ∧ (Msg.want W).op.bytes ∈ g ∧
        (a, plainFrame cid g) ∈ ((n.onFrame (psync fam cfg rms) a bytes now).run h).1.2.send := by
  obtain ⟨h0, bundle, hb', hi⟩ := plainFrame_of_peek hp
  rw [onFrame_sealed fam cfg rms hw n a bytes now h cid bundle inner c h0 hb' hi hc]
  have ok0 := setAddr_ok n cid a h ok
  obtain ⟨pre, post, e⟩ := fold_at (frameStep fam cfg rms cid now) inner _ hb ((n.setAddr cid a, {}), h)
  rw [e]
  obtain ⟨ok1, e1, c1, a1, -⟩ := frame_fold fam cfg rms hw cid now pre ((n.setAddr cid a, {}), h) ok0
  generalize pre.foldl (frameStep fam cfg rms cid now) ((n.setAddr cid a, {}), h) = st1 at ok1 e1 c1 a1
  obtain ⟨c1', hc1⟩ := (conn_iff _ _).2 (by rw [c1]; exact (conn_iff _ _).1 ⟨c, hc⟩)
  obtain ⟨ok2, e2, -, a2, s2⟩ := frameStep_ok fam cfg rms hw cid now st1 (Msg.rbsr r kr [.ids rg L]).op.bytes ok1
  obtain ⟨ok3, e3, -, a3, s3⟩ := frame_fold fam cfg rms hw cid now post _ ok2
  by_cases hn : Named st1.2 x
  · left
    rw [frame_end_store fam cfg rms now _ ok3]
    exact (hn.ext e2).ext e3
  · right
    obtain ⟨W, hxW, hl, hm⟩ := claim_step fam cfg rms cid now st1 ok1 c1' hc1 r kr rg L x (hr _) hx hmax hn
    have ha : (post.foldl (frameStep fam cfg rms cid now) (frameStep fam cfg rms cid now st1
        (Msg.rbsr r kr [.ids rg L]).op.bytes)).1.1.addr? cid = some a := by
      unfold Node.addr?; rw [a3, a2, a1]; exact setAddr_addr n cid a
    obtain ⟨g, hg, hf⟩ := frame_end fam cfg rms cid now _ ok3 a _ ha (s3 _ hm)
    exact ⟨W, g, hxW, hl, hg, hf⟩

/-- **H2: a want, delivered, for an op the node holds in a room the
session shows, is answered with the op**, in a frame back to the
want's sender. -/
theorem want_sends (n : Node) (h : Held F) (ok : NodeOk n h) (a bytes : ByteArray) (now : Nat) (cid : Id)
    (inner : List ByteArray) (hp : plainPeek bytes = some (cid, inner)) (c : Conn) (hc : n.conn? cid = some c)
    (r : Id) (hr : ∀ h', r ∈ rms h' cid) (W : List Id) (x : Id) (o : Op)
    (hb : (Msg.want W).op.bytes ∈ inner) (hW : W.length ≤ cfg.maxIds) (hx : x ∈ W) (ho : h.db.ops x = some o)
    (hor : fam.room o = some r) :
    ∃ g, o.bytes ∈ g ∧ (a, plainFrame cid g) ∈ ((n.onFrame (psync fam cfg rms) a bytes now).run h).1.2.send := by
  obtain ⟨h0, bundle, hb', hi⟩ := plainFrame_of_peek hp
  rw [onFrame_sealed fam cfg rms hw n a bytes now h cid bundle inner c h0 hb' hi hc]
  have ok0 := setAddr_ok n cid a h ok
  obtain ⟨pre, post, e⟩ := fold_at (frameStep fam cfg rms cid now) inner _ hb ((n.setAddr cid a, {}), h)
  rw [e]
  obtain ⟨ok1, e1, c1, a1, -⟩ := frame_fold fam cfg rms hw cid now pre ((n.setAddr cid a, {}), h) ok0
  generalize pre.foldl (frameStep fam cfg rms cid now) ((n.setAddr cid a, {}), h) = st1 at ok1 e1 c1 a1
  obtain ⟨c1', hc1⟩ := (conn_iff _ _).2 (by rw [c1]; exact (conn_iff _ _).1 ⟨c, hc⟩)
  obtain ⟨ok2, -, -, a2, -⟩ := frameStep_ok fam cfg rms hw cid now st1 (Msg.want W).op.bytes ok1
  obtain ⟨ok3, -, -, a3, s3⟩ := frame_fold fam cfg rms hw cid now post _ ok2
  have hm := want_step fam cfg rms cid now st1 c1' hc1 r W x o (hr _) hW hx (e1.1 x o ho) hor
  have ha : (post.foldl (frameStep fam cfg rms cid now) (frameStep fam cfg rms cid now st1
      (Msg.want W).op.bytes)).1.1.addr? cid = some a := by
    unfold Node.addr?; rw [a3, a2, a1]; exact setAddr_addr n cid a
  exact frame_end fam cfg rms cid now _ ok3 a _ ha (s3 _ hm)

/-- **H3: an op, delivered in a frame, of a room the session shows, is
stored.** -/
theorem op_taken (n : Node) (h : Held F) (ok : NodeOk n h) (a bytes : ByteArray) (now : Nat) (cid : Id)
    (inner : List ByteArray) (hp : plainPeek bytes = some (cid, inner)) (c : Conn) (hc : n.conn? cid = some c)
    (r : Id) (hr : ∀ h', r ∈ rms h' cid) (o : Op) (hb : o.bytes ∈ inner) (hwire : isWire o.kind = false)
    (hor : fam.room o = some r) :
    Named ((n.onFrame (psync fam cfg rms) a bytes now).run h).2 o.id := by
  obtain ⟨h0, bundle, hb', hi⟩ := plainFrame_of_peek hp
  rw [onFrame_sealed fam cfg rms hw n a bytes now h cid bundle inner c h0 hb' hi hc]
  have ok0 := setAddr_ok n cid a h ok
  obtain ⟨pre, post, e⟩ := fold_at (frameStep fam cfg rms cid now) inner _ hb ((n.setAddr cid a, {}), h)
  rw [e]
  obtain ⟨ok1, -, c1, -, -⟩ := frame_fold fam cfg rms hw cid now pre ((n.setAddr cid a, {}), h) ok0
  generalize pre.foldl (frameStep fam cfg rms cid now) ((n.setAddr cid a, {}), h) = st1 at ok1 c1
  obtain ⟨c1', hc1⟩ := (conn_iff _ _).2 (by rw [c1]; exact (conn_iff _ _).1 ⟨c, hc⟩)
  obtain ⟨ok2, -, -, -, -⟩ := frameStep_ok fam cfg rms hw cid now st1 o.bytes ok1
  obtain ⟨ok3, e3, -, -, -⟩ := frame_fold fam cfg rms hw cid now post _ ok2
  rw [frame_end_store fam cfg rms now _ ok3]
  exact (op_step fam cfg rms cid now st1 c1' hc1 r o (hr _) hwire hor).ext e3

end

/-! ## Every entry point keeps the node invariant, in every reachable world -/

@[simp] theorem readH_run {α} (f : Held F → α) (h : Held F) : (readH f).run h = (f h, h) := rfl

section
variable (fam : Family F) (cfg : Config) (rms : Held F → Id → List Id)

/-- One connection's turn of the clock. -/
def tickStep (now : Nat) (st : (Node × Acts) × Held F) (p : Id × Conn) : (Node × Acts) × Held F :=
  match st.1.1.conn? p.1 with
  | some c =>
    let s := ((Conn.tick fam cfg st.1.1.ix (c.setRooms (rms st.2 p.1)) now : HeldM F Step).run st.2).1
    let r := (st.1.1.apply (psync fam cfg rms) p.1 s now).run st.2
    ((r.1.1, st.1.2 ++ r.1.2), r.2)
  | none => st

theorem finish_ok (n : Node) (out : Acts) (now : Nat) (h : Held F) (ok : NodeOk n h) :
    NodeOk ((n.finish (psync fam cfg rms) out now).run h).1.1 ((n.finish (psync fam cfg rms) out now).run h).2 := by
  rw [finish_run fam cfg rms _ _ _ _ ok.managed]
  exact ⟨ok.sub, ok.managed, ok.ids, ok.log⟩

theorem onWrite_ok (n : Node) (ops : List Op) (now : Nat) (h : Held F) (ok : NodeOk n h) :
    NodeOk ((n.onWrite (psync fam cfg rms) ops now).run h).1.1 ((n.onWrite (psync fam cfg rms) ops now).run h).2 := by
  unfold Node.onWrite
  simp only [HeldM.run_bind]
  exact finish_ok fam cfg rms _ _ _ _ (store_ok fam cfg rms n ops true h ok)

theorem connect_ok (n : Node) (cid : Id) (a : ByteArray) (d : Bool) (now : Nat) (h : Held F) (ok : NodeOk n h) :
    NodeOk ((n.connect (psync fam cfg rms) cid a d now).run h).1.1 ((n.connect (psync fam cfg rms) cid a d now).run h).2 := by
  unfold Node.connect Node.open
  simp only [HeldM.run_bind, psync_rooms, readH_run, HeldM.run_pure]
  apply finish_ok
  refine ⟨⟨ok.sub.1, ?_⟩, ?_, ok.ids, ok.log⟩
  · intro p hp
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · intro e he; cases he
    · simp only [Node.setAddr, Node.close] at hp
      exact ok.sub.2 p (List.mem_filter.1 hp).1
  · simp [Node.setAddr, Node.close, ok.managed]

variable (hw : WalkLaws (F := F) fam cfg)
include hw

theorem onTick_run (n : Node) (now : Nat) (h : Held F) :
    (n.onTick (psync fam cfg rms) now).run h =
      ((n.conns.foldl (tickStep fam cfg rms now) ((n, {}), h)).1.1.finish (psync fam cfg rms)
        (n.conns.foldl (tickStep fam cfg rms now) ((n, {}), h)).1.2 now).run
        (n.conns.foldl (tickStep fam cfg rms now) ((n, {}), h)).2 := by
  unfold Node.onTick
  simp only [psync_dial, HeldM.pure_bind, HeldM.run_bind, store_nil]
  rw [forIn_fold _ _ (fun b st h => by obtain ⟨cid, _⟩ := b; dsimp only; split <;> rfl)]
  rw [foldl_ext _ (tickStep fam cfg rms now) (fun p b => ?_)]
  obtain ⟨cid, c0⟩ := b
  unfold tickStep
  dsimp only
  cases hcp : p.1.1.conn? cid with
  | none => rfl
  | some c' =>
    simp only [HeldM.run_bind, refresh_run, psync_fam, psync_cfg]
    rw [Keeps.run_eq (tick_keeps fam cfg hw _ _ _) _]
    rfl

theorem tickStep_ok (now : Nat) (st : (Node × Acts) × Held F) (p : Id × Conn) (ok : NodeOk st.1.1 st.2) :
    NodeOk (tickStep fam cfg rms now st p).1.1 (tickStep fam cfg rms now st p).2 := by
  unfold tickStep
  cases hc : st.1.1.conn? p.1 with
  | none => exact ok
  | some c =>
    exact apply_ok fam cfg rms _ _ _ _ _ ok (tick_snaps fam cfg hw _ _ _ _ ok.sub.1 ((ok.sub.2 _ (conn_mem hc)).setRooms _))

theorem onTick_ok (n : Node) (now : Nat) (h : Held F) (ok : NodeOk n h) :
    NodeOk ((n.onTick (psync fam cfg rms) now).run h).1.1 ((n.onTick (psync fam cfg rms) now).run h).2 := by
  rw [onTick_run fam cfg rms hw]
  apply finish_ok
  have : ∀ (l : List (Id × Conn)) st, NodeOk st.1.1 st.2 →
      NodeOk (l.foldl (tickStep fam cfg rms now) st).1.1 (l.foldl (tickStep fam cfg rms now) st).2 := by
    intro l
    induction l with
    | nil => intro st h; exact h
    | cons p t ih => intro st h; exact ih _ (tickStep_ok fam cfg rms hw now st p h)
  exact this _ _ ok


theorem onFrame_ok (n : Node) (a b : ByteArray) (now : Nat) (h : Held F) (ok : NodeOk n h) :
    NodeOk ((n.onFrame (psync fam cfg rms) a b now).run h).1.1 ((n.onFrame (psync fam cfg rms) a b now).run h).2 := by
  cases h0 : b[0]? with
  | none => simp only [Node.onFrame, h0, HeldM.run_pure]; exact ok
  | some t =>
    by_cases t1 : t = 1
    · subst t1
      cases hd : (Codec.decode (b.extract 1 b.size) : Option (Id × ByteArray)) with
      | none => simp only [Node.onFrame, h0, psync_openFrame, HeldM.pure_bind, hd, HeldM.run_pure]; exact ok
      | some q =>
        obtain ⟨cid, bundle⟩ := q
        cases hc : n.conn? cid with
        | none => simp only [Node.onFrame, h0, psync_openFrame, HeldM.pure_bind, hd, hc, HeldM.run_pure]; exact ok
        | some c =>
          cases hi : (Codec.decode bundle : Option (List ByteArray)) with
          | none => simp only [Node.onFrame, h0, psync_openFrame, HeldM.pure_bind, hd, hc, hi, HeldM.run_pure]; exact ok
          | some inner =>
            rw [onFrame_sealed fam cfg rms hw n a b now h cid bundle inner c h0 hd hi hc]
            exact finish_ok fam cfg rms _ _ _ _ (frame_fold fam cfg rms hw cid now inner _ (setAddr_ok n cid a h ok)).1
    · by_cases t0 : t = 0
      · subst t0
        cases hd : Op.decode (b.extract 1 b.size) with
        | none => simp only [Node.onFrame, h0, hd, HeldM.run_pure]; exact ok
        | some o =>
          by_cases he : (intakeConn fam [o]).isEmpty = true
          · simp only [Node.onFrame, h0, hd, psync_fam, he, ↓reduceIte, HeldM.run_pure]; exact ok
          · simp only [Node.onFrame, h0, hd, psync_fam, he, ↓reduceIte, Bool.false_eq_true, HeldM.run_bind,
              psync_recv, HeldM.pure_bind, store_nil]
            exact finish_ok fam cfg rms _ _ _ _ (write_ok fam cfg rms _ _ _ ok)
      · unfold Node.onFrame
        rw [h0]
        split
        · rename_i e; cases e; exact absurd rfl t0
        · rename_i e; cases e; exact absurd rfl t1
        · exact ok

end

/-- A booted node, from a store that files ops under their ids and holds
what it logged, keeps the invariant. -/
theorem boot_ok (fam : Family F) (h : Held F) (hi : IdsOk h) (hl : LogIn h) (floor : Nat) :
    NodeOk (Node.boot fam h.log floor) h := by
  refine ⟨⟨fun r it hit => ?_, fun p hp => by cases hp⟩, rfl, hi, hl⟩
  rcases items_foldl fam h.log {} r it hit with hit | ⟨o, ho, e⟩
  · simp [Index.items] at hit
  · rw [e]; exact hl o ho

theorem enter_ok (Q : Plain F) (w : World (Held F) Q.n) (i : Fin Q.n) (t : Nat) (f : Node → HeldM F (Node × Effects))
    (hf : NodeOk (w.node i) (w.box i) → NodeOk ((f (w.node i)).run (w.box i)).1.1 ((f (w.node i)).run (w.box i)).2)
    (ok : ∀ j, NodeOk (w.node j) (w.box j)) : ∀ j, NodeOk ((w.enter Q.setup i t f).node j) ((w.enter Q.setup i t f).box j) := by
  intro j
  simp only [World.enter, upd]
  by_cases e : j = i
  · subst e; simp only [ite_true]; exact hf (ok j)
  · simp only [e, ite_false]; exact ok j

/-- **Every node of every world the plain world reaches keeps the node
invariant**, against any attacker. -/
theorem reach_ok' (Q : Plain F) (hw : WalkLaws (F := F) Q.fam Q.cfg)
    (adv : World (Held F) Q.setup.n → ByteArray → Prop) (w₀ w : World (Held F) Q.setup.n)
    (h0 : ∀ i, NodeOk (w₀.node i) (w₀.box i)) (hr : Reachable Q.setup adv w₀ w) :
    ∀ i, NodeOk (w.node i) (w.box i) := by
  induction hr with
  | init => exact h0
  | @step w a _ _ ih =>
    cases a with
    | deliver k t =>
      simp only [World.step]
      split
      · exact ih
      · rename_i p _
        split
        · exact ih
        · rename_i j' _
          exact enter_ok Q { w with flight := w.flight.eraseIdx k } j' t
            (fun nd => nd.onFrame (psync Q.fam Q.cfg (Q.rooms j')) p.origin p.bytes t)
            (fun h => onFrame_ok Q.fam Q.cfg (Q.rooms j') hw _ _ _ _ _ h) ih
    | dup k => simp only [World.step]; split <;> exact ih
    | drop k => exact ih
    | tick i t =>
      exact enter_ok Q w i t (fun nd => nd.onTick (psync Q.fam Q.cfg (Q.rooms i)) t)
        (fun h => onTick_ok Q.fam Q.cfg (Q.rooms i) hw _ _ _ h) ih
    | write i ops t =>
      exact enter_ok Q w i t (fun nd => nd.onWrite (psync Q.fam Q.cfg (Q.rooms i)) ops t)
        (fun h => onWrite_ok Q.fam Q.cfg (Q.rooms i) _ _ _ _ h) ih
    | restart i t =>
      intro j
      simp only [World.step, upd]
      by_cases e : j = i
      · subst e; simp only [ite_true]
        exact boot_ok Q.fam _ (ih j).ids (ih j).log _
      · simp only [e, ite_false]; exact ih j
    | connect i j cid d t =>
      exact enter_ok Q w i t (fun nd => nd.connect (psync Q.fam Q.cfg (Q.rooms i)) cid (Q.setup.addr j) d t)
        (fun h => connect_ok Q.fam Q.cfg (Q.rooms i) _ _ _ _ _ _ h) ih
    | inject i o b t =>
      exact enter_ok Q w i t (fun nd => nd.onFrame (psync Q.fam Q.cfg (Q.rooms i)) o b t)
        (fun h => onFrame_ok Q.fam Q.cfg (Q.rooms i) hw _ _ _ _ _ h) ih


theorem reach_ok (Q : Plain F) (hw : WalkLaws (F := F) Q.fam Q.cfg) (adv : World (Held F) Q.n → ByteArray → Prop)
    (w : World (Held F) Q.n) (hr : Q.Reach adv w) : ∀ i, NodeOk (w.node i) (w.box i) :=
  reach_ok' Q hw adv Q.start w (fun _ => boot_ok Q.fam {} (fun x o h => by cases h) (fun o ho => by cases ho) _) hr

end Engine.World
