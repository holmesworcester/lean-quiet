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
  simp only [h0, psync_openFrame, HeldM.pure_bind, hb]
  unfold Node.onSealed
  simp only [hc, hi, HeldM.run_bind]
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

attribute [local instance] byteArray_lawfulBEq

/-- Every op is stored under its own id. -/
def IdsOk (h : Held F) : Prop := ∀ x o, h.db.ops x = some o → o.id = x

/-- Every logged op is stored. -/
def LogIn (h : Held F) : Prop := ∀ o ∈ h.log, Named h o.id

/-! ## The index names exactly the stored ops of each room -/

/-- Room r's index names id x. -/
def Named' (ix : Index) (r x : Id) : Prop := ∃ it ∈ ix.items r, it.2 = x

/-- Every item's key carries its id's number, so equal keys mean equal ids. -/
def IxWf (ix : Index) : Prop := ∀ r it, it ∈ ix.items r → it.1.n = num it.2.data.toList

/-- **The index is the store:** room r's index names exactly the ids of
the stored ops of room r. -/
def IxExact (fam : Family F) (ix : Index) (h : Held F) : Prop :=
  ∀ r x, Named' ix r x ↔ ∃ o, h.db.ops x = some o ∧ fam.room o = some r

theorem id_of_key {a b : Item} (ha : a.1.n = num a.2.data.toList) (hb : b.1.n = num b.2.data.toList)
    (e : b.1 = a.1) : b.2 = a.2 := by
  have : num b.2.data.toList = num a.2.data.toList := by rw [← ha, ← hb, e]
  have h2 := num_inj this
  cases hA : a.2 with | mk da => cases hB : b.2 with | mk db =>
    rw [hA, hB] at h2; simp only at h2
    rw [Array.toList_inj] at h2; rw [h2]

theorem sub_ins (a : Item) : ∀ (l : List Item), ∀ it ∈ l, it ∈ Engine.Sync.ins a l := by
  intro l
  induction l with
  | nil => intro it h; cases h
  | cons b t ih =>
    intro it h
    simp only [Engine.Sync.ins]
    split
    · exact List.mem_cons_of_mem _ h
    · split
      · exact h
      · rcases List.mem_cons.1 h with rfl | h
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (ih it h)

theorem ins_has (a : Item) : ∀ (l : List Item), a ∈ Engine.Sync.ins a l ∨ ∃ b ∈ l, b.1 = a.1 := by
  intro l
  induction l with
  | nil => left; simp [Engine.Sync.ins]
  | cons b t ih =>
    simp only [Engine.Sync.ins]
    split
    · left; exact List.mem_cons_self ..
    · split
      · rename_i e; right; exact ⟨b, List.mem_cons_self .., e.symm⟩
      · rcases ih with h | ⟨b', hb', e⟩
        · left; exact List.mem_cons_of_mem _ h
        · right; exact ⟨b', List.mem_cons_of_mem _ hb', e⟩

theorem named_ins (a : Item) (l : List Item) (hl : ∀ b ∈ l, b.1.n = num b.2.data.toList)
    (ha : a.1.n = num a.2.data.toList) (x : Id) :
    (∃ it ∈ Engine.Sync.ins a l, it.2 = x) ↔ (∃ it ∈ l, it.2 = x) ∨ a.2 = x := by
  constructor
  · rintro ⟨it, hit, e⟩
    rcases mem_ins a l it hit with h | rfl
    · exact Or.inl ⟨it, h, e⟩
    · exact Or.inr e
  · rintro (⟨it, hit, e⟩ | e)
    · exact ⟨it, sub_ins a l it hit, e⟩
    · rcases ins_has a l with h | ⟨b, hb, eb⟩
      · exact ⟨a, h, e⟩
      · exact ⟨b, sub_ins a l b hb, by rw [id_of_key ha (hl b hb) eb, e]⟩

theorem ins_wf (a : Item) (l : List Item) (hl : ∀ b ∈ l, b.1.n = num b.2.data.toList)
    (ha : a.1.n = num a.2.data.toList) : ∀ b ∈ Engine.Sync.ins a l, b.1.n = num b.2.data.toList := by
  intro b hb
  rcases mem_ins a l b hb with h | rfl
  · exact hl b h
  · exact ha

/-- What adding an op does to each room's items. -/
theorem items_add_eq (fam : Family F) (ix : Index) (o : Op) (r : Id) :
    (ix.add fam o).items r =
      if fam.room o = some r then Engine.Sync.ins (keyOf fam o, o.id) (ix.items r) else ix.items r := by
  unfold Index.add
  cases hr : fam.room o with
  | none => simp
  | some c =>
    dsimp only
    rw [items_def, items_def]
    split
    · rw [find_map_fst _ (fun p => by split <;> rfl)]
      by_cases e : c = r
      · subst e
        simp only [↓reduceIte]
        cases hf : ix.rooms.find? fun p => Decidable.decide (p.1 = c) with
        | none =>
          rename_i hany
          exfalso
          obtain ⟨p, hp, hpc⟩ := List.any_eq_true.1 hany
          have := List.find?_eq_none.1 hf p hp
          exact this hpc
        | some p =>
          have hp := List.find?_some hf
          simp only [decide_eq_true_eq] at hp
          simp [hp]
      · have e' : ¬ (some c = some r) := fun h => e (Option.some.inj h)
        simp only [e', ↓reduceIte]
        cases hf : ix.rooms.find? fun p => Decidable.decide (p.1 = r) with
        | none => rfl
        | some p =>
          have hp := List.find?_some hf
          simp only [decide_eq_true_eq] at hp
          have e2 : ¬ r = c := fun h => e h.symm
          simp [hp, e2]
    · rename_i hany
      by_cases e : c = r
      · subst e
        simp only [↓reduceIte, List.find?_cons, decide_true, Option.map_some, Option.getD_some]
        have : ix.rooms.find? (fun p => Decidable.decide (p.1 = c)) = none := by
          apply List.find?_eq_none.2
          intro p hp hpc
          exact hany (List.any_eq_true.2 ⟨p, hp, hpc⟩)
        rw [this]; rfl
      · have e' : ¬ (some c = some r) := fun h => e (Option.some.inj h)
        simp only [e', ↓reduceIte, List.find?_cons]
        simp [e]

theorem add_wf (fam : Family F) (ix : Index) (o : Op) (hw : IxWf ix) : IxWf (ix.add fam o) := by
  intro r it hit
  rw [items_add_eq] at hit
  split at hit
  · exact ins_wf _ _ (hw r) rfl it hit
  · exact hw r it hit

theorem named_add (fam : Family F) (ix : Index) (o : Op) (hw : IxWf ix) (r x : Id) :
    Named' (ix.add fam o) r x ↔ Named' ix r x ∨ (o.id = x ∧ fam.room o = some r) := by
  unfold Named'
  rw [items_add_eq]
  split
  · rename_i hr
    rw [named_ins _ _ (hw r) rfl]
    simp [hr]
  · rename_i hr
    simp [hr]

theorem fold_add (fam : Family F) (r x : Id) : ∀ (l : List Op) (ix : Index), IxWf ix →
    IxWf (l.foldl (Index.add fam) ix) ∧
    (Named' (l.foldl (Index.add fam) ix) r x ↔ Named' ix r x ∨ ∃ o ∈ l, o.id = x ∧ fam.room o = some r) := by
  intro l
  induction l with
  | nil => intro ix hw; exact ⟨hw, by simp⟩
  | cons o t ih =>
    intro ix hw
    obtain ⟨w1, e1⟩ := ih _ (add_wf fam ix o hw)
    refine ⟨w1, ?_⟩
    rw [List.foldl_cons, e1, named_add fam ix o hw]
    constructor
    · rintro ((h | h) | ⟨o', ho', h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨o, List.mem_cons_self .., h⟩
      · exact Or.inr ⟨o', List.mem_cons_of_mem _ ho', h⟩
    · rintro (h | ⟨o', ho', h⟩)
      · exact Or.inl (Or.inl h)
      · rcases List.mem_cons.1 ho' with rfl | ho'
        · exact Or.inl (Or.inr h)
        · exact Or.inr ⟨o', ho', h⟩

/-! ## What a write turn stores -/

/-- An op the turn stored was there, or is one of the turn's. -/
theorem ingest_from (l : List Op) : ∀ (s : DB F) x o', (l.foldl (fun s o => ingestS o s) s).ops x = some o' →
    s.ops x = some o' ∨ (o' ∈ l ∧ o'.id = x) := by
  induction l with
  | nil => intro s x o' h; exact Or.inl h
  | cons o t ih =>
    intro s x o' h
    rcases ih _ x o' h with h | h
    · unfold ingestS at h
      dsimp only at h
      split at h
      · exact Or.inl h
      · simp only [DB.push, DB.putOp] at h
        split at h
        · rename_i e; cases h; exact Or.inr ⟨List.mem_cons_self .., e.symm⟩
        · exact Or.inl h
    · exact Or.inr ⟨List.mem_cons_of_mem _ h.1, h.2⟩

/-- A turn of ops absent from the store, no two with one id, stores each
under its id. -/
theorem ingest_each (l : List Op) : ∀ (s : DB F), (∀ o ∈ l, s.ops o.id = none) →
    l.Pairwise (fun a b => a.id ≠ b.id) → ∀ o ∈ l, (l.foldl (fun s o => ingestS o s) s).ops o.id = some o := by
  induction l with
  | nil => intro s _ _ o h; cases h
  | cons a t ih =>
    intro s ha hp o ho
    have hpt := (List.pairwise_cons.1 hp)
    have hs : (ingestS a s).ops a.id = some a := by
      unfold ingestS; rw [ha a (List.mem_cons_self ..)]; simp [DB.push, DB.putOp]
    have hrest : ∀ o ∈ t, (ingestS a s).ops o.id = none := by
      intro o' ho'
      unfold ingestS; rw [ha a (List.mem_cons_self ..)]
      simp only [DB.push, DB.putOp]
      have : o'.id ≠ a.id := fun e => hpt.1 o' ho' e.symm
      simp [this, ha o' (List.mem_cons_of_mem _ ho')]
    rcases List.mem_cons.1 ho with rfl | ho
    · rw [List.foldl_cons]
      exact (foldl_ingest_ext t _ _ _ hs)
    · exact ih _ hrest hpt.2 o ho

/-- The write's new ops: absent from the store, from the ops given, no two
with one id. -/
theorem absent_props (db : DB F) : ∀ (l acc : List Op),
    (∀ o ∈ acc, db.ops o.id = none) → acc.Pairwise (fun a b => a.id ≠ b.id) →
    (∀ o ∈ l.foldl (absentStep db) acc, db.ops o.id = none ∧ (o ∈ acc ∨ o ∈ l)) ∧
      (l.foldl (absentStep db) acc).Pairwise (fun a b => a.id ≠ b.id) := by
  intro l
  induction l with
  | nil => intro acc ha hp; exact ⟨fun o h => ⟨ha o h, Or.inl h⟩, hp⟩
  | cons o t ih =>
    intro acc ha hp
    rw [List.foldl_cons]
    unfold absentStep
    split
    · rename_i hc
      simp only [Bool.and_eq_true, Bool.not_eq_true', Option.isNone_iff_eq_none] at hc
      have ha' : ∀ o' ∈ o :: acc, db.ops o'.id = none := by
        intro o' h; rcases List.mem_cons.1 h with rfl | h
        · exact hc.2
        · exact ha o' h
      have hp' : (o :: acc).Pairwise (fun a b => a.id ≠ b.id) := by
        refine List.pairwise_cons.2 ⟨fun b hb e => ?_, hp⟩
        have : (acc.any fun x => x.id == o.id) = true := List.any_eq_true.2 ⟨b, hb, by simp [e]⟩
        rw [hc.1] at this; cases this
      obtain ⟨h1, h2⟩ := ih _ ha' hp'
      refine ⟨fun o' h => ⟨(h1 o' h).1, ?_⟩, h2⟩
      rcases (h1 o' h).2 with h | h
      · rcases List.mem_cons.1 h with rfl | h
        · exact Or.inr (List.mem_cons_self ..)
        · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · obtain ⟨h1, h2⟩ := ih _ ha hp
      refine ⟨fun o' h => ⟨(h1 o' h).1, ?_⟩, h2⟩
      rcases (h1 o' h).2 with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)

/-! ## What the store keeps -/

/-- Every logged op is stored as itself. -/
def LogExact (h : Held F) : Prop := ∀ o ∈ h.log, h.db.ops o.id = some o

/-- Every stored op is logged. -/
def StoredLogged (h : Held F) : Prop := ∀ x o, h.db.ops x = some o → o ∈ h.log

theorem addStep_fst (fam : Family F) (db : DB F) : ∀ (l : List Op) (st : Index × List Id),
    (∀ o ∈ l, (db.ops o.id).isSome = true) → (l.foldl (addStep fam db) st).1 = l.foldl (Index.add fam) st.1 := by
  intro l
  induction l with
  | nil => intro st _; rfl
  | cons o t ih =>
    intro st h
    rw [List.foldl_cons, List.foldl_cons, ih _ (fun o' ho' => h o' (List.mem_cons_of_mem _ ho'))]
    unfold addStep
    rw [if_pos (h o (List.mem_cons_self ..))]

section
variable (fam : Family F) (cfg : Config) (rms : Held F → Id → List Id)

/-- **A write keeps the index the store**, and the store's log exact. -/
theorem write_ix (n : Node) (ops : List Op) (h : Held F) (hw : IxWf n.ix) (hx : IxExact fam n.ix h)
    (hl : LogExact h) (hs : StoredLogged h) :
    IxWf ((n.write (psync fam cfg rms) ops).run h).1.1.ix ∧
    IxExact fam ((n.write (psync fam cfg rms) ops).run h).1.1.ix ((n.write (psync fam cfg rms) ops).run h).2 ∧
    LogExact ((n.write (psync fam cfg rms) ops).run h).2 ∧ StoredLogged ((n.write (psync fam cfg rms) ops).run h).2 := by
  rw [write_run]
  simp only [psync_fam]
  split
  · exact ⟨hw, hx, hl, hs⟩
  · obtain ⟨hA, hP⟩ := absent_props h.db ops [] (fun o h => by cases h) List.Pairwise.nil
    have hA' : ∀ o ∈ (List.foldl (absentStep h.db) [] ops).reverse, h.db.ops o.id = none :=
      fun o ho => (hA o (List.mem_reverse.1 ho)).1
    have hP' : (List.foldl (absentStep h.db) [] ops).reverse.Pairwise (fun a b => a.id ≠ b.id) :=
      List.pairwise_reverse.2 (hP.imp fun h e => h e.symm)
    have each := ingest_each _ h.db hA' hP'
    have stored : ∀ o ∈ (List.foldl (absentStep h.db) [] ops).reverse,
        ((turnH fam (List.foldl (absentStep h.db) [] ops).reverse h).db.ops o.id) = some o := by
      intro o ho; simp only [turnH, drainS_ops]; exact each o ho
    rw [addStep_fst _ _ _ _ (fun o ho => by rw [stored o ho]; rfl)]
    refine ⟨(fold_add fam ByteArray.empty ByteArray.empty _ _ hw).1, fun r x => ?_, ?_, ?_⟩
    · rw [(fold_add fam r x _ _ hw).2]
      constructor
      · rintro (h1 | ⟨o, ho, e, hr⟩)
        · obtain ⟨o, ho, hr⟩ := (hx r x).1 h1
          exact ⟨o, (turnH_ext fam _ h).1 x o ho, hr⟩
        · exact ⟨o, by rw [← e]; exact stored o ho, hr⟩
      · rintro ⟨o', ho', hr⟩
        simp only [turnH, drainS_ops] at ho'
        rcases ingest_from _ h.db x o' ho' with h1 | ⟨hm, e⟩
        · exact Or.inl ((hx r x).2 ⟨o', h1, hr⟩)
        · exact Or.inr ⟨o', hm, e, hr⟩
    · intro o ho
      simp only [turnH, List.mem_append] at ho
      rcases ho with ho | ho
      · exact (turnH_ext fam _ h).1 _ _ (hl o ho)
      · exact stored o ho
    · intro x o' ho'
      simp only [turnH, drainS_ops] at ho'
      simp only [turnH, List.mem_append]
      rcases ingest_from _ h.db x o' ho' with h1 | ⟨hm, _⟩
      · exact Or.inl (hs x o' h1)
      · exact Or.inr hm

end

/-- **A booted node's index is its store**, when the store's log is
exact and holds every stored op. -/
theorem boot_ix (fam : Family F) (h : Held F) (hi : IdsOk h) (hl : LogExact h) (hs : StoredLogged h) (floor : Nat) :
    IxWf (Node.boot fam h.log floor).ix ∧ IxExact fam (Node.boot fam h.log floor).ix h := by
  have hw0 : IxWf ({} : Index) := fun r it hit => by simp [Index.items] at hit
  refine ⟨(fold_add fam ByteArray.empty ByteArray.empty h.log {} hw0).1, fun r x => ?_⟩
  show Named' (h.log.foldl (Index.add fam) {}) r x ↔ _
  rw [(fold_add fam r x h.log {} hw0).2]
  constructor
  · rintro (⟨it, hit, _⟩ | ⟨o, ho, e, hr⟩)
    · simp [Index.items] at hit
    · exact ⟨o, by rw [← e]; exact hl o ho, hr⟩
  · rintro ⟨o, ho, hr⟩
    exact Or.inr ⟨o, hs x o ho, hi x o ho, hr⟩


/-- **What every plain node keeps:** its index names exactly the stored
ops of each room, its snapshots name stored ops, no session is the
family's, and its store files each op under its id, and logs exactly
what it stores. -/
structure NodeOk (fam : Family F) (n : Node) (h : Held F) : Prop where
  sub : Sub n h
  managed : n.managed = []
  ids : IdsOk h
  log : LogIn h
  /-- Its index of each room names exactly the stored ops of that room. -/
  wf : IxWf n.ix
  exact : IxExact fam n.ix h
  /-- Its log is exactly what it stores. -/
  logx : LogExact h
  stored : StoredLogged h
  /-- Every id a connection has offered names a stored op. -/
  offered : ∀ p ∈ n.conns, ∀ x ∈ p.2.offered, Named h x

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

theorem mem_foldl_insert {y : Id} : ∀ (l : List Id) (s : Std.HashSet Id),
    y ∈ l.foldl (·.insert ·) s → y ∈ s ∨ y ∈ l := by
  intro l
  induction l with
  | nil => intro s h; exact Or.inl h
  | cons a t ih =>
    intro s h
    rcases ih _ h with h | h
    · rw [Std.HashSet.mem_insert] at h
      rcases h with e | h
      · exact Or.inr (by rw [show a = y from eq_of_beq e]; exact List.mem_cons_self ..)
      · exact Or.inl h
    · exact Or.inr (List.mem_cons_of_mem _ h)

/-- A loop on a fixed store, every turn keeping it and a property of the
loop's state. -/
theorem forIn_inv_at {α β} (l : List α) (f : α → β → HeldM F (ForInStep β)) (h : Held F) (Q : β → Prop)
    (hk : ∀ a b, ((f a b).run h).2 = h) (hf : ∀ a b, Q b → Q ((f a b).run h).1.value) :
    ∀ b, Q b → Q ((forIn l b f).run h).1 := by
  induction l with
  | nil => intro b hb; exact hb
  | cons a t ih =>
    intro b hb
    rw [List.forIn_cons, HeldM.run_bind, hk a b]
    have := hf a b hb
    cases e : ((f a b).run h).1 with
    | done b' => rw [e] at this; exact this
    | yield b' => rw [e] at this; exact ih b' this

theorem finish_offered (st : Step) : (Conn.finish st).conn.offered = st.conn.offered := by
  unfold Conn.finish Conn.report
  by_cases h : st.conn.asked.isEmpty = true <;> simp [h]

/-- **The stream marks offered only ops it holds.** -/
theorem filed_offered (c : Conn) (ids : List Id) (h : Held F) (x : Id)
    (hx : x ∈ ((c.filed fam cfg ids : HeldM F Step).run h).1.conn.offered) : x ∈ c.offered ∨ Named h x := by
  unfold Conn.filed at hx
  simp only [HeldM.run_bind, HeldM.run_pure, finish_offered] at hx
  revert x
  refine forIn_inv_at _ _ h (fun st : List (Id × Id) × Conn => ∀ x ∈ st.2.offered, x ∈ c.offered ∨ Named h x)
    ?_ ?_ _ (fun x hx => Or.inl hx)
  · intro i st
    obtain ⟨off, c'⟩ := st
    dsimp only
    split
    · simp only [HeldM.run_bind, HeldM.run_getOp]
      split <;> (try split) <;> rfl
    · rfl
  · intro i st hst
    obtain ⟨off, c'⟩ := st
    dsimp only at hst ⊢
    split
    · simp only [HeldM.run_bind, HeldM.run_getOp]
      cases hg : h.db.ops i with
      | none => exact hst
      | some o =>
        dsimp only
        split
        · intro y hy
          change y ∈ c'.offered.insert i at hy
          rw [Std.HashSet.mem_insert] at hy
          rcases hy with e | hy
          · right; rw [← (eq_of_beq e : i = y)]; unfold Named; rw [hg]; rfl
          · exact hst y hy
        · exact hst
    · exact hst

/-- What an answer offers, it holds. -/
theorem answer_holds (P : Params) (mine : List Item) (cl : Claim) (x : Id)
    (hx : x ∈ (answer Prod.fst Prod.snd sha256 P mine cl).flatMap (fun | .hold xs => xs | _ => [])) :
    ∃ it ∈ mine, it.2 = x := by
  obtain ⟨o, ho, hxo⟩ := List.mem_flatMap.1 hx
  cases cl with
  | fp rg n l =>
    simp only [answer] at ho
    split at ho
    · cases ho
    · split at ho
      · rw [List.mem_singleton] at ho; subst ho; simp at hxo
      · obtain ⟨q, _, rfl⟩ := List.mem_map.1 ho; simp at hxo
  | ids rg xs =>
    simp only [answer, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · simp only [List.mem_map] at hxo
      obtain ⟨it, hit, rfl⟩ := hxo
      exact ⟨it, (mem_within.1 (List.mem_filter.1 hit).1).1, rfl⟩
    · simp at hxo

theorem onRbsr_offered (ix : Index) (c : Conn) (r : Id) (k : Nat) (cs : List Claim) (now : Nat) (x : Id)
    (hx : x ∈ (c.onRbsr cfg ix r k cs now).conn.offered) : x ∈ c.offered ∨ ∃ it ∈ Conn.snap ix c r k, it.2 = x := by
  unfold Conn.onRbsr at hx
  split at hx
  · exact Or.inl hx
  · dsimp only at hx
    split at hx
    · exact Or.inl hx
    · rcases mem_foldl_insert _ _ hx with hx | hx
      · left; split at hx <;> exact hx
      · right
        obtain ⟨o, ho, hxo⟩ := List.mem_flatMap.1 hx
        obtain ⟨cl, _, hcl⟩ := List.mem_flatMap.1 ho
        exact answer_holds cfg.params _ cl x (List.mem_flatMap.2 ⟨o, hcl, hxo⟩)

theorem start_offered (ix : Index) (c : Conn) (now : Nat) : (c.start cfg ix now).conn.offered = c.offered := by
  unfold Conn.start; split <;> rfl

theorem write_ok (n : Node) (ops : List Op) (h : Held F) (ok : NodeOk fam n h) :
    NodeOk fam ((n.write (psync fam cfg rms) ops).run h).1.1 ((n.write (psync fam cfg rms) ops).run h).2 := by
  have e := write_grows fam cfg rms n ops h
  obtain ⟨w1, x1, l1, s1⟩ := write_ix fam cfg rms n ops h ok.wf ok.exact ok.logx ok.stored
  refine ⟨write_sub fam cfg rms n ops h ok.sub, by rw [(write_node fam cfg rms n ops h).2.2]; exact ok.managed,
    ?_, ok.log.ext e, w1, x1, l1, s1,
    fun p hp x hx => by rw [(write_node fam cfg rms n ops h).1] at hp; exact (ok.offered p hp x hx).ext e⟩
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

theorem fanout_ok (n : Node) (ids : List Id) (h : Held F) (ok : NodeOk fam n h) :
    NodeOk fam ((n.fanout (psync fam cfg rms) ids).run h).1.1 ((n.fanout (psync fam cfg rms) ids).run h).2 := by
  obtain ⟨e1, e2, -, e4, e5⟩ := fanout_node fam cfg rms n ids h
  rw [e1]
  refine ⟨⟨by rw [e2]; exact ok.sub.1, ?_⟩, by rw [e4]; exact ok.managed, ok.ids, ok.log,
    by rw [e2]; exact ok.wf, by rw [e2]; exact ok.exact, ok.logx, ok.stored, ?_⟩
  rotate_left
  · intro p hp x hx
    rw [e5] at hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    rcases filed_offered fam cfg _ ids h x hx with hx | hx
    · exact ok.offered q hq x hx
    · exact hx
  intro p hp
  rw [e5] at hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
  intro x hx
  rw [filed_snaps] at hx
  exact (ok.sub.2 q hq).setRooms _ x hx

theorem fanout_cids (n : Node) (ids : List Id) (h : Held F) :
    cids ((n.fanout (psync fam cfg rms) ids).run h).1.1 = cids n := by
  rw [cids, (fanout_node fam cfg rms n ids h).2.2.2.2]; simp [cids]

theorem store_ok (n : Node) (ops : List Op) (mine : Bool) (h : Held F) (ok : NodeOk fam n h) :
    NodeOk fam ((n.store (psync fam cfg rms) ops mine).run h).1.1 ((n.store (psync fam cfg rms) ops mine).run h).2 := by
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

theorem apply_ok (n : Node) (cid : Id) (s : Step) (now : Nat) (h : Held F) (ok : NodeOk fam n h)
    (hs : SnapsIn s.conn h) (ho : ∀ x ∈ s.conn.offered, Named h x) :
    NodeOk fam ((n.apply (psync fam cfg rms) cid s now).run h).1.1 ((n.apply (psync fam cfg rms) cid s now).run h).2 := by
  cases hd : s.drop
  · rw [apply_run fam cfg rms n cid s now h hd]
    apply store_ok
    refine ⟨⟨ok.sub.1, ?_⟩, ok.managed, ok.ids, ok.log, ok.wf, ok.exact, ok.logx, ok.stored, ?_⟩
    · intro p hp
      simp only [setConn, List.mem_map] at hp
      obtain ⟨q, hq, e⟩ := hp
      split at e
      · rw [← e]; exact hs
      · rw [← e]; exact ok.sub.2 q hq
    · intro p hp
      simp only [setConn, List.mem_map] at hp
      obtain ⟨q, hq, e⟩ := hp
      split at e
      · rw [← e]; exact ho
      · rw [← e]; exact ok.offered q hq
  · simp only [Node.apply, hd, ite_true, HeldM.run_pure]
    refine ⟨⟨ok.sub.1, fun p hp => ok.sub.2 p ?_⟩, ?_, ok.ids, ok.log, ok.wf, ok.exact, ok.logx, ok.stored,
      fun p hp => ok.offered p ?_⟩
    · simp only [Node.drop, Node.close] at hp; exact (List.mem_filter.1 hp).1
    · simp [Node.drop, Node.close, ok.managed]
    · simp only [Node.drop, Node.close] at hp; exact (List.mem_filter.1 hp).1

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

theorem snapOf_named (ix : Index) (c : Conn) (r : Id) (k : Nat) (h : Held F) (hi : IxIn ix h) (hc : SnapsIn c h) :
    ∀ it ∈ Conn.snap ix c r k, Named h it.2 := by
  intro it hit
  unfold Conn.snap at hit
  split at hit
  · rename_i q s e
    exact hc _ (List.mem_of_find?_eq_some e) it hit
  · exact hi r it hit

/-- **A claim of ids is answered with a want for each id the snapshot
lacks.** -/
theorem onRbsr_wants (cfg : Config) (ix : Index) (c : Conn) (r : Id) (k : Nat) (cs : List Claim) (rg : Range)
    (L : List Id) (now : Nat) (x : Id) (hr : r ∈ c.rooms) (hc : Claim.ids rg L ∈ cs) (hx : x ∈ L)
    (hmax : 0 < cfg.maxIds) (hs : ∀ it ∈ Conn.snap ix c r k, it.2 ≠ x) :
    ∃ W, x ∈ W ∧ W.length ≤ cfg.maxIds ∧ (Msg.want W).op ∈ (c.onRbsr cfg ix r k cs now).send := by
  have hw : x ∈ L.filter fun i => !named Prod.snd (within Prod.fst rg (Conn.snap ix c r k)) i := by
    refine List.mem_filter.2 ⟨hx, ?_⟩
    rw [Bool.not_eq_true']
    apply named_false.2
    intro a ha e
    exact hs a (mem_within.1 ha).1 e
  have hne : cs.isEmpty = false := by
    cases cs with
    | nil => cases hc
    | cons _ _ => rfl
  unfold Conn.onRbsr
  simp only [has_of_mem hr, Bool.not_true, Bool.false_eq_true, ite_false, hne]
  have hwl : x ∈ (cs.flatMap (answer Prod.fst Prod.snd sha256 cfg.params (c.snap ix r k))).flatMap
      (fun | .want xs => xs | _ => []) := by
    refine List.mem_flatMap.2 ⟨.want (L.filter fun i => !named Prod.snd (within Prod.fst rg (Conn.snap ix c r k)) i),
      List.mem_flatMap.2 ⟨.ids rg L, hc, by simp [answer]⟩, hw⟩
  obtain ⟨W, hxW, hl, hm⟩ := chunks_cover cfg _ Msg.want hmax hwl
  exact ⟨W, hxW, hl, List.mem_cons_of_mem _ (List.mem_append_right _ hm)⟩

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
      | hold r ids =>
        simp only [HeldM.run_bind, HeldM.run_pure, Conn.finish_drop, Conn.onHold]
        split
        · rfl
        · simp only [HeldM.run_bind, HeldM.run_pure]
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
theorem claim_step (cid : Id) (now : Nat) (st : (Node × Acts) × Held F) (ok : NodeOk fam st.1.1 st.2) (c : Conn)
    (hc : st.1.1.conn? cid = some c) (r : Id) (kr : Nat) (cs : List Claim) (rg : Range) (L : List Id) (x : Id)
    (hr : r ∈ rms st.2 cid) (hcs : Claim.ids rg L ∈ cs) (hx : x ∈ L) (hmax : 0 < cfg.maxIds) (hn : ¬ Named st.2 x) :
    ∃ W, x ∈ W ∧ W.length ≤ cfg.maxIds ∧
      (Route.conn cid, (Msg.want W).op.bytes) ∈ (frameStep fam cfg rms cid now st (Msg.rbsr r kr cs).op.bytes).1.2.send := by
  have hsc : SnapsIn ({ c.setRooms (rms st.2 cid) with heard := now } : Conn) st.2 :=
    (ok.sub.2 _ (conn_mem hc)).setRooms _
  obtain ⟨W, hxW, hl, hm⟩ := onRbsr_wants cfg st.1.1.ix ({ c.setRooms (rms st.2 cid) with heard := now } : Conn)
    r kr cs rg L now x hr hcs hx hmax (fun it hit e => hn (e ▸ snapOf_named _ _ _ _ st.2 ok.sub.1 hsc it hit))
  refine ⟨W, hxW, hl, ?_⟩
  unfold frameStep
  rw [hc]; dsimp only
  have hd := recv_drop fam cfg st.1.1.ix (c.setRooms (rms st.2 cid)) (Msg.rbsr r kr cs).op.bytes now st.2
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

theorem onHold_offered (c : Conn) (r : Id) (ids : List Id) (h : Held F) :
    ((c.onHold fam cfg r ids : HeldM F Step).run h).1.conn.offered = c.offered := by
  unfold Conn.onHold
  split
  · rfl
  · simp only [HeldM.run_bind, HeldM.run_pure]

theorem foldl_insert_ids {x : Id} : ∀ (l : List Op) (s : Std.HashSet Id),
    x ∈ l.foldl (fun (k : Std.HashSet Id) (o : Op) => k.insert o.id) s → x ∈ s ∨ ∃ o ∈ l, o.id = x := by
  intro l
  induction l with
  | nil => intro s h; exact Or.inl h
  | cons a t ih =>
    intro s h
    rcases ih _ h with h | ⟨o, ho, e⟩
    · rw [Std.HashSet.mem_insert] at h
      rcases h with e | h
      · exact Or.inr ⟨a, List.mem_cons_self .., eq_of_beq e⟩
      · exact Or.inl h
    · exact Or.inr ⟨o, List.mem_cons_of_mem _ ho, e⟩

variable (hw : WalkLaws (F := F) fam cfg)
include hw

/-- **A want marks offered only ops it holds.** -/
theorem onWant_offered (c : Conn) (ids : List Id) (h : Held F) (hi : IdsOk h) (x : Id)
    (hx : x ∈ ((c.onWant fam cfg ids : HeldM F Step).run h).1.conn.offered) : x ∈ c.offered ∨ Named h x := by
  unfold Conn.onWant at hx
  split at hx
  · exact Or.inl hx
  · simp only [HeldM.run_bind, HeldM.run_pure, filterMapM_getOp] at hx
    rcases hw.offered _ h x hx with hx | hx
    · rcases foldl_insert_ids _ _ hx with hx | ⟨o, ho, e⟩
      · exact Or.inl hx
      · right
        obtain ⟨i, _, hio⟩ := List.mem_filterMap.1 (List.mem_filter.1 ho).1
        rw [← e, hi i o hio]; unfold Named; rw [hio]; rfl
    · exact Or.inr hx

/-- **What a connection receives marks offered only ops it holds.** -/
theorem recv_offered (ix : Index) (c : Conn) (b : ByteArray) (now : Nat) (h : Held F) (hi : IxIn ix h)
    (hc : SnapsIn c h) (hid : IdsOk h) (x : Id)
    (hx : x ∈ ((Conn.recv fam cfg ix c b now : HeldM F Step).run h).1.conn.offered) : x ∈ c.offered ∨ Named h x := by
  unfold Conn.recv at hx
  cases hd : Op.decode b with
  | none => simp only [hd, HeldM.run_pure] at hx; exact Or.inl hx
  | some o =>
    simp only [hd] at hx
    cases hm : Msg.ofOp o with
    | none =>
      simp only [hm] at hx
      split at hx
      · exact Or.inl hx
      · simp only [HeldM.run_pure, finish_offered] at hx; exact Or.inl hx
    | some m =>
      simp only [hm] at hx
      cases m with
      | hello f =>
        simp only [HeldM.run_pure, finish_offered] at hx
        left
        split at hx
        · rw [start_offered] at hx; exact hx
        · exact hx
      | rbsr r k cs =>
        simp only [HeldM.run_pure, finish_offered] at hx
        rcases onRbsr_offered cfg ix _ r k cs now x hx with hx | ⟨it, hit, e⟩
        · exact Or.inl hx
        · exact Or.inr (e ▸ snapOf_named ix _ r k h hi hc it hit)
      | hold r ids =>
        simp only [HeldM.run_bind, HeldM.run_pure, finish_offered, onHold_offered] at hx
        exact Or.inl hx
      | want ids =>
        simp only [HeldM.run_bind, HeldM.run_pure, finish_offered] at hx
        exact onWant_offered fam cfg hw ({ c with heard := now } : Conn) ids h hid x hx

/-- **The clock marks offered only ops it holds.** -/
theorem tick_offered (ix : Index) (c : Conn) (now : Nat) (h : Held F) (x : Id)
    (hx : x ∈ ((c.tick fam cfg ix now : HeldM F Step).run h).1.conn.offered) : x ∈ c.offered ∨ Named h x := by
  unfold Conn.tick at hx
  split at hx
  · exact Or.inl hx
  · simp only [HeldM.run_bind, HeldM.run_pure, finish_offered] at hx
    have hw' : ∀ y, y ∈ ((c.walk fam cfg : HeldM F _).run h).1.1.offered → y ∈ c.offered ∨ Named h y :=
      fun y hy => hw.offered c h y hy
    split at hx
    · rw [start_offered] at hx; exact hw' x hx
    · exact hw' x hx

/-- **One payload keeps the node invariant**, grows the store, keeps the
sessions and addresses, and only adds to what is sent. -/
theorem frameStep_ok (cid : Id) (now : Nat) (st : (Node × Acts) × Held F) (b : ByteArray)
    (ok : NodeOk fam st.1.1 st.2) :
    NodeOk fam (frameStep fam cfg rms cid now st b).1.1 (frameStep fam cfg rms cid now st b).2 ∧
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
    have hof : ∀ x ∈ ((Conn.recv fam cfg st.1.1.ix (c.setRooms (rms st.2 cid)) b now : HeldM F Step).run st.2).1.conn.offered,
        Named st.2 x := fun x hx => by
      rcases recv_offered fam cfg hw _ _ b now st.2 ok.sub.1 ((ok.sub.2 _ (conn_mem hc)).setRooms _) ok.ids x hx with
        hx | hx
      · exact ok.offered _ (conn_mem hc) x hx
      · exact hx
    refine ⟨apply_ok fam cfg rms _ _ _ _ _ ok hsn hof, apply_grows fam cfg rms _ _ _ _ _, ?_, ?_, ?_⟩
    · rw [apply_run fam cfg rms _ _ _ _ _ hd]
      rw [(store_node fam cfg rms _ _ _ _).2, setConn_cids]
    · rw [apply_run fam cfg rms _ _ _ _ _ hd]
      rw [(store_node fam cfg rms _ _ _ _).1]; rfl
    · intro y hy; exact List.mem_append_left _ hy

/-- Through a frame's payloads: the invariant, growth, the sessions, the
addresses, and what is sent only grows. -/
theorem frame_fold (cid : Id) (now : Nat) : ∀ (l : List ByteArray) (st : (Node × Acts) × Held F),
    NodeOk fam st.1.1 st.2 →
    NodeOk fam (l.foldl (frameStep fam cfg rms cid now) st).1.1 (l.foldl (frameStep fam cfg rms cid now) st).2 ∧
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

theorem setAddr_ok (n : Node) (cid : Id) (a : ByteArray) (h : Held F) (ok : NodeOk fam n h) : NodeOk fam (n.setAddr cid a) h :=
  ⟨ok.sub, ok.managed, ok.ids, ok.log, ok.wf, ok.exact, ok.logx, ok.stored, ok.offered⟩

/-- A frame's payloads up to and after one of them. -/
theorem fold_at {α β : Type} (f : α → β → α) (l : List β) (b : β) (hb : b ∈ l) (st : α) :
    ∃ pre post : List β, l.foldl f st = post.foldl f (f (pre.foldl f st) b) := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hb
  exact ⟨pre, post, by simp [List.foldl_append]⟩

/-- The end of a session's frame: what it sent on the session goes out
to the frame's sender, and the store is as the payloads left it. -/
theorem frame_end (cid : Id) (now : Nat) (st : (Node × Acts) × Held F) (ok : NodeOk fam st.1.1 st.2) (a p : ByteArray)
    (ha : st.1.1.addr? cid = some a) (hp : (Route.conn cid, p) ∈ st.1.2.send) :
    ∃ g, p ∈ g ∧ (a, plainFrame cid g) ∈ ((st.1.1.finish (psync fam cfg rms) st.1.2 now).run st.2).1.2.send := by
  rw [finish_run fam cfg rms _ _ _ _ ok.managed]
  exact seal_mem fam cfg rms _ _ _ cid p a hp ha

theorem frame_end_store (now : Nat) (st : (Node × Acts) × Held F) (ok : NodeOk fam st.1.1 st.2) :
    ((st.1.1.finish (psync fam cfg rms) st.1.2 now).run st.2).2 = st.2 := by
  rw [finish_run fam cfg rms _ _ _ _ ok.managed]

end

section
variable (fam : Family F) (cfg : Config) (rms : Held F → Id → List Id) (hw : WalkLaws (F := F) fam cfg)
include hw

/-- **H1: a claim of ids, delivered, is answered with a want** for each
id it lists that the node lacks, in a frame back to the claim's sender;
or the node holds it by the frame's end. -/
theorem claim_wants (n : Node) (h : Held F) (ok : NodeOk fam n h) (a bytes : ByteArray) (now : Nat) (cid : Id)
    (inner : List ByteArray) (hp : plainPeek bytes = some (cid, inner)) (c : Conn) (hc : n.conn? cid = some c)
    (r : Id) (hr : ∀ h', r ∈ rms h' cid) (kr : Nat) (cs : List Claim) (rg : Range) (L : List Id) (x : Id)
    (hb : (Msg.rbsr r kr cs).op.bytes ∈ inner) (hcs : Claim.ids rg L ∈ cs) (hx : x ∈ L) (hmax : 0 < cfg.maxIds) :
    Named ((n.onFrame (psync fam cfg rms) a bytes now).run h).2 x ∨
      ∃ W g, x ∈ W ∧ W.length ≤ cfg.maxIds ∧ (Msg.want W).op.bytes ∈ g ∧
        (a, plainFrame cid g) ∈ ((n.onFrame (psync fam cfg rms) a bytes now).run h).1.2.send := by
  obtain ⟨h0, bundle, hb', hi⟩ := plainFrame_of_peek hp
  rw [onFrame_sealed fam cfg rms hw n a bytes now h cid bundle inner c h0 hb' hi hc]
  have ok0 := setAddr_ok fam n cid a h ok
  obtain ⟨pre, post, e⟩ := fold_at (frameStep fam cfg rms cid now) inner _ hb ((n.setAddr cid a, {}), h)
  rw [e]
  obtain ⟨ok1, e1, c1, a1, -⟩ := frame_fold fam cfg rms hw cid now pre ((n.setAddr cid a, {}), h) ok0
  generalize pre.foldl (frameStep fam cfg rms cid now) ((n.setAddr cid a, {}), h) = st1 at ok1 e1 c1 a1
  obtain ⟨c1', hc1⟩ := (conn_iff _ _).2 (by rw [c1]; exact (conn_iff _ _).1 ⟨c, hc⟩)
  obtain ⟨ok2, e2, -, a2, s2⟩ := frameStep_ok fam cfg rms hw cid now st1 (Msg.rbsr r kr cs).op.bytes ok1
  obtain ⟨ok3, e3, -, a3, s3⟩ := frame_fold fam cfg rms hw cid now post _ ok2
  by_cases hn : Named st1.2 x
  · left
    rw [frame_end_store fam cfg rms now _ ok3]
    exact (hn.ext e2).ext e3
  · right
    obtain ⟨W, hxW, hl, hm⟩ := claim_step fam cfg rms cid now st1 ok1 c1' hc1 r kr cs rg L x (hr _) hcs hx hmax hn
    have ha : (post.foldl (frameStep fam cfg rms cid now) (frameStep fam cfg rms cid now st1
        (Msg.rbsr r kr cs).op.bytes)).1.1.addr? cid = some a := by
      unfold Node.addr?; rw [a3, a2, a1]; exact setAddr_addr n cid a
    obtain ⟨g, hg, hf⟩ := frame_end fam cfg rms cid now _ ok3 a _ ha (s3 _ hm)
    exact ⟨W, g, hxW, hl, hg, hf⟩

/-- **H2: a want, delivered, for an op the node holds in a room the
session shows, is answered with the op**, in a frame back to the
want's sender. -/
theorem want_sends (n : Node) (h : Held F) (ok : NodeOk fam n h) (a bytes : ByteArray) (now : Nat) (cid : Id)
    (inner : List ByteArray) (hp : plainPeek bytes = some (cid, inner)) (c : Conn) (hc : n.conn? cid = some c)
    (r : Id) (hr : ∀ h', r ∈ rms h' cid) (W : List Id) (x : Id) (o : Op)
    (hb : (Msg.want W).op.bytes ∈ inner) (hW : W.length ≤ cfg.maxIds) (hx : x ∈ W) (ho : h.db.ops x = some o)
    (hor : fam.room o = some r) :
    ∃ g, o.bytes ∈ g ∧ (a, plainFrame cid g) ∈ ((n.onFrame (psync fam cfg rms) a bytes now).run h).1.2.send := by
  obtain ⟨h0, bundle, hb', hi⟩ := plainFrame_of_peek hp
  rw [onFrame_sealed fam cfg rms hw n a bytes now h cid bundle inner c h0 hb' hi hc]
  have ok0 := setAddr_ok fam n cid a h ok
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
theorem op_taken (n : Node) (h : Held F) (ok : NodeOk fam n h) (a bytes : ByteArray) (now : Nat) (cid : Id)
    (inner : List ByteArray) (hp : plainPeek bytes = some (cid, inner)) (c : Conn) (hc : n.conn? cid = some c)
    (r : Id) (hr : ∀ h', r ∈ rms h' cid) (o : Op) (hb : o.bytes ∈ inner) (hwire : isWire o.kind = false)
    (hor : fam.room o = some r) :
    Named ((n.onFrame (psync fam cfg rms) a bytes now).run h).2 o.id := by
  obtain ⟨h0, bundle, hb', hi⟩ := plainFrame_of_peek hp
  rw [onFrame_sealed fam cfg rms hw n a bytes now h cid bundle inner c h0 hb' hi hc]
  have ok0 := setAddr_ok fam n cid a h ok
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

theorem finish_ok (n : Node) (out : Acts) (now : Nat) (h : Held F) (ok : NodeOk fam n h) :
    NodeOk fam ((n.finish (psync fam cfg rms) out now).run h).1.1 ((n.finish (psync fam cfg rms) out now).run h).2 := by
  rw [finish_run fam cfg rms _ _ _ _ ok.managed]
  exact ⟨ok.sub, ok.managed, ok.ids, ok.log, ok.wf, ok.exact, ok.logx, ok.stored, ok.offered⟩

theorem onWrite_ok (n : Node) (ops : List Op) (now : Nat) (h : Held F) (ok : NodeOk fam n h) :
    NodeOk fam ((n.onWrite (psync fam cfg rms) ops now).run h).1.1 ((n.onWrite (psync fam cfg rms) ops now).run h).2 := by
  unfold Node.onWrite
  simp only [HeldM.run_bind]
  exact finish_ok fam cfg rms _ _ _ _ (store_ok fam cfg rms n ops true h ok)

theorem connect_ok (n : Node) (cid : Id) (a : ByteArray) (d : Bool) (now : Nat) (h : Held F) (ok : NodeOk fam n h) :
    NodeOk fam ((n.connect (psync fam cfg rms) cid a d now).run h).1.1 ((n.connect (psync fam cfg rms) cid a d now).run h).2 := by
  unfold Node.connect Node.open
  simp only [HeldM.run_bind, psync_rooms, readH_run, HeldM.run_pure]
  apply finish_ok
  refine ⟨⟨ok.sub.1, ?_⟩, ?_, ok.ids, ok.log, ok.wf, ok.exact, ok.logx, ok.stored, ?_⟩
  · intro p hp
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · intro e he; cases he
    · simp only [Node.setAddr, Node.close] at hp
      exact ok.sub.2 p (List.mem_filter.1 hp).1
  · simp [Node.setAddr, Node.close, ok.managed]
  · intro p hp
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · intro x hx; simp [Conn.open] at hx
    · simp only [Node.setAddr, Node.close] at hp
      exact ok.offered p (List.mem_filter.1 hp).1

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

theorem tickStep_ok (now : Nat) (st : (Node × Acts) × Held F) (p : Id × Conn) (ok : NodeOk fam st.1.1 st.2) :
    NodeOk fam (tickStep fam cfg rms now st p).1.1 (tickStep fam cfg rms now st p).2 := by
  unfold tickStep
  cases hc : st.1.1.conn? p.1 with
  | none => exact ok
  | some c =>
    exact apply_ok fam cfg rms _ _ _ _ _ ok (tick_snaps fam cfg hw _ _ _ _ ok.sub.1 ((ok.sub.2 _ (conn_mem hc)).setRooms _))
      (fun x hx => by
        rcases tick_offered fam cfg hw _ _ now st.2 x hx with hx | hx
        · exact ok.offered _ (conn_mem hc) x hx
        · exact hx)

theorem onTick_ok (n : Node) (now : Nat) (h : Held F) (ok : NodeOk fam n h) :
    NodeOk fam ((n.onTick (psync fam cfg rms) now).run h).1.1 ((n.onTick (psync fam cfg rms) now).run h).2 := by
  rw [onTick_run fam cfg rms hw]
  apply finish_ok
  have : ∀ (l : List (Id × Conn)) st, NodeOk fam st.1.1 st.2 →
      NodeOk fam (l.foldl (tickStep fam cfg rms now) st).1.1 (l.foldl (tickStep fam cfg rms now) st).2 := by
    intro l
    induction l with
    | nil => intro st h; exact h
    | cons p t ih => intro st h; exact ih _ (tickStep_ok fam cfg rms hw now st p h)
  exact this _ _ ok


theorem onFrame_ok (n : Node) (a b : ByteArray) (now : Nat) (h : Held F) (ok : NodeOk fam n h) :
    NodeOk fam ((n.onFrame (psync fam cfg rms) a b now).run h).1.1 ((n.onFrame (psync fam cfg rms) a b now).run h).2 := by
  cases h0 : b[0]? with
  | none => simp only [Node.onFrame, h0, HeldM.run_pure]; exact ok
  | some t =>
    by_cases t1 : t = 1
    · subst t1
      cases hd : (Codec.decode (b.extract 1 b.size) : Option (Id × ByteArray)) with
      | none => simp only [Node.onFrame, h0, psync_openFrame, HeldM.pure_bind, hd, Node.onSealed, HeldM.run_pure]; exact ok
      | some q =>
        obtain ⟨cid, bundle⟩ := q
        cases hc : n.conn? cid with
        | none => simp only [Node.onFrame, h0, psync_openFrame, HeldM.pure_bind, hd, Node.onSealed, hc, HeldM.run_pure]; exact ok
        | some c =>
          cases hi : (Codec.decode bundle : Option (List ByteArray)) with
          | none => simp only [Node.onFrame, h0, psync_openFrame, HeldM.pure_bind, hd, Node.onSealed, hc, hi, HeldM.run_pure]; exact ok
          | some inner =>
            rw [onFrame_sealed fam cfg rms hw n a b now h cid bundle inner c h0 hd hi hc]
            exact finish_ok fam cfg rms _ _ _ _ (frame_fold fam cfg rms hw cid now inner _ (setAddr_ok fam n cid a h ok)).1
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

/-! ## Only the clock and the harness close a session -/

section
variable (fam : Family F) (cfg : Config) (rms : Held F → Id → List Id) (hw : WalkLaws (F := F) fam cfg)

omit hw in
theorem finish_cids (n : Node) (out : Acts) (now : Nat) (h : Held F) (hm : n.managed = []) :
    cids ((n.finish (psync fam cfg rms) out now).run h).1.1 = cids n := by
  rw [finish_run fam cfg rms _ _ _ _ hm]; rfl

omit hw in
theorem onWrite_cids (n : Node) (ops : List Op) (now : Nat) (h : Held F) (ok : NodeOk fam n h) :
    cids ((n.onWrite (psync fam cfg rms) ops now).run h).1.1 = cids n := by
  unfold Node.onWrite
  simp only [HeldM.run_bind]
  rw [finish_cids fam cfg rms _ _ _ _ (store_ok fam cfg rms n ops true h ok).managed]
  exact (store_node fam cfg rms n ops true h).2

omit hw in
theorem connect_cids (n : Node) (cid cid' : Id) (a : ByteArray) (d : Bool) (now : Nat) (h : Held F)
    (ok : NodeOk fam n h) (hne : cid ≠ cid') (hc : cid ∈ cids n) :
    cid ∈ cids ((n.connect (psync fam cfg rms) cid' a d now).run h).1.1 := by
  have hk := connect_ok fam cfg rms n cid' a d now h ok
  unfold Node.connect Node.open at hk ⊢
  simp only [HeldM.run_bind, psync_rooms, readH_run, HeldM.run_pure] at hk ⊢
  rw [finish_cids fam cfg rms _ _ _ _ (by simp [Node.setAddr, Node.close, ok.managed])]
  simp only [cids, Node.setAddr, Node.close, List.map_cons, List.mem_cons]
  right
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hc
  exact List.mem_map.2 ⟨p, List.mem_filter.2 ⟨hp, by simp [hne]⟩, rfl⟩

include hw

theorem onFrame_cids (n : Node) (a b : ByteArray) (now : Nat) (h : Held F) (ok : NodeOk fam n h) :
    cids ((n.onFrame (psync fam cfg rms) a b now).run h).1.1 = cids n := by
  cases h0 : b[0]? with
  | none => simp only [Node.onFrame, h0, HeldM.run_pure]
  | some t =>
    by_cases t1 : t = 1
    · subst t1
      cases hd : (Codec.decode (b.extract 1 b.size) : Option (Id × ByteArray)) with
      | none => simp only [Node.onFrame, h0, psync_openFrame, HeldM.pure_bind, hd, Node.onSealed, HeldM.run_pure]
      | some q =>
        obtain ⟨cid, bundle⟩ := q
        cases hc : n.conn? cid with
        | none => simp only [Node.onFrame, h0, psync_openFrame, HeldM.pure_bind, hd, Node.onSealed, hc, HeldM.run_pure]
        | some c =>
          cases hi : (Codec.decode bundle : Option (List ByteArray)) with
          | none => simp only [Node.onFrame, h0, psync_openFrame, HeldM.pure_bind, hd, Node.onSealed, hc, hi, HeldM.run_pure]
          | some inner =>
            rw [onFrame_sealed fam cfg rms hw n a b now h cid bundle inner c h0 hd hi hc]
            obtain ⟨ok1, -, c1, -, -⟩ := frame_fold fam cfg rms hw cid now inner ((n.setAddr cid a, {}), h)
              (setAddr_ok fam n cid a h ok)
            rw [finish_cids fam cfg rms _ _ _ _ ok1.managed, c1]; rfl
    · by_cases t0 : t = 0
      · subst t0
        cases hd : Op.decode (b.extract 1 b.size) with
        | none => simp only [Node.onFrame, h0, hd, HeldM.run_pure]
        | some o =>
          by_cases he : (intakeConn fam [o]).isEmpty = true
          · simp only [Node.onFrame, h0, hd, psync_fam, he, ↓reduceIte, HeldM.run_pure]
          · simp only [Node.onFrame, h0, hd, psync_fam, he, ↓reduceIte, Bool.false_eq_true, HeldM.run_bind,
              psync_recv, HeldM.pure_bind, store_nil]
            rw [finish_cids fam cfg rms _ _ _ _ (write_ok fam cfg rms _ _ _ ok).managed]
            rw [cids, (write_node fam cfg rms _ _ _).1]; rfl
      · unfold Node.onFrame
        rw [h0]
        split
        · rename_i e; cases e; exact absurd rfl t0
        · rename_i e; cases e; exact absurd rfl t1
        · rfl

end

/-- A booted node, from a store that files ops under their ids and holds
what it logged, keeps the invariant. -/
theorem boot_ok (fam : Family F) (h : Held F) (hi : IdsOk h) (hl : LogIn h) (hx : LogExact h)
    (hs : StoredLogged h) (floor : Nat) : NodeOk fam (Node.boot fam h.log floor) h := by
  obtain ⟨w, e⟩ := boot_ix fam h hi hx hs floor
  refine ⟨⟨fun r it hit => ?_, fun p hp => by cases hp⟩, rfl, hi, hl, w, e, hx, hs, fun p hp => by cases hp⟩
  rcases items_foldl fam h.log {} r it hit with hit | ⟨o, ho, e⟩
  · simp [Index.items] at hit
  · rw [e]; exact hl o ho

theorem enter_ok (Q : Plain F) (w : World (Held F) Q.n) (i : Fin Q.n) (t : Nat) (f : Node → HeldM F (Node × Effects))
    (hf : NodeOk Q.fam (w.node i) (w.box i) → NodeOk Q.fam ((f (w.node i)).run (w.box i)).1.1 ((f (w.node i)).run (w.box i)).2)
    (ok : ∀ j, NodeOk Q.fam (w.node j) (w.box j)) : ∀ j, NodeOk Q.fam ((w.enter Q.setup i t f).node j) ((w.enter Q.setup i t f).box j) := by
  intro j
  simp only [World.enter, upd]
  by_cases e : j = i
  · subst e; simp only [ite_true]; exact hf (ok j)
  · simp only [e, ite_false]; exact ok j

/-- **Every node of every world the plain world reaches keeps the node
invariant**, against any attacker. -/
theorem reach_ok' (Q : Plain F) (hw : WalkLaws (F := F) Q.fam Q.cfg)
    (adv : World (Held F) Q.setup.n → ByteArray → Prop) (w₀ w : World (Held F) Q.setup.n)
    (h0 : ∀ i, NodeOk Q.fam (w₀.node i) (w₀.box i)) (hr : Reachable Q.setup adv w₀ w) :
    ∀ i, NodeOk Q.fam (w.node i) (w.box i) := by
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
        exact boot_ok Q.fam _ (ih j).ids (ih j).log (ih j).logx (ih j).stored _
      · simp only [e, ite_false]; exact ih j
    | connect i j cid d t =>
      exact enter_ok Q w i t (fun nd => nd.connect (psync Q.fam Q.cfg (Q.rooms i)) cid (Q.setup.addr j) d t)
        (fun h => connect_ok Q.fam Q.cfg (Q.rooms i) _ _ _ _ _ _ h) ih
    | inject i o b t =>
      exact enter_ok Q w i t (fun nd => nd.onFrame (psync Q.fam Q.cfg (Q.rooms i)) o b t)
        (fun h => onFrame_ok Q.fam Q.cfg (Q.rooms i) hw _ _ _ _ _ h) ih


theorem reach_ok (Q : Plain F) (hw : WalkLaws (F := F) Q.fam Q.cfg) (adv : World (Held F) Q.n → ByteArray → Prop)
    (w : World (Held F) Q.n) (hr : Q.Reach adv w) : ∀ i, NodeOk Q.fam (w.node i) (w.box i) :=
  reach_ok' Q hw adv Q.start w (fun _ => boot_ok Q.fam {} (fun x o h => by cases h) (fun o ho => by cases ho)
    (fun o ho => by cases ho) (fun x o h => by cases h) _) hr

end Engine.World
