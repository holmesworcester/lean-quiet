/-
The plain setup's nodes, run on held stores: what each entry point does
to the store and to the node's index and snapshots, for any state.

- **Stores only grow** (`Ext`): nothing a plain node runs takes an op
  out of its store (it never purges).
- **Indexes and snapshots name stored ops** (`Sub`): every item of a
  node's room index, and of every snapshot its connections keep, names
  an op of that room in its store. Rounds are answered from these, so
  an op a round says this side holds, it holds.
- **Sessions persist through a frame:** taking a session's payloads never
  closes it, and everything the payloads' steps send on it goes out
  sealed to the session's address (`seal_mem`, after a3's).

Each entry point is shown to keep both, so `grows` and `sub_reach`
lift them to every world the plain setup reaches.
-/
import engine.world.Run
import engine.world.Statements

namespace Engine.World
open Engine Engine.Sync

variable {F : Type}

/-! ## The plain hooks -/

section
variable (fam : Family F) (cfg : Config) (rms : Held F → Id → List Id)

@[simp] theorem psync_fam : (psync fam cfg rms).fam = fam := rfl
@[simp] theorem psync_cfg : (psync fam cfg rms).cfg = cfg := rfl
@[simp] theorem psync_rooms (cid : Id) : (psync fam cfg rms).hooks.rooms cid = readH fun h => rms h cid := rfl
@[simp] theorem psync_openFrame (b : ByteArray) :
    (psync fam cfg rms).hooks.openFrame b = pure (Codec.decode b) := rfl
@[simp] theorem psync_sealFor (cid : Id) (b : ByteArray) :
    (psync fam cfg rms).hooks.sealFor cid b = pure (some (Codec.encode (cid, b))) := rfl
@[simp] theorem psync_recv (o : Option Id) (a : ByteArray) (op : Op) (t : Nat) :
    (psync fam cfg rms).hooks.recv o a op t = pure [] := rfl
@[simp] theorem psync_settled (cid r : Id) : (psync fam cfg rms).hooks.settled cid r = [] := rfl
@[simp] theorem psync_outbox : (psync fam cfg rms).hooks.outbox = pure [] := rfl
@[simp] theorem psync_closing (cid : Id) : (psync fam cfg rms).hooks.closing cid = pure [] := rfl
@[simp] theorem psync_retired : (psync fam cfg rms).hooks.retired = pure [] := rfl
@[simp] theorem psync_react : (psync fam cfg rms).hooks.react = pure [] := rfl
@[simp] theorem psync_dial (now : Nat) : (psync fam cfg rms).hooks.dial now = pure [] := rfl
@[simp] theorem psync_established : (psync fam cfg rms).hooks.established = pure [] := rfl

@[simp] theorem refresh_run (cid : Id) (c : Conn) (h : Held F) :
    (Node.refresh (psync fam cfg rms) cid c).run h = (c.setRooms (rms h cid), h) := rfl

end

@[simp] theorem setup_sync (Q : Plain F) (i : Fin Q.n) : Q.setup.sync i = psync Q.fam Q.cfg (Q.rooms i) := rfl

/-! ## Stores only grow -/

/-- The store holds an op under id x. -/
def Named (h : Held F) (x : Id) : Prop := (h.db.ops x).isSome = true

/-- h' holds every op h holds, and every op h' logged that h had not, it
stores. -/
def Ext (h h' : Held F) : Prop :=
  (∀ x o, h.db.ops x = some o → h'.db.ops x = some o) ∧ ∀ o ∈ h'.log, o ∈ h.log ∨ Named h' o.id

theorem Named.ext {h h' : Held F} {x : Id} (e : Ext h h') (hx : Named h x) : Named h' x := by
  unfold Named at *
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 hx
  rw [e.1 x o ho]; rfl

theorem Ext.refl (h : Held F) : Ext h h := ⟨fun _ _ e => e, fun _ ho => Or.inl ho⟩
theorem Ext.trans {h₁ h₂ h₃ : Held F} (a : Ext h₁ h₂) (b : Ext h₂ h₃) : Ext h₁ h₃ :=
  ⟨fun x o e => b.1 x o (a.1 x o e), fun o ho => by
    rcases b.2 o ho with h | h
    · rcases a.2 o h with h | h
      · exact Or.inl h
      · exact Or.inr (h.ext b)
    · exact Or.inr h⟩

/-- A step that only adds to the store, from any store. -/
def Grows {α} (p : HeldM F α) : Prop := ∀ h, Ext h (p.run h).2

theorem Keeps.grows {α} {p : HeldM F α} (hp : Keeps p) : Grows p := fun h => by rw [hp h]; exact Ext.refl h
theorem Grows.pure' {α} (a : α) : Grows (pure a : HeldM F α) := fun h => Ext.refl h
theorem Grows.bind' {α β} {m : HeldM F α} {k : α → HeldM F β} (hm : Grows m) (hk : ∀ a, Grows (k a)) :
    Grows (m >>= k) := fun h => by
  simp only [HeldM.run_bind]; exact (hm h).trans (hk _ _)
theorem Grows.forIn' {α β} (l : List α) (b : β) {f : α → β → HeldM F (ForInStep β)}
    (hf : ∀ a b, Grows (f a b)) : Grows (forIn l b f) := by
  induction l generalizing b with
  | nil => exact Grows.pure' b
  | cons a t ih =>
    intro h
    rw [List.forIn_cons, HeldM.run_bind]
    refine (hf a b h).trans ?_
    cases ((f a b).run h).1 with
    | done b' => exact Ext.refl _
    | yield b' => exact ih b' _
theorem Grows.range' {β} (r : Std.Legacy.Range) (b : β) {f : Nat → β → HeldM F (ForInStep β)}
    (hf : ∀ a b, Grows (f a b)) : Grows (forIn r b f) := by
  intro h; rw [Std.Legacy.Range.forIn_eq_forIn_range']; exact Grows.forIn' _ b hf h
theorem Grows.getOp' (x : Id) : Grows (Store.getOp (F := F) x : HeldM F _) := (Keeps.getOp' x).grows
theorem Grows.getStatus' (x : Id) : Grows (Store.getStatus (F := F) x : HeldM F _) := (Keeps.getStatus' x).grows
theorem Grows.read' {α} (f : Held F → α) : Grows (readH f) := (Keeps.read' f).grows

theorem ingestS_ext (o : Op) (s : DB F) : ∀ x p, s.ops x = some p → (ingestS o s).ops x = some p := by
  intro x p hx
  unfold ingestS
  split
  · exact hx
  · rename_i hn
    show (if x = o.id then some o else s.ops x) = some p
    by_cases e : x = o.id
    · subst e; rw [hn] at hx; cases hx
    · simp [e, hx]

theorem foldl_ingest_ext (ops : List Op) : ∀ (s : DB F) x p, s.ops x = some p →
    (ops.foldl (fun s o => ingestS o s) s).ops x = some p := by
  induction ops with
  | nil => intro s x p h; exact h
  | cons o t ih => intro s x p h; exact ih _ x p (ingestS_ext o s x p h)

theorem foldl_ingest_named (ops : List Op) : ∀ (s : DB F), ∀ o ∈ ops,
    ((ops.foldl (fun s o => ingestS o s) s).ops o.id).isSome = true := by
  induction ops with
  | nil => intro s o ho; cases ho
  | cons p t ih =>
    intro s o ho
    rcases List.mem_cons.1 ho with rfl | ho
    · have : ((ingestS o s).ops o.id).isSome = true := by
        unfold ingestS
        split
        · rename_i q hq; rw [hq]; rfl
        · show ((if o.id = o.id then some o else s.ops o.id)).isSome = true
          simp
      obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 this
      rw [List.foldl_cons, foldl_ingest_ext t _ _ q hq]; rfl
    · exact ih _ o ho

theorem turnH_ext (fam : Family F) (ops : List Op) (h : Held F) : Ext h (turnH fam ops h) := by
  refine ⟨fun x p hx => ?_, fun o ho => ?_⟩
  · simp only [turnH, drainS_ops]
    exact foldl_ingest_ext ops h.db x p hx
  · simp only [turnH, List.mem_append] at ho
    rcases ho with ho | ho
    · exact Or.inl ho
    · right; show (((turnH fam ops h).db.ops o.id).isSome = true)
      simp only [turnH, drainS_ops]
      exact foldl_ingest_named ops _ o ho

theorem Grows.turn' (fam : Family F) (ops : List Op) : Grows (Turn.turn fam ops : HeldM F Unit) := fun h => by
  rw [HeldM.run_turn]; exact turnH_ext fam ops h

/-- Prove `Grows` of a do block from its structure, with these lemmas for
the calls in it. -/
syntax "grows" "[" term,* "]" : tactic

macro_rules
  | `(tactic| grows [$ts,*]) => do
    let mut tac : Lean.TSyntax `tactic ← `(tactic| first | split | intro)
    for t in ts.getElems.reverse do
      tac ← `(tactic| first | with_reducible_and_instances apply $t | $tac:tactic)
    `(tactic| repeat' (concrete_goal; first
      | dsimp only | with_reducible_and_instances apply Grows.bind'
      | with_reducible_and_instances apply Grows.pure' | with_reducible_and_instances apply Grows.forIn'
      | with_reducible_and_instances apply Grows.range'
      | with_reducible_and_instances apply Grows.getOp' | with_reducible_and_instances apply Grows.getStatus'
      | with_reducible_and_instances apply Grows.turn' | with_reducible_and_instances apply Grows.read'
      | $tac:tactic))

/-! ## Every entry point grows the store -/

section
variable (fam : Family F) (cfg : Config) (rms : Held F → Id → List Id)

theorem filed_grows (c : Conn) (ids : List Id) : Grows (c.filed fam cfg ids : HeldM F Step) :=
  (filed_keeps fam cfg c ids).grows

theorem write_grows (n : Node) (ops : List Op) : Grows (n.write (psync fam cfg rms) ops) := by
  unfold Node.write; grows []

theorem put_grows (n : Node) (ops : List Op) (mine : Bool) : Grows (n.put (psync fam cfg rms) ops mine) :=
  write_grows fam cfg rms n _

theorem settle_grows (n : Node) (st : List (Id × Status)) : Grows (n.settle (psync fam cfg rms) st) := by
  unfold Node.settle; grows [put_grows]

theorem fanout_grows (n : Node) (ids : List Id) : Grows (n.fanout (psync fam cfg rms) ids) := by
  unfold Node.fanout; simp only [psync_rooms, Node.refresh]
  grows [settle_grows, filed_grows]

theorem store_grows (n : Node) (ops : List Op) (mine : Bool) : Grows (n.store (psync fam cfg rms) ops mine) := by
  unfold Node.store; simp only [psync_react]
  grows [put_grows, fanout_grows]

theorem apply_grows (n : Node) (cid : Id) (s : Step) (now : Nat) : Grows (n.apply (psync fam cfg rms) cid s now) := by
  unfold Node.apply; simp only [psync_recv]
  grows [settle_grows, store_grows]

theorem seal_grows (n : Node) (out : Acts) : Grows (n.seal (psync fam cfg rms) out) := by
  unfold Node.seal; simp only [psync_sealFor]; grows []

theorem open_grows (n : Node) (cid : Id) (a : ByteArray) (d : Bool) (now : Nat) :
    Grows (n.open (psync fam cfg rms) cid a d now) := by
  unfold Node.open; simp only [psync_rooms]; grows []

theorem finish_grows (n : Node) (out : Acts) (now : Nat) : Grows (n.finish (psync fam cfg rms) out now) := by
  unfold Node.finish Node.follow Node.flush
  simp only [psync_established, psync_outbox, psync_retired, psync_closing, HeldM.pure_bind,
    List.isEmpty_nil, ite_true, List.append_nil, Bool.not_true, Bool.false_eq_true, ite_false]
  grows [seal_grows, open_grows]

theorem onWrite_grows (n : Node) (ops : List Op) (now : Nat) : Grows (n.onWrite (psync fam cfg rms) ops now) := by
  unfold Node.onWrite; grows [store_grows, finish_grows]

theorem connect_grows (n : Node) (cid : Id) (a : ByteArray) (d : Bool) (now : Nat) :
    Grows (n.connect (psync fam cfg rms) cid a d now) := by
  unfold Node.connect; grows [open_grows, finish_grows]

end

section
variable (fam : Family F) (cfg : Config) (rms : Held F → Id → List Id) (hw : WalkLaws (F := F) fam cfg)
include hw

theorem recv_keeps (ix : Index) (c : Conn) (b : ByteArray) (now : Nat) :
    Keeps (Conn.recv fam cfg ix c b now : HeldM F Step) := by
  unfold Conn.recv; keeps [onHold_keeps, onWant_keeps fam cfg hw]

theorem recv_grows (ix : Index) (c : Conn) (b : ByteArray) (now : Nat) :
    Grows (Conn.recv fam cfg ix c b now : HeldM F Step) := (recv_keeps fam cfg hw ix c b now).grows
theorem tick_grows (ix : Index) (c : Conn) (now : Nat) : Grows (c.tick fam cfg ix now : HeldM F Step) :=
  (tick_keeps fam cfg hw ix c now).grows

/-- The same, with the family and settings as a plain node reads them. -/
theorem recv_grows' (ix : Index) (c : Conn) (b : ByteArray) (now : Nat) :
    Grows (Conn.recv (psync fam cfg rms).fam (psync fam cfg rms).cfg ix c b now : HeldM F Step) :=
  recv_grows fam cfg hw ix c b now
theorem tick_grows' (ix : Index) (c : Conn) (now : Nat) :
    Grows (c.tick (psync fam cfg rms).fam (psync fam cfg rms).cfg ix now : HeldM F Step) :=
  tick_grows fam cfg hw ix c now

theorem onSealed_grows (n : Node) (a : ByteArray) (o : Option (Id × ByteArray)) (now : Nat) :
    Grows (n.onSealed (psync fam cfg rms) a o now) := by
  unfold Node.onSealed; simp only [Node.refresh, psync_rooms]
  grows [finish_grows, apply_grows, recv_grows' fam cfg rms hw]

theorem onFrame_grows (n : Node) (a b : ByteArray) (now : Nat) : Grows (n.onFrame (psync fam cfg rms) a b now) := by
  unfold Node.onFrame; simp only [psync_openFrame, psync_recv]
  grows [write_grows, store_grows, finish_grows, onSealed_grows fam cfg rms hw]

theorem onTick_grows (n : Node) (now : Nat) : Grows (n.onTick (psync fam cfg rms) now) := by
  unfold Node.onTick; simp only [psync_dial, Node.refresh, psync_rooms]
  grows [store_grows, finish_grows, apply_grows, tick_grows' fam cfg rms hw]

end

/-! ## In the world: stores only grow -/

section
variable (Q : Plain F)

theorem enter_ext (w : World (Held F) Q.n) (i : Fin Q.n) (t : Nat) (f : Node → HeldM F (Node × Effects))
    (hf : ∀ nd, Grows (f nd)) (j : Fin Q.n) :
    Ext (w.box j) ((w.enter Q.setup i t f).box j) := by
  simp only [World.enter, upd]
  split
  · rename_i e; subst e; exact hf _ _
  · exact Ext.refl _

/-- **No step takes an op out of any store.** -/
theorem step_ext (hw : WalkLaws (F := F) Q.fam Q.cfg) (w : World (Held F) Q.n) (a : Act Q.n) (j : Fin Q.n) :
    Ext (w.box j) ((w.step Q.setup a).box j) := by
  cases a with
  | deliver k t =>
    simp only [World.step]
    split
    · exact Ext.refl _
    · rename_i p _
      split
      · exact Ext.refl _
      · rename_i j' _
        exact enter_ext Q { w with flight := w.flight.eraseIdx k } j' t
          (fun nd => Node.onFrame (Q.setup.sync j') nd p.origin p.bytes t)
          (fun nd => onFrame_grows Q.fam Q.cfg _ hw nd _ _ _) j
  | dup k => simp only [World.step]; split <;> exact Ext.refl _
  | drop k => exact Ext.refl _
  | tick i t => simp only [World.step]; apply enter_ext; intro nd; exact onTick_grows Q.fam Q.cfg _ hw _ _
  | write i ops t =>
    simp only [World.step]
    exact enter_ext Q w i t _ (fun nd => onWrite_grows Q.fam Q.cfg _ nd _ _) j
  | restart i t =>
    simp only [World.step, upd]
    split
    · rename_i e; subst e; exact Ext.refl _
    · exact Ext.refl _
  | connect i j' cid d t =>
    simp only [World.step]; apply enter_ext; intro nd; exact connect_grows Q.fam Q.cfg _ _ _ _ _ _
  | inject i o b t =>
    simp only [World.step]
    exact enter_ext Q w i t _ (fun nd => onFrame_grows Q.fam Q.cfg _ hw nd _ _ _) j

end

/-- **Shared stores only grow,** proven: no step of any node, against any
attacker, takes an op out of a plain node's store (given the walk's
laws, until a3/hostile's `walkN` lands). -/
theorem grows_proof (hw : walk_stmt) : grows_stmt := by
  intro F Q adv w a i r x _ _ hx
  obtain ⟨o, ho, hr⟩ := hx
  exact ⟨o, (step_ext Q (hw F Q.fam Q.cfg) w a i).1 x o ho, hr⟩

/-! ## Indexes and snapshots name stored ops -/

/-- Every item of an index names a stored op. -/
def IxIn (ix : Index) (h : Held F) : Prop := ∀ r it, it ∈ ix.items r → Named h it.2

/-- Every item of every snapshot a connection keeps names a stored op. -/
def SnapsIn (c : Conn) (h : Held F) : Prop := ∀ e ∈ c.snaps, ∀ it ∈ e.2, Named h it.2

/-- **The node invariant:** its index and its connections' snapshots
name only stored ops. -/
def Sub (n : Node) (h : Held F) : Prop := IxIn n.ix h ∧ ∀ p ∈ n.conns, SnapsIn p.2 h

theorem IxIn.ext {ix : Index} {h h' : Held F} (e : Ext h h') (hi : IxIn ix h) : IxIn ix h' :=
  fun r it hit => (hi r it hit).ext e
theorem SnapsIn.ext {c : Conn} {h h' : Held F} (e : Ext h h') (hc : SnapsIn c h) : SnapsIn c h' :=
  fun x hx it hit => (hc x hx it hit).ext e
theorem Sub.ext {n : Node} {h h' : Held F} (e : Ext h h') (hs : Sub n h) : Sub n h' :=
  ⟨hs.1.ext e, fun p hp => (hs.2 p hp).ext e⟩

theorem mem_ins (a : Item) : ∀ (l : List Item) it, it ∈ Engine.Sync.ins a l → it ∈ l ∨ it = a := by
  intro l
  induction l with
  | nil => intro it h; simp [Engine.Sync.ins] at h; exact Or.inr h
  | cons b t ih =>
    intro it h
    simp only [Engine.Sync.ins] at h
    split at h
    · simp only [List.mem_cons] at h
      rcases h with rfl | rfl | h
      · exact Or.inr rfl
      · exact Or.inl (List.mem_cons_self ..)
      · exact Or.inl (List.mem_cons_of_mem _ h)
    · split at h
      · exact Or.inl h
      · simp only [List.mem_cons] at h
        rcases h with rfl | h
        · exact Or.inl (List.mem_cons_self ..)
        · rcases ih it h with h | h
          · exact Or.inl (List.mem_cons_of_mem _ h)
          · exact Or.inr h

theorem find_map_fst {β : Type} (f : Id × β → Id × β) (hf : ∀ p, (f p).1 = p.1) (r : Id) :
    ∀ (l : List (Id × β)), (l.map f).find? (fun p => Decidable.decide (p.1 = r)) =
      (l.find? fun p => Decidable.decide (p.1 = r)).map f := by
  intro l
  induction l with
  | nil => rfl
  | cons p t ih =>
    simp only [List.map_cons, List.find?_cons, hf]
    split <;> simp [ih]

theorem items_def (ix : Index) (r : Id) :
    ix.items r = ((ix.rooms.find? fun p => Decidable.decide (p.1 = r)).map (·.2)).getD [] := by
  unfold Index.items
  cases e : ix.rooms.find? fun p => Decidable.decide (p.1 = r) with
  | none => rfl
  | some p => rfl

/-- **Adding an op to the index adds only it.** -/
theorem items_add (fam : Family F) (ix : Index) (o : Op) (r : Id) (it : Item)
    (h : it ∈ (ix.add fam o).items r) : it ∈ ix.items r ∨ it.2 = o.id := by
  unfold Index.add at h
  split at h
  · exact Or.inl h
  · rename_i c _
    rw [items_def] at h ⊢
    split at h
    · rw [find_map_fst _ (fun p => by split <;> rfl)] at h
      cases e : ix.rooms.find? fun p => Decidable.decide (p.1 = r) with
      | none => rw [e] at h; simp at h
      | some p =>
        rw [e] at h
        simp only [Option.map_some, Option.getD_some] at h ⊢
        split at h
        · rcases mem_ins _ _ _ h with h | h
          · exact Or.inl h
          · exact Or.inr (by rw [h])
        · exact Or.inl h
    · simp only [List.find?_cons] at h
      split at h
      · simp only [Option.map_some, Option.getD_some, List.mem_singleton] at h
        exact Or.inr (by rw [h])
      · exact Or.inl h

/-- What a fold of adds holds came from the start or from the ops. -/
theorem items_foldl (fam : Family F) (ops : List Op) : ∀ (ix : Index) r it,
    it ∈ (ops.foldl (Index.add fam) ix).items r → it ∈ ix.items r ∨ ∃ o ∈ ops, it.2 = o.id := by
  induction ops with
  | nil => intro ix r it h; exact Or.inl h
  | cons o t ih =>
    intro ix r it h
    rcases ih _ r it h with h | ⟨o', ho', e⟩
    · rcases items_add fam ix o r it h with h | e
      · exact Or.inl h
      · exact Or.inr ⟨o, List.mem_cons_self .., e⟩
    · exact Or.inr ⟨o', List.mem_cons_of_mem _ ho', e⟩

/-! ## Connections keep snapshots of what is stored -/

/-- A loop whose turns keep a property of its state and store keeps it. -/
theorem forIn_hoare {α β} (l : List α) (f : α → β → HeldM F (ForInStep β)) (Q : β → Held F → Prop)
    (hf : ∀ a ∈ l, ∀ b h, Q b h → Q ((f a b).run h).1.value ((f a b).run h).2) :
    ∀ b h, Q b h → Q ((forIn l b f).run h).1 ((forIn l b f).run h).2 := by
  induction l with
  | nil => intro b h hb; exact hb
  | cons a t ih =>
    intro b h hb
    rw [List.forIn_cons, HeldM.run_bind]
    have := hf a (List.mem_cons_self ..) b h hb
    cases e : ((f a b).run h).1 with
    | done b' => rw [e] at this; exact this
    | yield b' =>
      rw [e] at this
      exact ih (fun a ha => hf a (List.mem_cons_of_mem _ ha)) b' _ this

section
variable (fam : Family F) (cfg : Config)

theorem SnapsIn.setRooms {c : Conn} {h : Held F} (hc : SnapsIn c h) (rs : List Id) :
    SnapsIn (c.setRooms rs) h := fun e he => hc e ((List.mem_filter.1 he).1)

theorem mem_ite_snaps {p : Prop} [Decidable p] {A B : Conn} {e : (Id × Nat) × List Item}
    (h : e ∈ (if p then A else B).snaps) : e ∈ A.snaps ∨ e ∈ B.snaps := by
  by_cases hp : p
  · simp only [hp, ite_true] at h; exact Or.inl h
  · simp only [hp, ite_false] at h; exact Or.inr h

theorem start_snaps (ix : Index) (c : Conn) (now : Nat) (h : Held F) (hi : IxIn ix h) (hc : SnapsIn c h) :
    SnapsIn (c.start cfg ix now).conn h := by
  unfold Conn.start
  split
  · exact hc
  · intro e he it hit
    simp only [List.mem_map] at he
    obtain ⟨r, _, rfl⟩ := he
    exact hi r it hit

theorem onRbsr_snaps (ix : Index) (c : Conn) (r : Id) (k : Nat) (cs : List Claim) (now : Nat) (h : Held F)
    (hi : IxIn ix h) (hc : SnapsIn c h) : SnapsIn (c.onRbsr cfg ix r k cs now).conn h := by
  have hsnap : ∀ it ∈ (match c.snaps.find? fun p => Decidable.decide (p.1 = (r, k)) with
      | some (_, s) => s
      | none => ix.items r), Named h it.2 := by
    intro it hit
    split at hit
    · rename_i q s e
      exact hc _ (List.mem_of_find?_eq_some e) it hit
    · exact hi r it hit
  have hothers : ∀ e ∈ c.snaps.filter (fun p => !Decidable.decide (p.1.1 = r)), ∀ it ∈ e.2, Named h it.2 :=
    fun e he => hc e ((List.mem_filter.1 he).1)
  unfold Conn.onRbsr
  split
  · exact hc
  · dsimp only
    split
    · exact hothers
    · intro e he it hit
      dsimp only at he
      rcases mem_ite_snaps he with he | he
      · exact hothers e he it hit
      · simp only [List.mem_cons] at he
        rcases he with rfl | he
        · exact hsnap it hit
        · exact hothers e he it hit

theorem finish_snaps (st : Step) : (Conn.finish st).conn.snaps = st.conn.snaps := by
  unfold Conn.finish Conn.report
  by_cases h : st.conn.asked.isEmpty = true <;> simp [h]

theorem onHold_snaps (c : Conn) (r : Id) (ids : List Id) (h : Held F) :
    ((c.onHold fam cfg r ids : HeldM F Step).run h).1.conn.snaps = c.snaps := by
  unfold Conn.onHold
  split
  · rfl
  · simp only [HeldM.run_bind, HeldM.run_pure]

theorem onWant_snaps (hw : WalkLaws (F := F) fam cfg) (c : Conn) (ids : List Id) (h : Held F) :
    ((c.onWant fam cfg ids : HeldM F Step).run h).1.conn.snaps = c.snaps := by
  unfold Conn.onWant
  split
  · rfl
  · simp only [HeldM.run_bind, HeldM.run_pure]
    exact (hw.same _ _).snaps

theorem filed_snaps (c : Conn) (ids : List Id) (h : Held F) :
    ((c.filed fam cfg ids : HeldM F Step).run h).1.conn.snaps = c.snaps := by
  unfold Conn.filed
  simp only [HeldM.run_bind, HeldM.run_pure, finish_snaps]
  apply forIn_inv _ _ (fun st : List (Id × Id) × Conn => st.2.snaps = c.snaps)
  · intro i st h' hs
    obtain ⟨off, c'⟩ := st
    dsimp only at hs ⊢
    split
    · simp only [HeldM.run_bind]
      split
      · split <;> exact hs
      · exact hs
    · exact hs
  · rfl

theorem recv_snaps (hw : WalkLaws (F := F) fam cfg) (ix : Index) (c : Conn) (b : ByteArray) (now : Nat) (h : Held F) (hi : IxIn ix h)
    (hc : SnapsIn c h) : SnapsIn ((Conn.recv fam cfg ix c b now : HeldM F Step).run h).1.conn h := by
  unfold Conn.recv
  split
  · exact hc
  · rename_i o _
    have hc' : SnapsIn ({ c with heard := now } : Conn) h := hc
    dsimp only
    split
    · rename_i f _
      simp only [HeldM.run_pure]
      intro e he; rw [finish_snaps] at he
      split at he
      · exact start_snaps cfg ix ({ c with heard := now, peerFloor := some f } : Conn) now h hi hc e he
      · exact hc e he
    · simp only [HeldM.run_pure]
      intro e he; rw [finish_snaps] at he
      exact onRbsr_snaps cfg ix _ _ _ _ now h hi hc' e he
    · simp only [HeldM.run_bind, HeldM.run_pure]
      intro e he; rw [finish_snaps, onHold_snaps] at he; exact hc e he
    · simp only [HeldM.run_bind, HeldM.run_pure]
      intro e he; rw [finish_snaps, onWant_snaps fam cfg hw] at he; exact hc e he
    · split
      · exact hc
      · simp only [HeldM.run_pure]
        intro e he; rw [finish_snaps] at he; exact hc e he

theorem tick_snaps (hw : WalkLaws (F := F) fam cfg) (ix : Index) (c : Conn) (now : Nat) (h : Held F) (hi : IxIn ix h) (hc : SnapsIn c h) :
    SnapsIn ((c.tick fam cfg ix now : HeldM F Step).run h).1.conn h := by
  unfold Conn.tick
  split
  · exact hc
  · simp only [HeldM.run_bind, HeldM.run_pure]
    have e := hw.same c h
    have hw' : SnapsIn ((c.walk fam cfg : HeldM F (Conn × List (Id × Id))).run h).1.1 h := by
      intro x hx; rw [e.snaps] at hx; exact hc x hx
    intro x hx
    rw [finish_snaps] at hx
    dsimp only at hx
    split at hx
    · exact start_snaps cfg ix _ now h hi hw' x hx
    · exact hw' x hx

end

/-! ## Every entry point keeps the node invariant -/

/-- A loop whose turns keep the store, and a property of its state, run
on that store. -/
theorem forIn_at {α β} (l : List α) (f : α → β → HeldM F (ForInStep β)) (h : Held F) (Q : β → Prop)
    (hk : ∀ a ∈ l, ∀ b, Keeps (f a b)) (hf : ∀ a ∈ l, ∀ b, Q b → Q ((f a b).run h).1.value) :
    ∀ b, Q b → Q ((forIn l b f).run h).1 ∧ ((forIn l b f).run h).2 = h := by
  induction l with
  | nil => intro b hb; exact ⟨hb, rfl⟩
  | cons a t ih =>
    intro b hb
    rw [List.forIn_cons, HeldM.run_bind, hk a (List.mem_cons_self ..) b h]
    have := hf a (List.mem_cons_self ..) b hb
    cases e : ((f a b).run h).1 with
    | done b' => rw [e] at this; exact ⟨this, rfl⟩
    | yield b' =>
      rw [e] at this
      exact ih (fun a ha => hk a (List.mem_cons_of_mem _ ha)) (fun a ha => hf a (List.mem_cons_of_mem _ ha)) b' this

section
variable (fam : Family F) (cfg : Config) (rms : Held F → Id → List Id)

/-- What the write's second loop adds to the index names stored ops. -/
theorem items_addStep (fam : Family F) (db : DB F) (r : Id) : ∀ (l : List Op) (st : Index × List Id) it,
    it ∈ (l.foldl (addStep fam db) st).1.items r → it ∈ st.1.items r ∨ (db.ops it.2).isSome = true := by
  intro l
  induction l with
  | nil => intro st it h; exact Or.inl h
  | cons o t ih =>
    intro st it h
    rcases ih _ it h with h | h
    · unfold addStep at h
      split at h
      · rename_i hs
        rcases items_add fam st.1 o r it h with h | e
        · exact Or.inl h
        · exact Or.inr (by rw [e]; exact hs)
      · exact Or.inl h
    · exact Or.inr h

/-- **A write keeps the node invariant:** its index grows only by ops it
stored. -/
theorem write_sub (n : Node) (ops : List Op) (h : Held F) (hs : Sub n h) :
    Sub ((n.write (psync fam cfg rms) ops).run h).1.1 ((n.write (psync fam cfg rms) ops).run h).2 := by
  rw [write_run]
  dsimp only
  split
  · exact hs
  · have e := turnH_ext fam (List.foldl (absentStep h.db) [] ops).reverse h
    refine ⟨fun r it hit => ?_, fun p hp => (hs.2 p hp).ext e⟩
    rcases items_addStep _ _ r _ _ it hit with hit | hit
    · exact (hs.1 r it hit).ext e
    · exact hit

end

end Engine.World
