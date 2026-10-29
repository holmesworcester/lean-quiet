/-
What the two-node world does, proven of the running sync code (`Node`,
`Conn`) on held data:

- `stream_delivers`: an op written at a node whose session to the other
  node is up reaches the other node in one exchange, an offer, a want,
  and the op, when both sides' rooms on the session include its room.
  The frames each entry point emits are computed exactly.

The proofs run the code: each entry point, run on a `Held` store, is
rewritten lemma by lemma (`HeldM.run_bind` and the loop lemmas) until
its result is a term. Most of what a node does on the way leaves its
store as it is (`Reads`), and the `keeps` tactic proves that from a do
block's structure.

The world's family writes nothing (`Setup.sync`), so no session is
managed by it and none is purged; `stream_delivers` assumes so of both
nodes (`managed = []`), as `Node.connect` leaves them.
-/
import engine.wire.World
import engine.wire.LaneLaws
import ops.sync.ServeLaws
import Std.Data.HashSet.Lemmas

namespace Engine.Sync
variable {F : Type}

theorem byteArray_lawfulBEq : LawfulBEq ByteArray where
  eq_of_beq {a b} h := ByteArray.ext (eq_of_beq (show a.data == b.data from h))
  rfl {a} := show a.data == a.data from beq_self_eq_true a.data

attribute [local instance] byteArray_lawfulBEq

theorem remember_bounded (cap : Nat) (known : Std.HashSet Id) (i : Id) :
    (remember cap known i).size ≤ cap := by
  unfold remember
  split
  · simp
  · dsimp only
    split
    · assumption
    · simp [Std.HashSet.size_insert]; omega

theorem remember_fits (cap : Nat) (known : Std.HashSet Id) (i : Id)
    (hc : (known.insert i).size ≤ cap) : remember cap known i = known.insert i := by
  have hp : 0 < (known.insert i).size := by
    have hm : i ∈ (known.insert i).toList := by simp
    have := List.length_pos_of_mem hm
    simpa using this
  simp [remember, show cap ≠ 0 by omega, hc]

theorem admit_one (cap : Nat) (asked : Std.HashSet Id) (i : Id) (hi : i ∉ asked)
    (hc : (asked.insert i).size ≤ cap) : admitAsks cap asked [i] = [i] := by
  have hp : 0 < cap - asked.size := by simp [Std.HashSet.size_insert, hi] at hc; omega
  have he : (([i].filter fun x => !asked.contains x).eraseDups) = [i] := by simp [hi]; rfl
  unfold admitAsks
  rw [he]
  exact List.take_of_length_le (by simp; omega)

/-! ## Running on held data -/

@[simp] theorem HeldM.run_bind {α β} (m : HeldM F α) (k : α → HeldM F β) (h : Held F) :
    (m >>= k).run h = (k (m.run h).1).run (m.run h).2 := rfl
@[simp] theorem HeldM.run_pure {α} (a : α) (h : Held F) : (pure a : HeldM F α).run h = (a, h) := rfl
@[simp] theorem HeldM.pure_bind {α β} (a : α) (k : α → HeldM F β) : (pure a >>= k) = k a := rfl
@[simp] theorem HeldM.run_getOp (x : Id) (h : Held F) :
    (Store.getOp (F := F) x : HeldM F _).run h = (h.db.ops x, h) := rfl
@[simp] theorem HeldM.run_getStatus (x : Id) (h : Held F) :
    (Store.getStatus (F := F) x : HeldM F _).run h = (h.db.status x, h) := rfl

/-- The held store after a write turn of these ops. -/
def turnH (fam : Family F) (ops : List Op) (h : Held F) : Held F :=
  let s := ops.foldl (fun s o => ingestS o s) h.db
  { log := h.log ++ ops, db := drainS fam (budget (h.log ++ ops) s) s }

@[simp] theorem HeldM.run_turn (fam : Family F) (ops : List Op) (h : Held F) :
    (Turn.turn fam ops : HeldM F Unit).run h = ((), turnH fam ops h) := rfl

/-- A write turn of an op the store lacks stores it. -/
theorem turnH_one (fam : Family F) (o : Op) (h : Held F) (hn : h.db.ops o.id = none) :
    (turnH fam [o] h).db.ops o.id = some o := by
  simp [turnH, drainS_ops, ingestS, hn, DB.putOp, DB.push]

theorem Acts.append_def (a b : Acts) : a ++ b = ⟨a.send ++ b.send, a.drop ++ b.drop, a.serve ++ b.serve⟩ := rfl
@[simp] theorem Acts.empty_append (a : Acts) : ({} : Acts) ++ a = a := rfl
@[simp] theorem Acts.append_empty (a : Acts) : a ++ ({} : Acts) = a := by
  cases a; simp [Acts.append_def]

/-! ## Loops -/

/-- A loop whose every turn keeps the store keeps it. -/
theorem forIn_keeps {α β} (l : List α) (f : α → β → HeldM F (ForInStep β)) (h : Held F)
    (hf : ∀ a ∈ l, ∀ b, ((f a b).run h).2 = h) (b : β) : ((forIn l b f).run h).2 = h := by
  induction l generalizing b with
  | nil => rfl
  | cons a t ih =>
    rw [List.forIn_cons, HeldM.run_bind, hf a (List.mem_cons_self ..)]
    cases ((f a b).run h).1 with
    | done b => rfl
    | yield b => exact ih (fun a ha => hf a (List.mem_cons_of_mem _ ha)) b

/-- A loop whose every turn yields its state back, and keeps the store. -/
theorem forIn_fixed {α β} (l : List α) (f : α → β → HeldM F (ForInStep β)) (h : Held F) (b : β)
    (hf : ∀ a ∈ l, (f a b).run h = (.yield b, h)) : (forIn l b f).run h = (b, h) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.forIn_cons, HeldM.run_bind, hf a (List.mem_cons_self ..)]
    exact ih (fun a ha => hf a (List.mem_cons_of_mem _ ha))

/-- A loop whose every turn is a pure update of its state. -/
theorem forIn_yield {α β} (l : List α) (f : α → β → HeldM F (ForInStep β)) (g : α → β → β)
    (h : Held F) (hf : ∀ a ∈ l, ∀ b, (f a b).run h = (.yield (g a b), h)) (b : β) :
    (forIn l b f).run h = (l.foldl (fun b a => g a b) b, h) := by
  induction l generalizing b with
  | nil => rfl
  | cons a t ih =>
    rw [List.forIn_cons, HeldM.run_bind, hf a (List.mem_cons_self ..)]
    exact ih (fun a ha => hf a (List.mem_cons_of_mem _ ha)) _

/-! ## Steps that keep the store -/

/-- A step that leaves the store as it is, from any store. -/
def Reads {α} (p : HeldM F α) : Prop := ∀ h, (p.run h).2 = h

theorem Reads.pure' {α} (a : α) : Reads (pure a : HeldM F α) := fun _ => rfl
theorem Reads.bind' {α β} {m : HeldM F α} {k : α → HeldM F β} (hm : Reads m) (hk : ∀ a, Reads (k a)) :
    Reads (m >>= k) := by
  intro h; simp only [HeldM.run_bind]; rw [hk, hm]
theorem Reads.forIn' {α β} (l : List α) (b : β) {f : α → β → HeldM F (ForInStep β)}
    (hf : ∀ a b, Reads (f a b)) : Reads (forIn l b f) :=
  fun h => forIn_keeps l f h (fun a _ b => hf a b h) b
theorem Reads.getOp' (x : Id) : Reads (Store.getOp (F := F) x : HeldM F _) := fun _ => rfl
theorem Reads.getStatus' (x : Id) : Reads (Store.getStatus (F := F) x : HeldM F _) := fun _ => rfl

/-- Prove `Reads` of a do block from its structure, with these `Reads`
lemmas for the calls in it. -/
syntax "keeps" "[" term,* "]" : tactic

macro_rules
  | `(tactic| keeps [$ts,*]) => do
    let mut tac : Lean.TSyntax `tactic ← `(tactic| first | split | intro)
    for t in ts.getElems.reverse do
      tac ← `(tactic| first | with_reducible_and_instances apply $t | $tac:tactic)
    `(tactic| repeat' (first
      | dsimp only | with_reducible_and_instances apply Reads.bind'
      | with_reducible_and_instances apply Reads.pure' | with_reducible_and_instances apply Reads.forIn'
      | with_reducible_and_instances apply Reads.getOp' | with_reducible_and_instances apply Reads.getStatus'
      | $tac:tactic))

theorem filed_reads (fam : Family F) (cfg : Config) (c : Conn) (ids : List Id) :
    Reads (c.filed fam cfg ids : HeldM F Step) := by
  unfold Conn.filed; keeps []

theorem holdsIn_reads (fam : Family F) (r i : Id) : Reads (holdsIn fam r i : HeldM F Bool) := by
  unfold holdsIn; keeps []

theorem onHold_reads (fam : Family F) (c : Conn) (cfg : Config) (r : Id) (ids : List Id) :
    Reads (c.onHold fam cfg r ids : HeldM F Step) := by
  unfold Conn.onHold; keeps [holdsIn_reads]

theorem closureOps_reads (fam : Family F) (r : Id) (fuel : Nat) : ∀ (todo seen : List Id),
    Reads (closureOps fam r fuel todo seen : HeldM F (List Op)) := by
  induction fuel with
  | zero => intro todo seen h; rw [closureOps]; rfl
  | succ n ih =>
    intro todo
    induction todo with
    | nil => intro seen h; rw [closureOps_nil]; rfl
    | cons y rest ihr =>
      intro seen h
      rw [closureOps]
      split
      · exact ihr seen h
      · simp only [HeldM.run_bind, HeldM.run_getOp]
        cases h.db.ops y with
        | none => exact ih _ _ h
        | some o =>
          dsimp only
          split
          · simp only [HeldM.run_bind, HeldM.run_pure]; exact ih _ _ h
          · exact ih _ _ h

theorem give_reads (fam : Family F) (cfg : Config) :
    ∀ (l : List (Id × Id)) (c : Conn), Reads (c.give fam cfg l : HeldM F Step)
  | [], _ => Reads.pure' _
  | (r, x) :: rest, c => by
    unfold Conn.give
    split
    · exact give_reads fam cfg rest c
    · exact Reads.bind' (closureOps_reads fam r _ _ _) fun _ =>
        Reads.bind' (give_reads fam cfg rest _) fun _ => Reads.pure' _

theorem filedGive_reads (fam : Family F) (cfg : Config) (c : Conn) (ids : List Id) :
    Reads (c.filedGive fam cfg ids : HeldM F Step) :=
  Reads.bind' (give_reads fam cfg _ c) fun g =>
    Reads.bind' (filed_reads fam cfg g.conn ids) fun _ => Reads.pure' _

/-- A connection with no notices gives none: its store step is `filed`. -/
@[simp] theorem filedGive_quiet (fam : Family F) (cfg : Config) (c : Conn) (ids : List Id) (h : Held F)
    (hn : c.notices = []) :
    (c.filedGive fam cfg ids : HeldM F Step).run h = (c.filed fam cfg ids : HeldM F Step).run h := by
  simp [Conn.filedGive, Conn.notify, hn, Conn.give]

/-! ## The world's hooks -/

section
variable (S : Setup F) (s : Who)

@[simp] theorem sync_fam : (S.sync s).fam = S.fam := rfl
@[simp] theorem sync_cfg : (S.sync s).cfg = S.cfg := rfl
@[simp] theorem sync_openFrame : (S.sync s).hooks.openFrame = plainOpen := rfl
@[simp] theorem sync_sealFor (cid : Id) (b : ByteArray) :
    (S.sync s).hooks.sealFor cid b = pure (some (Codec.encode (cid, b))) := rfl
@[simp] theorem sync_rooms (cid : Id) : (S.sync s).hooks.rooms cid = pure ((S.rooms s cid).map .sync) := rfl
@[simp] theorem sync_recv (o : Option Id) (a : ByteArray) (op : Op) (t : Nat) :
    (S.sync s).hooks.recv o a op t = pure [] := rfl
@[simp] theorem sync_onGiven (cid : Id) (v : Id) : (S.sync s).hooks.onGiven cid v = [] := rfl
@[simp] theorem sync_outbox : (S.sync s).hooks.outbox = pure [] := rfl
@[simp] theorem sync_closing (cid : Id) : (S.sync s).hooks.closing cid = pure [] := rfl
@[simp] theorem sync_retired : (S.sync s).hooks.retired = pure [] := rfl
@[simp] theorem sync_react : (S.sync s).hooks.react = pure [] := rfl
@[simp] theorem sync_dial (now : Nat) : (S.sync s).hooks.dial now = pure [] := rfl
@[simp] theorem sync_established : (S.sync s).hooks.established = pure [] := rfl

/-! ## The entry points, piece by piece -/

/-- The world's rooms are synced, with no notices. -/
@[simp] theorem refresh_run (cid : Id) (c : Conn) (h : Held F) :
    (Node.refresh (S.sync s) cid c).run h = ({ c.setRooms (S.rooms s cid) with notices := [] }, h) := by
  simp [Node.refresh, Conn.carry]

theorem write_nil (x : Sync F (HeldM F)) (n : Node) (h : Held F) : (n.write x []).run h = ((n, []), h) := by
  simp [Node.write]

/-- A write of one op the store lacks: one write turn, and the index
grows by it. -/
theorem write_one (x : Sync F (HeldM F)) (n : Node) (o : Op) (h : Held F) (hn : h.db.ops o.id = none) :
    (n.write x [o]).run h =
      (({ n with ix := n.ix.add x.fam o, fresh := n.fresh ++ [o.id] }, [o.id]), turnH x.fam [o] h) := by
  simp [Node.write, hn, turnH_one _ _ _ hn]

/-- The world's family records no notices. -/
@[simp] theorem recordGiven_run (n : Node) (st : List (Id × Id)) (h : Held F) :
    (Node.recordGiven (S.sync s) n st).run h = (n, h) := by
  have : (st.flatMap fun (p : Id × Id) => match p with
      | (cid, v) => (S.sync s).hooks.onGiven cid v) = [] := by
    induction st with
    | nil => rfl
    | cons p t ih => obtain ⟨_, _⟩ := p; simp at ih ⊢
  simp only [Node.recordGiven, Node.put, this, intake]; simp [write_nil]

@[simp] theorem store_nil (n : Node) (mine : Bool) (h : Held F) :
    (n.store (S.sync s) [] mine).run h = ((n, {}), h) := by
  simp [Node.store, Node.put, intake, write_nil]

/-- The world's family answers nothing: storing is a put, then a fanout. -/
theorem store_run (n : Node) (ops : List Op) (mine : Bool) (h : Held F) :
    (n.store (S.sync s) ops mine).run h =
      let p := (n.put (S.sync s) ops mine).run h
      if p.1.2.isEmpty then ((p.1.1, {}), p.2) else (p.1.1.fanout (S.sync s) p.1.2).run p.2 := by
  simp only [Node.store, HeldM.run_bind]
  split
  · rfl
  · simp [Std.Legacy.Range.forIn_eq_forIn_range', List.range']

/-- What a node seals of one session's payloads: their bundles, each one
frame to the session's address; nothing without an address. -/
theorem seal_one (n : Node) (cid : Id) (ps : List ByteArray) (h : Held F) :
    (n.seal (S.sync s) { send := ps.map fun p => (.conn cid, p) }).run h =
      (((n.addr? cid).map fun a => (bundles S.cfg.bundle ps).map fun g => (a, plainFrame cid g)).getD [],
        h) := by
  cases ps with
  | nil => cases n.addr? cid <;> simp [Node.seal, bundles]
  | cons p ps =>
    simp only [Node.seal, HeldM.run_bind, List.map_cons, List.forIn_cons]
    simp only [HeldM.run_pure, has, Bool.not_false, ite_true]
    rw [forIn_fixed (ps.map fun p => (Route.conn cid, p)) _ _ _
      (fun a ha => by obtain ⟨_, _, rfl⟩ := List.mem_map.1 ha; simp [has])]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.forIn_cons, HeldM.run_bind]
    cases n.addr? cid with
    | none => simp
    | some a =>
      simp only [HeldM.run_bind]
      rw [forIn_yield _ _ (fun g acc => (a, plainFrame cid g) :: acc) _
        (fun g _ b => by simp [plainFrame])]
      simp [List.filterMap_map, Function.comp_def]

/-- One payload of a session, sealed: one frame to its address. -/
@[simp] theorem seal_single (n : Node) (cid : Id) (b : ByteArray) (h : Held F) :
    (n.seal (S.sync s) { send := [(.conn cid, b)] }).run h =
      (((n.addr? cid).map fun a => [(a, plainFrame cid [b])]).getD [], h) := by
  have e := seal_one S s n cid [b] h
  simp only [List.map_cons, List.map_nil] at e
  rw [e]
  cases n.addr? cid <;> simp [bundles]

/-- Sealing reads a node's addresses only, which heating keeps. -/
@[simp] theorem seal_heat (n : Node) (ids : List Id) (now : Nat) (out : Acts) :
    (n.heat (S.sync s) ids now).seal (S.sync s) out = n.seal (S.sync s) out := rfl

@[simp] theorem seal_sends (n : Node) (cid : Id) (ops : List Op) (h : Held F) :
    (n.seal (S.sync s) (sends cid ops)).run h =
      (((n.addr? cid).map fun a =>
        (bundles S.cfg.bundle (ops.map Op.bytes)).map fun g => (a, plainFrame cid g)).getD [], h) := by
  have := seal_one S s n cid (ops.map Op.bytes) h
  simp only [List.map_map, Function.comp_def] at this
  exact this

theorem seal_reads (n : Node) (out : Acts) : Reads (n.seal (S.sync s) out) := by
  simp only [Node.seal, sync_sealFor, HeldM.pure_bind]; keeps []

theorem finish_reads (n : Node) (out : Acts) (now : Nat) : Reads (n.finish (S.sync s) out now) := by
  simp only [Node.finish, Node.sent, Node.endSession, Effects.purge, List.foldl_nil, Node.follow, Node.flush, sync_established, sync_outbox, sync_retired,
    sync_closing, HeldM.pure_bind, List.isEmpty_nil, ite_true, List.forIn_nil, List.append_nil,
    Bool.not_true, Bool.false_eq_true, ite_false]
  keeps [seal_reads]

/-- Sealing nothing sends nothing. -/
@[simp] theorem seal_nil (n : Node) (h : Held F) :
    (n.seal (S.sync s) { send := [] }).run h = ([], h) := by
  simp [Node.seal]

/-- Sealing reads only what is to be sent. -/
theorem seal_empty (n : Node) (out : Acts) (h : Held F) (h0 : out.send = []) :
    (n.seal (S.sync s) out).run h = ([], h) := by
  obtain ⟨sd, dr, sv⟩ := out
  simp only at h0
  subst h0
  simp [Node.seal]

/-- An entry point's end, with no managed sessions: seal each lane, and
report. -/
theorem finish_run (n : Node) (out : Acts) (now : Nat) (h : Held F) (hm : n.managed = []) :
    (n.finish (S.sync s) out now).run h =
      (({ n.sent { out with send := out.send ++ out.serve } now with fresh := [], purged := [] },
        { send := ((n.seal (S.sync s) out).run h).1 ++ ((n.seal (S.sync s) { send := out.serve }).run h).1, drop := out.drop, stored := n.fresh, purged := n.purged,
          serve := ((n.seal (S.sync s) { send := out.serve }).run h).1.length }), h) := by
  have hk := finish_reads S s n out now h
  simp only [Node.finish, Node.sent, Node.endSession, Effects.purge, List.foldl_nil, Node.follow, Node.flush, hm, sync_established, sync_outbox, sync_retired,
    sync_closing, HeldM.pure_bind, List.isEmpty_nil, ite_true, List.forIn_nil, List.append_nil,
    Bool.not_true, Bool.false_eq_true, ite_false, HeldM.run_bind, HeldM.run_pure,
    Acts.append_empty] at hk ⊢
  rw [forIn_fixed _ _ _ _ (by intros; rfl)] at hk ⊢
  rw [hk, seal_reads S s n out h]

theorem fanout_reads (n : Node) (ids : List Id) : Reads (n.fanout (S.sync s) ids) := by
  have h1 := filedGive_reads (F := F) S.fam S.cfg
  have h2 : ∀ (n : Node) st, Reads (Node.recordGiven (S.sync s) n st) := fun n st h => by simp
  simp only [Node.fanout, sync_rooms, Node.refresh, HeldM.pure_bind, sync_fam, sync_cfg]
  keeps [h1, h2]

/-- A connection step that takes nothing keeps the store. -/
theorem apply_reads (n : Node) (cid : Id) (st : Step) (now : Nat) (ht : st.take = []) :
    Reads (n.apply (S.sync s) cid st now) := by
  intro h
  unfold Node.apply
  split
  · rfl
  · simp [ht]

/-- Serving a session's queue keeps the store: it only reads. -/
theorem serveOwed_reads (n : Node) (cid : Id) (now : Nat) : Reads (n.serveOwed (S.sync s) cid now) := by
  intro h
  unfold Node.serveOwed
  split
  · rfl
  · split
    · rfl
    · simp only [HeldM.run_bind, refresh_run, sync_rooms, HeldM.run_pure]
      exact (serveOwed_run _ _ _ _ _ h).2.2

/-- Storing an op this store lacks: one write turn of it, then a fanout
that keeps the store. -/
theorem store_one (n : Node) (o : Op) (mine : Bool) (h : Held F) (hn : h.db.ops o.id = none)
    (hi : intake S.fam mine [o] = [o]) :
    ((n.store (S.sync s) [o] mine).run h).2 = turnH S.fam [o] h := by
  rw [store_run]
  simp only [Node.put, sync_fam, hi, write_one _ _ _ _ hn]
  simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false]
  exact fanout_reads S s _ _ _

/-- A connection step that takes one shared op the store lacks stores it. -/
theorem apply_takes (n : Node) (cid : Id) (st : Step) (now : Nat) (o : Op) (h : Held F)
    (hd : st.drop = false) (ht : st.take = [o]) (hn : h.db.ops o.id = none)
    (hsh : S.fam.shared o = true) :
    ((n.apply (S.sync s) cid st now).run h).2 = turnH S.fam [o] h := by
  have hi : intake S.fam false [o] = [o] := by simp [intake, hsh]
  simp [Node.apply, hd, ht, store_one S s _ o false h hn hi]

end

/-! ## Frames and messages -/

theorem chunks_one (cfg : Config) (i : Id) (mk : List Id → Msg) (hmax : 0 < cfg.maxIds) :
    chunks cfg [i] mk = [(mk [i]).op] := by
  obtain ⟨k, hk⟩ : ∃ k, cfg.maxIds = k + 1 := ⟨cfg.maxIds - 1, by omega⟩
  simp [chunks, pieceIds, hk]

theorem holdsOf_one (cfg : Config) (r i : Id) (hmax : 0 < cfg.maxIds) :
    holdsOf cfg [(r, i)] = [(Msg.hold r [i]).op] := by
  simp [holdsOf, Engine.ins, has, chunks_one _ _ _ hmax]

@[simp] theorem bundles_one (max : Nat) (b : ByteArray) : bundles max [b] = [[b]] := rfl

theorem mem_bundles (max : Nat) (l : List ByteArray) : ∀ g ∈ bundles max l, ∀ x ∈ g, x ∈ l := by
  induction l with
  | nil => simp [bundles]
  | cons b rest ih =>
    intro g hg x hx
    unfold bundles at hg
    split at hg
    · simp at hg; subst hg; simp at hx; simp [hx]
    · rename_i g' gs he
      have ih' : ∀ g ∈ g' :: gs, ∀ x ∈ g, x ∈ rest := he ▸ ih
      split at hg
      · simp only [List.mem_cons] at hg
        rcases hg with rfl | hg
        · simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · simp
          · exact List.mem_cons_of_mem _ (ih' g' (by simp) x hx)
        · exact List.mem_cons_of_mem _ (ih' g (by simp [hg]) x hx)
      · simp only [List.mem_cons] at hg
        rcases hg with rfl | rfl | hg
        · simp at hx; simp [hx]
        · exact List.mem_cons_of_mem _ (ih' g (by simp) x hx)
        · exact List.mem_cons_of_mem _ (ih' g (by simp [hg]) x hx)

/-- The first bundle starts with the first payload. -/
theorem bundles_head (max : Nat) (b : ByteArray) (rest : List ByteArray) :
    ∃ g gs, bundles max (b :: rest) = (b :: g) :: gs ∧ ∀ x ∈ g, x ∈ rest := by
  have hm := mem_bundles max rest
  unfold bundles
  split
  · exact ⟨[], [], rfl, by simp⟩
  · rename_i g gs he
    split
    · exact ⟨g, gs, rfl, fun x hx => hm g (by rw [he]; simp) x hx⟩
    · exact ⟨[], g :: gs, rfl, by simp⟩

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

@[simp] theorem ofOp_hold (r : Id) (l : List Id) : Msg.ofOp (Msg.hold r l).op = some (.hold r l) := by
  simp [Msg.ofOp, Msg.op, kRbsr, kHave, Codec.decode_encode]

@[simp] theorem ofOp_want (l : List Id) : Msg.ofOp (Msg.want l).op = some (.want l) := by
  simp [Msg.ofOp, Msg.op, kRbsr, kHave, kWant]

theorem ofOp_data {o : Op} (h : isWire o.kind = false) : Msg.ofOp o = none := by
  simp [isWire, Bool.or_eq_false_iff] at h
  simp [Msg.ofOp, h.1.1, h.1.2, h.2]

theorem has_of_mem {l : List Id} {x : Id} (h : x ∈ l) : has l x = true := (Engine.has_iff l x).2 h

/-! ## What a connection does with each message -/

theorem recv_hold (fam : Family F) (cfg : Config) (ix : Index) (c : Conn) (r : Id) (l : List Id) (now : Nat)
    (h : Held F) :
    (Conn.recv fam cfg ix c (Msg.hold r l).op.bytes now : HeldM F Step).run h =
      ((({ c with heard := now }.onHold fam cfg r l : HeldM F Step).run h).1, h) := by
  simp only [Conn.recv, Op.decode_bytes, ofOp_hold]
  exact Prod.ext rfl (onHold_reads _ _ _ _ _ h)

theorem onHold_take (fam : Family F) (c : Conn) (cfg : Config) (r : Id) (l : List Id) (h : Held F) :
    ((c.onHold fam cfg r l : HeldM F Step).run h).1.take = [] := by
  unfold Conn.onHold; split
  · simp
  · split <;> simp

/-- A data op of the connection's rooms is taken. -/
theorem recv_data (fam : Family F) (cfg : Config) (ix : Index) (c : Conn) (o : Op) (now : Nat)
    (h : Held F) (hw : isWire o.kind = false) (hsh : c.shows fam o = true) :
    (Conn.recv fam cfg ix c o.bytes now : HeldM F Step).run h =
      (((Step.mk { c with heard := now, asked := c.asked.erase o.id, askTime := c.askTime.erase o.id, known := remember cfg.maxKnown c.known o.id }
        [] [o] [] false)), h) := by
  have hsh' : Conn.shows fam { c with heard := now } o = true := hsh
  simp [Conn.recv, Op.decode_bytes, ofOp_data hw, hw, hsh']

/-! ## The stream, one entry point at a time -/

section
variable (S : Setup F) (s : Who)

/-- **A write is offered on the session at once:** a node with one
session, which has neither offered op o nor heard that its peer holds
it, writes o, a shared op of a room the session carries. It stores o,
and sends exactly one frame, to the session's address, offering o. -/
theorem write_offers (n : Node) (cid : Id) (c : Conn) (o : Op) (r : Id) (a : ByteArray) (h : Held F)
    (t : Nat) (hc : n.conns = [(cid, c)]) (hm : n.managed = []) (ha : n.addr? cid = some a)
    (hn : h.db.ops o.id = none) (hk : o.id ∉ c.known) (ho : o.id ∉ c.offered)
    (hr : S.fam.room o = some r) (hs : r ∈ S.rooms s cid) (hmax : 0 < S.cfg.maxIds) :
    let p := (n.onWrite (S.sync s) [o] t).run h
    (∃ c', p.1.1.conns = [(cid, c')] ∧ c'.known = c.known ∧ c'.asked = c.asked ∧ c'.owed = c.owed ∧ c'.owing = c.owing) ∧
      p.1.1.managed = [] ∧ p.1.1.addrs = n.addrs ∧
      p.1.2.send = [(a, plainFrame cid [(Msg.hold r [o.id]).op.bytes])] ∧ p.2 = turnH S.fam [o] h ∧ p.1.1.ix = n.ix.add S.fam o := by
  have hs' := has_of_mem hs
  simp only [Node.addr?] at ha
  simp [Node.onWrite, store_run, Node.put, intake, write_one _ _ _ _ hn, Node.fanout, hc, Conn.filed,
    turnH_one _ _ _ hn, hk, ho, Conn.setRooms, Conn.shows, hr, hs', finish_run, hm, Node.heat, Node.sent, sends,
    holdsOf_one _ _ _ hmax, Node.addr?, ha]

/-- **An offer of an op the node lacks is answered with a want,** on the
session, to the address the offer came from; the store is unchanged. -/
theorem hold_wants (n : Node) (cid : Id) (c : Conn) (src : ByteArray) (r i : Id) (h : Held F) (t : Nat)
    (hc : n.conns = [(cid, c)]) (hm : n.managed = []) (hn : h.db.ops i = none) (hq : i ∉ c.asked)
    (hq0 : c.owed = [])
    (hs : r ∈ S.rooms s cid) (hmax : 0 < S.cfg.maxIds)
    (hasked : (c.asked.insert i).size ≤ S.cfg.maxKnown) :
    let p := (n.onFrame (S.sync s) src (plainFrame cid [(Msg.hold r [i]).op.bytes]) t).run h
    (∃ c', p.1.1.conns = [(cid, c')] ∧ c'.known = remember S.cfg.maxKnown c.known i ∧ c'.asked = c.asked.insert i) ∧ p.1.1.managed = [] ∧
      p.1.2.send = [(src, plainFrame cid [(Msg.want [i]).op.bytes])] ∧ p.2 = h := by
  have hs' := has_of_mem hs
  simp [Node.onFrame, Node.onSealed, plainOpen, Codec.decode_encode, Node.conn?, Node.setAddr, hc,
    Conn.recv, Op.decode_bytes, Conn.onHold, holdsIn, hs', hq, hn, Node.apply, finish_run, hm,
    split_one, Node.serveOwed, hq0, Node.sent,
    admit_one _ _ _ hq hasked, remember_bounded,
    chunks_one _ _ _ hmax, Node.addr?, Conn.setRooms, sends, hasked, show ¬S.cfg.maxIds < 1 by omega]

@[simp] theorem budget_world (a : Option ByteArray) (b : Nat) : (a.bind (S.sync s).room).getD b = b := by
  cases a <;> rfl

theorem serveOwed_eq_run (fam : Family F) (cfg : Config) (c : Conn) (budget : Nat) (first : List Id) (h : Held F) :
    (c.serveOwed fam cfg budget first : HeldM F _).run h =
      let urgent := ((fetch (c.shows fam) (c.hotOf first)).trace h.db.ops).1
      let t := ((serve (c.shows fam) budget (c.owedAfter first)).trace h.db.ops).1
      ((c.served cfg (c.hotOf first ++ (c.owedAfter first).take ((c.owedAfter first).length - t.2.length)) t.2
        (urgent ++ t.1), urgent, t.1), h) :=
  serveOwed_eq fam cfg c budget first h

/-- The fresh ids a step serves first, when the queue holds one id. -/
theorem hot_single (first : List Id) (a : Id) :
    (first.filter (({} : Std.HashSet Id).insert a).contains).eraseDups = if a ∈ first then [a] else [] := by
  have e : first.filter (({} : Std.HashSet Id).insert a).contains = first.filter (· == a) := by
    congr 1; funext b
    simp only [Std.HashSet.contains_insert, Std.HashSet.contains_empty, Bool.or_false]
    exact Bool.eq_iff_iff.2 ⟨fun h => beq_iff_eq.2 (beq_iff_eq.1 h).symm, fun h => beq_iff_eq.2 (beq_iff_eq.1 h).symm⟩
  rw [e, List.filter_beq]
  by_cases h : a ∈ first
  · obtain ⟨k, hk⟩ : ∃ k, List.count a first = k + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos (List.count_pos_iff.2 h)).symm⟩
    rw [hk, if_pos h, List.replicate_succ, List.eraseDups_cons]
    simp [List.filter_replicate]
  · rw [List.count_eq_zero.2 h, if_neg h]; rfl

/-- Serving a queue of one wanted op: its send, urgent if this node
wrote it within `hotMs`, in the serve lane otherwise. -/
theorem serveOwed_one (n : Node) (cid : Id) (c : Conn) (o : Op) (h : Held F) (now : Nat)
    (hc : n.conn? cid = some c) (hq : c.owed = [o.id]) (hw : c.owing = ({} : Std.HashSet Id).insert o.id)
    (hg : h.db.ops o.id = some o) (hsh : (c.setRooms (S.rooms s cid)).shows S.fam o = true) (hb : 0 < S.cfg.burst) :
    ∃ n', (n.serveOwed (S.sync s) cid now).run h = ((n', if o.id ∈ n.hotIds (S.sync s) now
        then sends cid [o] else { serve := [(.conn cid, o.bytes)] }), h) ∧
      n'.managed = n.managed ∧ n'.addrs = n.addrs := by
  have hsh' : (c.setRooms (S.rooms s cid)).shows S.fam o = true := hsh
  unfold Node.serveOwed
  rw [hc]
  simp only [hq, List.isEmpty_cons, Bool.false_eq_true, ite_false, HeldM.run_bind, refresh_run,
    HeldM.run_pure]
  rw [serveOwed_eq_run]
  simp only [Conn.hotOf, Conn.owedAfter, Conn.setRooms, hw, hq, hot_single, sync_cfg, sync_fam, budget_world]
  by_cases hh : o.id ∈ n.hotIds (S.sync s) now
  · simp only [hh, ite_true, List.isEmpty_cons, Bool.false_eq_true, ite_false]
    refine ⟨_, Prod.ext (Prod.ext rfl ?_) rfl, rfl, rfl⟩
    have h1 : (fetch (({ c.setRooms (S.rooms s cid) with notices := [] } : Conn).shows S.fam) [o.id]).trace h.db.ops = ([o], [o.id]) := by
      rw [fetch_cons]; simp [hg, show (({ c.setRooms (S.rooms s cid) with notices := [] } : Conn).shows S.fam o) = true from hsh', fetch, Read.trace]
    have h2 : List.filter (fun i => !([o.id] : List Id).contains i) [o.id] = [] := by simp
    simp only [Conn.setRooms, hq, hw, Conn.shows] at h1
    simp only [Conn.shows]
    simp only [h1, h2, serve_nil, sends, List.append_nil]
    rfl
  · simp only [hh, ite_false, List.isEmpty_nil, ite_true]
    refine ⟨_, Prod.ext (Prod.ext rfl ?_) rfl, rfl, rfl⟩
    have h1 : (serve (({ c.setRooms (S.rooms s cid) with notices := [] } : Conn).shows S.fam) S.cfg.burst [o.id]).trace h.db.ops = (([o], []), [o.id]) := by
      rw [serve_cons _ _ _ _ _ hb]; simp only [hg, show (({ c.setRooms (S.rooms s cid) with notices := [] } : Conn).shows S.fam o) = true from hsh', ite_true]; split <;> rfl
    simp only [Conn.setRooms, hq, hw, Conn.shows] at h1
    simp only [Conn.shows]
    simp only [h1, fetch, Read.trace, List.nil_append]
    try rfl

/-- `serveOwed_one` on a node whose only session is cid, by parts. -/
theorem serveOwed_world (n : Node) (cid : Id) (c1 : Conn) (A : List (Id × ByteArray)) (o : Op) (h : Held F)
    (now : Nat) (hq : c1.owed = [o.id]) (hw : c1.owing = ({} : Std.HashSet Id).insert o.id)
    (hg : h.db.ops o.id = some o) (hsh : (c1.setRooms (S.rooms s cid)).shows S.fam o = true)
    (hb : 0 < S.cfg.burst) :
    let N : Node := { n with conns := [(cid, c1)], addrs := A }
    ((N.serveOwed (S.sync s) cid now).run h).1.2 = (if o.id ∈ n.hotIds (S.sync s) now then sends cid [o]
        else { serve := [(.conn cid, o.bytes)] }) ∧
      ((N.serveOwed (S.sync s) cid now).run h).1.1.managed = n.managed ∧
      ((N.serveOwed (S.sync s) cid now).run h).1.1.addrs = A ∧
      ((N.serveOwed (S.sync s) cid now).run h).2 = h := by
  intro N
  obtain ⟨n', e, hm, ha⟩ := serveOwed_one S s N cid c1 o h now (by simp [N, Node.conn?]) hq hw hg hsh hb
  rw [e]
  exact ⟨rfl, hm, ha, rfl⟩

/-- **A fresh write the peer wants goes urgent:** when the session's
queue holds an op this node wrote within `hotMs`, the step serves it in
the urgent lane, ahead of any backlog (`urgent_ahead` on the socket). -/
theorem fresh_served (n : Node) (cid : Id) (c1 : Conn) (A : List (Id × ByteArray)) (o : Op) (h : Held F)
    (now t : Nat) (hq : c1.owed = [o.id]) (hw : c1.owing = ({} : Std.HashSet Id).insert o.id)
    (hg : h.db.ops o.id = some o) (hsh : (c1.setRooms (S.rooms s cid)).shows S.fam o = true)
    (hb : 0 < S.cfg.burst) (hh : (o.id, t) ∈ n.hot) (ht : now ≤ t + S.cfg.hotMs) :
    let N : Node := { n with conns := [(cid, c1)], addrs := A }
    ((N.serveOwed (S.sync s) cid now).run h).1.2 = sends cid [o] := by
  intro N
  rw [(serveOwed_world S s n cid c1 A o h now hq hw hg hsh hb).1, if_pos (hot_ids (S.sync s) n o.id t now hh ht)]

/-- **A want for a stored op the peer may see is answered with the op in
the same step,** when the session owes nothing else: the op joins the
queue and is served at once (urgent if this node just wrote it, in the
serve lane otherwise), and its frame is the step's only send. -/
theorem want_sends (n : Node) (cid : Id) (c : Conn) (src : ByteArray) (o : Op) (r : Id) (h : Held F)
    (t : Nat) (hc : n.conns = [(cid, c)]) (hm : n.managed = []) (hn : h.db.ops o.id = some o)
    (hr : S.fam.room o = some r) (hs : r ∈ S.rooms s cid) (hmax : 0 < S.cfg.maxIds)
    (hauth : authorize n.ix (c.setRooms (S.rooms s cid)) [o.id] = [o.id])
    (hq0 : c.owed = []) (hw0 : c.owing = {}) (hk : 0 < S.cfg.maxKnown)
    (hb : 0 < S.cfg.burst) :
    let p := (n.onFrame (S.sync s) src (plainFrame cid [(Msg.want [o.id]).op.bytes]) t).run h
    ∃ holds : List ByteArray, (∀ b ∈ holds, ∃ r l, b = (Msg.hold r l).op.bytes) ∧
      p.1.2.send = (bundles S.cfg.bundle (o.bytes :: holds)).map fun g => (src, plainFrame cid g) := by
  have hs' := has_of_mem hs
  have hsh : (c.setRooms (S.rooms s cid)).shows S.fam o = true := by
    simp [Conn.shows, Conn.setRooms, hr, hs']
  have hauth' : authorize n.ix ({ c.setRooms (S.rooms s cid) with notices := [], heard := t } : Conn) [o.id] = [o.id] := hauth
  have hrwant : (Conn.recv S.fam S.cfg n.ix { c.setRooms (S.rooms s cid) with notices := [] }
      (Msg.want [o.id]).op.bytes t : HeldM F Step).run h =
      ({ conn := { c.setRooms (S.rooms s cid) with notices := [], heard := t, owed := [o.id], owing := c.owing.insert o.id } }, h) := by
    simp only [Conn.recv, Op.decode_bytes, ofOp_want, HeldM.run_bind, HeldM.run_pure, Conn.onWant]
    rw [if_neg (by simp; omega), hauth']
    simp [Conn.setRooms, hw0, hq0, show [o.id].eraseDups = [o.id] from rfl, List.take_of_length_le (show [o.id].length ≤ S.cfg.maxKnown by simp; omega)]
  simp only [Node.onFrame, Node.onSealed, plainFrame_head, plainFrame_body, sync_openFrame,
    plainOpen, Codec.decode_encode, HeldM.pure_bind, Node.conn?, Node.setAddr, hc,
    List.find?_cons, decide_true, List.forIn_cons, Option.map_some, HeldM.run_bind,
    HeldM.run_pure, refresh_run, sync_fam, sync_cfg, hrwant]
  obtain ⟨e1, e2, e3, e4⟩ := serveOwed_world S s n cid
    { c.setRooms (S.rooms s cid) with notices := [], heard := t, owed := [o.id], owing := c.owing.insert o.id }
    ((cid, src) :: List.filter (fun p => !Decidable.decide (p.fst = cid)) n.addrs) o h t
    (by simp) (by simp [hw0]) hn (by simp [Conn.shows, Conn.setRooms, hr, hs']) hb
  simp only [Conn.setRooms] at e1 e2 e3 e4
  simp [Node.apply, Conn.setRooms]
  rw [e1, e4, finish_run _ _ _ _ _ _ (by rw [e2, hm])]
  refine ⟨[], by simp, ?_⟩
  simp only [split, List.filter_nil, List.map_nil]
  split
  · simp [sends, Node.addr?, e3]
  · rw [seal_empty _ _ _ _ _ rfl]
    simp [Node.addr?, e3]

/-- **A frame that brings a new op of the session's rooms stores it,**
whatever offers follow it in the frame. -/
theorem op_taken (n : Node) (cid : Id) (c : Conn) (src : ByteArray) (o : Op) (r : Id)
    (more : List ByteArray) (h : Held F) (t : Nat)
    (hc : n.conns = [(cid, c)]) (hn : h.db.ops o.id = none) (hw : isWire o.kind = false)
    (hr : S.fam.room o = some r) (hs : r ∈ S.rooms s cid)
    (hmore : ∀ b ∈ more, ∃ r l, b = (Msg.hold r l).op.bytes) :
    ((n.onFrame (S.sync s) src (plainFrame cid (o.bytes :: more)) t).run h).2 = turnH S.fam [o] h := by
  have hs' := has_of_mem hs
  simp only [Node.onFrame, Node.onSealed, plainFrame_head, plainFrame_body, sync_openFrame, plainOpen,
    Codec.decode_encode, HeldM.pure_bind, Node.conn?, Node.setAddr, hc, List.find?_cons, decide_true,
    List.forIn_cons, Option.map_some, HeldM.run_bind, HeldM.run_pure, refresh_run, sync_fam, sync_cfg]
  rw [finish_reads, serveOwed_reads, recv_data _ _ _ _ _ _ _ hw (by simp [Conn.shows, Conn.setRooms, hr, hs'])]
  dsimp only
  rw [forIn_keeps more _ _ ?_, apply_takes S s _ _ _ _ o h (by simp) (by simp) hn (by simp [Family.shared, hr])]
  intro b hb st
  obtain ⟨r', l, rfl⟩ := hmore b hb
  split
  · simp only [HeldM.run_bind, HeldM.run_pure, refresh_run, recv_hold]
    apply apply_reads
    rw [onHold_take]
  · rfl

/-- Opening a session at a node with no managed sessions: the session's
connection says hello, and the store is unchanged. -/
theorem connect_run (n : Node) (cid : Id) (a : ByteArray) (dialer : Bool) (now : Nat) (h : Held F)
    (hm : n.managed = []) :
    let p := (n.connect (S.sync s) cid a dialer now).run h
    p.1.1.conns = (cid, (Conn.open dialer (S.rooms s cid) n.floor now).conn) :: (n.close cid).conns ∧
      p.1.1.managed = [] ∧ p.1.1.addr? cid = some a ∧ p.2 = h := by
  simp [Node.connect, Node.open, finish_run, Node.sent, sends, Node.close, Node.setAddr, Node.addr?, hm, Conn.open]
  apply Eq.trans (List.map_congr_left (g := id) ?_) (List.map_id _)
  intro p hp
  have hn := (List.mem_filter.mp hp).2
  simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hn
  simp [Ne.symm hn]


end

/-! ## The world -/

@[simp] theorem Who.other_other (s : Who) : s.other.other = s := by cases s <;> rfl

@[simp] theorem World.run_peer_self (w : World F) (s : Who) (net : List Frame) (t : Nat)
    (f : Node → HeldM F (Node × Effects)) :
    (w.run s net t f).peer s =
      { w.peer s with node := ((f (w.peer s).node).run (w.peer s).held).1.1,
                      held := ((f (w.peer s).node).run (w.peer s).held).2 } := by
  cases s <;> rfl
@[simp] theorem World.run_peer_other (w : World F) (s : Who) (net : List Frame) (t : Nat)
    (f : Node → HeldM F (Node × Effects)) : (w.run s net t f).peer s.other = w.peer s.other := by
  cases s <;> rfl
@[simp] theorem World.run_peer_other' (w : World F) (s : Who) (net : List Frame) (t : Nat)
    (f : Node → HeldM F (Node × Effects)) : (w.run s.other net t f).peer s = w.peer s := by
  cases s <;> rfl
@[simp] theorem World.run_net (w : World F) (s : Who) (net : List Frame) (t : Nat)
    (f : Node → HeldM F (Node × Effects)) :
    (w.run s net t f).net = net ++ inFlight ((f (w.peer s).node).run (w.peer s).held).1.2 := rfl
@[simp] theorem World.run_now (w : World F) (s : Who) (net : List Frame) (t : Nat)
    (f : Node → HeldM F (Node × Effects)) : (w.run s net t f).now = t := by
  cases s <;> rfl

/-- The run of `stream_delivers`, step by step. -/
theorem stream_frames (S : Setup F) (w : World F) (s : Who) (cid : Id) (ca cb : Conn) (o : Op)
    (r : Id) (t1 t2 t3 t4 : Nat)
    (hca : (w.peer s).node.conns = [(cid, ca)]) (hcb : (w.peer s.other).node.conns = [(cid, cb)])
    (hma : (w.peer s).node.managed = []) (hmb : (w.peer s.other).node.managed = [])
    (haddr : (w.peer s).node.addr? cid = some (w.peer s.other).addr)
    (hr : S.fam.room o = some r) (hra : r ∈ S.rooms s cid) (hrb : r ∈ S.rooms s.other cid)
    (hw : isWire o.kind = false)
    (hna : (w.peer s).held.db.ops o.id = none) (hnb : (w.peer s.other).held.db.ops o.id = none)
    (hk : o.id ∉ ca.known) (ho : o.id ∉ ca.offered) (hq : o.id ∉ cb.asked)
    (hqa : ca.owed = []) (hwa : ca.owing = {}) (hqb : cb.owed = []) (hb : 0 < S.cfg.burst) (hkn : 0 < S.cfg.maxKnown)
    (hcap : (cb.asked.insert o.id).size ≤ S.cfg.maxKnown)
    (hix : authorize ((w.peer s).node.ix.add S.fam o)
      (ca.setRooms (S.rooms s cid)) [o.id] = [o.id])
    (hmax : 0 < S.cfg.maxIds) :
    let A := (w.peer s).addr
    let B := (w.peer s.other).addr
    let f1 : Frame := ⟨B, plainFrame cid [(Msg.hold r [o.id]).op.bytes]⟩
    let f2 : Frame := ⟨A, plainFrame cid [(Msg.want [o.id]).op.bytes]⟩
    let w1 := w.write S s [o] t1
    let w2 := w1.deliver S s.other w.net [] f1 t2
    let w3 := w2.deliver S s w.net [] f2 t3
    w1.net = w.net ++ [f1] ∧ w2.net = w.net ++ [f2] ∧
    ∃ more rest, w3.net = w.net ++ ⟨B, plainFrame cid (o.bytes :: more)⟩ :: rest ∧
      ((w3.deliver S s.other w.net rest ⟨B, plainFrame cid (o.bytes :: more)⟩ t4).peer s.other).held.db.ops
        o.id = some o := by
  intro A B f1 f2 w1 w2 w3
  -- s writes o, and offers it on the session.
  obtain ⟨⟨ca1, hca1, hka1, hqa1, hoa1, hwa1⟩, hma1, -, hs1, hh1, hix1⟩ :=
    write_offers S s _ cid ca o r B _ t1 hca hma haddr hna hk ho hr hra hmax
  have e1 : w1.net = w.net ++ [f1] := by simp [w1, World.write, inFlight, hs1, f1]
  -- The other node wants it.
  obtain ⟨⟨cb1, hcb1, hkb1, hqb1⟩, -, hs2, hh2⟩ :=
    hold_wants S s.other (w.peer s.other).node cid cb A r o.id (w.peer s.other).held t2 hcb hmb hnb hq hqb hrb hmax hcap
  have e2 : w2.net = w.net ++ [f2] := by
    simp [w2, World.deliver, inFlight, f1, f2, w1, World.write, hs2, A]
  -- s sends it, first in its first frame.
  have ha2 : (w2.peer s).node = ((Node.onWrite (S.sync s) (w.peer s).node [o] t1).run (w.peer s).held).1.1 ∧
      (w2.peer s).held = turnH S.fam [o] (w.peer s).held ∧ (w2.peer s).addr = A ∧
      (w2.peer s.other).addr = B := by
    simp [w2, World.deliver, w1, World.write, hh1, A, B]
  obtain ⟨holds, hholds, hs3⟩ := want_sends S s _ cid ca1 B o r (turnH S.fam [o] (w.peer s).held) t3
    hca1 hma1 (turnH_one S.fam o _ hna) hr hra hmax
    (by simpa only [hix1, authorize, Conn.setRooms] using hix) (by rw [hoa1, hqa]) (by rw [hwa1, hwa]) hkn hb
  obtain ⟨g, gs, hg, hgm⟩ := bundles_head S.cfg.bundle o.bytes holds
  refine ⟨e1, e2, g, gs.map fun g => ⟨B, plainFrame cid g⟩, ?_, ?_⟩
  · simp [w3, World.deliver, ha2, inFlight, f2, hs3, hg]
  -- The other node takes it.
  · have hb3 : w3.peer s.other = w2.peer s.other := by simp [w3, World.deliver]
    have hb2 : (w2.peer s.other).node = ((Node.onFrame (S.sync s.other) (w.peer s.other).node A
        (plainFrame cid [(Msg.hold r [o.id]).op.bytes]) t2).run (w.peer s.other).held).1.1 ∧
        (w2.peer s.other).held = (w.peer s.other).held := by
      simp [w2, World.deliver, hh2, A, f1, w1, World.write]
    have := op_taken S s.other _ cid cb1 (w3.peer s).addr o r g (w.peer s.other).held t4 hcb1 hnb hw hr
      hrb (fun b hb => hholds b (hgm b hb))
    simp only [World.deliver, World.run_peer_self, hb3, hb2.1, hb2.2, Who.other_other]
    rw [this]
    exact turnH_one _ _ _ hnb

/-- **New ops reach connected members.** Nodes s and s.other hold
session cid open (and no other), and s's frames on it go to the other
node. Op o is a data op of room r, which both sides' rooms on the
session include. Neither node holds o, s's connection has neither
offered it nor heard that the other holds it, and the other's has not
asked for it; neither owes the other anything (their queues are empty).
Then s's write of o sends one frame, an offer (`w1`);
delivered to the other node, it is answered with one frame, a want
(`w2`); delivered to s, that is answered with frames whose first begins
with o (`w3`); and delivered to the other node, that one leaves it
holding o (`w4`). Frames already in flight stay in flight. -/
theorem stream_delivers (S : Setup F) (w : World F) (s : Who) (cid : Id) (ca cb : Conn) (o : Op)
    (r : Id) (t1 t2 t3 t4 : Nat)
    (hca : (w.peer s).node.conns = [(cid, ca)]) (hcb : (w.peer s.other).node.conns = [(cid, cb)])
    (hma : (w.peer s).node.managed = []) (hmb : (w.peer s.other).node.managed = [])
    (haddr : (w.peer s).node.addr? cid = some (w.peer s.other).addr)
    (hr : S.fam.room o = some r) (hra : r ∈ S.rooms s cid) (hrb : r ∈ S.rooms s.other cid)
    (hw : isWire o.kind = false)
    (hna : (w.peer s).held.db.ops o.id = none) (hnb : (w.peer s.other).held.db.ops o.id = none)
    (hk : o.id ∉ ca.known) (ho : o.id ∉ ca.offered) (hq : o.id ∉ cb.asked)
    (hqa : ca.owed = []) (hwa : ca.owing = {}) (hqb : cb.owed = []) (hb : 0 < S.cfg.burst) (hkn : 0 < S.cfg.maxKnown)
    (hcap : (cb.asked.insert o.id).size ≤ S.cfg.maxKnown)
    (hix : authorize ((w.peer s).node.ix.add S.fam o)
      (ca.setRooms (S.rooms s cid)) [o.id] = [o.id])
    (hmax : 0 < S.cfg.maxIds) :
    ∃ w1 w2 w3 w4 more rest,
      w1 = w.write S s [o] t1 ∧
      w1.net = w.net ++ [⟨(w.peer s.other).addr, plainFrame cid [(Msg.hold r [o.id]).op.bytes]⟩] ∧
      w2 = w1.deliver S s.other w.net [] ⟨(w.peer s.other).addr, plainFrame cid [(Msg.hold r [o.id]).op.bytes]⟩ t2 ∧
      w2.net = w.net ++ [⟨(w.peer s).addr, plainFrame cid [(Msg.want [o.id]).op.bytes]⟩] ∧
      w3 = w2.deliver S s w.net [] ⟨(w.peer s).addr, plainFrame cid [(Msg.want [o.id]).op.bytes]⟩ t3 ∧
      w3.net = w.net ++ ⟨(w.peer s.other).addr, plainFrame cid (o.bytes :: more)⟩ :: rest ∧
      w4 = w3.deliver S s.other w.net rest ⟨(w.peer s.other).addr, plainFrame cid (o.bytes :: more)⟩ t4 ∧
      (w4.peer s.other).held.db.ops o.id = some o := by
  obtain ⟨e1, e2, more, rest, e3, hb⟩ :=
    stream_frames S w s cid ca cb o r t1 t2 t3 t4 hca hcb hma hmb haddr hr hra hrb hw hna hnb hk ho hq hqa hwa hqb hb hkn hcap hix hmax
  exact ⟨_, _, _, _, more, rest, rfl, e1, rfl, e2, rfl, e3, rfl, hb⟩

/-- The exchange of `stream_delivers` is a run of the world: a write,
then three deliveries, each of a frame in flight to the node at its
address. -/
theorem stream_delivers_steps (S : Setup F) (w : World F) (s : Who) (cid : Id) (ca cb : Conn) (o : Op)
    (r : Id) (t1 t2 t3 t4 : Nat)
    (hca : (w.peer s).node.conns = [(cid, ca)]) (hcb : (w.peer s.other).node.conns = [(cid, cb)])
    (hma : (w.peer s).node.managed = []) (hmb : (w.peer s.other).node.managed = [])
    (haddr : (w.peer s).node.addr? cid = some (w.peer s.other).addr)
    (hr : S.fam.room o = some r) (hra : r ∈ S.rooms s cid) (hrb : r ∈ S.rooms s.other cid)
    (hw : isWire o.kind = false)
    (hna : (w.peer s).held.db.ops o.id = none) (hnb : (w.peer s.other).held.db.ops o.id = none)
    (hk : o.id ∉ ca.known) (ho : o.id ∉ ca.offered) (hq : o.id ∉ cb.asked)
    (hqa : ca.owed = []) (hwa : ca.owing = {}) (hqb : cb.owed = []) (hb : 0 < S.cfg.burst) (hkn : 0 < S.cfg.maxKnown)
    (hcap : (cb.asked.insert o.id).size ≤ S.cfg.maxKnown)
    (hix : authorize ((w.peer s).node.ix.add S.fam o)
      (ca.setRooms (S.rooms s cid)) [o.id] = [o.id])
    (hmax : 0 < S.cfg.maxIds) (h1 : w.now ≤ t1) (h2 : t1 ≤ t2) (h3 : t2 ≤ t3) (h4 : t3 ≤ t4) :
    ∃ w', World.Steps S w w' ∧ (w'.peer s.other).held.db.ops o.id = some o := by
  obtain ⟨_, _, _, _, more, rest, rfl, e1, rfl, e2, rfl, e3, rfl, hb⟩ :=
    stream_delivers S w s cid ca cb o r t1 t2 t3 t4 hca hcb hma hmb haddr hr hra hrb hw hna hnb hk ho hq hqa hwa hqb hb hkn hcap hix hmax
  refine ⟨_, .step (.write s [o] h1) (.step (.deliver s.other (e1.trans (by simp)) ?_ (by simpa [World.write]))
    (.step (.deliver s (e2.trans (by simp)) ?_ (by simpa [World.deliver]))
      (.step (.deliver s.other e3 ?_ (by simpa [World.deliver])) (.refl _)))), hb⟩
  · simp [World.write]
  · simp [World.deliver, World.write]
  · simp [World.deliver, World.write]

/-- A family of one room: every op is shared in it, and valid. -/
def oneRoom (r : Id) : Family Unit :=
  { validate := fun _ _ => some (), keys := fun _ => [], scope := fun _ => .shared r }

/-- Two nodes with nothing stored and nothing in flight. -/
def World.empty (fam : Family F) : World F :=
  { a := Peer.empty fam 0 ⟨#[0]⟩, b := Peer.empty fam 0 ⟨#[1]⟩ }

/-- A session opened at node s, which has no managed sessions. -/
theorem World.connect_peer (S : Setup F) (w : World F) (s : Who) (cid : Id) (dialer : Bool) (t : Nat)
    (hm : (w.peer s).node.managed = []) :
    let w' := w.connect S s cid dialer t
    (w'.peer s).node.conns =
        (cid, (Conn.open dialer (S.rooms s cid) (w.peer s).node.floor t).conn) :: ((w.peer s).node.close cid).conns ∧
      (w'.peer s).node.managed = [] ∧ (w'.peer s).node.addr? cid = some (w.peer s.other).addr ∧
      (w'.peer s).held = (w.peer s).held ∧ w'.peer s.other = w.peer s.other := by
  obtain ⟨h1, h2, h3, h4⟩ := connect_run S s (w.peer s).node cid (w.peer s.other).addr dialer t (w.peer s).held hm
  simp only [World.connect, World.run_peer_self, World.run_peer_other, and_true]
  exact ⟨h1, h2, h3, h4⟩

/-- **`stream_delivers` is not vacuous.** From two empty nodes, open a
session at each end (`Node.connect`, as the pair harness does), then
run the stream: the other node holds the op written. -/
theorem stream_delivers_runs (r cid : Id) :
    ∃ w, World.Steps ⟨oneRoom r, {}, fun _ _ => [r]⟩ (World.empty (oneRoom r)) w ∧
      (w.peer .b).held.db.ops (Op.make 1 [] .empty).id = some (Op.make 1 [] .empty) := by
  let S : Setup Unit := ⟨oneRoom r, {}, fun _ _ => [r]⟩
  let o := Op.make 1 [] .empty
  show ∃ w, World.Steps S (World.empty S.fam) w ∧ (w.peer .b).held.db.ops o.id = some o
  let w0 := World.empty S.fam
  let w1 := w0.connect S .a cid true 0
  let w2 := w1.connect S .b cid false 0
  obtain ⟨hca, hma, haa, hha, hb1⟩ := World.connect_peer S w0 .a cid true 0 rfl
  have eb : w1.peer .b = w0.peer .b := hb1
  obtain ⟨hcb, hmb, -, hhb, ha2⟩ := World.connect_peer S w1 .b cid false 0 (by rw [eb]; rfl)
  have ea : w2.peer .a = w1.peer .a := ha2
  have hca' : (w2.peer .a).node.conns = [(cid, (Conn.open true [r] 0 0).conn)] := by rw [ea]; exact hca
  have hcb' : (w2.peer .b).node.conns = [(cid, (Conn.open false [r] 0 0).conn)] := by
    rw [hcb, eb]; rfl
  have hma' : (w2.peer .a).node.managed = [] := by rw [ea]; exact hma
  have haa' : (w2.peer .a).node.addr? cid = some (w2.peer .b).addr := by
    rw [ea, haa]; show some (w0.peer .b).addr = some (w2.peer .b).addr
    rw [← eb]; rfl
  have hna : (w2.peer .a).held.db.ops o.id = none := by rw [ea, hha]; rfl
  have hnb : (w2.peer .b).held.db.ops o.id = none := by rw [hhb, eb]; rfl
  obtain ⟨w, hs, hw⟩ := stream_delivers_steps S w2 .a cid _ _ o r 0 0 0 0 hca' hcb' hma' hmb haa'
    rfl (by simp [S]) (by simp [S]) (by decide) hna hnb
    (by simp [Conn.open]) (by simp [Conn.open]) (by simp [Conn.open])
    rfl rfl rfl (by simp [S]) (by simp [S])
    (by simp [Conn.open, S, Std.HashSet.size_insert])
    (by simp [authorize, w2, w1, w0, World.connect, World.run, World.set, World.peer, Peer.empty,
      World.empty, Node.boot, Index.ofOps, Index.add, Index.items, Conn.setRooms, S, oneRoom,
      Family.room, o, Node.connect, Node.open, finish_run, Node.close, Node.setAddr, Conn.open, Who.other, Room.syncs, Node.sent])
    (by simp [S])
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
  exact ⟨w, .step (.connect .a cid true (Nat.le_refl _)) (.step (.connect .b cid false (Nat.le_refl _)) hs), hw⟩

/-! ## The stream, on every session

`write_offers` above is one session's offer, computed exactly. Here a
write of any ops at a node with any sessions: every new op is offered on
every session that may show it (`stream_offered`). The lemmas follow the
code's loops: the write's (`writeAbsent`), the stream's (`filedStep`),
the fanout's (`fanoutStep`) and the seal's (`cidsStep`, `sealStep`).
`ByteArray`'s `==` is equality (`byteArray_lawfulBEq`, local here): the
write compares ids with it, and the connection's sets hash them. -/

/-- A write's first loop: the ops not stored, each id once, newest first. -/
def writeAbsent (db : DB F) (acc : List Op) (o : Op) : List Op :=
  if !acc.any (·.id == o.id) then (if (db.ops o.id).isNone then o :: acc else acc) else acc

theorem absent_sub (db : DB F) (L acc : List Op) : ∀ x ∈ L.foldl (writeAbsent db) acc, x ∈ acc ∨ x ∈ L := by
  induction L generalizing acc with
  | nil => intro x hx; exact Or.inl hx
  | cons y L ih =>
    intro x hx
    rcases ih _ x hx with h | h
    · unfold writeAbsent at h
      split at h
      · split at h
        · rcases List.mem_cons.1 h with rfl | h
          · exact Or.inr (List.mem_cons_self ..)
          · exact Or.inl h
        · exact Or.inl h
      · exact Or.inl h
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem absent_mem (db : DB F) (o : Op) (hn : db.ops o.id = none) (L acc : List Op)
    (hu : ∀ x ∈ acc ++ L, x.id = o.id → x = o) (ho : o ∈ acc ∨ o ∈ L) : o ∈ L.foldl (writeAbsent db) acc := by
  induction L generalizing acc with
  | nil => simpa using ho
  | cons y L ih =>
    simp only [List.foldl_cons]
    apply ih
    · intro x hx hxo
      rcases List.mem_append.1 hx with hx | hx
      · unfold writeAbsent at hx
        split at hx
        · split at hx
          · rcases List.mem_cons.1 hx with rfl | hx
            · exact hu x (by simp) hxo
            · exact hu x (by simp [hx]) hxo
          · exact hu x (by simp [hx]) hxo
        · exact hu x (by simp [hx]) hxo
      · exact hu x (by simp [hx]) hxo
    · rcases ho with ho | ho
      · left; unfold writeAbsent; split
        · split
          · exact List.mem_cons_of_mem _ ho
          · exact ho
        · exact ho
      · rcases List.mem_cons.1 ho with rfl | ho
        · left; unfold writeAbsent
          by_cases ha : acc.any (·.id == o.id) = true
          · obtain ⟨x, hx, hxo⟩ := List.any_eq_true.1 ha
            have := hu x (by simp [hx]) (eq_of_beq hxo)
            subst this
            simp [ha, hx]
          · simp [ha, hn]
        · right; exact ho


theorem ingest_get (o : Op) (L : List Op) (s : DB F) (hu : ∀ x ∈ L, x.id = o.id → x = o)
    (h : s.ops o.id = some o ∨ (s.ops o.id = none ∧ o ∈ L)) :
    (L.foldl (fun s o => ingestS o s) s).ops o.id = some o := by
  induction L generalizing s with
  | nil => simpa using h
  | cons y L ih =>
    simp only [List.foldl_cons]
    apply ih _ (fun x hx => hu x (List.mem_cons_of_mem _ hx))
    by_cases hy : y.id = o.id
    · have := hu y (List.mem_cons_self ..) hy; subst this
      left
      rcases h with h | ⟨h, _⟩ <;> simp [ingestS, h, DB.putOp, DB.push]
    · rcases h with h | ⟨h, ho⟩
      · left; unfold ingestS; split
        · exact h
        · simp [DB.putOp, DB.push, Ne.symm hy, h]
      · right
        refine ⟨?_, ?_⟩
        · unfold ingestS; split
          · exact h
          · simp [DB.putOp, DB.push, Ne.symm hy, h]
        · rcases List.mem_cons.1 ho with rfl | ho
          · exact absurd rfl hy
          · exact ho

theorem stored_ids_mem (fam : Family F) (db : DB F) (o : Op) (ho : (db.ops o.id).isSome = true) (L : List Op)
    (ix : Index) (acc : List Id) (hL : o ∈ L ∨ o.id ∈ acc) :
    o.id ∈ (L.foldl (fun (b : Index × List Id) a =>
      if (db.ops a.id).isSome then (b.1.add fam a, a.id :: b.2) else b) (ix, acc)).2 := by
  induction L generalizing ix acc with
  | nil => simpa using hL
  | cons y L ih =>
    simp only [List.foldl_cons]
    split
    · apply ih
      rcases hL with hL | hL
      · rcases List.mem_cons.1 hL with rfl | hL
        · exact Or.inr (List.mem_cons_self ..)
        · exact Or.inl hL
      · exact Or.inr (List.mem_cons_of_mem _ hL)
    · rename_i hy
      apply ih
      rcases hL with hL | hL
      · rcases List.mem_cons.1 hL with rfl | hL
        · exact absurd ho hy
        · exact Or.inl hL
      · exact Or.inr hL

theorem write_mem (x : Sync F (HeldM F)) (n : Node) (ops : List Op) (o : Op) (h : Held F)
    (ho : o ∈ ops) (hn : h.db.ops o.id = none) (hu : ∀ y ∈ ops, y.id = o.id → y = o) :
    let p := (n.write x ops).run h
    o.id ∈ p.1.2 ∧ p.2.db.ops o.id = some o ∧ p.1.1.conns = n.conns ∧ p.1.1.addrs = n.addrs ∧
      p.1.1.managed = n.managed := by
  simp only [Node.write, HeldM.run_bind]
  rw [forIn_yield ops _ (fun o acc => writeAbsent h.db acc o) h (fun y _ acc => by
    simp only [writeAbsent]; split
    · simp only [HeldM.run_bind, HeldM.run_getOp]
      by_cases hc : (h.db.ops y.id).isNone = true <;> simp [hc]
    · rfl)]
  have hA := absent_mem h.db o hn ops [] (by simpa using hu) (Or.inr ho)
  have hne : (List.foldl (fun acc o => writeAbsent h.db acc o) [] ops).isEmpty = false := by
    cases hl : List.foldl (fun acc o => writeAbsent h.db acc o) [] ops with
    | nil => rw [hl] at hA; cases hA
    | cons _ _ => rfl
  simp only [hne, Bool.false_eq_true, ite_false, HeldM.run_bind, HeldM.run_turn]
  have hA' : o ∈ (List.foldl (fun b a => writeAbsent h.db b a) [] ops).reverse := List.mem_reverse.2 hA
  have hsub : ∀ y ∈ (List.foldl (fun b a => writeAbsent h.db b a) [] ops).reverse, y ∈ ops := fun y hy => by
    rcases absent_sub h.db ops [] y (List.mem_reverse.1 hy) with h | h
    · cases h
    · exact h
  generalize (List.foldl (fun b a => writeAbsent h.db b a) [] ops).reverse = news at hA' hsub ⊢
  have hget : (turnH x.fam news h).db.ops o.id = some o := by
    simp only [turnH, drainS_ops]
    exact ingest_get o news h.db (fun y hy => hu y (hsub y hy)) (Or.inr ⟨hn, hA'⟩)
  rw [forIn_yield news _ (fun a b => if ((turnH x.fam news h).db.ops a.id).isSome then
    (b.1.add x.fam a, a.id :: b.2) else b) _ (fun y _ b => by
      simp only [HeldM.run_bind, HeldM.run_getOp]
      by_cases hc : ((turnH x.fam news h).db.ops y.id).isSome = true <;> simp [hc])]
  simp only [HeldM.run_pure, List.mem_reverse, and_true]
  exact ⟨stored_ids_mem x.fam _ o (by simp [hget]) news n.ix [] (Or.inl hA'), hget⟩


theorem pieceIds_cover (n : Nat) (hn : 0 < n) : ∀ (fuel : Nat) (l : List Id), l.length ≤ fuel →
    ∀ x ∈ l, ∃ p ∈ pieceIds n fuel l, x ∈ p := by
  intro fuel
  induction fuel with
  | zero => intro l hl x hx; cases l with
    | nil => cases hx
    | cons _ _ => simp at hl
  | succ k ih =>
    intro l hl x hx
    cases l with
    | nil => cases hx
    | cons y t =>
      simp only [pieceIds]
      have hs : x ∈ (y :: t).take n ++ (y :: t).drop n := by rw [List.take_append_drop]; exact hx
      rcases List.mem_append.1 hs with hx | hx
      · exact ⟨_, List.mem_cons_self .., hx⟩
      · obtain ⟨p, hp, hxp⟩ := ih _ (by simp at hl ⊢; omega) x hx
        exact ⟨p, List.mem_cons_of_mem _ hp, hxp⟩

theorem chunks_cover (cfg : Config) (ids : List Id) (mk : List Id → Msg) (hmax : 0 < cfg.maxIds) {x : Id}
    (hx : x ∈ ids) : ∃ l, (mk l).op ∈ chunks cfg ids mk ∧ x ∈ l := by
  obtain ⟨p, hp, hxp⟩ := pieceIds_cover cfg.maxIds hmax ids.length ids (Nat.le_refl _) x hx
  exact ⟨p, List.mem_map.2 ⟨p, hp, rfl⟩, hxp⟩

theorem mem_foldl_ins {y : Id} : ∀ (L acc : List Id), (y ∈ acc ∨ y ∈ L) → y ∈ L.foldl Engine.ins acc := by
  intro L
  induction L with
  | nil => intro acc h; rcases h with h | h; exact h; cases h
  | cons x L ih =>
    intro acc h
    simp only [List.foldl_cons]
    apply ih
    rcases h with h | h
    · exact Or.inl ((Engine.mem_ins _ _ _).2 (Or.inl h))
    · rcases List.mem_cons.1 h with rfl | h
      · exact Or.inl ((Engine.mem_ins _ _ _).2 (Or.inr rfl))
      · exact Or.inr h

/-- **Every offer goes out in a have of its room.** -/
theorem holdsOf_cover (cfg : Config) (offer : List (Id × Id)) (hmax : 0 < cfg.maxIds) {r x : Id}
    (hx : (r, x) ∈ offer) : ∃ l, (Msg.hold r l).op ∈ holdsOf cfg offer ∧ x ∈ l := by
  have hr : r ∈ (offer.map (·.1)).foldl Engine.ins [] :=
    mem_foldl_ins _ _ (Or.inr (List.mem_map.2 ⟨(r, x), hx, rfl⟩))
  obtain ⟨l, hl, hxl⟩ := chunks_cover cfg (offer.filterMap fun p => if p.1 = r then some p.2 else none)
    (.hold r) hmax (x := x) (List.mem_filterMap.2 ⟨(r, x), hx, by simp⟩)
  exact ⟨l, List.mem_flatMap.2 ⟨r, hr, hl⟩, hxl⟩

/-- One turn of the stream's loop (`Conn.filed`) on a store. -/
def filedStep (cfg : Config) (fam : Family F) (db : DB F) (st : List (Id × Id) × Conn) (i : Id) : List (Id × Id) × Conn :=
  if (!st.2.known.contains i && !st.2.offered.contains i) = true then
    match db.ops i with
    | some o => if st.2.shows fam o = true then
        (((fam.room o).getD .empty, i) :: st.1, { st.2 with offered := remember cfg.maxKnown st.2.offered i })
      else (st.1, st.2)
    | none => (st.1, st.2)
  else (st.1, st.2)

theorem filed_fold (cfg : Config) (fam : Family F) (db : DB F) (i : Id) (o : Op) (hget : db.ops i = some o) :
    ∀ (L : List Id) (st : List (Id × Id) × Conn), (((fam.room o).getD .empty, i) ∈ st.1 ∨
      (i ∈ L ∧ i ∉ st.2.known ∧ i ∉ st.2.offered ∧ st.2.shows fam o = true)) →
      ((fam.room o).getD .empty, i) ∈ (L.foldl (filedStep cfg fam db) st).1 := by
  intro L
  induction L with
  | nil => intro st h; rcases h with h | ⟨h, _⟩; exact h; cases h
  | cons j L ih =>
    intro st h
    simp only [List.foldl_cons]
    apply ih
    rcases h with h | ⟨hi, hk, ho, hs⟩
    · left; unfold filedStep; split
      · split
        · split
          · exact List.mem_cons_of_mem _ h
          · exact h
        · exact h
      · exact h
    · by_cases hj : j = i
      · subst hj
        left
        have hk' : st.2.known.contains j = false :=
          Bool.eq_false_iff.2 fun hc => hk (Std.HashSet.mem_iff_contains.2 hc)
        have ho' : st.2.offered.contains j = false :=
          Bool.eq_false_iff.2 fun hc => ho (Std.HashSet.mem_iff_contains.2 hc)
        simp [filedStep, hk', ho', hget, hs]
      · right
        have hiL : i ∈ L := by
          rcases List.mem_cons.1 hi with h | h
          · exact absurd h.symm hj
          · exact h
        refine ⟨hiL, ?_⟩
        unfold filedStep
        split
        · split
          · split
            · refine ⟨hk, ?_, hs⟩
              change i ∉ remember cfg.maxKnown st.2.offered j
              unfold remember
              split
              · simp
              · dsimp only
                split <;> simp [ho, hj]
            · exact ⟨hk, ho, hs⟩
          · exact ⟨hk, ho, hs⟩
        · exact ⟨hk, ho, hs⟩

/-- **The stream offers each new op it may show:** an id among those
filed, not known to the peer or offered before, of a stored op the
connection may show, goes out in an offer. -/
theorem filed_offers (fam : Family F) (cfg : Config) (c : Conn) (ids : List Id) (h : Held F) (i : Id) (o : Op)
    (r : Id) (hi : i ∈ ids) (hget : h.db.ops i = some o) (hr : fam.room o = some r) (hsh : c.shows fam o = true)
    (hk : i ∉ c.known) (ho : i ∉ c.offered) (hmax : 0 < cfg.maxIds) :
    ∃ l, (Msg.hold r l).op ∈ ((c.filed fam cfg ids : HeldM F Step).run h).1.send ∧ i ∈ l := by
  simp only [Conn.filed, HeldM.run_bind]
  rw [forIn_yield ids _ (fun i st => filedStep cfg fam h.db st i) h (fun j _ st => by
    simp only [filedStep]; split
    · simp only [HeldM.run_bind, HeldM.run_getOp]
      cases h.db.ops j with
      | none => rfl
      | some p => by_cases hs : st.2.shows fam p = true <;> simp [hs]
    · rfl)]
  simp only [HeldM.run_pure]
  have := filed_fold cfg fam h.db i o hget ids ([], c) (Or.inr ⟨hi, hk, ho, hsh⟩)
  rw [hr, Option.getD_some] at this
  exact holdsOf_cover cfg _ hmax (List.mem_reverse.2 this)


section
variable (S : Setup F) (s : Who)

/-- One turn of the fanout's loop on a store: the connection's stream. -/
def fanoutStep (ids : List Id) (h : Held F) (p : Id × Conn)
    (st : List (Id × Conn) × Acts × List (Id × Id)) : List (Id × Conn) × Acts × List (Id × Id) :=
  let f := ((({ p.2.setRooms (S.rooms s p.1) with notices := [] } : Conn).filed S.fam S.cfg ids :
    HeldM F Step).run h).1
  ((p.1, f.conn) :: st.1, st.2.1 ++ sends p.1 f.send, st.2.2 ++ f.given.map (p.1, ·))

theorem fanout_fold (ids : List Id) (h : Held F) (x : Route × ByteArray) :
    ∀ (L : List (Id × Conn)) st, ((∃ p ∈ L, ∀ st, x ∈ (fanoutStep S s ids h p st).2.1.send) ∨ x ∈ st.2.1.send) →
      x ∈ (L.foldl (fun b a => fanoutStep S s ids h a b) st).2.1.send := by
  intro L
  induction L with
  | nil => intro st hx; rcases hx with ⟨_, h, _⟩ | hx; cases h; exact hx
  | cons q L ih =>
    intro st hx
    simp only [List.foldl_cons]
    apply ih
    rcases hx with ⟨p, hp, hpx⟩ | hx
    · rcases List.mem_cons.1 hp with rfl | hp
      · exact Or.inr (hpx st)
      · exact Or.inl ⟨p, hp, hpx⟩
    · right; simp only [fanoutStep, Acts.append_def, List.mem_append]; exact Or.inl hx

/-- **A store's new ids are offered on every connection that may show
them**, and not known to hold or offered them before. -/
theorem fanout_offers (n : Node) (ids : List Id) (h : Held F) (cid : Id) (c : Conn) (hc : (cid, c) ∈ n.conns)
    (i : Id) (o : Op) (r : Id) (hi : i ∈ ids) (hget : h.db.ops i = some o) (hr : S.fam.room o = some r)
    (hsh : (c.setRooms (S.rooms s cid)).shows S.fam o = true) (hk : i ∉ c.known) (ho : i ∉ c.offered)
    (hmax : 0 < S.cfg.maxIds) :
    let p := (n.fanout (S.sync s) ids).run h
    (∃ l, (Route.conn cid, (Msg.hold r l).op.bytes) ∈ p.1.2.send ∧ i ∈ l) ∧ p.2 = h ∧
      p.1.1.addrs = n.addrs ∧ p.1.1.managed = n.managed := by
  simp only [Node.fanout, HeldM.run_bind]
  rw [forIn_yield n.conns _ (fun p st => fanoutStep S s ids h p st) h (fun p _ st => by
    simp only [HeldM.run_bind, refresh_run, HeldM.run_pure, sync_fam, sync_cfg]
    rw [filedGive_quiet _ _ _ _ _ rfl, filed_reads _ _ _ _ h]; rfl)]
  simp only [recordGiven_run, HeldM.run_pure, and_true]
  obtain ⟨l, hl, hil⟩ :=
    filed_offers S.fam S.cfg { c.setRooms (S.rooms s cid) with notices := [] } ids h i o r hi hget hr hsh hk ho
      hmax
  refine ⟨l, fanout_fold S s ids h _ n.conns _ (Or.inl ⟨(cid, c), hc, fun st => ?_⟩), hil⟩
  simp only [fanoutStep, Acts.append_def, List.mem_append, sends, List.mem_map]
  exact Or.inr ⟨_, hl, rfl⟩


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
def sealStep (S : Setup F) (n : Node) (out : Acts) (sent : List (ByteArray × ByteArray)) (cid : Id) :
    List (ByteArray × ByteArray) :=
  match n.addr? cid with
  | some a => (bundles S.cfg.bundle (payloadsOf out cid)).foldl (fun acc g => (a, plainFrame cid g) :: acc) sent
  | none => sent

theorem seal_fold (S : Setup F) (n : Node) (out : Acts) (x : ByteArray × ByteArray) (cid : Id)
    (hx : ∀ acc, x ∈ sealStep S n out acc cid) :
    ∀ (L : List Id) acc, (cid ∈ L ∨ x ∈ acc) → x ∈ L.foldl (sealStep S n out) acc := by
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
variable (S : Setup F) (s : Who)

/-- **Every payload a node sends on a session goes out in a frame** to
the session's address, sealed in the clear. -/
theorem seal_mem (n : Node) (out : Acts) (h : Held F) (cid : Id) (p a : ByteArray)
    (hp : (Route.conn cid, p) ∈ out.send) (ha : n.addr? cid = some a) :
    ∃ g, p ∈ g ∧ (a, plainFrame cid g) ∈ ((n.seal (S.sync s) out).run h).1 := by
  simp only [Node.seal, HeldM.run_bind]
  rw [forIn_yield out.send _ (fun x st => cidsStep st x) h (fun x _ st => by
    rcases x with ⟨r, b⟩; cases r <;> simp only [cidsStep] <;> (try split) <;> rfl)]
  rw [forIn_yield _ _ (fun c sent => sealStep S n out sent c) h (fun c _ sent => by
    simp only [sealStep]
    cases hc : n.addr? c with
    | none => rfl
    | some a' =>
      simp only [HeldM.run_bind]
      rw [forIn_yield _ _ (fun g acc => (a', plainFrame c g) :: acc) h (fun g _ acc => by
        simp [plainFrame])]
      rfl)]
  have hpl : p ∈ payloadsOf out cid := by
    simp only [payloadsOf, List.mem_filterMap]
    exact ⟨_, hp, by simp⟩
  obtain ⟨g, hg, hpg⟩ := bundles_cover S.cfg.bundle _ p hpl
  refine ⟨g, hpg, ?_⟩
  simp only [HeldM.run_pure, List.mem_reverse]
  refine seal_fold S n out _ cid (fun acc => ?_) _ _ (Or.inl (List.mem_reverse.2
    (cids_fold cid out.send ([], []) (Or.inl ⟨p, hp⟩))))
  simp only [sealStep, ha, foldl_cons_acc]
  exact List.mem_append_left _ (List.mem_reverse.2 (List.mem_map.2 ⟨g, hg, rfl⟩))

end


/-- **A write is offered on every session that may show it:** each op
of a write that the store lacked (and no other op of the write shares
its id) goes out in an offer, in a frame to the session's address, on
every session whose rooms include its room and whose connection has
neither offered it nor heard that the peer holds it. -/
theorem write_offers_all (n : Node) (ops : List Op) (t : Nat) (h : Held F) (hm : n.managed = [])
    (o : Op) (ho : o ∈ ops) (hn : h.db.ops o.id = none) (hu : ∀ y ∈ ops, y.id = o.id → y = o)
    (cid : Id) (c : Conn) (hc : (cid, c) ∈ n.conns) (r : Id) (hr : S.fam.room o = some r)
    (hs : r ∈ S.rooms s cid) (hk : o.id ∉ c.known) (hof : o.id ∉ c.offered) (a : ByteArray)
    (ha : n.addr? cid = some a) (hmax : 0 < S.cfg.maxIds) :
    ∃ ps l, (a, plainFrame cid ps) ∈ ((n.onWrite (S.sync s) ops t).run h).1.2.send ∧
      (Msg.hold r l).op.bytes ∈ ps ∧ o.id ∈ l := by
  obtain ⟨hid, hget, hcn, han, hmn⟩ := write_mem (S.sync s) n ops o h ho hn hu
  have hsh : (c.setRooms (S.rooms s cid)).shows S.fam o = true := by
    simp [Conn.shows, Conn.setRooms, hr, has_of_mem hs]
  have hc' : (cid, c) ∈ ((n.write (S.sync s) ops).run h).1.1.conns := by rw [hcn]; exact hc
  obtain ⟨⟨l, hl, hol⟩, -, han', hmn'⟩ := fanout_offers S s _ _ _ cid c hc' o.id o r hid hget hr hsh hk hof hmax
  have hne : (((n.write (S.sync s) ops).run h).1.2).isEmpty = false := by
    cases hx : ((n.write (S.sync s) ops).run h).1.2 with
    | nil => rw [hx] at hid; cases hid
    | cons _ _ => rfl
  simp only [Node.onWrite, HeldM.run_bind, store_run, Node.put, intake, ite_true, hne, Bool.false_eq_true,
    ite_false]
  rw [finish_run _ _ _ _ _ _ (by rw [heat_managed, hmn', hmn, hm]), seal_heat]
  have ha' : (((n.write (S.sync s) ops).run h).1.1.fanout (S.sync s)
      ((n.write (S.sync s) ops).run h).1.2).run ((n.write (S.sync s) ops).run h).2 |>.1.1.addr? cid = some a := by
    simp only [Node.addr?] at ha ⊢; rw [han', han]; exact ha
  obtain ⟨g, hpg, hg⟩ := seal_mem S s _ _ _ cid _ a hl ha'
  exact ⟨g, l, List.mem_append_left _ hg, hpg, hol⟩

end

section
variable (S : Setup F) (s : Who)

/-- A write turn changes a node's index and fresh ids only. -/
theorem write_keeps (x : Sync F (HeldM F)) (n : Node) (ops : List Op) (h : Held F) :
    ((n.write x ops).run h).1.1.managed = n.managed := by
  simp only [Node.write, HeldM.run_bind]
  rw [forIn_yield ops _ (fun o acc => writeAbsent h.db acc o) h (fun y _ acc => by
    simp only [writeAbsent]; split
    · simp only [HeldM.run_bind, HeldM.run_getOp]
      by_cases hc : (h.db.ops y.id).isNone = true <;> simp [hc]
    · rfl)]
  split
  · rfl
  · simp only [HeldM.run_bind, HeldM.run_turn]
    generalize (List.foldl (fun b a => writeAbsent h.db b a) [] ops).reverse = news
    rw [forIn_yield news _ (fun a b => if ((turnH x.fam news h).db.ops a.id).isSome then
      (b.1.add x.fam a, a.id :: b.2) else b) _ (fun y _ b => by
        simp only [HeldM.run_bind, HeldM.run_getOp]
        by_cases hc : ((turnH x.fam news h).db.ops y.id).isSome = true <;> simp [hc])]
    rfl

/-- Offering keeps a node's managed sessions. -/
theorem fanout_keeps (n : Node) (ids : List Id) (h : Held F) :
    ((n.fanout (S.sync s) ids).run h).1.1.managed = n.managed := by
  simp only [Node.fanout, HeldM.run_bind]
  rw [forIn_yield n.conns _ (fun p st => fanoutStep S s ids h p st) h (fun p _ st => by
    simp only [HeldM.run_bind, refresh_run, HeldM.run_pure, sync_fam, sync_cfg]
    rw [filedGive_quiet _ _ _ _ _ rfl, filed_reads _ _ _ _ h]; rfl)]
  simp [recordGiven_run]

theorem store_keeps (n : Node) (ops : List Op) (mine : Bool) (h : Held F) :
    ((n.store (S.sync s) ops mine).run h).1.1.managed = n.managed := by
  rw [store_run]
  simp only [Node.put]
  by_cases hb : ((Node.write (S.sync s) n (intake (S.sync s).fam mine ops)).run h).1.2.isEmpty = true
  · simp only [hb, ↓reduceIte]; exact write_keeps _ _ _ _
  · simp only [hb, ↓reduceIte, Bool.false_eq_true]; rw [fanout_keeps]; exact write_keeps _ _ _ _

/-- **A write's ops are hot when it returns.** Every id a local write
stores (at most `hotCap` of them) is hot from the write's time, so the
want that follows its offer is answered urgent (`lane_hot`). -/
theorem write_hot (n : Node) (ops : List Op) (t : Nat) (h : Held F) (hm : n.managed = [])
    (hc : ((n.onWrite (S.sync s) ops t).run h).1.2.stored.length ≤ S.cfg.hotCap) :
    ∀ i ∈ ((n.onWrite (S.sync s) ops t).run h).1.2.stored, (i, t) ∈ ((n.onWrite (S.sync s) ops t).run h).1.1.hot := by
  have e : (n.onWrite (S.sync s) ops t).run h =
      (((n.store (S.sync s) ops true).run h).1.1.heat (S.sync s) ((n.store (S.sync s) ops true).run h).1.1.fresh t
        |>.finish (S.sync s) ((n.store (S.sync s) ops true).run h).1.2 t).run ((n.store (S.sync s) ops true).run h).2 := rfl
  rw [e, finish_run _ _ _ _ _ _ (by rw [heat_managed, store_keeps, hm])] at hc ⊢
  exact heat_hot _ _ _ _ hc

end

/-- **New ops are offered on every session that may see them.** Node s
writes ops; op o among them is new to its store, and no other op of the
write shares its id. Then on every session of s whose rooms include o's
room, and whose connection has neither offered o nor heard that the
peer holds it, a frame to the session's address is in flight that
carries an offer naming o. -/
theorem stream_offered (S : Setup F) (w : World F) (s : Who) (ops : List Op) (t : Nat)
    (hm : (w.peer s).node.managed = []) (o : Op) (ho : o ∈ ops) (hn : (w.peer s).held.db.ops o.id = none)
    (hu : ∀ y ∈ ops, y.id = o.id → y = o) (cid : Id) (c : Conn) (hc : (cid, c) ∈ (w.peer s).node.conns)
    (r : Id) (hr : S.fam.room o = some r) (hs : r ∈ S.rooms s cid) (hk : o.id ∉ c.known)
    (hof : o.id ∉ c.offered) (a : ByteArray) (ha : (w.peer s).node.addr? cid = some a)
    (hmax : 0 < S.cfg.maxIds) :
    ∃ ps l, ⟨a, plainFrame cid ps⟩ ∈ (w.write S s ops t).net ∧ (Msg.hold r l).op.bytes ∈ ps ∧ o.id ∈ l := by
  obtain ⟨ps, l, hf, hps, hol⟩ :=
    write_offers_all S s _ ops t _ hm o ho hn hu cid c hc r hr hs hk hof a ha hmax
  refine ⟨ps, l, ?_, hps, hol⟩
  simp only [World.write, World.run_net, inFlight, List.mem_append, List.mem_map]
  exact Or.inr ⟨_, hf, rfl⟩

/-- **`stream_offered` is not vacuous.** From two empty nodes and a
session opened at each end, a write at one of them puts an offer of the
op in flight, to the other. -/
theorem stream_offered_runs (r cid : Id) :
    ∃ w ps l, World.Steps ⟨oneRoom r, {}, fun _ _ => [r]⟩ (World.empty (oneRoom r)) w ∧
      ⟨(w.peer .b).addr, plainFrame cid ps⟩ ∈ w.net ∧ (Msg.hold r l).op.bytes ∈ ps ∧
      (Op.make 1 [] .empty).id ∈ l := by
  let S : Setup Unit := ⟨oneRoom r, {}, fun _ _ => [r]⟩
  let o := Op.make 1 [] .empty
  let w0 := World.empty S.fam
  let w1 := w0.connect S .a cid true 0
  let w2 := w1.connect S .b cid false 0
  obtain ⟨hca, hma, haa, hha, hb1⟩ := World.connect_peer S w0 .a cid true 0 rfl
  have eb : w1.peer .b = w0.peer .b := hb1
  obtain ⟨-, -, -, -, ha2⟩ := World.connect_peer S w1 .b cid false 0 (by rw [eb]; rfl)
  have ea : w2.peer .a = w1.peer .a := ha2
  have hb2 : (w2.peer .b).addr = (w0.peer .b).addr := by
    show ((w1.connect S .b cid false 0).peer .b).addr = _
    simp [World.connect, eb]
  have hc : (cid, (Conn.open true [r] 0 0).conn) ∈ (w2.peer .a).node.conns := by
    rw [ea, hca]; exact List.mem_cons_self ..
  have hma' : (w2.peer .a).node.managed = [] := by rw [ea]; exact hma
  have haa' : (w2.peer .a).node.addr? cid = some (w2.peer .b).addr := by rw [ea, haa, hb2]; rfl
  have hna : (w2.peer .a).held.db.ops o.id = none := by rw [ea, hha]; rfl
  obtain ⟨ps, l, hf, hps, hol⟩ := stream_offered S w2 .a [o] 0 hma' o (List.mem_singleton_self _) hna
    (fun y hy _ => List.mem_singleton.1 hy) cid _ hc r rfl (by simp [S]) (by simp [Conn.open])
    (by simp [Conn.open]) _ haa' (by simp [S])
  refine ⟨w2.write S .a [o] 0, ps, l, .step (.connect .a cid true (t := 0) (Nat.le_refl 0))
    (.step (.connect .b cid false (t := 0) (Nat.le_refl 0)) (.step (.write .a [o] (t := 0) (Nat.le_refl 0))
      (.refl _))), ?_, hps, hol⟩
  have : (w2.write S .a [o] 0).peer .b = w2.peer .b := World.run_peer_other w2 .a _ _ _
  rw [this]; exact hf

/-! ## The round, at one connection -/

/-- **`conn_runs_exchange`, its first case: a claim of ids.** What
`conn_runs_exchange` is to say: in any run of the world, a round the
dialer opens in a room is `exchange` (`RoundLaws.lean`) between the two
sides' snapshots of the room, whatever order its frames arrive in. The
ids one side offers, or the other asks for, are exactly the ids
`exchange` sends from that side. Here is its base case, at the
connection that answers. It answers round k's claim listing ids, the
claimant's items in range rg (an honest claim). It offers exactly the
first side of `exchange` from the round's snapshot X, and asks for
the admitted part of the second. Deferred wants return on a later round. Those are the ids X holds in rg that the claimant
lacks, and the ids the claimant holds there that X lacks
(`exchange_ids`). It sends no claim back, so the round ends there. -/
theorem conn_answers_ids (cfg : Config) (ix : Index) (c : Conn) (r : Id) (k : Nat) (rg : Range)
    (X Y : List Item) (now : Nat) (hr : r ∈ c.rooms)
    (hX : X = ((c.snaps.find? fun p => Decidable.decide (p.1 = (r, k))).map (·.2)).getD (ix.items r)) :
    ∃ A B, (A, B) = exchange Prod.fst Prod.snd sha256 cfg.params 1 X Y
        (.ids rg ((within Prod.fst rg Y).map Prod.snd)) ∧
      (c.onRbsr cfg ix r k [.ids rg ((within Prod.fst rg Y).map Prod.snd)] now).send =
        (Msg.rbsr r k []).op :: (chunks cfg A (.hold r) ++ chunks cfg (admitAsks cfg.maxKnown c.asked B) .want) ∧
      ∀ i, (i ∈ A ↔ named Prod.snd (within Prod.fst rg X) i = true ∧
          named Prod.snd (within Prod.fst rg Y) i = false) ∧
        (i ∈ B ↔ named Prod.snd (within Prod.fst rg Y) i = true ∧
          named Prod.snd (within Prod.fst rg X) i = false) := by
  refine ⟨_, _, rfl, ?_, exchange_ids (P := cfg.params) 0 X Y rg _ rfl⟩
  have hr' := has_of_mem hr
  simp only [Conn.onRbsr, hr', Bool.not_true, Bool.false_eq_true, ite_false, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.isEmpty_cons]
  simp only [hX, Conn.snap, exchange, answer, give, get, Conn.beginRound]
  cases List.find? (fun p => Decidable.decide (p.fst = (r, k))) c.snaps with
  | none => simp
  | some p => obtain ⟨_, _⟩ := p; simp

end Engine.Sync
