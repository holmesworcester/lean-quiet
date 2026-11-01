/-
H2, a want is served, proven of the running node over frames of any
payloads (docs/PROOFS.md, "The hops"): a want for an op a plain node
holds, in a room the session shows and its index lists, joins the
session's queue (`owed`) or is answered with the op in the frame back to
the sender (`onSealed_queues`), when the queue has room for every id the
frame wants. Main's ServeLaws then serve the queue in order
(`serveOwed_head`, `serve_pending`, `owed_within`), and a fresh write
first (`serveOwed_hot`).

- **What a payload does to the queue** (`recv_owed`): queued ids stay
  queued, what the session owes stays within its queue, and the queue
  grows by at most the payload's want.
- **Serving keeps an owed op queued unless it sends it** (`node_serve`).
-/
import engine.world.Asks
import engine.sync.ClosureDelivery

namespace Engine.World
open Engine Engine.Sync

variable {F : Type}

attribute [local instance] byteArray_lawfulBEq

/-- How many ids a payload can queue: a want's ids. -/
def wantsOf (b : ByteArray) : Nat :=
  match Op.decode b with
  | some o =>
    match Msg.ofOp o with
    | some (.want ids) => ids.length
    | _ => 0
  | none => 0

theorem wantsOf_want (L : List Id) : wantsOf (Msg.want L).op.bytes = L.length := by
  simp [wantsOf, Op.decode_bytes, ofOp_want]

/-- Every id a connection owes is in its queue. -/
def OwesQueued (c : Conn) : Prop := ∀ y, y ∈ c.owing → y ∈ c.owed

/-- A round message leaves the queue as it is. -/
theorem onRbsr_owed (cfg : Config) (ix : Index) (c : Conn) (r : Id) (k : Nat) (cs : List Claim) (now : Nat) :
    (c.onRbsr cfg ix r k cs now).conn.owed = c.owed ∧ (c.onRbsr cfg ix r k cs now).conn.owing = c.owing := by
  unfold Conn.onRbsr
  split
  · exact ⟨rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl⟩
    · dsimp only
      split
      · exact ⟨rfl, rfl⟩
      · dsimp only; split <;> exact ⟨rfl, rfl⟩

/-- **What a payload does to the queue:** queued ids stay queued, what
the session owes stays within its queue, and the queue grows by at most
the payload's want. -/
theorem recv_owed (fam : Family F) (cfg : Config) (ix : Index) (c : Conn) (b : ByteArray) (now : Nat)
    (h : Held F) (hq : OwesQueued c) :
    OwesQueued ((Conn.recv fam cfg ix c b now : HeldM F Step).run h).1.conn ∧
      (∀ y ∈ c.owed, y ∈ ((Conn.recv fam cfg ix c b now : HeldM F Step).run h).1.conn.owed) ∧
      ((Conn.recv fam cfg ix c b now : HeldM F Step).run h).1.conn.owed.length ≤ c.owed.length + wantsOf b := by
  unfold Conn.recv wantsOf
  cases hd : Op.decode b with
  | none => exact ⟨hq, fun y hy => hy, Nat.le_add_right _ _⟩
  | some o =>
    simp only
    cases hm : Msg.ofOp o with
    | some m =>
      cases m with
      | hello f =>
        simp only [HeldM.run_pure]
        split
        · unfold Conn.start; split
          · exact ⟨hq, fun y hy => hy, Nat.le_add_right _ _⟩
          · exact ⟨hq, fun y hy => hy, Nat.le_add_right _ _⟩
        · exact ⟨hq, fun y hy => hy, Nat.le_add_right _ _⟩
      | rbsr r k cs =>
        simp only [HeldM.run_pure]
        obtain ⟨e1, e2⟩ := onRbsr_owed cfg ix { c with heard := now } r k cs now
        refine ⟨fun y hy => ?_, fun y hy => ?_, ?_⟩
        · rw [e2] at hy; rw [e1]; exact hq y hy
        · rw [e1]; exact hy
        · rw [e1]; exact Nat.le_add_right _ _
      | hold r ids =>
        simp only [HeldM.run_bind, HeldM.run_pure]
        simp only [show ∀ m : HeldM F Step, m.run h = m h from fun _ => rfl]
        rw [onHold_apply]
        split
        · exact ⟨hq, fun y hy => hy, Nat.le_add_right _ _⟩
        · split
          · exact ⟨hq, fun y hy => hy, Nat.le_add_right _ _⟩
          · exact ⟨hq, fun y hy => hy, Nat.le_add_right _ _⟩
      | want ids =>
        simp only [HeldM.run_pure, Conn.onWant]
        split
        · exact ⟨hq, fun y hy => hy, Nat.le_add_right _ _⟩
        · refine ⟨fun y hy => ?_, fun y hy => List.mem_append_left _ hy, ?_⟩
          · rcases (foldl_insert_mem _ _).1 hy with hy | hy
            · exact List.mem_append_left _ (hq y hy)
            · exact List.mem_append_right _ hy
          · simp only [List.length_append, List.length_take]
            have h2 := eraseDups_length_le ((authorize ix { c with heard := now } ids).filter fun i => !c.owing.contains i)
            have h3 := List.length_filter_le (fun i => !c.owing.contains i) (authorize ix { c with heard := now } ids)
            have h4 : (authorize ix { c with heard := now } ids).length ≤ ids.length := List.length_filter_le _ _
            omega
    | none =>
      simp only
      split
      · exact ⟨hq, fun y hy => hy, Nat.le_add_right _ _⟩
      · exact ⟨hq, fun y hy => hy, Nat.le_add_right _ _⟩

theorem recv_want (fam : Family F) (cfg : Config) (ix : Index) (c : Conn) (L : List Id) (now : Nat) (h : Held F) :
    (Conn.recv fam cfg ix c (Msg.want L).op.bytes now : HeldM F Step).run h =
      (({ c with heard := now } : Conn).onWant cfg ix L, h) := by
  simp [Conn.recv, Op.decode_bytes, ofOp_want]

section
variable (S : Engine.Sync.Setup F) (s : Who)

/-- The fanout keeps a node's index. -/
theorem fanout_ix (n : Node) (ids : List Id) (h : Held F) : ((n.fanout (S.sync s) ids).run h).1.1.ix = n.ix := by
  simp only [Node.fanout, HeldM.run_bind]
  rw [forIn_yield n.conns _ (fun p st => fanoutStep S s ids h p st) h (fun p _ st => by
    simp only [HeldM.run_bind, refresh_run, HeldM.run_pure, sync_fam, sync_cfg]
    rw [filedGive_quiet _ _ _ _ _ rfl, filed_reads _ _ _ _ h]; rfl)]
  simp [recordGiven_run]

/-- **Applying a step only adds to the index.** -/
theorem apply_ix (n : Node) (cid : Id) (st : Step) (now : Nat) (h : Held F) (hd : st.drop = false)
    {r : Id} {a : Item} (ha : a ∈ n.ix.items r) : a ∈ ((n.apply (S.sync s) cid st now).run h).1.1.ix.items r := by
  have hfold : ∀ (L : List Op), L.foldl (fun b (_ : Op) => b) ([] : List Op) = [] := by
    intro L; induction L with
    | nil => rfl
    | cons _ _ ih => exact ih
  unfold Node.apply
  simp only [hd, Bool.false_eq_true, ↓reduceIte, HeldM.run_bind, recordGiven_run]
  rw [forIn_yield _ _ (fun _ acc => acc) _ (fun o _ acc => by
    simp only [sync_recv, HeldM.run_bind, HeldM.run_pure, List.append_nil]), hfold, store_nil]
  simp only [HeldM.run_pure]
  rw [store_run]
  dsimp only
  obtain ⟨L, hL⟩ := write_ix (S.sync s) { n with conns := n.conns.map fun p => if p.1 = cid then (cid, st.conn) else p }
    (intake (S.sync s).fam false st.take) h
  have hw : a ∈ ((Node.put (S.sync s) { n with conns := n.conns.map fun p => if p.1 = cid then (cid, st.conn) else p }
      st.take false).run h).1.1.ix.items r := by
    unfold Node.put
    show a ∈ ((Node.write (S.sync s) _ _) h).1.1.ix.items r
    rw [hL]; exact items_foldl_mono S.fam ha
  split
  · exact hw
  · rw [fanout_ix]; exact hw

/-- **Serving the queue sends an owed op, or keeps it queued:** an id the
session owes, of an op the node holds in a room the session shows, is
sent (urgent if it is the selected fresh write, else in the serve lane)
or stays in the queue. -/
theorem node_serve (n : Node) (cid : Id) (now : Nat) (h : Held F) (c : Conn) (hc : n.conn? cid = some c)
    (x : Id) (o : Op) (r : Id) (hx : x ∈ c.owed) (hg : h.db.ops x = some o) (hr : S.fam.room o = some r)
    (hs : r ∈ S.rooms s cid) :
    (∃ c', ((n.serveOwed (S.sync s) cid now).run h).1.1.conn? cid = some c' ∧ x ∈ c'.owed) ∨
      (Route.conn cid, o.bytes) ∈ ((n.serveOwed (S.sync s) cid now).run h).1.2.send ∨
      (Route.conn cid, o.bytes) ∈ ((n.serveOwed (S.sync s) cid now).run h).1.2.serve := by
  have hne : c.owed.isEmpty = false := by
    cases e : c.owed with
    | nil => rw [e] at hx; cases hx
    | cons _ _ => rfl
  unfold Node.serveOwed
  rw [hc]
  simp only [hne, Bool.false_eq_true, ↓reduceIte, HeldM.run_bind, refresh_run, sync_fam, sync_cfg]
  generalize hb : ((n.addr? cid).bind (S.sync s).room).getD S.cfg.burst = budget
  generalize hc' : ({ c.setRooms (S.rooms s cid) with notices := [] } : Conn) = c'
  have hx' : x ∈ c'.owed := by rw [← hc']; exact hx
  have hsh : c'.shows S.fam o = true := by rw [← hc']; simp [Conn.shows, Conn.setRooms, hr, has_of_mem hs]
  obtain ⟨e1, e2, -⟩ := serveOwed_run S.fam S.cfg c' budget (n.hotIds (S.sync s) now) h
  have E : (c'.serveOwed S.fam S.cfg budget (n.hotIds (S.sync s) now) : HeldM F _).run h =
      (c'.serveOwed S.fam S.cfg budget (n.hotIds (S.sync s) now) : HeldM F _) h := rfl
  simp only [E, HeldM.run_pure]
  by_cases hhot : x ∈ c'.hotOf (n.hotIds (S.sync s) now)
  · right; left
    have ho := serveOwed_hot S.fam S.cfg c' budget (n.hotIds (S.sync s) now) h x o hhot hg hsh
    exact List.mem_map.2 ⟨o, ho, rfl⟩
  · have hxa : x ∈ c'.owedAfter (n.hotIds (S.sync s) now) := by
      unfold Conn.owedAfter
      split
      · exact hx'
      · exact List.mem_filter.2 ⟨hx', by simpa using hhot⟩
    by_cases hbulk : o ∈ ((serve (c'.shows S.fam) budget (c'.owedAfter (n.hotIds (S.sync s) now))).trace h.db.ops).1.1
    · right; right
      have hb2 : o ∈ ((c'.serveOwed S.fam S.cfg budget (n.hotIds (S.sync s) now) : HeldM F _) h).1.2.2 := by
        rw [e1]; exact hbulk
      exact List.mem_map.2 ⟨o, hb2, rfl⟩
    · left
      obtain ⟨hm, -, -⟩ := serve_pending (c'.shows S.fam) h.db.ops _ budget x o hxa hg hsh hbulk
      refine ⟨_, ?_, by rw [e2]; exact hm⟩
      rw [conn_replace, hc]; rfl

/-- A map that keeps every key keeps each key's first entry, mapped. -/
theorem find_map_owed (L : List (Id × Conn)) (g : Id × Conn → Id × Conn) (cid : Id) (c : Conn)
    (hk : ∀ q, (g q).1 = q.1) (ho : ∀ q, (g q).2.owed = q.2.owed)
    (hc : (L.find? fun p => Decidable.decide (p.1 = cid)).map (·.2) = some c) :
    ∃ c', ((L.map g).find? fun p => Decidable.decide (p.1 = cid)).map (·.2) = some c' ∧ c'.owed = c.owed := by
  induction L with
  | nil => cases hc
  | cons p t ih =>
    by_cases e : p.1 = cid
    · simp only [List.find?_cons, e, decide_true, Option.map_some, Option.some.injEq] at hc
      refine ⟨(g p).2, by simp [List.find?_cons, hk p, e], by rw [ho, hc]⟩
    · simp only [List.find?_cons, e, decide_false] at hc
      obtain ⟨c', h1, h2⟩ := ih hc
      exact ⟨c', by simpa [List.find?_cons, hk p, e] using h1, h2⟩

/-- **The end of an entry point keeps each session's queue.** -/
theorem finish_conn (n : Node) (out : Acts) (now : Nat) (h : Held F) (hm : n.managed = []) (cid : Id) (c : Conn)
    (hc : n.conn? cid = some c) :
    ∃ c', ((n.finish (S.sync s) out now).run h).1.1.conn? cid = some c' ∧ c'.owed = c.owed := by
  rw [finish_run S s n out now h hm]
  simp only [Node.conn?, Node.sent] at hc ⊢
  exact find_map_owed n.conns _ cid c (fun q => by cases q; rfl) (fun q => by cases q; dsimp only; split <;> rfl) hc

/-- **H2 at a session's frame.** A node whose session cid is open takes
a frame on it carrying a want naming x, an op the node holds in a room
the session shows and its index lists. Then after the frame x is in the
session's queue, or the frame back to the sender carries x's op,
wherever the want sits in the frame and whatever else the frame carries,
when the queue has room for every id the frame wants and owes nothing
outside its queue. -/
theorem onSealed_queues (n : Node) (src : ByteArray) (cid : Id) (inner : List ByteArray) (x : Id) (o : Op)
    (r : Id) (L : List Id) (now : Nat) (h : Held F) (c0 : Conn) (hc : n.conn? cid = some c0) (hm : n.managed = [])
    (hb : (Msg.want L).op.bytes ∈ inner) (hxL : x ∈ L) (hL : L.length ≤ S.cfg.maxIds)
    (hg : h.db.ops x = some o) (hr : S.fam.room o = some r) (hs : r ∈ S.rooms s cid)
    (hix : ∃ a ∈ n.ix.items r, a.2 = x) (hq0 : OwesQueued c0)
    (hroom : c0.owed.length + (inner.map wantsOf).sum ≤ S.cfg.maxKnown) :
    (∃ c', ((n.onSealed (S.sync s) src (some (cid, Codec.encode inner)) now).run h).1.1.conn? cid = some c' ∧
        x ∈ c'.owed) ∨
      ∃ g, o.bytes ∈ g ∧
        (src, plainFrame cid g) ∈ ((n.onSealed (S.sync s) src (some (cid, Codec.encode inner)) now).run h).1.2.send := by
  have hshared : S.fam.shared o = true := by simp [Family.shared, hr]
  unfold Node.onSealed
  simp only [hc, Codec.decode_encode, HeldM.run_bind]
  generalize hR : HeldM.run (forIn (m := HeldM F) (_ : List ByteArray)
    ((n.setAddr cid src, {}) : Node × Acts) _) h = R
  have key : R.1.1.managed = [] ∧ R.1.1.addr? cid = some src ∧ R.1.2.retry = [] ∧ R.2.db.ops x = some o ∧
      ((∃ c, R.1.1.conn? cid = some c ∧ x ∈ c.owed) ∨ (Route.conn cid, o.bytes) ∈ R.1.2.send ∨
        (Route.conn cid, o.bytes) ∈ R.1.2.serve) := by
    rw [← hR]
    refine forIn_suffix _ (fun rem h' (st : Node × Acts) => (st.1.conn? cid).isSome = true ∧ st.1.managed = [] ∧
        st.1.addr? cid = some src ∧ st.2.retry = [] ∧ h'.db.ops x = some o ∧ (∃ a ∈ st.1.ix.items r, a.2 = x) ∧
        ∀ c, st.1.conn? cid = some c → OwesQueued c ∧ c.owed.length + (rem.map wantsOf).sum ≤ S.cfg.maxKnown)
      (fun h' st => st.1.managed = [] ∧ st.1.addr? cid = some src ∧ st.2.retry = [] ∧ h'.db.ops x = some o ∧
        ((∃ c, st.1.conn? cid = some c ∧ x ∈ c.owed) ∨ (Route.conn cid, o.bytes) ∈ st.2.send ∨
          (Route.conn cid, o.bytes) ∈ st.2.serve)) (Msg.want L).op.bytes ?_ ?_ ?_ ?_ inner hb _ h ?_
    · intro a st h'
      split
      · simp only [HeldM.run_bind, HeldM.run_pure]; exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
    · intro a t st h' ⟨hc', hm', ha', hr', hx', hi', hk⟩
      split
      · rename_i c hcs
        simp only [HeldM.run_bind, refresh_run, sync_fam, sync_cfg, HeldM.run_pure, ForInStep.value]
        rw [recv_reads]
        obtain ⟨-, hd, -⟩ := recv_cases S.fam S.cfg st.1.ix { c.setRooms (S.rooms s cid) with notices := [] } a now h'
        obtain ⟨f1, f2, f3, -, f5⟩ := apply_facts S s st.1 cid _ now h' hd hc'
        obtain ⟨hq1, hk2⟩ := hk c hcs
        obtain ⟨g1, -, g3⟩ := recv_owed S.fam S.cfg st.1.ix { c.setRooms (S.rooms s cid) with notices := [] } a now h' hq1
        obtain ⟨ai, hai, eai⟩ := hi'
        refine ⟨(payload_run S s st.1 cid c a now h' hcs).1, by rw [f2]; exact hm', by rw [addr_of_addrs f3]; exact ha',
          by simp [Acts.append_def, hr', f1], ?_, ⟨ai, apply_ix S s st.1 cid _ now h' hd hai, eai⟩,
          fun c' hc'' => ⟨?_, ?_⟩⟩
        · rcases (payload_run S s st.1 cid c a now h' hcs).2 with e | ⟨o', _, _, e⟩
          · rw [e]; exact hx'
          · rw [e]; exact turnH_some _ _ _ hx'
        · obtain ⟨-, e2, e3⟩ := f5 c' hc''
          intro y hy; rw [e3] at hy; rw [e2]; exact g1 y hy
        · obtain ⟨-, e2, -⟩ := f5 c' hc''
          rw [e2]
          simp only [List.map_cons, List.sum_cons] at hk2
          have : ({ c.setRooms (S.rooms s cid) with notices := [] } : Conn).owed = c.owed := rfl
          rw [this] at g3; omega
      · rename_i hcn
        obtain ⟨c, hcc⟩ := Option.isSome_iff_exists.1 hc'
        exact (hcn c hcc).elim
    · intro a t st h' ⟨hc', _, _, _, _, _, hk⟩ ⟨qm, qa, qr, qx, qh⟩
      split
      · rename_i c hcs
        simp only [HeldM.run_bind, refresh_run, sync_fam, sync_cfg, HeldM.run_pure, ForInStep.value]
        rw [recv_reads]
        obtain ⟨-, hd, -⟩ := recv_cases S.fam S.cfg st.1.ix { c.setRooms (S.rooms s cid) with notices := [] } a now h'
        obtain ⟨f1, f2, f3, -, f5⟩ := apply_facts S s st.1 cid _ now h' hd hc'
        obtain ⟨hq1, -⟩ := hk c hcs
        obtain ⟨-, g2, -⟩ := recv_owed S.fam S.cfg st.1.ix { c.setRooms (S.rooms s cid) with notices := [] } a now h' hq1
        refine ⟨by rw [f2]; exact qm, by rw [addr_of_addrs f3]; exact qa, by simp [Acts.append_def, qr, f1], ?_, ?_⟩
        · rcases (payload_run S s st.1 cid c a now h' hcs).2 with e | ⟨o', _, _, e⟩
          · rw [e]; exact qx
          · rw [e]; exact turnH_some _ _ _ qx
        · rcases qh with ⟨c1, hc1, hx1⟩ | hq | hq
          · rw [hcs] at hc1; cases hc1
            obtain ⟨c', hc''⟩ := Option.isSome_iff_exists.1 (payload_run S s st.1 cid c a now h' hcs).1
            obtain ⟨-, e2, -⟩ := f5 c' hc''
            exact Or.inl ⟨c', hc'', by rw [e2]; exact g2 x hx1⟩
          · exact Or.inr (Or.inl (by simp only [Acts.append_def, List.mem_append]; exact Or.inl hq))
          · exact Or.inr (Or.inr (by simp only [Acts.append_def, List.mem_append]; exact Or.inl hq))
      · exact ⟨qm, qa, qr, qx, qh⟩
    · intro t st h' ⟨hc', hm', ha', hr', hx', hi', hk⟩
      split
      · rename_i c hcs
        simp only [HeldM.run_bind, refresh_run, sync_fam, sync_cfg, HeldM.run_pure, ForInStep.value]
        rw [recv_reads]
        obtain ⟨-, hd, -⟩ := recv_cases S.fam S.cfg st.1.ix { c.setRooms (S.rooms s cid) with notices := [] }
          (Msg.want L).op.bytes now h'
        obtain ⟨f1, f2, f3, -, f5⟩ := apply_facts S s st.1 cid _ now h' hd hc'
        refine ⟨by rw [f2]; exact hm', by rw [addr_of_addrs f3]; exact ha', by simp [Acts.append_def, hr', f1], ?_, ?_⟩
        · rcases (payload_run S s st.1 cid c _ now h' hcs).2 with e | ⟨o', _, _, e⟩
          · rw [e]; exact hx'
          · rw [e]; exact turnH_some _ _ _ hx'
        · left
          obtain ⟨hq1, hk2⟩ := hk c hcs
          obtain ⟨c', hc''⟩ := Option.isSome_iff_exists.1 (payload_run S s st.1 cid c _ now h' hcs).1
          obtain ⟨-, e2, -⟩ := f5 c' hc''
          refine ⟨c', hc'', ?_⟩
          rw [e2, recv_want]
          simp only [List.map_cons, List.sum_cons, wantsOf_want] at hk2
          have hauth : x ∈ authorize st.1.ix
              ({ ({ c.setRooms (S.rooms s cid) with notices := [] } : Conn) with heard := now } : Conn) L := by
            obtain ⟨ai, hai, eai⟩ := hi'
            exact (authorize_mem _ _ _ _).2 ⟨hxL, r, by simp [Conn.setRooms, hs], ai, hai, eai⟩
          rcases onWant_all S.cfg st.1.ix
            ({ ({ c.setRooms (S.rooms s cid) with notices := [] } : Conn) with heard := now } : Conn) L hL
            (by simp only [Conn.setRooms]; omega) x hauth with ho | ho
          · obtain ⟨add, eadd⟩ := onWant_order S.cfg st.1.ix
              ({ ({ c.setRooms (S.rooms s cid) with notices := [] } : Conn) with heard := now } : Conn) L
            rw [eadd]
            exact List.mem_append_left _ (hq1 x ho)
          · exact ho
      · rename_i hcn
        obtain ⟨c, hcc⟩ := Option.isSome_iff_exists.1 hc'
        exact (hcn c hcc).elim
    · have e0 : (n.setAddr cid src).conn? cid = n.conn? cid := rfl
      refine ⟨by show ((n.setAddr cid src).conn? cid).isSome = true; rw [e0, hc]; rfl, hm,
        setAddr_addr n cid src, rfl, hg, hix, fun c hcs => ?_⟩
      rw [e0, hc] at hcs; cases hcs; exact ⟨hq0, hroom⟩
  obtain ⟨k1, k2, k3, k4, k5⟩ := key
  obtain ⟨s1, s2, s3⟩ := serveOwed_facts S s R.1.1 cid now R.2
  have hS := serveOwed_reads S s R.1.1 cid now R.2
  have hsv : (∃ c', ((R.1.1.serveOwed (S.sync s) cid now).run R.2).1.1.conn? cid = some c' ∧ x ∈ c'.owed) ∨
      (Route.conn cid, o.bytes) ∈ (R.1.2 ++ ((R.1.1.serveOwed (S.sync s) cid now).run R.2).1.2).send ∨
      (Route.conn cid, o.bytes) ∈ (R.1.2 ++ ((R.1.1.serveOwed (S.sync s) cid now).run R.2).1.2).serve := by
    rcases k5 with ⟨c1, hc1, hx1⟩ | hq | hq
    · rcases node_serve S s R.1.1 cid now R.2 c1 hc1 x o r hx1 k4 hr hs with e | e | e
      · exact Or.inl e
      · exact Or.inr (Or.inl (List.mem_append_right _ e))
      · exact Or.inr (Or.inr (List.mem_append_right _ e))
    · exact Or.inr (Or.inl (List.mem_append_left _ hq))
    · exact Or.inr (Or.inr (List.mem_append_left _ hq))
  generalize HeldM.run (Node.serveOwed (S.sync s) R.1.1 cid now) R.2 = B at hS s1 s2 s3 hsv ⊢
  rcases hsv with ⟨c', hc', hx'⟩ | hp
  · left
    obtain ⟨c'', hc'', e⟩ := finish_conn S s B.1.1 (R.1.2 ++ B.1.2) now B.2 (by rw [s2, k1]) cid c' hc'
    exact ⟨c'', hc'', by rw [e]; exact hx'⟩
  · right
    obtain ⟨g, hg', hf⟩ := finish_sends S s B.1.1 (R.1.2 ++ B.1.2) now B.2 (by rw [s2, k1])
      (by simp [Acts.append_def, k3, s1]) cid _ src hp (by rw [addr_of_addrs s3]; exact k2)
    exact ⟨g, hg', hf⟩

end

end Engine.World
