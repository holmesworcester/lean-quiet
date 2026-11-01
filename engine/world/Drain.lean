/-
The queue drains, proven of the running node in the plain World: an id
waiting in a session's queue (`owed`) at its holder stays queued, never
moving back, or its op goes out on the session; and each tick of the
holder moves it forward or sends it (main's `serveOwed_pending`, at the
node's own calls). So it is sent within its queue position in ticks.

- At a connection: a payload's step only appends to the queue
  (`recv_appends`); the clock leaves it as it is (`tickGive_q`).
- At a node: applying another session's step, the stream, storing and
  the end of an entry point leave a session's queue as it was; serving it
  sends the op or moves it forward (`node_serve_waits`).
-/
import engine.world.Chain
import engine.world.InvIx

namespace Engine.World
open Engine Engine.Sync

variable {F : Type}

attribute [local instance] byteArray_lawfulBEq

/-- x waits in connection c's queue, at position p or nearer the front. -/
def Waits (x : Id) (p : Nat) (c : Conn) : Prop := x ∈ c.owed ∧ c.owed.idxOf x ≤ p

theorem Waits.append {x : Id} {p : Nat} {c c' : Conn} (h : Waits x p c) (add : List Id) (e : c'.owed = c.owed ++ add) :
    Waits x p c' := by
  refine ⟨by rw [e]; exact List.mem_append_left _ h.1, ?_⟩
  rw [e, List.idxOf_append, if_pos h.1]; exact h.2

theorem Waits.same {x : Id} {p : Nat} {c c' : Conn} (h : Waits x p c) (e : c'.owed = c.owed) : Waits x p c' := by
  rw [Waits, e]; exact h

theorem Waits.mono {x : Id} {p q : Nat} {c : Conn} (h : Waits x p c) (hpq : p ≤ q) : Waits x q c :=
  ⟨h.1, Nat.le_trans h.2 hpq⟩

/-- **A payload's step only appends to the queue.** -/
theorem recv_appends (fam : Family F) (cfg : Config) (ix : Index) (c : Conn) (b : ByteArray) (now : Nat)
    (h : Held F) : ∃ add, ((Conn.recv fam cfg ix c b now : HeldM F Step).run h).1.conn.owed = c.owed ++ add := by
  unfold Conn.recv
  cases hd : Op.decode b with
  | none => exact ⟨[], by simp⟩
  | some o =>
    simp only
    cases hm : Msg.ofOp o with
    | some m =>
      cases m with
      | hello f =>
        simp only [HeldM.run_pure]
        split
        · exact ⟨[], by rw [(start_q cfg ix _ now).1]; simp⟩
        · exact ⟨[], by simp⟩
      | rbsr r k cs =>
        simp only [HeldM.run_pure]
        exact ⟨[], by rw [(onRbsr_owed cfg ix _ r k cs now).1]; simp⟩
      | hold r ids =>
        simp only [HeldM.run_bind, HeldM.run_pure]
        simp only [show ∀ m : HeldM F Step, m.run h = m h from fun _ => rfl]
        rw [onHold_apply]
        refine ⟨[], ?_⟩
        split
        · simp
        · split <;> simp
      | want ids =>
        simp only [HeldM.run_pure]
        exact onWant_order cfg ix _ ids
    | none =>
      simp only
      split
      · exact ⟨[], by simp⟩
      · exact ⟨[], by simp⟩

/-- Replacing another session's connection leaves this one's. -/
theorem replace_other (n : Node) (cid cid' : Id) (c : Conn) (hne : cid ≠ cid') :
    Node.conn? { n with conns := n.conns.map fun p => if p.1 = cid' then (cid', c) else p } cid = n.conn? cid := by
  simp only [Node.conn?]
  induction n.conns with
  | nil => rfl
  | cons p t ih =>
    rw [List.map_cons]
    by_cases e1 : p.1 = cid'
    · have e3 : ¬ cid' = cid := fun h => hne h.symm
      have e2 : ¬ p.1 = cid := fun h => e3 (e1 ▸ h)
      rw [if_pos e1, List.find?_cons_of_neg (by simp [e3]), List.find?_cons_of_neg (by simp [e2])]
      exact ih
    · rw [if_neg e1]
      by_cases e2 : p.1 = cid
      · rw [List.find?_cons_of_pos (by simp [e2]), List.find?_cons_of_pos (by simp [e2])]
      · rw [List.find?_cons_of_neg (by simp [e2]), List.find?_cons_of_neg (by simp [e2])]; exact ih

section
variable (S : Engine.Sync.Setup F) (s : Who)

/-- **Applying another session's step leaves this session's queue.** -/
theorem apply_other_owed (n : Node) (cid cid' : Id) (st : Step) (now : Nat) (h : Held F) (hne : cid ≠ cid')
    (c' : Conn) (hc' : ((n.apply (S.sync s) cid' st now).run h).1.1.conn? cid = some c') :
    ∃ c, n.conn? cid = some c ∧ c'.owed = c.owed := by
  have hfold : ∀ (L : List Op), L.foldl (fun b (_ : Op) => b) ([] : List Op) = [] := by
    intro L; induction L with
    | nil => rfl
    | cons _ _ ih => exact ih
  unfold Node.apply at hc'
  split at hc'
  · exact ⟨c', close_conn n cid' cid c' hc', rfl⟩
  · simp only [HeldM.run_bind, recordGiven_run] at hc'
    rw [forIn_yield _ _ (fun _ acc => acc) _ (fun o _ acc => by
      simp only [sync_recv, HeldM.run_bind, HeldM.run_pure, List.append_nil]), hfold, store_nil] at hc'
    simp only [HeldM.run_pure] at hc'
    obtain ⟨c, hc, -, e, -⟩ := (store_facts S s _ st.take false h).2.2.2 cid c' hc'
    rw [replace_other n cid cid' st.conn hne] at hc
    exact ⟨c, hc, e⟩

/-- Serving another session's queue leaves this session's connection. -/
theorem serve_other (y : Sync F (HeldM F)) (n : Node) (cid cid' : Id) (now : Nat) (h : Held F) (hne : cid ≠ cid') :
    ((n.serveOwed y cid' now).run h).1.1.conn? cid = n.conn? cid := by
  unfold Node.serveOwed
  split
  · rfl
  · split
    · rfl
    · simp only [HeldM.run_bind, HeldM.run_pure]
      exact replace_other n cid cid' _ hne

/-- **Serving this session's queue sends the op or moves it forward**, on
any sync with the plain node's family, settings and hooks (the clock
serves on `afterActs`'s), with a positive budget. -/
theorem serve_moves (y : Sync F (HeldM F)) (hf : y.fam = S.fam) (hcfg : y.cfg = S.cfg)
    (hh : y.hooks = (S.sync s).hooks) (n : Node) (cid : Id) (now : Nat) (h : Held F) (c : Conn)
    (hc : n.conn? cid = some c) (x : Id) (o : Op) (r : Id) (hx : x ∈ c.owed) (hg : h.db.ops x = some o)
    (hr : S.fam.room o = some r) (hs : r ∈ S.rooms s cid)
    (hb : 0 < ((n.addr? cid).bind y.room).getD y.cfg.burst) :
    (∃ c', ((n.serveOwed y cid now).run h).1.1.conn? cid = some c' ∧ x ∈ c'.owed ∧
        c'.owed.idxOf x < c.owed.idxOf x) ∨
      (Route.conn cid, o.bytes) ∈ ((n.serveOwed y cid now).run h).1.2.send ∨
      (Route.conn cid, o.bytes) ∈ ((n.serveOwed y cid now).run h).1.2.serve := by
  have hne : c.owed.isEmpty = false := by
    cases e : c.owed with
    | nil => rw [e] at hx; cases hx
    | cons _ _ => rfl
  unfold Node.serveOwed
  rw [hc]
  simp only [hne, Bool.false_eq_true, ↓reduceIte, HeldM.run_bind, Node.refresh, hh, sync_rooms, HeldM.run_pure, hf]
  generalize hbud : ((n.addr? cid).bind y.room).getD y.cfg.burst = budget at hb
  generalize hc' : c.carry ((S.rooms s cid).map Room.sync) = c'
  have hx' : x ∈ c'.owed := by rw [← hc']; exact hx
  have hix : c'.owed.idxOf x = c.owed.idxOf x := by rw [← hc']; rfl
  have hsh : c'.shows S.fam o = true := by
    rw [← hc']; simp [Conn.carry, Conn.shows, Conn.setRooms, hr, has_of_mem hs]
  have E : (c'.serveOwed S.fam y.cfg budget (n.hotIds y now) : HeldM F _).run h =
      (c'.serveOwed S.fam y.cfg budget (n.hotIds y now) : HeldM F _) h := rfl
  simp only [E]
  by_cases hsent : o ∈ ((c'.serveOwed S.fam y.cfg budget (n.hotIds y now) : HeldM F _) h).1.2.1 ++
      ((c'.serveOwed S.fam y.cfg budget (n.hotIds y now) : HeldM F _) h).1.2.2
  · right
    rcases List.mem_append.1 hsent with ho | ho
    · left; exact List.mem_map.2 ⟨o, ho, rfl⟩
    · right; exact List.mem_map.2 ⟨o, ho, rfl⟩
  · left
    obtain ⟨hm, -, hlt⟩ := serveOwed_pending S.fam y.cfg c' h budget (n.hotIds y now) x o hx' hg hsh hsent
    refine ⟨_, by rw [conn_replace, hc]; rfl, hm, ?_⟩
    rw [← hix]; exact hlt hb

end

end Engine.World
