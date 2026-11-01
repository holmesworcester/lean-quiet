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

/-- A map that keeps every key: each key's first entry after it came from
that key's first entry before, with the same queue. -/
theorem find_map_back (L : List (Id × Conn)) (g : Id × Conn → Id × Conn) (cid : Id) (c' : Conn)
    (hk : ∀ q, (g q).1 = q.1) (ho : ∀ q, (g q).2.owed = q.2.owed)
    (h : ((L.map g).find? fun p => Decidable.decide (p.1 = cid)).map (·.2) = some c') :
    ∃ c, (L.find? fun p => Decidable.decide (p.1 = cid)).map (·.2) = some c ∧ c'.owed = c.owed := by
  induction L with
  | nil => cases h
  | cons p t ih =>
    by_cases e : p.1 = cid
    · simp only [List.map_cons, List.find?_cons, hk p, e, decide_true, Option.map_some, Option.some.injEq] at h
      refine ⟨p.2, by simp [List.find?_cons, e], by rw [← h, ho]⟩
    · simp only [List.map_cons, List.find?_cons, hk p, e, decide_false] at h
      obtain ⟨c, h1, h2⟩ := ih h
      exact ⟨c, by simpa [List.find?_cons, e] using h1, h2⟩

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

/-- **A frame keeps a waiting id queued, or sends its op back.** A node
whose session cid has x waiting at position p or nearer, holding x's op
in a room the session shows, takes a frame on any session from src.
After the frame x still waits at position p or nearer, or (the frame
being on cid) its op is in a frame back to src. -/
theorem onSealed_waits (n : Node) (src : ByteArray) (cid' : Id) (inner : List ByteArray) (now : Nat) (h : Held F)
    (cid x : Id) (o : Op) (r : Id) (p : Nat) (hm : n.managed = [])
    (hw : ∀ c, n.conn? cid = some c → Waits x p c) (hg : h.db.ops x = some o) (hr : S.fam.room o = some r)
    (hs : r ∈ S.rooms s cid) (hb : 0 < S.cfg.burst) :
    (∀ c', ((n.onSealed (S.sync s) src (some (cid', Codec.encode inner)) now).run h).1.1.conn? cid = some c' →
        Waits x p c') ∨
      ∃ g, o.bytes ∈ g ∧
        (src, plainFrame cid g) ∈ ((n.onSealed (S.sync s) src (some (cid', Codec.encode inner)) now).run h).1.2.send := by
  unfold Node.onSealed
  simp only [Codec.decode_encode]
  split
  · rename_i c0 hc0
    simp only [HeldM.run_bind]
    generalize hR : HeldM.run (forIn (m := HeldM F) (_ : List ByteArray)
      ((n.setAddr cid' src, {}) : Node × Acts) _) h = R
    have pR := forIn_inv hR (fun h' (st : Node × Acts) => st.1.managed = [] ∧ st.2.retry = [] ∧
        h'.db.ops x = some o ∧ st.1.addr? cid' = some src ∧ ∀ c, st.1.conn? cid = some c → Waits x p c)
      ⟨hm, rfl, hg, setAddr_addr n cid' src, fun c hc => hw c hc⟩ (fun b _ st h' ⟨hm', hr', hx', ha', hw'⟩ => by
        split
        · rename_i c hcs
          simp only [HeldM.run_bind, refresh_run, sync_fam, sync_cfg, HeldM.run_pure, ForInStep.value]
          rw [recv_reads]
          obtain ⟨-, hd, -⟩ := recv_cases S.fam S.cfg st.1.ix { c.setRooms (S.rooms s cid') with notices := [] } b now h'
          have hcs' : (st.1.conn? cid').isSome = true := by rw [hcs]; rfl
          obtain ⟨f1, f2, f3, -, f5⟩ := apply_facts S s st.1 cid' _ now h' hd hcs'
          refine ⟨by rw [f2]; exact hm', by simp [Acts.append_def, hr', f1], ?_, by rw [addr_of_addrs f3]; exact ha', ?_⟩
          · rcases (payload_run S s st.1 cid' c b now h' hcs).2 with e | ⟨o', _, _, e⟩
            · rw [e]; exact hx'
            · rw [e]; exact turnH_some _ _ _ hx'
          · intro c' hc'
            by_cases e : cid = cid'
            · subst e
              obtain ⟨-, e2, -⟩ := f5 c' hc'
              obtain ⟨add, eadd⟩ := recv_appends S.fam S.cfg st.1.ix
                { c.setRooms (S.rooms s cid) with notices := [] } b now h'
              exact (hw' c hcs).append add (by rw [e2, eadd]; rfl)
            · obtain ⟨c1, hc1, e1⟩ := apply_other_owed S s st.1 cid cid' _ now h' e c' hc'
              exact (hw' c1 hc1).same e1
        · exact ⟨hm', hr', hx', ha', hw'⟩)
    obtain ⟨k1, k2, k3, k4, k5⟩ := pR
    obtain ⟨s1, s2, s3⟩ := serveOwed_facts S s R.1.1 cid' now R.2
    have hS := serveOwed_reads S s R.1.1 cid' now R.2
    have hsv : (∀ c', ((R.1.1.serveOwed (S.sync s) cid' now).run R.2).1.1.conn? cid = some c' → Waits x p c') ∨
        (cid = cid' ∧ ((Route.conn cid, o.bytes) ∈ ((R.1.1.serveOwed (S.sync s) cid' now).run R.2).1.2.send ∨
          (Route.conn cid, o.bytes) ∈ ((R.1.1.serveOwed (S.sync s) cid' now).run R.2).1.2.serve)) := by
      by_cases e : cid = cid'
      · subst e
        cases hc1 : R.1.1.conn? cid with
        | none =>
          left; intro c' hc'
          rw [show ((R.1.1.serveOwed (S.sync s) cid now).run R.2).1.1.conn? cid = none by
            unfold Node.serveOwed; rw [hc1]; exact hc1] at hc'
          cases hc'
        | some c1 =>
          have hw1 := k5 c1 hc1
          rcases serve_moves S s (S.sync s) rfl rfl rfl R.1.1 cid now R.2 c1 hc1 x o r hw1.1 k3 hr hs
            (by cases R.1.1.addr? cid <;> exact hb) with ⟨c', hc', hm', hlt⟩ | e | e
          · left; intro c'' hc''
            rw [hc'] at hc''; cases hc''
            exact ⟨hm', Nat.le_trans (Nat.le_of_lt hlt) hw1.2⟩
          · exact Or.inr ⟨rfl, Or.inl e⟩
          · exact Or.inr ⟨rfl, Or.inr e⟩
      · left; intro c' hc'
        rw [serve_other (S.sync s) R.1.1 cid cid' now R.2 e] at hc'
        exact k5 c' hc'
    generalize HeldM.run (Node.serveOwed (S.sync s) R.1.1 cid' now) R.2 = B at hS s1 s2 s3 hsv ⊢
    rcases hsv with hw2 | ⟨rfl, hp⟩
    · left; intro c' hc'
      rw [finish_run S s B.1.1 _ now B.2 (by rw [s2, k1])] at hc'
      simp only [Node.conn?, Node.sent] at hc'
      obtain ⟨c1, hc1, e1⟩ := find_map_back B.1.1.conns _ cid c' (fun q => by cases q; rfl)
        (fun q => by cases q; dsimp only; split <;> rfl) hc'
      exact (hw2 c1 hc1).same e1
    · right
      have hp' : (Route.conn cid, o.bytes) ∈ (R.1.2 ++ B.1.2).send ∨ (Route.conn cid, o.bytes) ∈ (R.1.2 ++ B.1.2).serve := by
        rcases hp with hp | hp
        · exact Or.inl (List.mem_append_right _ hp)
        · exact Or.inr (List.mem_append_right _ hp)
      exact finish_sends S s B.1.1 (R.1.2 ++ B.1.2) now B.2 (by rw [s2, k1])
        (by simp [Acts.append_def, k2, s1]) cid _ src hp' (by rw [addr_of_addrs s3]; exact k4)
  · left; intro c' hc'; exact hw c' hc'

end

end Engine.World
