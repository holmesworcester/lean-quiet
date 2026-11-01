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

/-- The clock's step at a connection takes nothing. -/
theorem give_take (fam : Family F) (cfg : Config) : ∀ (l : List (Id × Id)) (c : Conn) (h : Held F),
    ((c.give fam cfg l : HeldM F Step) h).1.take = []
  | [], _, _ => rfl
  | (r, x) :: rest, c, h => by
    unfold Conn.give
    split
    · exact give_take fam cfg rest c h
    · simp only [HeldM.bind_apply, HeldM.pure_apply]
      exact give_take fam cfg rest _ _

theorem tickGive_take (fam : Family F) (cfg : Config) (ix : Index) (c : Conn) (now : Nat) (h : Held F) :
    ((c.tickGive fam cfg ix now : HeldM F Step).run h).1.take = [] := by
  show ((c.tickGive fam cfg ix now : HeldM F Step) h).1.take = []
  simp only [Conn.tickGive, Conn.notify, HeldM.bind_apply, HeldM.pure_apply]
  have hg := give_take fam cfg c.notices c h
  have ht : ∀ (c' : Conn) (h' : Held F), ((c'.tick fam cfg ix now : HeldM F Step) h').1.take = [] := by
    intro c' h'
    unfold Conn.tick Conn.work
    split
    · rfl
    · simp only [HeldM.bind_apply, HeldM.pure_apply, Step.pulse_take]
      split
      · unfold Conn.start; split <;> rfl
      · rfl
  split
  · exact ht _ _
  · simp only [Step.then, hg, ht, List.append_nil]

/-- Serving a queue, on any sync: the store is only read, managed sessions
and addresses stay, and no retries ride along. -/
theorem serve_facts (y : Sync F (HeldM F)) (hr : ∀ cid, Reads (y.hooks.rooms cid)) (n : Node) (cid : Id)
    (now : Nat) (h : Held F) :
    ((n.serveOwed y cid now).run h).2 = h ∧ ((n.serveOwed y cid now).run h).1.2.retry = [] ∧
      ((n.serveOwed y cid now).run h).1.1.addrs = n.addrs := by
  unfold Node.serveOwed
  split
  · exact ⟨rfl, rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl, rfl⟩
    · simp only [HeldM.run_bind, Node.refresh, HeldM.run_pure]
      rw [hr cid h]
      exact ⟨serveOwed_reads' _ _ _ _ _ h, by simp, by simp⟩

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

/-- Applying a step, either way: no retries ride along and addresses stay. -/
theorem apply_retry_addrs (n : Node) (cid : Id) (st : Step) (now : Nat) (h : Held F)
    (hc : (n.conn? cid).isSome = true) :
    ((n.apply (S.sync s) cid st now).run h).1.2.retry = [] ∧ ((n.apply (S.sync s) cid st now).run h).1.1.addrs = n.addrs := by
  cases hd : st.drop with
  | true => unfold Node.apply; simp only [hd, ↓reduceIte]; exact ⟨rfl, rfl⟩
  | false => obtain ⟨f1, -, f3, -, -⟩ := apply_facts S s n cid st now h hd hc; exact ⟨f1, f3⟩

/-- **A frame keeps a waiting id queued, or sends its op back.** A node
whose session cid has x waiting at position p or nearer, holding x's op
in a room the session shows, takes a frame on any session from src.
After the frame x still waits at position p or nearer, or (the frame
being on cid) its op is in a frame back to src. -/
theorem onSealed_waits (n : Node) (src : ByteArray) (opened : Option (Id × ByteArray)) (now : Nat) (h : Held F)
    (cid x : Id) (o : Op) (r : Id) (p : Nat) (hm : n.managed = [])
    (hw : ∀ c, n.conn? cid = some c → Waits x p c) (hg : h.db.ops x = some o) (hr : S.fam.room o = some r)
    (hs : r ∈ S.rooms s cid) (hb : 0 < S.cfg.burst) :
    (∀ c', ((n.onSealed (S.sync s) src opened now).run h).1.1.conn? cid = some c' → Waits x p c') ∨
      ∃ g, o.bytes ∈ g ∧ (src, plainFrame cid g) ∈ ((n.onSealed (S.sync s) src opened now).run h).1.2.send ∧
        ∃ bundle, opened = some (cid, bundle) := by
  unfold Node.onSealed
  split
  · left; intro c' hc'; exact hw c' hc'
  · rename_i cid' bundle
    split
    · rename_i c0 inner hc0 hdec
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
        obtain ⟨g, hg', hf⟩ := finish_sends S s B.1.1 (R.1.2 ++ B.1.2) now B.2 (by rw [s2, k1])
          (by simp [Acts.append_def, k2, s1]) cid _ src hp' (by rw [addr_of_addrs s3]; exact k4)
        exact ⟨g, hg', hf, bundle, rfl⟩
    · left; intro c' hc'; exact hw c' hc'

/-- What the tick's turns keep: no managed sessions, no retries, the op,
the session's address. -/
def TInv (cid x : Id) (o : Op) (a : ByteArray) (h : Held F) (st : Node × Acts) : Prop :=
  st.1.managed = [] ∧ st.2.retry = [] ∧ h.db.ops x = some o ∧ st.1.addr? cid = some a

/-- x waits no further back than q0. -/
def TWait (cid x : Id) (q0 : Nat) (st : Node × Acts) : Prop :=
  ∀ c, st.1.conn? cid = some c → x ∈ c.owed ∧ c.owed.idxOf x ≤ q0

/-- x has moved: the session is gone, x is strictly nearer the front than
q0, or its op is in the acts. -/
def TProg (cid x : Id) (o : Op) (q0 : Nat) (st : Node × Acts) : Prop :=
  st.1.conn? cid = none ∨ (∃ c, st.1.conn? cid = some c ∧ x ∈ c.owed ∧ c.owed.idxOf x < q0) ∨
    (Route.conn cid, o.bytes) ∈ st.2.send ∨ (Route.conn cid, o.bytes) ∈ st.2.serve

theorem Acts.retry_append (a b : Acts) : (a ++ b).retry = a.retry ++ b.retry := rfl
theorem Acts.send_append (a b : Acts) : (a ++ b).send = a.send ++ b.send := rfl
theorem Acts.serve_append (a b : Acts) : (a ++ b).serve = a.serve ++ b.serve := rfl

/-- A dropped session has no connection. -/
theorem drop_conn_none (n : Node) (cid : Id) : (n.drop cid).conn? cid = none := by
  simp only [Node.drop, Node.close, Node.conn?]
  rw [List.find?_eq_none.2]
  · rfl
  · intro q hq
    simp only [List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not] at hq
    simp [hq.2]

/-- **One turn of the tick's loop**, at session b.1's entry: its clock
step S1, applied (B), then its queue served (C). It keeps `TInv`; it keeps
x waiting or moved, and moved once moved; and at x's own session it
moves x. -/
theorem tick_turn (st : Node × Acts) (h' : Held F) (b : Id × Conn) (c : Conn) (now : Nat)
    (hcs : st.1.conn? b.1 = some c) (cid x : Id) (o : Op) (r : Id) (a : ByteArray) (q0 : Nat)
    (hi : TInv cid x o a h' st) (hwp : TWait cid x q0 st ∨ TProg cid x o q0 st)
    (hr : S.fam.room o = some r) (hs : r ∈ S.rooms s cid) (hb : 0 < S.cfg.burst)
    (S1 : Step × Held F) (hS1 : S1 = (Conn.tickGive (S.sync s).fam (S.sync s).cfg st.1.ix
      ({ c.setRooms (S.rooms s b.1) with notices := [] } : Conn) now : HeldM F Step).run h')
    (B : (Node × Acts) × Held F) (hB : B = (st.1.apply (S.sync s) b.1 S1.1 now).run S1.2)
    (C : (Node × Acts) × Held F)
    (hC : C = (B.1.1.serveOwed (B.1.1.afterActs (S.sync s) (st.2 ++ B.1.2 ++ {})) b.1 now).run B.2) :
    TInv cid x o a C.2 (C.1.1, st.2 ++ B.1.2 ++ {} ++ C.1.2) ∧
      (TWait cid x q0 (C.1.1, st.2 ++ B.1.2 ++ {} ++ C.1.2) ∨ TProg cid x o q0 (C.1.1, st.2 ++ B.1.2 ++ {} ++ C.1.2)) ∧
      (TProg cid x o q0 st → TProg cid x o q0 (C.1.1, st.2 ++ B.1.2 ++ {} ++ C.1.2)) ∧
      (b.1 = cid → TProg cid x o q0 (C.1.1, st.2 ++ B.1.2 ++ {} ++ C.1.2)) := by
  obtain ⟨i1, i2, i3, i4⟩ := hi
  have hcs' : (st.1.conn? b.1).isSome = true := by rw [hcs]; rfl
  have t1 : S1.2 = h' := by rw [hS1]; exact tickGive_reads _ _ _ _ now h'
  have t2 : S1.1.take = [] := by rw [hS1]; exact tickGive_take _ _ _ _ now h'
  have t3 : S1.1.conn.owed = c.owed := by
    rw [hS1]; exact (tickGive_q S.fam S.cfg st.1.ix ({ c.setRooms (S.rooms s b.1) with notices := [] } : Conn) now h').1
  have b1 : B.2 = h' := by rw [hB, apply_reads S s st.1 b.1 S1.1 now t2 S1.2, t1]
  have b2 : B.1.1.managed = [] := by rw [hB]; exact apply_managed S s st.1 b.1 S1.1 now S1.2 i1
  have b3 : B.1.2.retry = [] := by rw [hB]; exact (apply_retry_addrs S s st.1 b.1 S1.1 now S1.2 hcs').1
  have b4 : B.1.1.addrs = st.1.addrs := by rw [hB]; exact (apply_retry_addrs S s st.1 b.1 S1.1 now S1.2 hcs').2
  have hro : ∀ cid, Reads ((B.1.1.afterActs (S.sync s) (st.2 ++ B.1.2 ++ {})).hooks.rooms cid) :=
    fun cid h => rfl
  obtain ⟨c1, c2, c3⟩ := serve_facts (B.1.1.afterActs (S.sync s) (st.2 ++ B.1.2 ++ {})) hro B.1.1 b.1 now B.2
  rw [← hC] at c1 c2 c3
  have c4 : C.1.1.managed = [] := by rw [hC, serveOwed_managed]; exact b2
  have inv' : TInv cid x o a C.2 (C.1.1, st.2 ++ B.1.2 ++ {} ++ C.1.2) := by
    refine ⟨c4, ?_, ?_, ?_⟩
    · show (st.2 ++ B.1.2 ++ {} ++ C.1.2).retry = []
      rw [Acts.retry_append, Acts.retry_append, Acts.retry_append, i2, b3, c2]; rfl
    · show C.2.db.ops x = some o
      rw [c1, b1]; exact i3
    · show C.1.1.addr? cid = some a
      rw [addr_of_addrs c3, addr_of_addrs b4]; exact i4
  have keepE : ((Route.conn cid, o.bytes) ∈ st.2.send ∨ (Route.conn cid, o.bytes) ∈ st.2.serve) →
      ((Route.conn cid, o.bytes) ∈ (st.2 ++ B.1.2 ++ {} ++ C.1.2).send ∨
        (Route.conn cid, o.bytes) ∈ (st.2 ++ B.1.2 ++ {} ++ C.1.2).serve) := by
    intro e
    rw [Acts.send_append, Acts.send_append, Acts.send_append, Acts.serve_append, Acts.serve_append, Acts.serve_append]
    rcases e with e | e
    · exact Or.inl (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ e)))
    · exact Or.inr (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ e)))
  have newE : ((Route.conn cid, o.bytes) ∈ C.1.2.send ∨ (Route.conn cid, o.bytes) ∈ C.1.2.serve) →
      ((Route.conn cid, o.bytes) ∈ (st.2 ++ B.1.2 ++ {} ++ C.1.2).send ∨
        (Route.conn cid, o.bytes) ∈ (st.2 ++ B.1.2 ++ {} ++ C.1.2).serve) := by
    intro e
    rw [Acts.send_append, Acts.send_append, Acts.send_append, Acts.serve_append, Acts.serve_append, Acts.serve_append]
    rcases e with e | e
    · exact Or.inl (List.mem_append_right _ e)
    · exact Or.inr (List.mem_append_right _ e)
  by_cases hk : b.1 = cid
  · -- x's own session: the clock step keeps the queue, then serving moves x
    have prog : TProg cid x o q0 (C.1.1, st.2 ++ B.1.2 ++ {} ++ C.1.2) := by
      cases hBc : B.1.1.conn? cid with
      | none =>
        left
        show C.1.1.conn? cid = none
        rw [hC]; unfold Node.serveOwed; rw [hk, hBc]; exact hBc
      | some cB =>
        have hdrop : S1.1.drop = false := by
          cases e : S1.1.drop with
          | false => rfl
          | true =>
            exfalso
            have : B.1.1 = st.1.drop b.1 := by rw [hB]; unfold Node.apply; simp [e]
            rw [this, ← hk, drop_conn_none] at hBc; cases hBc
        obtain ⟨-, -, -, -, f5⟩ := apply_facts S s st.1 b.1 S1.1 now S1.2 hdrop hcs'
        rw [← hB, hk] at f5
        have hcB : cB.owed = c.owed := by rw [(f5 cB hBc).2.1, t3]
        have hcs2 : st.1.conn? cid = some c := by rw [← hk]; exact hcs
        have hbud : 0 < ((B.1.1.addr? b.1).bind (B.1.1.afterActs (S.sync s) (st.2 ++ B.1.2 ++ {})).room).getD
            (B.1.1.afterActs (S.sync s) (st.2 ++ B.1.2 ++ {})).cfg.burst := by
          cases B.1.1.addr? b.1 <;> simp [Node.afterActs, hb, Engine.Sync.Setup.sync]
        have hx : x ∈ cB.owed ∧ (cB.owed.idxOf x ≤ q0 ∨ cB.owed.idxOf x < q0) ∨
            ((Route.conn cid, o.bytes) ∈ st.2.send ∨ (Route.conn cid, o.bytes) ∈ st.2.serve) := by
          rcases hwp with hw | hn | ⟨c2', hc2', hx2, hl2⟩ | e
          · obtain ⟨hxc, hic⟩ := hw c hcs2
            exact Or.inl ⟨by rw [hcB]; exact hxc, Or.inl (by rw [hcB]; exact hic)⟩
          · rw [hcs2] at hn; cases hn
          · rw [hcs2] at hc2'; cases hc2'
            exact Or.inl ⟨by rw [hcB]; exact hx2, Or.inr (by rw [hcB]; exact hl2)⟩
          · exact Or.inr e
        rcases hx with ⟨hxc, hle⟩ | e
        · have hBc' : B.1.1.conn? b.1 = some cB := by rw [hk]; exact hBc
          rcases serve_moves S s (B.1.1.afterActs (S.sync s) (st.2 ++ B.1.2 ++ {})) rfl rfl rfl B.1.1 b.1 now B.2 cB hBc'
              x o r hxc (by rw [b1]; exact i3) hr (by rw [hk]; exact hs) hbud with ⟨c', hc', hm', hlt⟩ | e | e
          · right; left
            refine ⟨c', by show C.1.1.conn? cid = some c'; rw [hC, ← hk]; exact hc', hm', ?_⟩
            rcases hle with hle | hle <;> omega
          · right; right; rw [← hC, hk] at e; exact newE (Or.inl e)
          · right; right; rw [← hC, hk] at e; exact newE (Or.inr e)
        · right; right; exact keepE e
    exact ⟨inv', Or.inr prog, fun _ => prog, fun _ => prog⟩
  · -- another session: x's session is as it was
    have back : ∀ c', C.1.1.conn? cid = some c' → ∃ c, st.1.conn? cid = some c ∧ c'.owed = c.owed := by
      intro c' hc'
      have hc'' : B.1.1.conn? cid = some c' := by
        rw [hC, serve_other (B.1.1.afterActs (S.sync s) (st.2 ++ B.1.2 ++ {})) B.1.1 cid b.1 now B.2
          (fun e => hk e.symm)] at hc'
        exact hc'
      rw [hB] at hc''
      exact apply_other_owed S s st.1 cid b.1 S1.1 now S1.2 (fun e => hk e.symm) c' hc''
    have keepW : TWait cid x q0 st → TWait cid x q0 (C.1.1, st.2 ++ B.1.2 ++ {} ++ C.1.2) := by
      intro hw c' hc'
      obtain ⟨c1', hc1', e1⟩ := back c' hc'
      rw [e1]; exact hw c1' hc1'
    have keepP : TProg cid x o q0 st → TProg cid x o q0 (C.1.1, st.2 ++ B.1.2 ++ {} ++ C.1.2) := by
      intro hp
      cases hc' : C.1.1.conn? cid with
      | none => exact Or.inl hc'
      | some c' =>
        obtain ⟨c1', hc1', e1⟩ := back c' hc'
        rcases hp with hn | ⟨c2', hc2', hx2, hl2⟩ | e
        · rw [hc1'] at hn; cases hn
        · rw [hc1'] at hc2'; cases hc2'
          exact Or.inr (Or.inl ⟨c', hc', by rw [e1]; exact hx2, by rw [e1]; exact hl2⟩)
        · exact Or.inr (Or.inr (keepE e))
    exact ⟨inv', hwp.imp keepW keepP, keepP, fun e => absurd e hk⟩

/-- **A tick moves a waiting id forward, or sends its op.** -/
theorem onTick_moves (n : Node) (now : Nat) (h : Held F) (cid x : Id) (o : Op) (r : Id) (c0 : Conn) (a : ByteArray)
    (hc0 : n.conn? cid = some c0) (hx0 : x ∈ c0.owed) (hm : n.managed = []) (ha : n.addr? cid = some a)
    (hg : h.db.ops x = some o) (hr : S.fam.room o = some r) (hs : r ∈ S.rooms s cid) (hb : 0 < S.cfg.burst) :
    ((n.onTick (S.sync s) now).run h).1.1.conn? cid = none ∨
      (∃ c', ((n.onTick (S.sync s) now).run h).1.1.conn? cid = some c' ∧ x ∈ c'.owed ∧
        c'.owed.idxOf x < c0.owed.idxOf x) ∨
      ∃ g, o.bytes ∈ g ∧ (a, plainFrame cid g) ∈ ((n.onTick (S.sync s) now).run h).1.2.send := by
  have hd : (S.sync s).deferredRetries = false := rfl
  unfold Node.onTick
  rw [hd]
  unfold Node.onTickDirect
  simp only [Bool.false_eq_true, ↓reduceIte, HeldM.run_bind, sync_dial, HeldM.run_pure, store_nil]
  generalize hR : HeldM.run (forIn (m := HeldM F) n.conns ((n, {}) : Node × Acts) _) h = R
  obtain ⟨ent, hent, hk⟩ : ∃ ent, ent ∈ n.conns ∧ ent.1 = cid := by
    unfold Node.conn? at hc0
    cases e : n.conns.find? (fun p => Decidable.decide (p.1 = cid)) with
    | none => rw [e] at hc0; cases hc0
    | some q =>
      refine ⟨q, List.mem_of_find?_eq_some e, ?_⟩
      have := List.find?_some e; simpa using this
  have key : TInv cid x o a R.2 R.1 ∧ TProg cid x o (c0.owed.idxOf x) R.1 := by
    rw [← hR]
    refine forIn_after _ (fun h' st => TInv cid x o a h' st ∧
        (TWait cid x (c0.owed.idxOf x) st ∨ TProg cid x o (c0.owed.idxOf x) st))
      (fun h' st => TInv cid x o a h' st ∧ TProg cid x o (c0.owed.idxOf x) st) ent n.conns ?_ ?_ ?_ ?_ hent _ h
      ⟨⟨hm, rfl, hg, ha⟩, Or.inl (fun c hc => by rw [hc0] at hc; cases hc; exact ⟨hx0, Nat.le_refl _⟩)⟩
    · intro b _ st h'
      split
      · exact ⟨_, rfl⟩
      · simp only [HeldM.run_bind, refresh_run]
        split
        · exact ⟨_, rfl⟩
        · simp only [HeldM.run_bind]; rw [sweep_none _ rfl]; simp only [HeldM.run_pure]; exact ⟨_, rfl⟩
    · intro b _ st h' ⟨hi, hwp⟩
      split
      · exact ⟨hi, hwp⟩
      · rename_i c hcs
        simp only [HeldM.run_bind, refresh_run]
        split
        · exact ⟨hi, hwp⟩
        · simp only [HeldM.run_bind]
          generalize hS1 : HeldM.run (Conn.tickGive _ _ _ _ now) h' = S1
          generalize hB : HeldM.run (Node.apply (S.sync s) st.1 b.1 S1.1 now) S1.2 = B
          rw [sweep_none _ rfl]
          simp only [HeldM.run_pure, ForInStep.value]
          generalize hC : HeldM.run (Node.serveOwed _ B.1.1 b.1 now) B.2 = C
          obtain ⟨t1, t2, -, -⟩ := tick_turn S s st h' b c now hcs cid x o r a _ hi hwp hr hs hb
            S1 hS1.symm B hB.symm C hC.symm
          exact ⟨t1, t2⟩
    · intro b _ st h' ⟨hi, hwp⟩ ⟨_, hp⟩
      split
      · exact ⟨hi, hp⟩
      · rename_i c hcs
        simp only [HeldM.run_bind, refresh_run]
        split
        · exact ⟨hi, hp⟩
        · simp only [HeldM.run_bind]
          generalize hS1 : HeldM.run (Conn.tickGive _ _ _ _ now) h' = S1
          generalize hB : HeldM.run (Node.apply (S.sync s) st.1 b.1 S1.1 now) S1.2 = B
          rw [sweep_none _ rfl]
          simp only [HeldM.run_pure, ForInStep.value]
          generalize hC : HeldM.run (Node.serveOwed _ B.1.1 b.1 now) B.2 = C
          obtain ⟨t1, -, t3, -⟩ := tick_turn S s st h' b c now hcs cid x o r a _ hi hwp hr hs hb
            S1 hS1.symm B hB.symm C hC.symm
          exact ⟨t1, t3 hp⟩
    · intro st h' ⟨hi, hwp⟩
      split
      · rename_i hcn
        refine ⟨hi, Or.inl ?_⟩
        rw [hk] at hcn; exact hcn
      · rename_i c hcs
        simp only [HeldM.run_bind, refresh_run]
        split
        · rename_i hcont
          exfalso; simp [Engine.Sync.Setup.sync] at hcont
        · simp only [HeldM.run_bind]
          generalize hS1 : HeldM.run (Conn.tickGive _ _ _ _ now) h' = S1
          generalize hB : HeldM.run (Node.apply (S.sync s) st.1 ent.1 S1.1 now) S1.2 = B
          rw [sweep_none _ rfl]
          simp only [HeldM.run_pure, ForInStep.value]
          generalize hC : HeldM.run (Node.serveOwed _ B.1.1 ent.1 now) B.2 = C
          obtain ⟨t1, -, -, t4⟩ := tick_turn S s st h' ent c now hcs cid x o r a _ hi hwp hr hs hb
            S1 hS1.symm B hB.symm C hC.symm
          exact ⟨t1, t4 hk⟩
  obtain ⟨⟨k1, k2, k3, k4⟩, kp⟩ := key
  rcases kp with hn | ⟨c', hc', hxc, hlt⟩ | e
  · left
    cases hf : ((R.1.1.finish (S.sync s) R.1.2 now).run R.2).1.1.conn? cid with
    | none => rfl
    | some c'' =>
      exfalso
      rw [finish_run S s R.1.1 _ now R.2 k1] at hf
      simp only [Node.conn?, Node.sent] at hf
      obtain ⟨c1, hc1, -⟩ := find_map_back R.1.1.conns _ cid c'' (fun q => by cases q; rfl)
        (fun q => by cases q; dsimp only; split <;> rfl) hf
      simp only [Node.conn?] at hn
      rw [hn] at hc1; cases hc1
  · right; left
    obtain ⟨c'', hc'', e⟩ := finish_conn S s R.1.1 R.1.2 now R.2 k1 cid c' hc'
    exact ⟨c'', hc'', by rw [e]; exact hxc, by rw [e]; exact hlt⟩
  · right; right
    exact finish_sends S s R.1.1 R.1.2 now R.2 k1 k2 cid _ a e k4

/-- The end of an entry point: a session after it was a session before,
with the same queue. -/
theorem finish_back (n : Node) (out : Acts) (now : Nat) (h : Held F) (hm : n.managed = []) (cid : Id) (c' : Conn)
    (hc' : ((n.finish (S.sync s) out now).run h).1.1.conn? cid = some c') :
    ∃ c, n.conn? cid = some c ∧ c'.owed = c.owed := by
  rw [finish_run S s n out now h hm] at hc'
  simp only [Node.conn?, Node.sent] at hc'
  exact find_map_back n.conns _ cid c' (fun q => by cases q; rfl) (fun q => by cases q; dsimp only; split <;> rfl) hc'

theorem store_back (n : Node) (ops : List Op) (mine : Bool) (h : Held F) (cid : Id) (c' : Conn)
    (hc' : ((n.store (S.sync s) ops mine).run h).1.1.conn? cid = some c') :
    ∃ c, n.conn? cid = some c ∧ c'.owed = c.owed := by
  obtain ⟨c, hc, -, e, -⟩ := (store_facts S s n ops mine h).2.2.2 cid c' hc'
  exact ⟨c, hc, e⟩

/-- **A local write keeps a waiting id where it was.** -/
theorem onWrite_waits (n : Node) (ops : List Op) (now : Nat) (h : Held F) (cid x : Id) (p : Nat) (hm : n.managed = [])
    (hw : ∀ c, n.conn? cid = some c → Waits x p c) :
    ∀ c', ((n.onWrite (S.sync s) ops now).run h).1.1.conn? cid = some c' → Waits x p c' := by
  intro c' hc'
  unfold Node.onWrite at hc'
  simp only [HeldM.run_bind] at hc'
  obtain ⟨c1, hc1, e1⟩ := finish_back S s _ _ now _ (by rw [heat_managed, store_keeps]; exact hm) cid c' hc'
  obtain ⟨c2, hc2, e2⟩ := store_back S s n ops true h cid c1 hc1
  exact (hw c2 hc2).same (e1.trans e2)

/-- **A transport close keeps a waiting id where it was, or ends its
session.** -/
theorem onClose_waits (n : Node) (addr : ByteArray) (now : Nat) (h : Held F) (cid x : Id) (p : Nat)
    (hm : n.managed = []) (hw : ∀ c, n.conn? cid = some c → Waits x p c) :
    ∀ c', ((n.onClose (S.sync s) addr now).run h).1.1.conn? cid = some c' → Waits x p c' := by
  intro c' hc'
  unfold Node.onClose at hc'
  have hdm : ∀ (L : List Id) (m : Node), m.managed = [] → (L.foldl Node.drop m).managed = [] := by
    intro L
    induction L with
    | nil => intro m h; exact h
    | cons a t ih => intro m h; exact ih _ (drop_managed m a h)
  obtain ⟨c1, hc1, e1⟩ := finish_back S s _ _ now _ (hdm _ n hm) cid c' hc'
  have back : ∀ (L : List Id) (m : Node) (c : Conn), (L.foldl Node.drop m).conn? cid = some c → m.conn? cid = some c := by
    intro L
    induction L with
    | nil => intro m c h; exact h
    | cons a t ih =>
      intro m c h; rw [List.foldl_cons] at h
      have h2 : (m.drop a).conn? cid = some c := ih _ c h
      exact close_conn m a cid c h2
  exact (hw c1 (back _ n c1 hc1)).same e1

/-- **Opening another session keeps a waiting id where it was.** -/
theorem connect_waits (n : Node) (cid' : Id) (a : ByteArray) (dialer : Bool) (now : Nat) (h : Held F) (cid x : Id)
    (p : Nat) (hne : cid ≠ cid') (hm : n.managed = []) (hw : ∀ c, n.conn? cid = some c → Waits x p c) :
    ∀ c', ((n.connect (S.sync s) cid' a dialer now).run h).1.1.conn? cid = some c' → Waits x p c' := by
  intro c' hc'
  unfold Node.connect Node.open at hc'
  simp only [HeldM.run_bind, sync_rooms, HeldM.run_pure] at hc'
  obtain ⟨c1, hc1, e1⟩ := finish_back S s _ _ now _ (by simp [Node.close, Node.setAddr, hm]) cid c' hc'
  have hne' : ¬ cid' = cid := fun e => hne e.symm
  simp only [Node.conn?, Node.setAddr, List.find?_cons, hne', decide_false] at hc1
  exact (hw c1 (close_conn n cid' cid c1 hc1)).same e1

/-- **A frame keeps a waiting id where it was, or sends its op back.** -/
theorem onFrame_waits (n : Node) (src bytes : ByteArray) (now : Nat) (h : Held F) (cid x : Id) (o : Op) (r : Id)
    (p : Nat) (hm : n.managed = []) (hw : ∀ c, n.conn? cid = some c → Waits x p c) (hg : h.db.ops x = some o)
    (hr : S.fam.room o = some r) (hs : r ∈ S.rooms s cid) (hb : 0 < S.cfg.burst) :
    (∀ c', ((n.onFrame (S.sync s) src bytes now).run h).1.1.conn? cid = some c' → Waits x p c') ∨
      ∃ g, o.bytes ∈ g ∧ (src, plainFrame cid g) ∈ ((n.onFrame (S.sync s) src bytes now).run h).1.2.send ∧
        bytes[0]? = some 1 ∧ ∃ bundle, (Codec.decode (bytes.extract 1 bytes.size) : Option (Id × ByteArray)) = some (cid, bundle) := by
  unfold Node.onFrame
  split
  · dsimp only
    split
    · exact Or.inl hw
    · split
      · exact Or.inl hw
      · left; intro c' hc'
        simp only [HeldM.run_bind] at hc'
        obtain ⟨c1, hc1, e1⟩ := finish_back S s _ _ now _ (by rw [store_keeps, write_keeps]; exact hm) cid c' hc'
        obtain ⟨c2, hc2, e2⟩ := store_back S s _ _ true _ cid c1 hc1
        simp only [Node.conn?] at hc2
        rw [write_conns] at hc2
        exact (hw c2 hc2).same (e1.trans e2)
  · rename_i htag
    simp only [HeldM.run_bind, sync_openFrame, plainOpen, HeldM.run_pure]
    rcases onSealed_waits S s n src _ now h cid x o r p hm hw hg hr hs hb with e | ⟨g, hg', hf, bundle, hb'⟩
    · exact Or.inl e
    · exact Or.inr ⟨g, hg', hf, htag, bundle, hb'⟩
  · exact Or.inl hw

end

namespace Plain
variable {Q : Plain F}

/-- **The session's frames come from its peer:** every frame on session
cid delivered to a from step k on says it comes from b. (The harness
opens cid only between a and b; a node seals frames on a session only
for its own connection.) -/
def FromPeer (E : Q.Run) (a b : Fin Q.n) (cid : Id) (k : Nat) : Prop :=
  ∀ m idx t p, k ≤ m → E.act m = .deliver idx t → (E.world m).flight[idx]? = some p → Q.setup.at? p.dst = some a →
    p.bytes[0]? = some 1 →
    (∃ bundle, (Codec.decode (p.bytes.extract 1 p.bytes.size) : Option (Id × ByteArray)) = some (cid, bundle)) →
    p.origin = Q.addr b

/-- An entry point at another node leaves node a as it was. -/
theorem enter_other (w : World (Held F) Q.n) (i a : Fin Q.n) (t : Nat) (f : Node → HeldM F (Node × Effects))
    (hne : a ≠ i) : (w.enter Q.setup i t f).node a = w.node a := by
  simp only [World.enter]; exact upd_other _ _ hne

theorem enter_self_node (w : World (Held F) Q.n) (i : Fin Q.n) (t : Nat) (f : Node → HeldM F (Node × Effects)) :
    (w.enter Q.setup i t f).node i = ((f (w.node i)).run (w.box i)).1.1 := by
  simp only [World.enter, upd_same]

/-- **One step keeps a waiting id where it was, or sends its op to the
peer**, whatever the act, in an execution with no attacker: x waits in
a's queue for session cid, a holds x's op in a room the session shows,
and no step reopens cid at a. -/
theorem step_waits (E : Q.Run) (k : Nat) (a b : Fin Q.n) (cid x : Id) (o : Op) (r : Id) (p : Nat)
    (hm : ((E.world k).node a).managed = []) (hw : ∀ c, ((E.world k).node a).conn? cid = some c → Waits x p c)
    (hg : ((E.world k).box a).db.ops x = some o) (hr : Q.fam.room o = some r) (hs : r ∈ Q.rooms a cid)
    (hb : 0 < Q.cfg.burst) (hnc : ∀ j dl t, E.act k ≠ .connect a j cid dl t) (hfp : FromPeer E a b cid k)
    (ha : ((E.world k).node a).addr? cid = some (Q.addr b)) (hcs : (((E.world k).node a).conn? cid).isSome = true) :
    (∀ c', ((E.world (k + 1)).node a).conn? cid = some c' → Waits x p c') ∨
      ∃ sr g, o.bytes ∈ g ∧
        (⟨sr, some a, Q.addr a, Q.addr b, plainFrame cid g, (E.world (k + 1)).now⟩ : Packet Q.n) ∈
          (E.world (k + 1)).flight := by
  have hlegal := E.legal k
  rw [Exec.world_succ]
  cases hact : E.act k with
  | deliver idx t =>
    rw [hact] at hlegal
    cases hp : (E.world k).flight[idx]? with
    | none =>
      left; intro c' hc'
      simp only [World.step, hp] at hc'
      exact hw c' hc'
    | some q =>
      cases hj : Q.setup.at? q.dst with
      | none =>
        left; intro c' hc'
        simp only [World.step, hp, hj] at hc'
        exact hw c' hc'
      | some j =>
        by_cases e : a = j
        · subst e
          rcases onFrame_waits (Q.two a) .a ((E.world k).node a) q.origin q.bytes t ((E.world k).box a) cid x o r p
              hm hw hg hr hs hb with e1 | ⟨g, hg', hf, htag, hdec⟩
          · left; intro c' hc'
            rw [deliver_node _ idx t q a hp hj] at hc'
            exact e1 c' hc'
          · right
            have hor : q.origin = Q.addr b := hfp k idx t q (Nat.le_refl _) hact hp hj htag hdec
            obtain ⟨sr, hsr⟩ := deliver_sends (E.world k) idx t q a hp hj _ _ hf
            rw [hor] at hsr
            exact ⟨sr, g, hg', by rw [deliver_now _ idx t q a hp hj]; exact hsr⟩
        · left; intro c' hc'
          simp only [World.step, hp, hj] at hc'
          rw [enter_other _ j a t _ e] at hc'
          exact hw c' hc'
  | dup idx =>
    left; intro c' hc'
    simp only [World.step] at hc'
    cases hp : (E.world k).flight[idx]? with
    | none => rw [hp] at hc'; exact hw c' hc'
    | some q => rw [hp] at hc'; exact hw c' hc'
  | drop idx => left; intro c' hc'; simp only [World.step] at hc'; exact hw c' hc'
  | tick i t =>
    by_cases e : a = i
    · subst e
      cases hc : ((E.world k).node a).conn? cid with
      | none => rw [hc] at hcs; cases hcs
      | some c =>
        rcases onTick_moves (Q.two a) .a ((E.world k).node a) t ((E.world k).box a) cid x o r c (Q.addr b) hc
            (hw c hc).1 hm ha hg hr hs hb with e1 | ⟨c', hc', hxc, hlt⟩ | ⟨g, hg', hf⟩
        · left; intro c' hc'
          simp only [World.step] at hc'; rw [enter_self_node] at hc'
          rw [e1] at hc'; cases hc'
        · left; intro c'' hc''
          simp only [World.step] at hc''; rw [enter_self_node] at hc''
          rw [hc'] at hc''; cases hc''
          exact ⟨hxc, Nat.le_trans (Nat.le_of_lt hlt) (hw c hc).2⟩
        · right
          obtain ⟨sr, hsr⟩ := enter_sends (E.world k) a t (fun nd => nd.onTick ((Q.two a).sync .a) t) _ _ hf
          refine ⟨sr, g, hg', ?_⟩
          simp only [World.step]
          simp only [World.enter] at hsr ⊢
          exact hsr
    · left; intro c' hc'
      simp only [World.step] at hc'; rw [enter_other _ i a t _ e] at hc'; exact hw c' hc'
  | write i ops t =>
    by_cases e : a = i
    · subst e; left; intro c' hc'
      simp only [World.step] at hc'; rw [enter_self_node] at hc'
      exact onWrite_waits (Q.two a) .a _ ops t _ cid x p hm hw c' hc'
    · left; intro c' hc'
      simp only [World.step] at hc'; rw [enter_other _ i a t _ e] at hc'; exact hw c' hc'
  | restart i t =>
    left; intro c' hc'
    simp only [World.step] at hc'
    by_cases e : a = i
    · subst e; rw [upd_same] at hc'; simp [Node.boot, Node.conn?] at hc'
    · rw [upd_other _ _ e] at hc'; exact hw c' hc'
  | close i ad t =>
    by_cases e : a = i
    · subst e; left; intro c' hc'
      simp only [World.step] at hc'; rw [enter_self_node] at hc'
      exact onClose_waits (Q.two a) .a _ ad t _ cid x p hm hw c' hc'
    · left; intro c' hc'
      simp only [World.step] at hc'; rw [enter_other _ i a t _ e] at hc'; exact hw c' hc'
  | connect i j cid' dl t =>
    by_cases e : a = i
    · subst e
      have hne : cid ≠ cid' := fun e' => hnc j dl t (by rw [hact, e'])
      left; intro c' hc'
      simp only [World.step] at hc'; rw [enter_self_node] at hc'
      exact connect_waits (Q.two a) .a _ cid' _ dl t _ cid x p hne hm hw c' hc'
    · left; intro c' hc'
      simp only [World.step] at hc'; rw [enter_other _ i a t _ e] at hc'; exact hw c' hc'
  | inject i o' b' t =>
    rw [hact] at hlegal
    exact absurd hlegal.1 (by simp [noAdv])

/-- **The holder's tick moves a waiting id strictly forward, or sends
its op to the peer.** -/
theorem tick_moves_world (E : Q.Run) (k : Nat) (a b : Fin Q.n) (cid x : Id) (o : Op) (r : Id) (t : Nat)
    (hact : E.act k = .tick a t) (c : Conn) (hc : ((E.world k).node a).conn? cid = some c) (hxc : x ∈ c.owed)
    (hm : ((E.world k).node a).managed = []) (ha : ((E.world k).node a).addr? cid = some (Q.addr b))
    (hg : ((E.world k).box a).db.ops x = some o) (hr : Q.fam.room o = some r) (hs : r ∈ Q.rooms a cid)
    (hb : 0 < Q.cfg.burst) :
    ((E.world (k + 1)).node a).conn? cid = none ∨
      (∃ c', ((E.world (k + 1)).node a).conn? cid = some c' ∧ x ∈ c'.owed ∧ c'.owed.idxOf x < c.owed.idxOf x) ∨
      ∃ sr g, o.bytes ∈ g ∧
        (⟨sr, some a, Q.addr a, Q.addr b, plainFrame cid g, (E.world (k + 1)).now⟩ : Packet Q.n) ∈
          (E.world (k + 1)).flight := by
  rw [Exec.world_succ, hact]
  rcases onTick_moves (Q.two a) .a ((E.world k).node a) t ((E.world k).box a) cid x o r c (Q.addr b) hc hxc hm ha hg hr
      hs hb with e1 | ⟨c', hc', hxc', hlt⟩ | ⟨g, hg', hf⟩
  · left; simp only [World.step]; rw [enter_self_node]; exact e1
  · right; left; refine ⟨c', ?_, hxc', hlt⟩; simp only [World.step]; rw [enter_self_node]; exact hc'
  · right; right
    obtain ⟨sr, hsr⟩ := enter_sends (E.world k) a t (fun nd => nd.onTick ((Q.two a).sync .a) t) _ _ hf
    refine ⟨sr, g, hg', ?_⟩
    simp only [World.step]
    simp only [World.enter] at hsr ⊢
    exact hsr

/-- **The queue drains in ticks.** At its holder a, from step k after gst,
x waits at position p of session cid's queue; a holds x's op in a room the
session shows, stays online, keeps the session open to b, and nobody
reopens cid at a; the session's frames come from b. Then within
(p + 1) · τ, x's op is in flight from a to b on the session. -/
theorem drain (E : Q.Run) {N : Net Q.n} (hN : N.Admits E) {a b : Fin Q.n} {cid r x : Id} {o : Op} {k T : Nat}
    (hJ : ∀ m, k ≤ m → (((E.world m).node a).conn? cid).isSome = true)
    (haddr : ∀ m, k ≤ m → ((E.world m).node a).addr? cid = some (Q.addr b))
    (hm : ∀ m, ((E.world m).node a).managed = [])
    (hnc : ∀ m j dl t, k ≤ m → E.act m ≠ .connect a j cid dl t) (hfp : FromPeer E a b cid k)
    (hx : ∀ m, k ≤ m → ((E.world m).box a).db.ops x = some o) (hr : Q.fam.room o = some r)
    (hs : r ∈ Q.rooms a cid) (hb : 0 < Q.cfg.burst) (hgst : N.gst ≤ (E.world k).now) (hup : N.Up a (E.world k).now T) :
    ∀ (p : Nat), (∀ c, ((E.world k).node a).conn? cid = some c → Waits x p c) →
      (E.world k).now + (p + 1) * N.τ ≤ T →
      ∃ m sr g, k ≤ m ∧ (E.world (m + 1)).now ≤ (E.world k).now + (p + 1) * N.τ ∧ o.bytes ∈ g ∧
        (⟨sr, some a, Q.addr a, Q.addr b, plainFrame cid g, (E.world (m + 1)).now⟩ : Packet Q.n) ∈
          (E.world (m + 1)).flight := by
  have tick_now : ∀ k1 t1, E.act k1 = .tick a t1 → (E.world (k1 + 1)).now = t1 := by
    intro k1 t1 h1; rw [Exec.world_succ, h1]; simp only [World.step, World.enter]
  suffices H : ∀ p k', k ≤ k' → (∀ c, ((E.world k').node a).conn? cid = some c → Waits x p c) →
      (E.world k').now + (p + 1) * N.τ ≤ T →
      ∃ m sr g, k' ≤ m ∧ (E.world (m + 1)).now ≤ (E.world k').now + (p + 1) * N.τ ∧ o.bytes ∈ g ∧
        (⟨sr, some a, Q.addr a, Q.addr b, plainFrame cid g, (E.world (m + 1)).now⟩ : Packet Q.n) ∈
          (E.world (m + 1)).flight by
    intro p hw hT
    obtain ⟨m, sr, g, hkm, ht, hg', hf⟩ := H p k (Nat.le_refl _) hw hT
    exact ⟨m, sr, g, hkm, ht, hg', hf⟩
  intro p
  induction p using Nat.strongRecOn with
  | ind p ih =>
  intro k' hk' hw hT
  have hnow : (E.world k).now ≤ (E.world k').now := Exec.now_mono E hk'
  have hg' : N.gst ≤ (E.world k').now := Nat.le_trans hgst hnow
  have hupk : N.Up a (E.world k').now ((E.world k').now + N.τ) := fun t h1 h2 =>
    hup t (by omega) (by have := Nat.le_mul_of_pos_left N.τ (show 0 < p + 1 by omega); omega)
  obtain ⟨k1, t1, hk1, hact1, ht1⟩ := hN.ticks a k' hg' hupk
  -- until the tick, x keeps waiting, or its op goes out
  have walk : ∀ d, k' + d ≤ k1 → (∀ c, ((E.world (k' + d)).node a).conn? cid = some c → Waits x p c) ∨
      ∃ m sr g, k' ≤ m ∧ m < k' + d ∧ o.bytes ∈ g ∧
        (⟨sr, some a, Q.addr a, Q.addr b, plainFrame cid g, (E.world (m + 1)).now⟩ : Packet Q.n) ∈
          (E.world (m + 1)).flight := by
    intro d
    induction d with
    | zero => intro _; exact Or.inl hw
    | succ d ihd =>
      intro hd
      rcases ihd (by omega) with hwd | ⟨m, sr, g, h1, h2, hg2, hf2⟩
      · rcases step_waits E (k' + d) a b cid x o r p (hm _) hwd (hx _ (by omega)) hr hs hb
            (fun j dl t => hnc _ j dl t (by omega))
            (fun m idx t q hmq => hfp m idx t q (by omega)) (haddr _ (by omega)) (hJ _ (by omega)) with
          e | ⟨sr, g, hg2, hf2⟩
        · left; rw [show k' + (d + 1) = k' + d + 1 by omega]; exact e
        · exact Or.inr ⟨k' + d, sr, g, by omega, by omega, hg2, hf2⟩
      · exact Or.inr ⟨m, sr, g, h1, by omega, hg2, hf2⟩
  have hk1' : k1 = k' + (k1 - k') := by omega
  have hnow1 : (E.world k1).now ≤ t1 := by
    have := E.legal k1; rw [hact1] at this; exact this
  rcases walk (k1 - k') (by omega) with hw1 | ⟨m, sr, g, h1, h2, hg2, hf2⟩
  · rw [← hk1'] at hw1
    obtain ⟨c1, hc1⟩ := Option.isSome_iff_exists.1 (hJ k1 (by omega))
    obtain ⟨hxc1, hic1⟩ := hw1 c1 hc1
    rcases tick_moves_world E k1 a b cid x o r t1 hact1 c1 hc1 hxc1 (hm k1) (haddr k1 (by omega)) (hx k1 (by omega))
        hr hs hb with hn | ⟨c', hc', hxc', hlt⟩ | ⟨sr, g, hg2, hf2⟩
    · have := hJ (k1 + 1) (by omega); rw [hn] at this; cases this
    · -- strictly forward: one position fewer, from the step after the tick
      have hp : 0 < p := by omega
      have hw2 : ∀ c, ((E.world (k1 + 1)).node a).conn? cid = some c → Waits x (p - 1) c := by
        intro c hc; rw [hc'] at hc; cases hc; exact ⟨hxc', by omega⟩
      have hT2 : (E.world (k1 + 1)).now + (p - 1 + 1) * N.τ ≤ T := by
        rw [tick_now k1 t1 hact1, show p - 1 + 1 = p by omega]
        have : (p + 1) * N.τ = p * N.τ + N.τ := Nat.succ_mul p N.τ
        omega
      obtain ⟨m, sr, g, h1, h2, hg2, hf2⟩ := ih (p - 1) (by omega) (k1 + 1) (by omega) hw2 hT2
      refine ⟨m, sr, g, by omega, ?_, hg2, hf2⟩
      rw [tick_now k1 t1 hact1, show p - 1 + 1 = p by omega] at h2
      have : (p + 1) * N.τ = p * N.τ + N.τ := Nat.succ_mul p N.τ
      omega
    · refine ⟨k1, sr, g, by omega, ?_, hg2, hf2⟩
      rw [tick_now k1 t1 hact1]
      have := Nat.le_mul_of_pos_left N.τ (show 0 < p + 1 by omega)
      omega
  · refine ⟨m, sr, g, h1, ?_, hg2, hf2⟩
    have h3 : (E.world (m + 1)).now ≤ (E.world k1).now := Exec.now_mono E (by omega)
    have := Nat.le_mul_of_pos_left N.τ (show 0 < p + 1 by omega)
    omega

end Plain

end Engine.World
