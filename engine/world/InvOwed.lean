/-
**Every session's queue holds at most `maxKnown` ids**, at every plain
node in every execution against any attacker (`Plain.owed_bounded`):
a want joins the queue only while it has room (main's
`onWant_bounded_owed`), serving leaves a suffix, a new session's queue is
empty, and nothing else touches it. Over the `Pieces` of every entry
point (engine/world/InvIx.lean).
-/
import engine.world.Drain

namespace Engine.World
open Engine Engine.Sync

variable {F : Type}

/-- Every session's queue at node n holds at most `cap` ids. -/
def NodeBounded (cap : Nat) (n : Node) : Prop := ∀ cid c, n.conn? cid = some c → c.owed.length ≤ cap

theorem bounded_conns {cap : Nat} {n n' : Node} (e : n'.conns = n.conns) (hn : NodeBounded cap n) :
    NodeBounded cap n' := by
  intro cid c hc; simp only [Node.conn?] at hc; rw [e] at hc; exact hn cid c hc

theorem bounded_map {cap : Nat} (n : Node) (g : Id × Conn → Id × Conn) (hk : ∀ q, (g q).1 = q.1)
    (hq : ∀ q, q.2.owed.length ≤ cap → (g q).2.owed.length ≤ cap) (hn : NodeBounded cap n) :
    NodeBounded cap { n with conns := n.conns.map g } := by
  intro cid c hc
  simp only [Node.conn?, List.find?_map, Option.map_map] at hc
  have e : ((fun p : Id × Conn => Decidable.decide (p.1 = cid)) ∘ g) = fun p => Decidable.decide (p.1 = cid) := by
    funext p; simp [Function.comp, hk]
  rw [e] at hc
  cases e' : n.conns.find? (fun p => Decidable.decide (p.1 = cid)) with
  | none => rw [e'] at hc; cases hc
  | some p =>
    rw [e'] at hc
    simp only [Option.map_some, Option.some.injEq, Function.comp] at hc
    subst hc
    apply hq
    apply hn cid
    simp [Node.conn?, e']

theorem bounded_replace {cap : Nat} (n : Node) (cid : Id) (c' : Conn) (hc' : c'.owed.length ≤ cap)
    (hn : NodeBounded cap n) :
    NodeBounded cap { n with conns := n.conns.map fun p => if p.1 = cid then (cid, c') else p } :=
  bounded_map n _ (fun q => by split <;> simp_all) (fun q hq => by
    split
    · exact hc'
    · exact hq) hn

theorem bounded_drop {cap : Nat} (n : Node) (cid : Id) (hn : NodeBounded cap n) : NodeBounded cap (n.drop cid) :=
  fun cid' c hc => hn cid' c (close_conn n cid cid' c hc)

theorem bounded_sent {cap : Nat} (n : Node) (out : Acts) (now : Nat) (hn : NodeBounded cap n) :
    NodeBounded cap (n.sent out now) := by
  unfold Node.sent
  exact bounded_map n _ (fun q => by cases q; rfl) (fun q hq => by
    obtain ⟨cid, c⟩ := q
    dsimp only
    split
    · exact hq
    · exact hq) hn

/-- **A payload's step keeps the queue within its bound.** -/
theorem recv_bounded (fam : Family F) (cfg : Config) (ix : Index) (c : Conn) (b : ByteArray) (now : Nat)
    (h : Held F) (hb : c.owed.length ≤ cfg.maxKnown) :
    ((Conn.recv fam cfg ix c b now : HeldM F Step).run h).1.conn.owed.length ≤ cfg.maxKnown := by
  unfold Conn.recv
  cases hd : Op.decode b with
  | none => exact hb
  | some o =>
    simp only
    cases hm : Msg.ofOp o with
    | some m =>
      cases m with
      | hello f =>
        simp only [HeldM.run_pure]
        split
        · rw [(start_q cfg ix _ now).1]; exact hb
        · exact hb
      | rbsr r k cs =>
        simp only [HeldM.run_pure]
        rw [(onRbsr_owed cfg ix _ r k cs now).1]; exact hb
      | hold r ids =>
        simp only [HeldM.run_bind, HeldM.run_pure]
        simp only [show ∀ m : HeldM F Step, m.run h = m h from fun _ => rfl]
        rw [onHold_apply]
        split
        · exact hb
        · split <;> exact hb
      | want ids =>
        simp only [HeldM.run_pure]
        exact onWant_bounded_owed cfg ix _ ids hb
    | none =>
      simp only
      split
      · exact hb
      · exact hb

/-- **Serving leaves a suffix of the queue.** -/
theorem serveOwed_bounded (fam : Family F) (cfg : Config) (c : Conn) (budget : Nat) (first : List Id) (h : Held F)
    (cap : Nat) (hb : c.owed.length ≤ cap) :
    ((c.serveOwed fam cfg budget first : HeldM F _) h).1.1.owed.length ≤ cap := by
  rw [(serveOwed_run fam cfg c budget first h).2.1]
  obtain ⟨pre, hpre⟩ := serve_rest (c.shows fam) h.db.ops (c.owedAfter first) budget
  have h1 : (c.owedAfter first).length ≤ c.owed.length := by
    unfold Conn.owedAfter; split
    · exact Nat.le_refl _
    · exact List.length_filter_le _ _
  have h2 := congrArg List.length hpre
  rw [List.length_append] at h2
  omega

section
variable (S : Engine.Sync.Setup F) (s : Who)

theorem store_bounded (n : Node) (ops : List Op) (mine : Bool) (h : Held F) (hn : NodeBounded S.cfg.maxKnown n) :
    NodeBounded S.cfg.maxKnown ((n.store (S.sync s) ops mine).run h).1.1 := by
  intro cid c' hc'
  obtain ⟨c, hc, -, e, -⟩ := (store_facts S s n ops mine h).2.2.2 cid c' hc'
  rw [e]; exact hn cid c hc

theorem serve_bounded (y : Sync F (HeldM F)) (n : Node) (cid : Id) (now : Nat) (h : Held F)
    (hn : NodeBounded S.cfg.maxKnown n) : NodeBounded S.cfg.maxKnown ((n.serveOwed y cid now).run h).1.1 := by
  unfold Node.serveOwed
  split
  · exact hn
  · rename_i c hc
    split
    · exact hn
    · simp only [HeldM.run_bind, Node.refresh, HeldM.run_pure]
      exact bounded_replace n cid _ (serveOwed_bounded _ _ _ _ _ _ _ (hn cid c hc)) hn

/-- **Every piece of a plain node keeps each queue within `maxKnown`.** -/
theorem bounded_pieces : Pieces S s (fun n _ => NodeBounded S.cfg.maxKnown n) where
  write n ops h hn := bounded_conns (write_conns _ n ops h) hn
  store n ops mine h hn := store_bounded S s n ops mine h hn
  recv n cid c b now h hc hn := apply_gen S s (fun n _ => NodeBounded S.cfg.maxKnown n)
    (fun n ops mine h hn => store_bounded S s n ops mine h hn)
    n cid _ now h (fun _ => bounded_drop n cid hn)
    (fun _ => bounded_replace n cid _ (recv_bounded S.fam S.cfg n.ix
      { c.setRooms (S.rooms s cid) with notices := [] } b now h (hn cid c hc)) hn)
  tick n cid c now h hc hn := apply_gen S s (fun n _ => NodeBounded S.cfg.maxKnown n)
    (fun n ops mine h hn => store_bounded S s n ops mine h hn)
    n cid _ now h (fun _ => bounded_drop n cid hn)
    (fun _ => bounded_replace n cid _ (by
      have e : ((Conn.tickGive S.fam S.cfg n.ix { c.setRooms (S.rooms s cid) with notices := [] } now :
          HeldM F Step).run h).1.conn.owed = c.owed :=
        (tickGive_q S.fam S.cfg n.ix { c.setRooms (S.rooms s cid) with notices := [] } now h).1
      rw [e]; exact hn cid c hc) hn)
  serve y _ _ n cid now h hn := serve_bounded S y n cid now h hn
  finish n out now h hn := finish_node S s (NodeBounded S.cfg.maxKnown) (fun m cid hm => bounded_drop m cid hm)
    (fun m o t hm => bounded_sent m o t hm) (fun _ hm => bounded_conns rfl hm) n out now h hn
  setAddr n cid a h hn := bounded_conns rfl hn
  heat n ids now h hn := bounded_conns rfl hn
  drop n cid h hn := bounded_drop n cid hn
  opens n cid a dialer now h hn := by
    unfold Node.open
    simp only [HeldM.run_bind, sync_rooms, HeldM.run_pure]
    intro cid' c hc
    simp only [Node.conn?, List.find?_cons] at hc
    split at hc
    · simp only [Option.map_some, Option.some.injEq] at hc
      subst hc
      simp [Conn.open]
    · exact hn cid' c (close_conn n cid cid' c hc)

end

namespace Plain
variable {Q : Plain F}

/-- **Every session's queue holds at most `maxKnown` ids**, at every node
in every execution from empty stores, against any attacker. -/
theorem owed_bounded_start {adv : World (Held F) Q.n → ByteArray → Prop} (E : Exec Q.setup adv Q.start) :
    ∀ k i cid c, ((E.world k).node i).conn? cid = some c → c.owed.length ≤ Q.cfg.maxKnown :=
  always E (fun n _ => NodeBounded Q.cfg.maxKnown n) (fun i => bounded_pieces (Q.two i) .a)
    (fun _ _ _ cid c hc => by simp [Node.boot, Node.conn?] at hc)
    (fun _ _ _ hc => by simp [Plain.start, World.init, Node.boot, Node.conn?] at hc)

end Plain

end Engine.World
