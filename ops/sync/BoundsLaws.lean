/-
The live connection invariant: no peer-controlled id set, nor the
queue of what the peer wants, exceeds maxKnown. Hints forget at
capacity, asks past it are sent and not remembered, wants past it wait
for the next ask; none ends the session. Ticks age asks.
-/
import ops.sync.OfferLaws

namespace Engine.Sync

local instance : LawfulBEq ByteArray where
  eq_of_beq {a b} h := ByteArray.ext (eq_of_beq (show a.data == b.data from h))
  rfl {a} := show a.data == a.data from beq_self_eq_true a.data

variable {F : Type} (fam : Family F) (cfg : Config)

theorem limit_bounded (s : Step) (ho : s.conn.owed.length ≤ cfg.maxKnown) : (s.limit cfg).conn.Bounded cfg := by
  unfold Step.limit
  split
  · rename_i h; exact ⟨h.1, h.2, ho⟩
  · simp [Conn.Bounded, ho]

@[simp] theorem report_known (c : Conn) : c.report.1.known = c.known := by unfold Conn.report; split <;> rfl
@[simp] theorem report_asked (c : Conn) : c.report.1.asked = c.asked := by unfold Conn.report; split <;> rfl
@[simp] theorem report_owed (c : Conn) : c.report.1.owed = c.owed := by unfold Conn.report; split <;> rfl

theorem finish_bounded (s : Step) (hb : s.conn.Bounded cfg) : (Conn.finish s).conn.Bounded cfg := by
  simpa [Conn.finish, Conn.Bounded] using hb

theorem remember_le (cap : Nat) (known : Std.HashSet Id) (i : Id) : (remember cap known i).size ≤ cap := by
  unfold remember
  split
  · simp
  · dsimp only
    split
    · assumption
    · simp [Std.HashSet.size_insert]; omega

theorem noteAsks_bounded (cap : Nat) (asked : Std.HashSet Id) (ids : List Id) (hb : asked.size ≤ cap) :
    (noteAsks cap asked ids).size ≤ cap := by
  unfold noteAsks
  induction ids generalizing asked with
  | nil => exact hb
  | cons i t ih =>
    simp only [List.foldl_cons]
    apply ih
    split
    · rename_i h
      exact Nat.le_trans Std.HashSet.size_insert_le (by omega)
    · exact hb

theorem start_bounded (ix : Index) (c : Conn) (now : Nat) (hb : c.Bounded cfg) :
    (c.start cfg ix now).conn.Bounded cfg := by
  unfold Conn.start; split <;> exact hb

theorem round_bounded (ix : Index) (c : Conn) (r : Id) (k : Nat) (cs : List Claim) (now : Nat)
    (hb : c.Bounded cfg) : (c.onRbsr cfg ix r k cs now).conn.Bounded cfg := by
  unfold Conn.onRbsr
  split
  · exact hb
  · dsimp only; split
    · exact hb
    · exact limit_bounded cfg _ (by dsimp only; split <;> exact hb.2.2)

theorem hold_bounded (c : Conn) (r : Id) (ids : List Id) (h : Held F) (hb : c.Bounded cfg) :
    ((c.onHold fam cfg r ids : HeldM F Step) h).1.conn.Bounded cfg := by
  rw [onHold_apply]
  split
  · exact hb
  · split
    · exact hb
    · exact limit_bounded cfg _ hb.2.2

theorem onWant_bounded (ix : Index) (c : Conn) (ids : List Id) (hb : c.Bounded cfg) :
    (c.onWant cfg ix ids).conn.Bounded cfg := by
  refine ⟨?_, ?_, onWant_bounded_owed cfg ix c ids hb.2.2⟩ <;> unfold Conn.onWant <;> split
  · exact hb.1
  · exact hb.1
  · exact hb.2.1
  · exact hb.2.1

theorem foldl_remember_le (cap : Nat) : ∀ (l : List Op) (k : Std.HashSet Id), k.size ≤ cap →
    (l.foldl (fun (k : Std.HashSet Id) (o : Op) => remember cap k o.id) k).size ≤ cap
  | [], _, hk => hk
  | o :: l, k, _ => foldl_remember_le cap l _ (remember_le cap k o.id)

theorem owedAfter_length (c : Conn) (first : List Id) : (c.owedAfter first).length ≤ c.owed.length := by
  unfold Conn.owedAfter; split
  · exact Nat.le_refl _
  · exact List.length_filter_le _ _

/-- Serving the queue only shortens it, and keeps every set bounded. -/
theorem serveOwed_bounded (c : Conn) (budget : Nat) (first : List Id) (h : Held F) (hb : c.Bounded cfg) :
    ((c.serveOwed fam cfg budget first : HeldM F _) h).1.1.Bounded cfg := by
  rw [serveOwed_eq]
  refine ⟨foldl_remember_le cfg.maxKnown _ _ hb.1, hb.2.1, ?_⟩
  simp only [Conn.served]
  obtain ⟨pre, e⟩ := serve_rest (c.shows fam) h.db.ops (c.owedAfter first) budget
  have h1 := congrArg List.length e
  simp only [List.length_append] at h1
  have := owedAfter_length c first
  have := hb.2.2
  omega

theorem walkN_bounded (h : Held F) : ∀ (k : Nat) (c : Conn) (offer : List (Id × Id)),
    c.Bounded cfg → ((c.walkN fam offer k : HeldM F _) h).1.1.Bounded cfg := by
  intro k
  induction k with
  | zero => intro c offer hb; exact hb
  | succ k ih =>
    intro c offer hb
    rw [Conn.walkN]
    cases hf : c.frontier with
    | nil => exact hb
    | cons x rest =>
      dsimp only
      by_cases hc : (!c.closed.contains x) = true
      · rw [ite_eq_left hc, HeldM.bind_apply, HeldM.getOp_apply]
        dsimp only
        cases ho : h.db.ops x with
        | none => exact ih _ _ hb
        | some o =>
          dsimp only
          split
          · split
            · rw [HeldM.bind_apply, HeldM.getStatus_apply]
              cases h.db.status x with
              | none => exact ih _ _ hb
              | some v => cases v <;> exact ih _ _ hb
            · rw [HeldM.bind_apply, HeldM.getStatus_apply]
              cases h.db.status x with
              | none => exact ih _ _ hb
              | some v => cases v <;> exact ih _ _ hb
          · exact ih _ _ hb
      · rw [ite_eq_right hc]; exact ih _ _ hb

theorem age_bounded (c : Conn) (now : Nat) (hb : c.Bounded cfg) :
    (c.age cfg now).Bounded cfg := by
  unfold Conn.age; split
  · exact ⟨hb.1, by simp, hb.2.2⟩
  · exact hb

theorem tick_bounded (ix : Index) (c : Conn) (now : Nat) (h : Held F) (hb : c.Bounded cfg) :
    ((c.tick fam cfg ix now : HeldM F Step) h).1.conn.Bounded cfg := by
  unfold Conn.tick
  split
  · exact hb
  · rw [HeldM.bind_apply]
    apply finish_bounded
    have hw := walkN_bounded fam cfg h cfg.walk c [] hb
    change ((c.walk fam cfg : HeldM F _) h).1.1.Bounded cfg at hw
    have hw := age_bounded cfg _ now hw
    split
    · exact start_bounded cfg _ _ _ hw
    · exact hw

theorem recv_bounded (ix : Index) (c : Conn) (bytes : ByteArray) (now : Nat) (h : Held F)
    (hb : c.Bounded cfg) : ((c.recv fam cfg ix bytes now : HeldM F Step) h).1.conn.Bounded cfg := by
  unfold Conn.recv
  cases hd : Op.decode bytes with
  | none => exact hb
  | some o =>
    dsimp only
    cases hm : Msg.ofOp o with
    | none =>
      dsimp only
      split
      · exact hb
      · exact finish_bounded cfg _ (limit_bounded cfg _ hb.2.2)
    | some msg =>
      cases msg with
      | hello f =>
        apply finish_bounded
        split
        · exact start_bounded cfg _ _ _ hb
        · exact hb
      | rbsr r k cs => exact finish_bounded cfg _ (round_bounded cfg _ _ _ _ _ _ hb)
      | hold r ids =>
        dsimp only
        rw [HeldM.bind_apply]
        exact finish_bounded cfg _ (hold_bounded fam cfg _ _ _ _ hb)
      | want ids =>
        dsimp only
        exact finish_bounded cfg _ (onWant_bounded cfg _ _ _ hb)

theorem filed_bounded (c : Conn) (ids : List Id) (h : Held F) (hb : c.Bounded cfg) :
    ((c.filed fam cfg ids : HeldM F Step) h).1.conn.Bounded cfg := by
  unfold Conn.filed
  simp only [HeldM.bind_apply]
  rw [HeldM.forIn_reads (g := fileOffer fam h.db)]
  · apply finish_bounded
    exact foldl_inv (fun b : List (Id × Id) × Conn => b.2.Bounded cfg) (fileOffer fam h.db)
      (by intro b i hb; unfold fileOffer; split <;> try exact hb
          split <;> try exact hb
          split <;> exact hb) ids ([], c) hb
  · intro a b
    unfold fileOffer
    by_cases h1 : (!b.2.known.contains a && !b.2.offered.contains a) = true
    · rw [ite_eq_left h1, ite_eq_left h1, HeldM.bind_apply, HeldM.getOp_apply]
      dsimp only
      cases h.db.ops a with
      | none => rfl
      | some o =>
        dsimp only
        by_cases h2 : b.2.shows fam o = true
        · rw [ite_eq_left h2, ite_eq_left h2]; rfl
        · rw [ite_eq_right h2, ite_eq_right h2]; rfl
    · rw [ite_eq_right h1, ite_eq_right h1]; rfl

/-- Reachability through every public connection transition on held stores. -/
inductive Conn.Reachable (fam : Family F) (cfg : Config) : Conn → Prop where
  | open (dialer : Bool) (rooms : List Id) (floor now : Nat) :
      Reachable fam cfg (Conn.open dialer rooms floor now).conn
  | start {c} (hc : Reachable fam cfg c) (ix now) : Reachable fam cfg (c.start cfg ix now).conn
  | round {c} (hc : Reachable fam cfg c) (ix r k cs now) : Reachable fam cfg (c.onRbsr cfg ix r k cs now).conn
  | hold {c} (hc : Reachable fam cfg c) (r ids) (h : Held F) :
      Reachable fam cfg ((c.onHold fam cfg r ids : HeldM F Step) h).1.conn
  | want {c} (hc : Reachable fam cfg c) (ix ids) : Reachable fam cfg (c.onWant cfg ix ids).conn
  | serve {c} (hc : Reachable fam cfg c) (budget first) (h : Held F) :
      Reachable fam cfg ((c.serveOwed fam cfg budget first : HeldM F _) h).1.1
  | recv {c} (hc : Reachable fam cfg c) (ix bytes now) (h : Held F) :
      Reachable fam cfg ((c.recv fam cfg ix bytes now : HeldM F Step) h).1.conn
  | tick {c} (hc : Reachable fam cfg c) (ix now) (h : Held F) :
      Reachable fam cfg ((c.tick fam cfg ix now : HeldM F Step) h).1.conn
  | filed {c} (hc : Reachable fam cfg c) (ids) (h : Held F) :
      Reachable fam cfg ((c.filed fam cfg ids : HeldM F Step) h).1.conn
  | rooms {c} (hc : Reachable fam cfg c) (rs) : Reachable fam cfg (c.setRooms rs)

/-- **A live connection's peer-controlled state is bounded:** what it
remembers the peer holds, what it asked for, and the queue of what the
peer wants, each at most `maxKnown` ids. -/
theorem conn_bounded {c : Conn} (hc : c.Reachable fam cfg) :
    c.known.size ≤ cfg.maxKnown ∧ c.asked.size ≤ cfg.maxKnown ∧ c.owed.length ≤ cfg.maxKnown := by
  induction hc with
  | «open» => simp [Conn.open, Conn.Bounded]
  | start _ _ _ ih => exact start_bounded cfg _ _ _ ih
  | round _ _ _ _ _ _ ih => exact round_bounded cfg _ _ _ _ _ _ ih
  | hold _ _ _ _ ih => exact hold_bounded fam cfg _ _ _ _ ih
  | want _ _ _ ih => exact onWant_bounded cfg _ _ _ ih
  | serve _ _ _ _ ih => exact serveOwed_bounded fam cfg _ _ _ _ ih
  | recv _ _ _ _ _ ih => exact recv_bounded fam cfg _ _ _ _ _ ih
  | tick _ _ _ _ ih => exact tick_bounded fam cfg _ _ _ _ ih
  | filed _ _ _ ih => exact filed_bounded fam cfg _ _ _ ih
  | rooms _ _ ih => exact ih

end Engine.Sync
