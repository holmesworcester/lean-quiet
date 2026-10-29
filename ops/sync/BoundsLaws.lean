/-
The live connection invariant: neither peer-controlled id set exceeds
maxKnown. Hints forget and asks defer at capacity; neither ends the session.
Ticks expire asks without renewing their original timestamps. Every
step the node runs on a connection keeps it (`conn_bounded`), the rooms
it carries afresh and the notices it gives included (`notify_bounded`).
-/
import ops.sync.OfferLaws
import ops.sync.Notice
import engine.wire.WorldLaws

namespace Engine.Sync

local instance : LawfulBEq ByteArray where
  eq_of_beq {a b} h := ByteArray.ext (eq_of_beq (show a.data == b.data from h))
  rfl {a} := show a.data == a.data from beq_self_eq_true a.data

variable {F : Type} (fam : Family F) (cfg : Config)

theorem inserts_size (ids : List Id) (asked : Std.HashSet Id) :
    (ids.foldl (·.insert ·) asked).size ≤ asked.size + ids.length := by
  induction ids generalizing asked with
  | nil => simp
  | cons i ids ih =>
    have hi := Std.HashSet.size_insert_le (m := asked) (k := i)
    have ht := ih (asked.insert i)
    simp only [List.foldl_cons, List.length_cons]
    omega

theorem admitAsks_bounded (cap : Nat) (asked : Std.HashSet Id) (ids : List Id)
    (hb : asked.size ≤ cap) :
    ((admitAsks cap asked ids).foldl (·.insert ·) asked).size ≤ cap := by
  have hi := inserts_size (admitAsks cap asked ids) asked
  have hl : (admitAsks cap asked ids).length ≤ cap - asked.size := List.length_take_le ..
  omega

theorem remembers_bounded {α : Type} (cap : Nat) (key : α → Id) (ids : List α)
    (known : Std.HashSet Id) (hb : known.size ≤ cap) :
    (ids.foldl (fun k i => remember cap k (key i)) known).size ≤ cap := by
  induction ids generalizing known with
  | nil => exact hb
  | cons i ids ih => exact ih _ (remember_bounded ..)

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
    · split <;> exact ⟨hb.1, admitAsks_bounded _ _ _ hb.2⟩

theorem hold_bounded (c : Conn) (r : Id) (ids : List Id) (h : Held F) (hb : c.Bounded cfg) :
    ((c.onHold fam cfg r ids : HeldM F Step) h).1.conn.Bounded cfg := by
  rw [onHold_apply]
  split
  · exact hb
  · split
    · exact hb
    · exact ⟨remembers_bounded _ id _ _ hb.1, admitAsks_bounded _ _ _ hb.2⟩

theorem onWant_bounded (ix : Index) (c : Conn) (ids : List Id) (h : Held F) (hb : c.Bounded cfg) :
    ((c.onWant fam cfg ix ids : HeldM F Step) h).1.conn.Bounded cfg := by
  unfold Conn.onWant
  split
  · exact hb
  · simp only [HeldM.bind_apply, HeldM.pure_apply]
    exact ⟨remembers_bounded _ Op.id _ _ hb.1, hb.2⟩

theorem walkN_bounded (h : Held F) : ∀ (k : Nat) (c : Conn) (offer : List (Id × Id)),
    c.Bounded cfg → ((c.walkN fam cfg offer k : HeldM F _) h).1.1.Bounded cfg := by
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
      split
      · exact ih _ _ hb
      · rw [HeldM.bind_apply, HeldM.getOp_apply]
        cases h.db.ops x with
        | none => exact ih _ _ hb
        | some o =>
          dsimp only
          split
          · exact ih _ _ hb
          · exact ih _ _ hb

theorem expire_bounded (c : Conn) (now : Nat) (hb : c.Bounded cfg) :
    (c.expireAsks cfg now).Bounded cfg :=
  ⟨hb.1, Nat.le_trans Std.HashSet.size_filter_le_size hb.2⟩

theorem tick_bounded (ix : Index) (c : Conn) (now : Nat) (h : Held F) (hb : c.Bounded cfg) :
    ((c.tick fam cfg ix now : HeldM F Step) h).1.conn.Bounded cfg := by
  unfold Conn.tick Conn.work
  split
  · exact hb
  · simp only [HeldM.bind_apply, HeldM.pure_apply, Step.pulse_conn]
    have hw := walkN_bounded fam cfg h cfg.walk c [] hb
    change ((c.walk fam cfg : HeldM F _) h).1.1.Bounded cfg at hw
    have hw := expire_bounded cfg _ now hw
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
      · exact ⟨remember_bounded .., Nat.le_trans Std.HashSet.size_erase_le hb.2⟩
    | some msg =>
      cases msg with
      | hello f =>
        dsimp only
        split
        · exact start_bounded cfg _ _ _ hb
        · exact hb
      | rbsr r k cs => exact (round_bounded cfg _ _ _ _ _ _ hb)
      | hold r ids =>
        dsimp only
        exact (hold_bounded fam cfg _ _ _ _ hb)
      | want ids =>
        dsimp only
        exact (onWant_bounded fam cfg _ _ _ _ hb)

theorem filed_bounded (c : Conn) (ids : List Id) (h : Held F) (hb : c.Bounded cfg) :
    ((c.filed fam cfg ids : HeldM F Step) h).1.conn.Bounded cfg := by
  unfold Conn.filed
  simp only [HeldM.bind_apply]
  rw [HeldM.forIn_reads (g := fileOffer fam cfg h.db)]
  · exact foldl_inv (fun b : List (Id × Id) × Conn => b.2.Bounded cfg) (fileOffer fam cfg h.db)
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

/-- Giving notices keeps both peer-controlled id sets as they were. -/
theorem give_ids (h : Held F) : ∀ (l : List (Id × Id)) (c : Conn),
    ((c.give fam cfg l : HeldM F Step) h).1.conn.known = c.known ∧
      ((c.give fam cfg l : HeldM F Step) h).1.conn.asked = c.asked
  | [], _ => ⟨rfl, rfl⟩
  | (r, x) :: rest, c => by
    unfold Conn.give
    split
    · exact give_ids h rest c
    · simp only [HeldM.bind_apply, HeldM.pure_apply]
      exact give_ids _ rest _

theorem notify_bounded (c : Conn) (h : Held F) (hb : c.Bounded cfg) :
    ((c.notify fam cfg : HeldM F Step) h).1.conn.Bounded cfg := by
  obtain ⟨e1, e2⟩ := give_ids fam cfg h c.notices c
  unfold Conn.notify Conn.Bounded
  rw [e1, e2]; exact hb

/-- Reachability through every public connection transition on held stores. -/
inductive Conn.Reachable (fam : Family F) (cfg : Config) : Conn → Prop where
  | open (dialer : Bool) (rooms : List Id) (floor now : Nat) :
      Reachable fam cfg (Conn.open dialer rooms floor now).conn
  | start {c} (hc : Reachable fam cfg c) (ix now) : Reachable fam cfg (c.start cfg ix now).conn
  | round {c} (hc : Reachable fam cfg c) (ix r k cs now) : Reachable fam cfg (c.onRbsr cfg ix r k cs now).conn
  | hold {c} (hc : Reachable fam cfg c) (r ids) (h : Held F) :
      Reachable fam cfg ((c.onHold fam cfg r ids : HeldM F Step) h).1.conn
  | want {c} (hc : Reachable fam cfg c) (ix ids) (h : Held F) :
      Reachable fam cfg ((c.onWant fam cfg ix ids : HeldM F Step) h).1.conn
  | recv {c} (hc : Reachable fam cfg c) (ix bytes now) (h : Held F) :
      Reachable fam cfg ((c.recv fam cfg ix bytes now : HeldM F Step) h).1.conn
  | tick {c} (hc : Reachable fam cfg c) (ix now) (h : Held F) :
      Reachable fam cfg ((c.tick fam cfg ix now : HeldM F Step) h).1.conn
  | filed {c} (hc : Reachable fam cfg c) (ids) (h : Held F) :
      Reachable fam cfg ((c.filed fam cfg ids : HeldM F Step) h).1.conn
  | rooms {c} (hc : Reachable fam cfg c) (rs) : Reachable fam cfg (c.setRooms rs)
  | carry {c} (hc : Reachable fam cfg c) (rs : List Room) : Reachable fam cfg (c.carry rs)
  | notify {c} (hc : Reachable fam cfg c) (h : Held F) :
      Reachable fam cfg ((c.notify fam cfg : HeldM F Step) h).1.conn

/-- The node's notice wrappers are compositions of reachable transitions. -/
theorem filedGive_reachable {c : Conn} (hc : c.Reachable fam cfg) (ids : List Id) (h : Held F) :
    (((c.filedGive fam cfg ids : HeldM F Step) h).1.conn).Reachable fam cfg := by
  simp only [Conn.filedGive, HeldM.bind_apply, HeldM.pure_apply, Step.then]
  exact .filed (.notify hc h) ids _

theorem tickGive_reachable {c : Conn} (hc : c.Reachable fam cfg) (ix : Index) (now : Nat) (h : Held F) :
    (((c.tickGive fam cfg ix now : HeldM F Step) h).1.conn).Reachable fam cfg := by
  simp only [Conn.tickGive, HeldM.bind_apply, HeldM.pure_apply]
  split <;> exact .tick (.notify hc h) ix now _

theorem conn_bounded {c : Conn} (hc : c.Reachable fam cfg) :
    c.known.size ≤ cfg.maxKnown ∧ c.asked.size ≤ cfg.maxKnown := by
  induction hc with
  | «open» => simp [Conn.open, Conn.Bounded]
  | start _ _ _ ih => exact start_bounded cfg _ _ _ ih
  | round _ _ _ _ _ _ ih => exact round_bounded cfg _ _ _ _ _ _ ih
  | hold _ _ _ _ ih => exact hold_bounded fam cfg _ _ _ _ ih
  | want _ _ _ _ ih => exact onWant_bounded fam cfg _ _ _ _ ih
  | recv _ _ _ _ _ ih => exact recv_bounded fam cfg _ _ _ _ _ ih
  | tick _ _ _ _ ih => exact tick_bounded fam cfg _ _ _ _ ih
  | filed _ _ _ ih => exact filed_bounded fam cfg _ _ _ ih
  | rooms _ _ ih => exact ih
  | carry _ _ ih => exact ih
  | notify _ _ ih => exact notify_bounded fam cfg _ _ ih

end Engine.Sync
