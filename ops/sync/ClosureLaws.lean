/-
Window closure admission and walking use one shared id budget. Full
rounds leave the closure and stream hint untouched, including delayed
wants after the round's empty end. These laws run Conn on Held stores.
-/
import ops.sync.ServeLaws
import Std.Data.HashSet.Lemmas

namespace Engine.Sync

local instance : LawfulBEq ByteArray where
  eq_of_beq {a b} h := ByteArray.ext (eq_of_beq (show a.data == b.data from h))
  rfl {a} := show a.data == a.data from beq_self_eq_true a.data

/-- The closure's entire persistent id state, pending plus visited. -/
def Conn.ClosureBounded (cfg : Config) (c : Conn) : Prop :=
  c.closed.size + c.frontier.length ≤ cfg.closureCap

theorem queueClosure_bounded (cap : Nat) (closed : Std.HashSet Id) (frontier ids : List Id)
    (hb : closed.size + frontier.length ≤ cap) :
    closed.size + (queueClosure cap closed frontier ids).1.length ≤ cap := by
  simp only [queueClosure, List.length_append, List.length_take]
  omega

theorem queue_bounded (cfg : Config) (c : Conn) (ids : List Id) (hb : c.ClosureBounded cfg) :
    (c.queue cfg ids).ClosureBounded cfg := by
  unfold Conn.ClosureBounded Conn.queue
  dsimp only
  split
  · exact hb
  · exact queueClosure_bounded _ _ _ _ hb

theorem begin_closure_bounded (cfg : Config) (c : Conn) (k : Nat) (hb : c.ClosureBounded cfg) :
    (c.beginRound k).ClosureBounded cfg := by
  unfold Conn.beginRound Conn.ClosureBounded
  split
  · exact hb
  · simp

variable {F : Type} (fam : Family F) (cfg : Config)

/-- Every prefix of the actual walk stays inside the closure budget. -/
theorem closure_capped (h : Held F) : ∀ (fuel : Nat) (c : Conn) (offers : List (Id × Id)),
    c.ClosureBounded cfg → ((c.walkN fam cfg offers fuel : HeldM F _) h).1.1.ClosureBounded cfg := by
  intro fuel
  induction fuel with
  | zero => intro c offers hb; exact hb
  | succ fuel ih =>
    intro c offers hb
    rw [Conn.walkN]
    cases hf : c.frontier with
    | nil => exact hb
    | cons x rest =>
      have hb' : ({ c with frontier := rest } : Conn).ClosureBounded cfg := by
        simp only [Conn.ClosureBounded, hf, List.length_cons] at hb ⊢
        omega
      have hb'' : ({ c with frontier := rest, closed := c.closed.insert x } : Conn).ClosureBounded cfg := by
        have hi := Std.HashSet.size_insert_le (m := c.closed) (k := x)
        simp only [Conn.ClosureBounded, hf, List.length_cons] at hb ⊢
        omega
      dsimp only
      split
      · exact ih _ _ hb'
      · rw [HeldM.bind_apply, HeldM.getOp_apply]
        cases h.db.ops x with
        | none => exact ih _ _ hb''
        | some o =>
          dsimp only
          split
          · exact ih _ _ (queue_bounded cfg _ _ hb'')
          · exact ih _ _ hb''

/-- Wants in a full round keep all three sender bookkeeping collections. -/
theorem full_round_stateless (ix : Index) (c : Conn) (ids : List Id) (h : Held F)
    (hf : c.roundFloor ≤ 1) :
    let d := ((c.onWant fam cfg ix ids : HeldM F Step) h).1.conn
    d.offered = c.offered ∧ d.closed = c.closed ∧ d.frontier = c.frontier := by
  unfold Conn.onWant
  split
  · exact ⟨rfl, rfl, rfl⟩
  · simp only [HeldM.bind_apply, Read.run_held, HeldM.pure_apply]
    simp [Conn.queue, hf]

end Engine.Sync

namespace Engine.Sync
/-- Every new full round supplies the statelessness premise. -/
theorem full_round_runs (c : Conn) (hf : c.floor ≤ 1) (hp : c.peerFloor.getD c.floor ≤ 1) :
    (c.beginRound (c.round + 1)).roundFloor ≤ 1 := by
  simp only [Conn.beginRound, Nat.ne_add_one, ite_false]
  omega
end Engine.Sync
