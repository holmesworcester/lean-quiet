/-
The node runs its connection steps on held data (`HeldM`); their laws
are stated over the model's tables (`Model`). The two runs agree: a step
run on a held store gives what it gives on the store's tables, and
leaves the tables as it leaves them (`Sim`). So a law of a step over the
model (ops/sync/NoticeLaws.lean, ops/connection/RemovalLaws.lean) is a
law of the step the node runs.

- `recv_sim`, `filedGive_sim`, `tickGive_sim`, `serveOwed_sim`: the
  steps the node runs on a connection (`Node.onSealed`, `Node.fanout`,
  `Node.onTick`, `Node.serveOwed`).
- `recv_held`, `filedGive_held`, `tickGive_held`, `serveOwed_held`: so
  each gives the same answer on held data as on its tables.

Held data and the model share the store's code: held data's reads are
the model's, lifted (engine/core/Held.lean). So the proofs follow the
code's structure, as `keeps` does for `Reads`, and the `sim` tactic does
it from a do block.
-/
import engine.wire.WorldLaws

namespace Engine.Sync
variable {F : Type}

/-- Code on held data runs as code on the tables: from any held store,
it gives what the tables' run gives, and leaves the store with the
tables that run leaves (and its log as it was). -/
def Sim {α} (p : HeldM F α) (q : Model F α) : Prop :=
  ∀ h, p.run h = ((q.run h.db).1, { h with db := (q.run h.db).2 })

/-- The same answer, on held data and on its tables. -/
theorem Sim.run1 {α} {p : HeldM F α} {q : Model F α} (hs : Sim p q) (h : Held F) :
    (p.run h).1 = (q.run h.db).1 := by
  rw [hs h]

theorem Sim.pure' {α} (a : α) : Sim (pure a : HeldM F α) (pure a : Model F α) := fun _ => rfl

theorem Sim.bind' {α β} {p : HeldM F α} {q : Model F α} {k : α → HeldM F β} {k' : α → Model F β}
    (hp : Sim p q) (hk : ∀ a, Sim (k a) (k' a)) : Sim (p >>= k) (q >>= k') := by
  intro h
  rw [HeldM.run_bind, hp h]
  exact hk _ _

theorem Sim.forIn' {α β} (l : List α) (b : β) {f : α → β → HeldM F (ForInStep β)}
    {g : α → β → Model F (ForInStep β)} (hf : ∀ a b, Sim (f a b) (g a b)) :
    Sim (forIn l b f) (forIn l b g) := by
  induction l generalizing b with
  | nil => exact Sim.pure' b
  | cons a t ih =>
    rw [List.forIn_cons, List.forIn_cons]
    refine Sim.bind' (hf a b) fun r => ?_
    cases r with
    | done b => exact Sim.pure' b
    | yield b => exact ih b

theorem Sim.getOp' (x : Id) : Sim (Store.getOp (F := F) x : HeldM F _) (Store.getOp (F := F) x : Model F _) :=
  fun _ => rfl

theorem Sim.getStatus' (x : Id) :
    Sim (Store.getStatus (F := F) x : HeldM F _) (Store.getStatus (F := F) x : Model F _) :=
  fun _ => rfl

theorem Sim.list' [SortKey F] (q : ListQ) : Sim (Lists.list q : HeldM F (Answer F)) (Lists.list q : Model F _) :=
  fun _ => rfl

/-- A read program (ops/sync/Serve.lean), run by the store's reader. -/
theorem Read.run_sim {α} (p : Read α) :
    Sim (p.run (Store.getOp (F := F)) : HeldM F α) (p.run (Store.getOp (F := F)) : Model F α) := by
  induction p with
  | done a => exact Sim.pure' a
  | get i next ih => exact Sim.bind' (Sim.getOp' i) fun o => ih o

/-- Prove `Sim` of a do block run on held data and on the tables, from
its structure, with these `Sim` lemmas for the calls in it. -/
syntax "sim" "[" term,* "]" : tactic

macro_rules
  | `(tactic| sim [$ts,*]) => do
    let mut tac : Lean.TSyntax `tactic ← `(tactic| first | split | intro)
    for t in ts.getElems.reverse do
      tac ← `(tactic| first | with_reducible_and_instances apply $t | $tac:tactic)
    `(tactic| repeat' (first
      | dsimp only | with_reducible_and_instances apply Sim.bind'
      | with_reducible_and_instances apply Sim.pure' | with_reducible_and_instances apply Sim.forIn'
      | with_reducible_and_instances apply Sim.getOp' | with_reducible_and_instances apply Sim.getStatus'
      | $tac:tactic))

section
variable (fam : Family F) (cfg : Config)

theorem holdsIn_sim (r i : Id) : Sim (holdsIn fam r i : HeldM F Bool) (holdsIn fam r i : Model F Bool) := by
  unfold holdsIn; sim []

theorem onHold_sim (c : Conn) (r : Id) (ids : List Id) :
    Sim (c.onHold fam cfg r ids : HeldM F Step) (c.onHold fam cfg r ids : Model F Step) := by
  unfold Conn.onHold; sim [holdsIn_sim]

theorem filed_sim (c : Conn) (ids : List Id) :
    Sim (c.filed fam cfg ids : HeldM F Step) (c.filed fam cfg ids : Model F Step) := by
  unfold Conn.filed; sim []

/-- `closureOps`, one step of its walk, in any store. -/
theorem closureOps_cons {m : Type → Type} [Monad m] [Store F m] (r : Id) (n : Nat) (y : Id)
    (rest seen : List Id) :
    (closureOps fam r (n + 1) (y :: rest) seen : m (List Op)) =
      (if has seen y then closureOps fam r (n + 1) rest seen
      else do
        match ← Store.getOp (F := F) y with
        | some o =>
          if fam.room o = some r then
            return o :: (← closureOps fam r n (o.reqs ++ rest) (y :: seen))
          else closureOps fam r n rest (y :: seen)
        | none => closureOps fam r n rest (y :: seen)) := by
  rw [closureOps]; rfl

theorem closureOps_zero {m : Type → Type} [Monad m] [Store F m] (r : Id) (todo seen : List Id) :
    (closureOps fam r 0 todo seen : m (List Op)) = pure [] := by
  rw [closureOps]

theorem closureOps_sim (r : Id) (fuel : Nat) : ∀ (todo seen : List Id),
    Sim (closureOps fam r fuel todo seen : HeldM F (List Op)) (closureOps fam r fuel todo seen : Model F (List Op)) := by
  induction fuel with
  | zero => intro todo seen; rw [closureOps_zero, closureOps_zero]; exact Sim.pure' _
  | succ n ih =>
    intro todo
    induction todo with
    | nil => intro seen; rw [closureOps_nil, closureOps_nil]; exact Sim.pure' _
    | cons y rest ihr =>
      intro seen
      rw [closureOps_cons, closureOps_cons]
      split
      · exact ihr seen
      · refine Sim.bind' (Sim.getOp' y) fun oo => ?_
        cases oo with
        | none => exact ih _ _
        | some o =>
          dsimp only
          split
          · exact Sim.bind' (ih _ _) fun _ => Sim.pure' _
          · exact ih _ _

theorem give_sim : ∀ (l : List (Id × Id)) (c : Conn),
    Sim (c.give fam cfg l : HeldM F Step) (c.give fam cfg l : Model F Step)
  | [], _ => Sim.pure' _
  | (r, x) :: rest, c => by
    unfold Conn.give
    split
    · exact give_sim rest c
    · exact Sim.bind' (closureOps_sim fam r _ _ _) fun _ =>
        Sim.bind' (give_sim rest _) fun _ => Sim.pure' _

theorem notify_sim (c : Conn) : Sim (c.notify fam cfg : HeldM F Step) (c.notify fam cfg : Model F Step) :=
  give_sim fam cfg _ c

/-- **Ops just stored, as the node runs them on a connection
(`Node.fanout`)**: the same step on held data as on its tables. -/
theorem filedGive_sim (c : Conn) (ids : List Id) :
    Sim (c.filedGive fam cfg ids : HeldM F Step) (c.filedGive fam cfg ids : Model F Step) :=
  Sim.bind' (notify_sim fam cfg c) fun g => Sim.bind' (filed_sim fam cfg g.conn ids) fun _ => Sim.pure' _

theorem walkN_sim : ∀ (budget : Nat) (c : Conn) (offer : List (Id × Id)),
    Sim (c.walkN fam cfg offer budget : HeldM F (Conn × List (Id × Id)))
      (c.walkN fam cfg offer budget : Model F (Conn × List (Id × Id)))
  | 0, _, _ => Sim.pure' _
  | budget + 1, c, offer => by
    unfold Conn.walkN
    split
    · exact Sim.pure' _
    · dsimp only
      split
      · exact walkN_sim budget _ _
      · refine Sim.bind' (Sim.getOp' _) fun oo => ?_
        cases oo with
        | none => exact walkN_sim budget _ _
        | some o =>
          dsimp only
          split
          · exact walkN_sim budget _ _
          · exact walkN_sim budget _ _

theorem walk_sim (c : Conn) :
    Sim (c.walk fam cfg : HeldM F (Conn × List (Id × Id))) (c.walk fam cfg : Model F (Conn × List (Id × Id))) :=
  walkN_sim fam cfg _ c []

theorem work_sim (ix : Index) (c : Conn) (now : Nat) :
    Sim (c.work fam cfg ix now : HeldM F Step) (c.work fam cfg ix now : Model F Step) := by
  unfold Conn.work; sim [walk_sim]

theorem tick_sim (ix : Index) (c : Conn) (now : Nat) :
    Sim (c.tick fam cfg ix now : HeldM F Step) (c.tick fam cfg ix now : Model F Step) := by
  unfold Conn.tick; sim [work_sim]

/-- **The clock, as the node runs it on a connection (`Node.onTick`)**:
the same step on held data as on its tables. -/
theorem tickGive_sim (ix : Index) (c : Conn) (now : Nat) :
    Sim (Conn.tickGive fam cfg ix c now : HeldM F Step) (Conn.tickGive fam cfg ix c now : Model F Step) :=
  Sim.bind' (notify_sim fam cfg c) fun g => Sim.bind' (tick_sim fam cfg ix g.conn now) fun _ => Sim.pure' _

/-- **A frame's payload, as the node runs it on a connection
(`Node.onSealed`)**: the same step on held data as on its tables. -/
theorem recv_sim (ix : Index) (c : Conn) (bytes : ByteArray) (now : Nat) :
    Sim (Conn.recv fam cfg ix c bytes now : HeldM F Step) (Conn.recv fam cfg ix c bytes now : Model F Step) := by
  unfold Conn.recv; sim [onHold_sim]

/-- **Serving the queue (`Node.serveOwed`)**: the same step on held data
as on its tables. -/
theorem serveOwed_sim (c : Conn) (budget : Nat) (first : List Id) :
    Sim (c.serveOwed fam cfg budget first : HeldM F (Conn × List Op × List Op))
      (c.serveOwed fam cfg budget first : Model F (Conn × List Op × List Op)) := by
  unfold Conn.serveOwed; sim [Read.run_sim]

theorem recv_held (ix : Index) (c : Conn) (bytes : ByteArray) (now : Nat) (h : Held F) :
    ((Conn.recv fam cfg ix c bytes now : HeldM F Step).run h).1 =
      ((Conn.recv fam cfg ix c bytes now : Model F Step).run h.db).1 :=
  (recv_sim fam cfg ix c bytes now).run1 h

theorem filedGive_held (c : Conn) (ids : List Id) (h : Held F) :
    ((c.filedGive fam cfg ids : HeldM F Step).run h).1 = ((c.filedGive fam cfg ids : Model F Step).run h.db).1 :=
  (filedGive_sim fam cfg c ids).run1 h

theorem tickGive_held (ix : Index) (c : Conn) (now : Nat) (h : Held F) :
    ((Conn.tickGive fam cfg ix c now : HeldM F Step).run h).1 =
      ((Conn.tickGive fam cfg ix c now : Model F Step).run h.db).1 :=
  (tickGive_sim fam cfg ix c now).run1 h

theorem serveOwed_held (c : Conn) (budget : Nat) (first : List Id) (h : Held F) :
    ((c.serveOwed fam cfg budget first : HeldM F (Conn × List Op × List Op)).run h).1 =
      ((c.serveOwed fam cfg budget first : Model F (Conn × List Op × List Op)).run h.db).1 :=
  (serveOwed_sim fam cfg c budget first).run1 h

end

end Engine.Sync
