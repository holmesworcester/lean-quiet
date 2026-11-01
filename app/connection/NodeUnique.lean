import app.Proofs
import engine.wire.NodeUniqueLaws

namespace Connection.Execution
open Engine Engine.Sync
open Engine.Sync.NodeUnique

private instance : LawfulMonad M := inferInstanceAs (LawfulMonad (StateM Memory))

/-- Arbitrary production hooks/entropy and the actual entry-point dispatch.
No read-only, fairness, admission or uniqueness assumption about hook output. -/
theorem production_step_unique (S : Setup) (side : Side) (n : Engine.Sync.Node)
    (input : Node.Input) (now : Nat) (s : Memory) (h : Valid n) :
    Valid ((n.step (S.sync side) input now) s).1.1 :=
  Ensures.state (step_valid (S.sync side) n input now h) s

private theorem world_run_unique (S : Setup) (w : World) (side : Side) (queue : List Packet)
    (f : Engine.Sync.Node → M (Engine.Sync.Node × Effects)) (closed : Bool)
    (hf : ∀ n s, Valid n → Valid (f n s).1.1)
    (hw : ∀ side, Valid (w.peer side).node) :
    ∀ target, Valid ((w.run S side queue f closed).peer target).node := by
  intro target
  cases side <;> cases target
  · exact hf _ _ (hw .a)
  · exact hw .b
  · exact hw .a
  · exact hf _ _ (hw .b)

/-- Reuses the existing production World transition, including two-sided
transport close, delivery, dropped frames, writes, ticks and idle actions. -/
theorem world_step_unique (S : Setup) (w : World) (a : Action)
    (hw : ∀ side, Valid (w.peer side).node) :
    ∀ target, Valid ((step S w a).peer target).node := by
  have hp : ∀ (w : World) (side : Side) (queue : List Packet) (input : Node.Input) (closed : Bool),
      (∀ s, Valid (w.peer s).node) →
      ∀ target, Valid ((w.run S side queue
        (fun n => n.step (S.sync side) input w.now) closed).peer target).node :=
    fun w side queue input closed h => world_run_unique S w side queue _ closed
      (fun n s hn => production_step_unique S side n input w.now s hn) h
  intro target
  have time : ∀ w' : World, ({ w' with now := w.now + 1 }.peer target).node =
      (w'.peer target).node := by intro w'; cases target <;> rfl
  unfold step
  rw [time]
  cases a with
  | tick side => exact hp w side w.net .tick false hw target
  | write side ops => exact hp w side w.net (.write ops) false hw target
  | idle => exact hw target
  | drop => cases target with
    | a => exact hw .a
    | b => exact hw .b
  | close =>
    have ha := hp w .a [] (.close (S.addr .b)) true hw
    let wa := w.run S .a [] (fun n => n.onClose (S.sync .a) (S.addr .b) w.now) true
    exact world_run_unique S wa .b wa.net _ true
      (fun n s hn => production_step_unique S .b n (.close (S.addr .a)) w.now s hn) ha target
  | deliver =>
    cases hnet : w.net with
    | nil => simpa only [World.deliver, hnet] using hw target
    | cons p rest =>
      by_cases ha : p.dst = S.addr .a
      · simpa only [World.deliver, hnet, ite_eq_left ha, Node.step] using
          hp w .a rest (.frame p.src p.bytes) false hw target
      · by_cases hb : p.dst = S.addr .b
        · simpa only [World.deliver, hnet, ite_eq_right ha, ite_eq_left hb, Node.step] using
            hp w .b rest (.frame p.src p.bytes) false hw target
        · simp only [World.deliver, hnet, ite_eq_right ha, ite_eq_right hb]
          cases target with
          | a => exact hw .a
          | b => exact hw .b

theorem world_trace_unique (S : Setup) (w : World) (actions : List Action)
    (hw : ∀ side, Valid (w.peer side).node) :
    ∀ target, Valid ((trace S w actions).peer target).node := by
  induction actions generalizing w with
  | nil => exact hw
  | cons a rest ih => exact ih (step S w a) (world_step_unique S w a hw)

/-- Every finite execution from the actual boot has unique live IDs and retry
order. The schedule, entropy, user writes and packet drops are arbitrary. -/
theorem empty_trace_unique (S : Setup) (ea eb : Nat → ByteArray)
    (actions : List Action) (target : Side) :
    Valid ((trace S (empty ea eb) actions).peer target).node :=
  world_trace_unique S (empty ea eb) actions (fun side => by
    cases side <;> exact boot_valid family [] 0) target

/-- Every position in an arbitrary infinite production-interpreter execution;
fairness is irrelevant to this invariant and is not a premise. -/
theorem Run.unique {S : Setup} {ea eb : Nat → ByteArray}
    (r : Run S (empty ea eb)) (i : Nat) (target : Side) :
    Valid ((r.state i).peer target).node := by
  induction i generalizing target with
  | zero => rw [r.zero]; cases target <;> exact boot_valid family [] 0
  | succ i ih =>
    rw [r.next]
    exact world_step_unique S (r.state i) (r.action i) (fun side => ih side) target

end Connection.Execution
