import ops.connection.Execution
import ops.connection.bootstrap.FIFO

namespace Connection.Execution
open Engine Engine.Sync

theorem run_queue (S : Setup) (w : World) (s : Side) (q : List Packet)
    (f : Engine.Sync.Node → M (Engine.Sync.Node × Effects)) :
    ∃ added, (w.run S s q f).net = q ++ added := by
  exact ⟨_, rfl⟩

theorem deliver_queue (S : Setup) (w : World) :
    Net.FIFO.Advance w.net (w.deliver S).net w.net.head? := by
  unfold World.deliver
  cases h : w.net with
  | nil => simpa [h] using (Net.FIFO.Advance.append ([] : List Packet) [])
  | cons p rest =>
    simp only [List.head?_cons]
    split
    · obtain ⟨added, he⟩ := run_queue S w .a rest _
      rw [he]; exact .pop p rest added
    · split
      · obtain ⟨added, he⟩ := run_queue S w .b rest _
        rw [he]; exact .pop p rest added
      · simpa using (Net.FIFO.Advance.pop p rest [])

theorem schedule_queue (S : Setup) (w : World) (i : Nat) :
    Net.FIFO.Advance w.net (step S w (schedule i)).net (dequeued w (schedule i)) := by
  unfold schedule
  split
  · let f := fun n : Engine.Sync.Node => n.onTick (S.sync .a) w.now
    have eqn : (step S w (.tick .a)).net = (w.run S .a w.net f).net := by simp only [step]; rfl
    rw [eqn]
    obtain ⟨added, he⟩ := run_queue S w .a w.net f
    rw [he]
    exact Net.FIFO.Advance.append w.net added
  · split
    · let f := fun n : Engine.Sync.Node => n.onTick (S.sync .b) w.now
      have eqn : (step S w (.tick .b)).net = (w.run S .b w.net f).net := by simp only [step]; rfl
      rw [eqn]
      obtain ⟨added, he⟩ := run_queue S w .b w.net f
      rw [he]
      exact Net.FIFO.Advance.append w.net added
    · exact deliver_queue S w

theorem fairRun_fair (S : Setup) (initial : World) : (fairRun S initial).Fair := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro N
    refine ⟨3 * N, by omega, ?_⟩
    simp [fairRun, schedule]
  · intro N
    refine ⟨3 * N + 1, by omega, ?_⟩
    simp [fairRun, schedule]
  · intro n p hp
    apply Net.FIFO.eventually_delivered
      (fun i => (states S initial i).net)
      (fun i => dequeued (states S initial i) (schedule i))
      (fun i => schedule_queue S (states S initial i) i) ?_ hp
    intro N
    refine ⟨3 * N + 2, by omega, ?_⟩
    intro hn
    simp only [schedule, Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.zero_mul,
      Nat.zero_mod, Nat.reduceMod, Nat.zero_add, show ¬(2 : Nat) = 0 from by decide,
      show ¬(2 : Nat) = 1 from by decide, ↓reduceIte, dequeued]
    cases he : (states S initial (3 * N + 2)).net with
    | nil => exact False.elim (hn he)
    | cons p rest => rfl
  · intro i
    change (states S initial i).now = _
    induction i with
    | zero => simp [states]
    | succ i ih => simpa [states, step, ih, Nat.add_assoc]

/-- Prefix a real transition; no state is reset or invented at the join. -/
def Run.cons {S initial} (a : Action) (r : Run S (step S initial a)) : Run S initial where
  state
    | 0 => initial
    | i + 1 => r.state i
  action
    | 0 => a
    | i + 1 => r.action i
  zero := rfl
  next i := by cases i with
    | zero => exact r.zero
    | succ i => exact r.next i

def prepend (S : Setup) (initial : World) (actions : List Action)
    (r : Run S (trace S initial actions)) : Run S initial :=
  match actions with
  | [] => r
  | a :: rest => Run.cons a (prepend S (step S initial a) rest r)

theorem prepend_state (S : Setup) (initial : World) (actions : List Action)
    (r : Run S (trace S initial actions)) (i : Nat) :
    (prepend S initial actions r).state (actions.length + i) = r.state i := by
  induction actions generalizing initial with
  | nil => simp [prepend]
  | cons a rest ih =>
    simpa only [List.length_cons, Nat.add_right_comm, prepend, Run.cons] using
      ih (step S initial a) r

theorem prepend_action (S : Setup) (initial : World) (actions : List Action)
    (r : Run S (trace S initial actions)) (i : Nat) :
    (prepend S initial actions r).action (actions.length + i) = r.action i := by
  induction actions generalizing initial with
  | nil => simp [prepend]
  | cons a rest ih =>
    simpa only [List.length_cons, Nat.add_right_comm, prepend, Run.cons] using
      ih (step S initial a) r

/-- A finite execution with delays/drops/closes can be followed by an infinite
fair suffix through the production node. The goal is checked on the finite
prefix, not assumed as a scheduler property. This is existence of a successful
prefix with a fair node-interpreter continuation, not convergence of every
fair execution or a guarantee that future socket-close effects are modeled. -/
theorem successful_fair_extension (S : Setup) (initial : World) (actions : List Action)
    (Goal : World → Prop) (success : Goal (trace S initial actions)) :
    ∃ r : Run S initial,
      Goal (r.state actions.length) ∧
      ∃ tail : Run S (trace S initial actions), tail.Fair ∧
        (∀ i, r.state (actions.length + i) = tail.state i) ∧
        (∀ i, r.action (actions.length + i) = tail.action i) := by
  let tail := fairRun S (trace S initial actions)
  refine ⟨prepend S initial actions tail, ?_, tail, fairRun_fair S _,
    prepend_state S initial actions tail, prepend_action S initial actions tail⟩
  have h := prepend_state S initial actions tail 0
  simpa only [Nat.add_zero, tail.zero] using h ▸ success

end Connection.Execution
