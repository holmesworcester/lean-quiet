/-
One completed turn of the application's runner. TCP supplies the native
callbacks; the inbox selection, dispatch, timer decision and stopping order
live here. Proof interpreters use this same function with explicit backend
state, rather than choosing an independent sequence of node entry points.
-/
import engine.wire.Node
import engine.wire.Priority

namespace Engine.Sync

/-- The node entry points reached by the runner, including closes generated
while applying effects or shutting down. Socket administration remains in
the transport backend. -/
inductive Node.Input where
  | write (ops : List Op)
  | frame (addr bytes : ByteArray)
  | tick
  | close (addr : ByteArray)

/-- The production entry-point dispatch. The TCP backend calls this function
for every node invocation, including invocations made while applying effects. -/
def Node.step {F : Type} {m : Type → Type} [Monad m] [Store F m] [Turn F m]
    (x : Sync F m) (n : Node) (input : Node.Input) (now : Nat) : m (Node × Effects) :=
  match input with
  | .write ops => n.onWrite x ops now
  | .frame addr bytes => n.onFrame x addr bytes now
  | .tick => n.onTick x now
  | .close addr => n.onClose x addr now

namespace Loop

/-- Scheduler state has one owner; native socket state is the backend's value. -/
structure State (σ : Type) where
  value : σ
  slot : Inbox.Priority.Slot := Inbox.Priority.first
  lastTick : Nat := 0

/-- Inputs observed by one completed poll. `turn` samples the clock before
polling, just as the native runner does. -/
structure Observation (W E : Type) where
  now : Nat
  selected : Option (W ⊕ E)

/-- Native operations needed by a turn. A backend must expose its store,
transport and entropy semantics when used in a proof; this type does not
assert that SQLite, socket I/O or arbitrary callbacks satisfy such contracts.

`event = none` requests shutdown. A due tick runs after the primary handler,
and expiry runs after the tick's effects have been applied. -/
structure Backend (m : Type → Type) (σ W E : Type) where
  clock : m Nat
  writes : m (Option W)
  events : m (Option E)
  write : σ → W → Nat → m σ
  event : σ → E → Nat → m (Option σ)
  tick : σ → Nat → m σ
  expire : σ → Nat → m σ
  stop : σ → Nat → m σ
  idle : m Unit

/-- A turn records both its primary input and whether it also ran the timer.
A stopped turn does not run a tick, expiry check or idle sleep. -/
structure Result (σ W E : Type) where
  state : State σ
  observed : Observation W E
  ticked : Bool
  stopped : Bool

/-- Dispatch one observed input. `state.slot` is the phase already returned
by the completed inbox poll; dispatch leaves it unchanged. -/
def dispatch {m : Type → Type} [Monad m] {σ W E : Type}
    (backend : Backend m σ W E) (period : Nat) (state : State σ)
    (observed : Observation W E) : m (Result σ W E) := do
  let next ← match observed.selected with
    | some (.inl w) => some <$> backend.write state.value w observed.now
    | some (.inr e) => backend.event state.value e observed.now
    | none => pure (some state.value)
  match next with
  | none =>
    let value ← backend.stop state.value observed.now
    return { state := { state with value }, observed, ticked := false, stopped := true }
  | some value =>
    let (ticked, lastTick) := Tick.next period state.lastTick observed.now
    let value ← if ticked then do
      let value ← backend.tick value observed.now
      backend.expire value observed.now
    else pure value
    if observed.selected.isNone then backend.idle
    return { state := { state with value, lastTick }, observed, ticked, stopped := false }

/-- The actual polling and dispatch core called by `Tcp.runLoop`. In
particular, ongoing writes cannot bypass the timer or reset inbox preference. -/
def turn {m : Type → Type} [Monad m] {σ W E : Type}
    (backend : Backend m σ W E) (period : Nat) (state : State σ) : m (Result σ W E) := do
  let now ← backend.clock
  let (selected, nextSlot) ← Inbox.Priority.next state.slot backend.writes backend.events
  dispatch backend period { state with slot := nextSlot } { now, selected }

/-- The transition relation for an explicit state interpreter of the *same*
turn. Environment steps between turns, and the correspondence of this
interpreter with native I/O, are separate obligations. This relation does
not silently assume successful queue admission or frame delivery. -/
def Step {σ W E μ : Type} (backend : Backend (StateM μ) σ W E) (period : Nat)
    (before after : State σ × μ) (observed : Observation W E) (ticked : Bool) : Prop :=
  (turn backend period before.1).run before.2 =
    ({ state := after.1, observed, ticked, stopped := false }, after.2)

end Loop
end Engine.Sync
