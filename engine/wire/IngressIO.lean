/- Native ownership for the bounded ingress core. Never block on a channel's
producer promise: a producer retries a single bounded offer and observes both
its own retirement and global shutdown. -/
import engine.wire.Ingress
import Std.Sync.Mutex

namespace Engine.Sync.Ingress

structure Source where
  index : Nat
  closed : IO.Ref Bool

structure Registry (α : Type) (n : Nat) where
  state : State α n := {}
  live : Vector Bool (n + 1) := Vector.replicate (n + 1) false
  closed : Bool := false

structure Hub (α : Type) where
  peers : Nat
  registry : Std.Mutex (Registry α peers)

inductive Offered where
  | accepted
  | full
  | closed
  deriving BEq, Repr

def Hub.new {α : Type} (peers : Nat) : IO (Hub α × Source) := do
  let registry ← Std.Mutex.new (α := Registry α peers)
    { live := (Vector.replicate (peers + 1) false).set 0 true }
  let closed ← IO.mkRef false
  return (⟨peers, registry⟩, ⟨0, closed⟩)

/-- Slot zero belongs permanently to runner control. Peers retain fixed
positions until retirement; adding another peer never moves them. -/
def Hub.reserve {α : Type} (hub : Hub α) : IO (Option Source) :=
  hub.registry.atomically do
    let r ← getThe (Registry α hub.peers)
    if r.closed then return none
    for i in [:hub.peers + 1] do
      if h : i < hub.peers + 1 then
        unless r.live[i] do
          let closed ← IO.mkRef false
          set { r with live := r.live.set i true }
          return some ⟨i, closed⟩
    return none

/-- The close flag is checked inside the same critical section that admits
the value. An old producer cannot fill a slot that has since been reused. -/
def Hub.offer {α : Type} (hub : Hub α) (source : Source) (value : α) : IO Offered :=
  hub.registry.atomically do
    let r ← getThe (Registry α hub.peers)
    if r.closed || (← source.closed.get) then return .closed
    if h : source.index < hub.peers + 1 then
      unless r.live[source.index] do return .closed
      let (accepted, state) := r.state.offer ⟨source.index, h⟩ value
      set { r with state }
      return if accepted then .accepted else .full
    return .closed

def Hub.retire {α : Type} (hub : Hub α) (source : Source) : IO Unit :=
  hub.registry.atomically do
    if ← source.closed.get then return
    source.closed.set true
    let r ← getThe (Registry α hub.peers)
    if h : source.index < hub.peers + 1 then
      set { r with
        live := r.live.set source.index false
        state := r.state.cancel ⟨source.index, h⟩ }

def Hub.stop {α : Type} (hub : Hub α) : IO Unit :=
  hub.registry.atomically do
    modify fun r => { r with
      closed := true
      state := { r.state with slots := Vector.replicate (hub.peers + 1) none } }

def Hub.stopped {α : Type} (hub : Hub α) : IO Bool :=
  hub.registry.atomically do return (← getThe (Registry α hub.peers)).closed

/-- Bounded snapshot of already admitted values. It neither consumes input
nor advances the source cursor; the actual loop remains its sole consumer. -/
def Hub.pending {α : Type} (hub : Hub α) : IO (List α) :=
  hub.registry.atomically do
    return (← getThe (Registry α hub.peers)).state.slots.toArray.toList.filterMap id

/-- Control is sampled only into its own empty slot. It cannot occupy a
peer's slot. Polling calls the exact proved pure core while holding its lock. -/
def Hub.poll {α : Type} (hub : Hub α) (control : IO (Option α)) : IO (Option α) :=
  hub.registry.atomically do
    let mut r ← getThe (Registry α hub.peers)
    if r.closed then return none
    if r.state.slots[0].isNone then
      if let some value ← control then
        r := { r with state := (r.state.offer ⟨0, by omega⟩ value).2 }
    let (selected, state) := r.state.poll
    set { r with state }
    return selected.map Prod.snd

/-- One value remains on this dedicated producer's stack during backpressure.
Retirement/shutdown ends that wait without depending on channel.close. -/
def Hub.send {α : Type} (hub : Hub α) (source : Source) (value : α)
    (cancel : IO Bool := pure false) : IO Bool := do
  repeat
    if ← cancel then return false
    match ← hub.offer source value with
    | .accepted => return true
    | .closed => return false
    | .full => IO.sleep 1

end Engine.Sync.Ingress
