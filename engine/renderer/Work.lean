/- Cooperative execution for component-owned work. Only queue bookkeeping
is locked. A worker never holds the mutex while reading, decoding, painting,
sleeping, or waiting for a native effect. There is at most one worker per
pool, and it exits when idle. Cancellation is checked at each continuation
and again, atomically with publication, when a result completes. -/
import engine.renderer.Demand
import Std.Sync.Mutex

namespace Work

/-- One bounded step. None yields; the closure keeps its private progress.
Some completes. A failed step is retired, never repeatedly retried. -/
abbrev Action (V : Type) := Unit → IO (Option V)

structure Handle (K V : Type) where
  ticket : Demand.Ticket K
  result : Task (Option V)

structure Job (K V : Type) where
  ticket : Demand.Ticket K
  action : Action V
  promise : IO.Promise (Option V)

structure Stats where
  started : Nat := 0
  steps : Nat := 0
  completed : Nat := 0
  cancelled : Nat := 0
  maxUs : Nat := 0
  deriving Repr

structure State (K V : Type) where
  plan : Demand.Plan K := {}
  jobs : List (Job K V) := []
  handles : List (Handle K V) := []
  running : Bool := false
  paused : Bool := false
  background : Bool := true
  stats : Stats := {}

structure Pool (K V : Type) where
  state : Std.Mutex (State K V)

variable {K V : Type} [BEq K]

def Pool.new : IO (Pool K V) := return ⟨← Std.Mutex.new {}⟩

def Pool.stats (p : Pool K V) : IO Stats := p.state.atomically do return (← get).stats

def Pool.pause (p : Pool K V) (paused : Bool) : IO Unit :=
  p.state.atomically do modify fun s => { s with paused }

/-- Hold speculative work while a foreground dependency is still in flight.
Visible work remains admitted, including work published by a later frame. -/
def Pool.allowBackground (p : Pool K V) (allow : Bool) : IO Unit :=
  p.state.atomically do modify fun s => { s with background := allow }

/-- Revoke immediately, and resolve retired queued handles without
running their closures. An in-flight step is checked when it returns. -/
def Pool.reconcile (p : Pool K V) (needs : List (Demand.Need K)) : IO Unit := do
  let retired ← p.state.atomically do
    let s ← get
    if s.plan.needs == needs then return []
    let plan := s.plan.reconcile needs
    let retired := s.jobs.filter (fun j => !plan.current j.ticket)
    set { s with
      plan, jobs := s.jobs.filter (fun j => plan.current j.ticket),
      handles := s.handles.filter (fun h => plan.current h.ticket),
      stats := { (s.stats) with cancelled := s.stats.cancelled + retired.length } }
    return retired
  for j in retired do j.promise.resolve none

private partial def run (p : Pool K V) : IO Unit := do
  let choice ← p.state.atomically do
    let s ← get
    if s.jobs.isEmpty then
      set { s with running := false }
      return (false, none)
    if s.paused then return (true, none)
    let key := Demand.next (fun t => s.plan.visible t.key) s.background (s.jobs.map (·.ticket))
    let job := key.bind fun k => s.jobs.find? (fun j => j.ticket == k)
    if let some j := job then
      set { s with jobs := s.jobs.filter (fun x => x.ticket != j.ticket) }
    return (true, job)
  match choice with
  | (false, _) => return
  | (true, none) => IO.sleep 1
  | (true, some job) =>
    -- Reconciliation can win after selection. Check again before IO.
    let current ← p.state.atomically do return (← get).plan.current job.ticket
    let start ← IO.monoNanosNow
    let result ← if current then
      try pure (some (← job.action ()))
      catch e => IO.eprintln s!"component work: {e}"; pure none
    else pure none
    let elapsed := ((← IO.monoNanosNow) - start) / 1000
    p.state.atomically do
      let s ← get
      let stats := { (s.stats) with
        steps := s.stats.steps + (if current then 1 else 0),
        maxUs := max s.stats.maxUs elapsed }
      match result with
      | some none =>
        if s.plan.current job.ticket then
          set { s with jobs := s.jobs ++ [job], stats }
        else
          job.promise.resolve none
          set { s with stats := { stats with cancelled := stats.cancelled + 1 } }
      | some (some value) =>
        let accepted := Demand.complete s.plan job.ticket value
        job.promise.resolve accepted
        set { s with stats := { stats with
          completed := stats.completed + (if accepted.isSome then 1 else 0),
          cancelled := stats.cancelled + (if accepted.isNone then 1 else 0) } }
      | none =>
        job.promise.resolve none
        set { s with stats := { stats with cancelled := stats.cancelled + 1 } }
  run p

/-- Declare an owned request and start it once. The end-of-frame
reconciliation removes declarations not made by any mounted component.
`action` is a thunk: even constructing an unused request performs no IO. -/
def Pool.request (p : Pool K V) (need : Demand.Need K) (action : Action V) : IO (Handle K V) := do
  let (handle, start) ← p.state.atomically do
    let s ← get
    let plan := if s.plan.needs.contains need then s.plan else
      s.plan.reconcile (need :: s.plan.needs.filter (fun n => !(n.owner == need.owner && n.key == need.key)))
    let some ticket := plan.ticket need.key | throw (IO.userError "missing declared demand")
    if let some handle := s.handles.find? (fun h => h.ticket == ticket) then
      set { s with plan }
      return (handle, false)
    let promise : IO.Promise (Option V) ← IO.Promise.new
    let handle := { ticket, result := promise.resultD none : Handle K V }
    let job : Job K V := ⟨ticket, action, promise⟩
    set { s with
      plan, jobs := s.jobs ++ [job],
      handles := handle :: s.handles, running := true,
      stats := { (s.stats) with started := s.stats.started + 1 } }
    return (handle, !s.running)
  if start then
    let _ ← IO.asTask (prio := .dedicated) (run p)
  return handle

def Handle.value (h : Handle K V) : IO (Option V) := do
  if ← IO.hasFinished h.result then return h.result.get else return none

end Work
