/- Exact branch/order checks of the same monadic turn used by TCP. The
backend records completed calls; JoinFair additionally exercises its native
SQLite/socket implementation under delay, disconnect and continuous writes. -/
import engine.wire.Loop
import tests.engine.Checks

namespace LoopChecks
open Engine.Sync Tests

structure Memory where
  now : Nat := 0
  writes : List Nat := []
  events : List Nat := []
  calls : List String := []

def record (call : String) : StateM Memory Unit :=
  modify fun s => { s with calls := s.calls ++ [call] }

def backend : Loop.Backend (StateM Memory) Nat Nat Nat where
  clock := do record "clock"; return (← get).now
  writes := do
    record "poll-write"
    modifyGet fun s => (s.writes.head?, { s with writes := s.writes.drop 1 })
  events := do
    record "poll-event"
    modifyGet fun s => (s.events.head?, { s with events := s.events.drop 1 })
  write := fun value w _ => do record "write"; return value + w
  event := fun value e _ => do
    record "event"
    return if e = 0 then none else some (value + e)
  tick := fun value _ => do record "tick"; return value + 1000
  expire := fun value _ => do record "expire"; return value + 10000
  stop := fun value _ => do record "stop"; return value + 100000
  idle := record "idle"

def run (t : Checks) : IO Unit := do
  let (first, mem) := (Loop.turn backend 10 { value := 0 }).run
    { now := 10, writes := [7, 8], events := [9] }
  t.ok "shared turn handles write then due tick then socket expiry"
    (mem.calls == ["clock", "poll-write", "write", "tick", "expire"] &&
      first.state.value == 11007 && first.state.lastTick == 10 && first.ticked && !first.stopped)
  t.ok "shared turn reports the actual selected primary write and sampled time"
    (first.observed.now == 10 && first.observed.selected == some (.inl 7) &&
      !first.state.writeFirst && mem.writes == [8] && mem.events == [9])
  let (second, mem') := (Loop.turn backend 10 first.state).run
    { mem with now := 11, writes := mem.writes ++ [10], calls := [] }
  t.ok "shared turn persists preference while writes remain continuously available"
    (mem'.calls == ["clock", "poll-event", "event"] &&
      second.observed.selected == some (.inr 9) && second.state.value == 11016 &&
      second.state.writeFirst && !second.ticked && second.state.lastTick == 10 &&
      mem'.writes == [8, 10])
  let (stop, mem) := (Loop.turn backend 10
    { value := 5, writeFirst := false, lastTick := 0 }).run
    { now := 30, writes := [7], events := [0] }
  t.ok "stop dispatch cleans up once and bypasses an otherwise due timer"
    (mem.calls == ["clock", "poll-event", "event", "stop"] &&
      stop.stopped && !stop.ticked && stop.state.value == 100005 &&
      stop.state.lastTick == 0 && stop.state.writeFirst && mem.writes == [7])
  let (idle, mem) := (Loop.turn backend 10 { value := 0, lastTick := 10 }).run
    { now := 20 }
  t.ok "empty inbox still ticks and checks expiry before idle sleep"
    (mem.calls == ["clock", "poll-write", "poll-event", "tick", "expire", "idle"] &&
      idle.ticked && !idle.stopped && idle.state.value == 11000 &&
      idle.observed.selected.isNone && idle.state.lastTick == 20)
  let (fallback, mem) := (Loop.turn backend 10 { value := 2 }).run
    { now := 1, events := [3] }
  t.ok "empty preferred write queue immediately falls back to a network event"
    (mem.calls == ["clock", "poll-write", "poll-event", "event"] &&
      fallback.state.value == 5 && fallback.observed.selected == some (.inr 3) &&
      !fallback.ticked && !fallback.stopped)
  let (fallback, mem) := (Loop.turn backend 10 { value := 2, writeFirst := false }).run
    { now := 1, writes := [4] }
  t.ok "empty preferred event queue immediately falls back to a local write"
    (mem.calls == ["clock", "poll-event", "poll-write", "write"] &&
      fallback.state.value == 6 && fallback.observed.selected == some (.inl 4) &&
      !fallback.ticked && !fallback.stopped)
  let (idle, mem) := (Loop.turn backend 10 { value := 2, lastTick := 10 }).run
    { now := 19 }
  t.ok "non-due empty turn retains last tick and sleeps exactly once"
    (mem.calls == ["clock", "poll-write", "poll-event", "idle"] &&
      !idle.ticked && !idle.stopped && idle.state.value == 2 && idle.state.lastTick == 10)

end LoopChecks
