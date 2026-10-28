/-
The runner's socket waits do not depend on the shared task pool.

A phone decodes photos on every pool worker for seconds at a time. If a
socket read or send needed a pool task, as `Async.block` does (it runs
the operation, and maps its result, as default-priority tasks), sync
would wait behind the decodes. This fills the pool with busy tasks for
a few seconds, then times one 64 KiB frame sent and received over
loopback with the runner's `sendOn` and `awaitUv`: it must take well
under a second. The negative control does the same with `Async.block`
and must stall until the busy tasks end.
-/
import engine.wire.Tcp
import tests.engine.Lib

open Std Std.Async Std.Net Engine.Sync Tests

def loopback (port : UInt16) : SocketAddress := .v4 ⟨IPv4Addr.ofParts 127 0 0 1, port⟩

/-- A connected pair over loopback: the dialer and the accepted socket. -/
def pair : IO (TCP.Socket.Client × TCP.Socket.Client) := do
  let srv ← TCP.Socket.Server.mk
  srv.bind (loopback 0)
  srv.listen 4
  let port := match ← srv.getSockName with
    | .v4 a => a.port
    | .v6 a => a.port
  let c ← TCP.Socket.Client.mk
  let dial ← IO.asTask (prio := .dedicated) (awaitUv (c.native.connect (loopback port)))
  let rec accept (fuel : Nat) : IO TCP.Socket.Client := do
    match fuel, ← srv.tryAccept with
    | _, some a => pure a
    | 0, none => throw (.userError "no connection accepted")
    | k + 1, none => IO.sleep 5; accept k
  let a ← accept 2000
  let _ ← IO.wait dial
  return (c, a)

/-- Fill the pool: 64 busy tasks (more than this machine's 32 workers),
each spinning for `ms`. -/
def fillPool (ms : Nat) : IO (List (Task (Except IO.Error Unit))) := do
  let n := 64
  let mut ts := []
  for _ in [0:n] do
    ts := (← IO.asTask (prio := .default) do
      let t0 ← IO.monoMsNow
      while (← IO.monoMsNow) < t0 + ms do pure ()) :: ts
  return ts

/-- Time one frame through: send on `a`, receive it whole on `b`. -/
def through (send : TCP.Socket.Client → ByteArray → IO Bool)
    (recv : TCP.Socket.Client → IO (Option ByteArray)) (a b : TCP.Socket.Client) (n : Nat) :
    IO (Nat × Bool) := do
  let payload := ByteArray.mk ((List.range n).map (·.toUInt8)).toArray
  let t0 ← IO.monoMsNow
  let ok ← send a payload
  let mut buf := ByteArray.empty
  let mut done := false
  while !done do
    match ← recv b with
    | some chunk =>
      buf := buf ++ chunk
      match unframe buf with
      | .frame p _ => done := true; buf := p
      | _ => pure ()
    | none => done := true
  return ((← IO.monoMsNow) - t0, ok && buf == payload)

def main : IO UInt32 := do
  let t ← Checks.new
  let n := 65536
  let busyMs := 3000
  -- The runner's way: no task on the pool.
  let (a, b) ← pair
  let busy ← fillPool busyMs
  IO.sleep 50
  let (ms, ok) ← through sendOn
    (fun c => do match ← awaitUv (c.native.recv? 65536) with | .ok r => pure r | .error _ => pure none)
    a b n
  IO.println s!"poolstarve: pool busy, runner path: {ms} ms"
  t.ok s!"with every pool worker busy, a 64 KiB frame crosses loopback in {ms} ms" (ok && ms < 1000)
  for x in busy do discard <| IO.wait x
  -- Negative control: Async.block waits behind the busy tasks.
  let (c, d) ← pair
  let busy2 ← fillPool busyMs
  IO.sleep 50
  let (ms2, ok2) ← through
    (fun c p => do match ← (c.send (frame p)).block.toBaseIO with | .ok _ => pure true | .error _ => pure false)
    (fun c => do match ← (c.recv? 65536).block.toBaseIO with | .ok r => pure r | .error _ => pure none)
    c d n
  IO.println s!"poolstarve: pool busy, Async.block path: {ms2} ms"
  t.ok s!"control: through Async.block the same frame waits {ms2} ms, behind the busy tasks" (ok2 && ms2 ≥ 2000)
  for x in busy2 do discard <| IO.wait x
  t.finish "poolstarve"
