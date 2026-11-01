/- Actual signed bootstrap, Noise, TCP and SQLite supply nonempty live sessions.
The direct repeat-open case then checks the same production handler in isolation;
it does not pretend the network itself requested that extra open. -/
import tests.engine.EpochFixture

namespace NodeUniqueChecks
open Engine Engine.Sync Community Connection Tests EpochIngress

def unique (n : Node) : Bool :=
  decide ((n.conns.map Prod.fst).Nodup ∧ n.retryOrder.Nodup)

def run (dir : String) (t : Checks) : IO Unit := do
  let (a0, b0, community, _) ← setup dir 60000
  let mut a := a0
  let mut b := b0
  try
    t.ok "signed bootstrap establishes a nonempty shared Noise session" (shared a b)
    t.ok "both actual bootstrapped Nodes have unique session IDs" (unique a.state.value.node && unique b.state.value.node)
    let post := JoinFair.postAt community community "A" 401 "actual uniqueness write".toUTF8
    submit a [post]
    let mut every := true
    for _ in [0:6000] do
      a ← tick a
      b ← tick b
      every := every && unique a.state.value.node && unique b.state.value.node
      if ← has b post then break
      IO.sleep 1
    t.ok "signed write crosses actual SQLite TCP handlers" (← has b post)
    t.ok "every completed write frame and timer prefix retains uniqueness" every
    let n := a.state.value.node
    let established ← a.x.hooks.established.run a.state.value.db
    t.ok "production established hook supplies an actual authenticated session" (!established.isEmpty)
    let duplicate := { a.x with hooks := { a.x.hooks with
      established := do let es ← a.x.hooks.established; pure (es ++ es) } }
    let (followed, _) ← (n.follow duplicate (← IO.monoMsNow)).run a.state.value.db
    t.ok "repeated actual established rows do not duplicate live IDs"
      (unique followed && followed.conns.length == n.conns.length)
    let (swept, _) ← (n.sweepAll a.x (n.conns.map Prod.fst) {}).run a.state.value.db
    t.ok "actual nonempty retry sweep retains each session once"
      (unique swept && !swept.retryOrder.isEmpty && swept.retryOrder.length == n.conns.length)
    let (sweptAgain, _) ← (swept.sweepAll a.x (swept.conns.map Prod.fst) {}).run a.state.value.db
    t.ok "repeated actual retry sweeps do not duplicate queue entries"
      (unique sweptAgain && sweptAgain.retryOrder.length == n.conns.length)
    if let some (cid, addr, dialer) := established.head? then
      let mut reopened := n
      for _ in [0:3] do
        reopened := (← (reopened.open a.x cid addr dialer (← IO.monoMsNow)).run a.state.value.db).1
      t.ok "actual repeat-open replaces the existing session ID"
        (unique reopened && reopened.conns.length == n.conns.length)
      let (closed, _) ← (sweptAgain.step a.x (.close addr) (← IO.monoMsNow)).run a.state.value.db
      t.ok "actual transport close removes sessions while preserving retry uniqueness"
        (unique closed && closed.conns.all (fun p => p.1 != cid))
    else
      t.ok "actual repeat-open replaces the existing session ID" false
      t.ok "actual transport close removes sessions while preserving retry uniqueness" false
  finally
    discard <| (stop a).toBaseIO
    discard <| (stop b).toBaseIO

end NodeUniqueChecks

def main (args : List String) : IO UInt32 := do
  let t ← Tests.Checks.new
  NodeUniqueChecks.run (args.headD "out/node-uniqueness/runtime") t
  t.finish "node-uniqueness"
