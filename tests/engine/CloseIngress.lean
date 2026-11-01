/- A native transport close must not overtake the one frame it already
admitted. Real TCP/Noise/SQLite supplies the frame and writer failure; the
actual close/reap handlers and Loop.turn consume it. Native time is measured
separately from the proved selector opportunity bound. -/
import tests.engine.EpochFixture

namespace CloseIngress
open Engine Engine.Sync Community Connection Tests Std.Async Std.Net EpochIngress

def waitFor (ms : Nat) (p : IO Bool) : IO Bool := do
  let start ← IO.monoMsNow
  while (← IO.monoMsNow) < start + ms do
    if ← p then return true
    IO.sleep 1
  return ← p

def frameIs (peer : Peer) (target : Op) : IO Bool := do
  return (← queuedTarget peer target).isSome

/-- Discard older setup traffic at the real mailbox boundary. No Node
handler or new outbound work runs while waiting for the target frame. -/
def captureOnly (peer : Peer) (isTarget : IO Bool) : IO Bool := do
  return ← waitFor 2000 do
    if ← isTarget then return true
    discard <| peer.state.value.ingress.poll (pure none)
    return false

def failWriter (p : Peer) (s : Sock) : IO Bool := do
  for _ in [0:20] do
    if ← IO.hasFinished s.done then return true
    discard <| s.push p.cfg [(.serve, "closed-peer-write".toUTF8)]
    IO.sleep 5
  return ← waitFor 1000 (IO.hasFinished s.done)

def closedControl (p : Peer) (sid : Nat) : IO (Option Event) := do
  let start ← IO.monoMsNow
  while (← IO.monoMsNow) < start + 1000 do
    if let some e ← p.ch.tryRecv then
      if let .closed found := e then
        if found == sid then return some e
    IO.sleep 1
  return none

/-- The sender really commits removal and drains its protected notice.
The receiver has no loop turn while older setup traffic is discarded. -/
def notice (dir : String) : IO (Peer × Peer × Id × Op × Sock) := do
  let (a0, b, c, _) ← setup dir
  let some sock := b.state.value.socks.head? | throw (IO.userError "missing receiving socket")
  let settled ← waitFor 1000 do
    let o ← sock.out.atomically (getThe Outbox)
    return !o.ready && o.since.isNone
  unless settled do throw (IO.userError "setup writer did not settle")
  let adms ← view a0 (admission.byDevice.read [c, (JoinFair.device "B").pk])
  let some (_, .admission _ user _ _) := adms.rows.head? | throw (IO.userError "missing removal member")
  let removal ← view a0 (removeMember c user (JoinFair.device "A"))
  let some op := removal.ops.head? | throw (IO.userError "missing signed removal")
  submit a0 removal.ops
  let some source := a0.state.value.socks.head? | throw (IO.userError "missing sending socket")
  let mut a := a0
  for _ in [0:8] do
    a ← tick a
    if a.state.value.node.conns.isEmpty then break
  unless a.state.value.node.conns.isEmpty do throw (IO.userError "source did not retire")
  unless ← captureOnly b (frameIs b op) do throw (IO.userError "signed removal did not enter actual mailbox")
  -- Then the source's transport fails outright, as when its process dies:
  -- its retirement alone ends gracefully (`Tcp.linger`) and resets nothing.
  let some cap := source.aborter | throw (IO.userError "sending socket lacks abort")
  unless ← cap.abort do throw (IO.userError "sending socket abort failed")
  return (a, b, c, op, sock)

def freezeHub (t : Checks) : IO Unit := do
  let (hub, _) ← Ingress.Hub.new (α := Nat) 1
  let some source ← hub.reserve | throw (IO.userError "source unavailable")
  discard <| hub.offer source 7
  let observed ← IO.Promise.new
  let blocked ← IO.asTask (prio := .dedicated) do
    let first ← hub.offer source 8
    observed.resolve (first == .full)
    hub.send source 8
  t.ok "producer observes actual mailbox backpressure before freeze"
    ((← IO.wait observed.result?) == some true)
  t.ok "freeze captures exactly the already admitted value" ((← hub.freeze source) == some 7)
  t.ok "freeze cancels a backpressured producer without consuming its frame"
    ((← waitFor 500 (IO.hasFinished blocked)) && (← hub.pending) == [7])
  if ← IO.hasFinished blocked then
    t.ok "frozen producer receives explicit refusal" (match ← IO.wait blocked with | .ok false => true | _ => false)
  else
    t.ok "frozen producer receives explicit refusal" false
    hub.retire source
  let mut refused := true
  for i in [0:1000] do refused := refused && ((← hub.offer source i) == .closed)
  t.ok "flood after freeze cannot refill or replace the single owed frame" refused
  let premature ← hub.reserve
  t.ok "frozen source keeps its ownership and cannot be reused" premature.isNone
  -- A broken ownership control may reserve here; retain its failed assertion
  -- and release that exact unexpected incarnation before later cleanup.
  if let some replacement := premature then hub.retire replacement
  t.ok "normal poll still selects the original frozen value" ((← hub.poll (pure none)) == some 7)
  t.ok "repeated freeze cannot create another owed value" (← hub.freeze source).isNone
  hub.retire source
  let some replacement ← hub.reserve | throw (IO.userError "retired source not reusable")
  t.ok "retirement reuses the bounded source after frozen consumption" (replacement.index == source.index)
  discard <| hub.offer replacement 9
  discard <| hub.freeze source
  t.ok "stale freeze cannot seal a replacement incarnation"
    ((← hub.poll (pure none)) == some 9 && (← hub.offer replacement 10) == .accepted)
  hub.stop

def retained (t : Checks) (dir : String) (reap : Bool) : IO Unit := do
  let (a, b0, c, removal, sock) ← notice dir
  let some (cid, conn) := b0.state.value.node.conns.head? | throw (IO.userError "missing Noise session")
  let label := if reap then "reap" else "closed"
  t.ok s!"{label} fixture has exactly one actual admitted authenticated notice"
    ((← pending b0).length == 1 && (← frameIs b0 removal) && !(← has b0 removal))
  t.ok s!"{label} fixture reaches actual failed writer and reader completion"
    ((← failWriter b0 sock) && (← IO.hasFinished sock.readerDone))
  let control ← closedControl b0 sock.id
  t.ok s!"{label} fixture receives the writer's actual close notification" control.isSome
  let now ← IO.monoMsNow
  let st ← if reap then b0.state.value.reap b0.x b0.ch b0.notify b0.cfg now
    else match control with
      | none => pure b0.state.value
      | some event => do
        let next ← b0.state.value.handle b0.x b0.ch b0.notify b0.cfg event now
        pure (next.getD b0.state.value)
  let some source := sock.input | throw (IO.userError "native socket lacks source")
  t.ok s!"{label} retains admitted notice and session keys ahead of transport teardown"
    (st.socks.any (fun s => s.id == sock.id && s.closeAfterFrame) &&
      (← (sessionKeys cid : SqlM F _).run st.db).isSome && (← st.ingress.pending).length == 1)
  let mut refused := true
  for _ in [0:100] do
    refused := refused && ((← st.ingress.offer source (.frame sock.id "junk".toUTF8)) == .closed)
  t.ok s!"{label} refuses all later source input without releasing ownership"
    (refused && !(← source.closed.get))
  -- Deliberately exercise the exact runtime state with its old silence grace
  -- exhausted. This is an explicit transition precondition, not a claim that
  -- this fixture's earlier handshake traversed every counter value.
  let expired : RunState := { st with
    sessionGrace := [(cid, ⟨conn.heard, 0⟩)]
    socketGrace := [(sock.id, ⟨sock.heard, 0⟩)] }
  let mut b : Peer := { b0 with
    x := { b0.x with cfg := { b0.x.cfg with live := 0 } }
    cfg := { b0.cfg with idle := 0, tickMs := 0 }
    state := { b0.state with value := expired, slot := ⟨3, by decide⟩ } }
  let members ← view b (admission.byDevice.read [c, (JoinFair.device "B").pk])
  let some ((_, adm), _) := members.rows.head? | throw (IO.userError "missing Bob admission")
  let own := JoinFair.postAt c adm "B" 12345 "local write while one frozen frame is owed".toUTF8
  submit b [own]
  IO.sleep 2
  b ← tick b
  t.ok s!"{label} local write completes while same-turn tick and expiry preserve owed input"
    ((← has b own) && b.state.value.socks.any (·.closeAfterFrame) && (← frameIs b removal))
  let mut selected := 0
  for i in [0:ExpiryGrace.budget b.cfg.maxSocks] do
    if ← has b removal then break
    submit b [JoinFair.postAt c adm "B" (13000+i) "continuing queued local work".toUTF8]
    b ← tick b
    selected := selected + 1
  t.ok s!"{label} actual loop applies retained authenticated notice within its source bound"
    ((← has b removal) && selected ≤ ExpiryGrace.budget b.cfg.maxSocks &&
      !(← view b (allowPeer c (JoinFair.nodeKey "B"))))
  t.ok s!"{label} selected notice closes immediately and grants no second input grace"
    (b.state.value.socks.isEmpty && b.state.value.node.conns.isEmpty &&
      (← pending b).isEmpty && (← source.closed.get))
  stop b
  stop a


/-- An invalid native frame has no protocol-driven retirement of its own;
only the one-shot transport obligation can close after refusing this input. -/
def invalid (t : Checks) (dir : String) : IO Unit := do
  let (a, b0, _, _) ← setup dir
  let some sender := a.state.value.socks.head? | throw (IO.userError "missing sender")
  let some receiver := b0.state.value.socks.head? | throw (IO.userError "missing receiver")
  let some source := receiver.input | throw (IO.userError "missing source")
  let some (cid, _) := b0.state.value.node.conns.head? | throw (IO.userError "missing session")
  let raw : ByteArray := ⟨#[255]⟩
  discard <| sender.push a.cfg [(.urgent, raw)]
  let ready ← captureOnly b0 do
    return (← pending b0).any fun e => match e with | .frame sid bytes => sid == receiver.id && bytes == raw | _ => false
  t.ok "invalid fixture receives one real native frame before transport failure" (ready && (← pending b0).length == 1)
  stop a
  t.ok "invalid fixture reaches actual failed writer completion" (← failWriter b0 receiver)
  let some control ← closedControl b0 receiver.id | throw (IO.userError "missing actual close control")
  let st := (← b0.state.value.handle b0.x b0.ch b0.notify b0.cfg control (← IO.monoMsNow)).getD b0.state.value
  t.ok "invalid captured input retains keys for exactly one real handler"
    (st.socks.any (·.closeAfterFrame) && (← (sessionKeys cid : SqlM F _).run st.db).isSome)
  let mut b := { b0 with state := { b0.state with value := st } }
  for _ in [0:ExpiryGrace.budget b.cfg.maxSocks] do
    if b.state.value.socks.isEmpty then break
    b ← tick b
  t.ok "invalid frame refusal still closes and erases keys in its selected handler"
    (b.state.value.socks.isEmpty && (← (sessionKeys cid : SqlM F _).run st.db).isNone &&
      (← source.closed.get) && (← pending b).isEmpty)
  stop b

/-- A local authenticated removal must not be postponed behind transport's
captured incoming frame. Both payload and removal are real signed operations. -/
def localRemoval (t : Checks) (dir : String) : IO Unit := do
  let (a0, b0, c, adm) ← setup dir
  let (b, a0, target, _) ← capture b0 a0 c adm "B" 2
  let some sock := a0.state.value.socks.head? | throw (IO.userError "missing founder socket")
  let some source := sock.input | throw (IO.userError "missing founder source")
  let some (cid, _) := a0.state.value.node.conns.head? | throw (IO.userError "missing founder session")
  let members ← view a0 (admission.byDevice.read [c, (JoinFair.device "B").pk])
  let some (_, .admission _ user _ _) := members.rows.head? | throw (IO.userError "missing removed member")
  let removal ← view a0 (removeMember c user (JoinFair.device "A"))
  stop b
  t.ok "local removal fixture reaches a real transport failure with admitted peer data"
    ((← failWriter a0 sock) && (← frameIs a0 target))
  let some event ← closedControl a0 sock.id | throw (IO.userError "missing founder close control")
  let st := (← a0.state.value.handle a0.x a0.ch a0.notify a0.cfg event (← IO.monoMsNow)).getD a0.state.value
  t.ok "local removal starts with exactly one frozen transport obligation"
    (st.socks.any (·.closeAfterFrame) && (← st.ingress.pending).length == 1)
  let mut a := { a0 with state := { a0.state with value := st, slot := ⟨3, by decide⟩ } }
  submit a removal.ops
  a ← tick a
  t.ok "authenticated local removal immediately bypasses transport frame retention"
    (a.state.value.socks.isEmpty && a.state.value.node.conns.isEmpty &&
      (← (sessionKeys cid : SqlM F _).run st.db).isNone && (← source.closed.get) &&
      !(← has a target) && (← pending a).isEmpty && !(← view a (allowPeer c (JoinFair.nodeKey "B"))))
  stop a

/-- A real SQLite refusal or post-commit notification exception happens
only after the retained valid frame has been selected out of its mailbox. -/
def handlerFailure (t : Checks) (dir : String) (database : Bool) : IO Unit := do
  let (a0, b0, c, adm) ← setup dir
  let (b, a0, target, _) ← capture b0 a0 c adm "B" 3
  let some sock := a0.state.value.socks.head? | throw (IO.userError "missing failure socket")
  let some source := sock.input | throw (IO.userError "missing failure source")
  let some (cid, _) := a0.state.value.node.conns.head? | throw (IO.userError "missing failure session")
  stop b
  unless ← failWriter a0 sock do throw (IO.userError "failure fixture writer still running")
  let some event ← closedControl a0 sock.id | throw (IO.userError "missing failure close control")
  let st := (← a0.state.value.handle a0.x a0.ch a0.notify a0.cfg event (← IO.monoMsNow)).getD a0.state.value
  let label := if database then "SQLite error" else "notification error"
  let retained := st.socks.any (·.closeAfterFrame) && (← st.ingress.pending).length == 1 &&
    (← (sessionKeys cid : SqlM F _).run st.db).isSome && !(← has a0 target)
  t.ok s!"{label} starts with one frozen valid frame and live session" retained
  unless retained do
    stop a0
    return
  let some selected ← st.ingress.poll (pure none) | throw (IO.userError "missing selected failing frame")
  if database then st.db.exec "PRAGMA query_only=ON"
  let notify : List Id → IO Unit := if database then a0.notify
    else fun _ => throw (IO.userError "expected CloseIngress notification failure")
  let failed ← try
    discard <| st.handle a0.x a0.ch notify a0.cfg selected (← IO.monoMsNow)
    pure false
  catch error =>
    pure <| if database then (error.toString.splitOn "readonly").length > 1
      else (error.toString.splitOn "expected CloseIngress notification failure").length > 1
  t.ok s!"{label} reports the original selected-handler failure" failed
  t.ok s!"{label} releases frozen native source even when close-time SQL can fail"
    ((← source.closed.get) && (← st.ingress.pending).isEmpty &&
      (← st.ingress.offer source selected) == .closed && (← sock.stopped.get))
  if database then st.db.exec "PRAGMA query_only=OFF"
  else
    t.ok "post-commit notification failure still applies input and erases the session"
      ((← has a0 target) && (← (sessionKeys cid : SqlM F _).run st.db).isNone)
  -- Restore storage only after the failure/ownership assertions. A failed
  -- runner cannot promise durable erasure while the store refuses writes.
  stop a0

end CloseIngress

def main (args : List String) : IO UInt32 := do
  let dir := args.headD "out/close-ingress/manual"
  let t ← Tests.Checks.new
  CloseIngress.freezeHub t
  CloseIngress.retained t (dir ++ "/closed") false
  CloseIngress.retained t (dir ++ "/reap") true
  CloseIngress.invalid t (dir ++ "/invalid")
  CloseIngress.localRemoval t (dir ++ "/local-removal")
  CloseIngress.handlerFailure t (dir ++ "/sqlite-error") true
  CloseIngress.handlerFailure t (dir ++ "/notification-error") false
  t.finish "close-ingress"
