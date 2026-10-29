/- Home's count and the app's parked writes against the real node loop,
without TCP. The boot and consumer gates force both pending-start and
full-channel paths; store counts never include the app's outbox. -/
import platforms.headless.Sim
import tests.engine.Checks

open App Engine Engine.Sync Community Data Tests

namespace LifecycleNode

@[extern "lq_test_listener"] opaque listener : IO Std.Internal.UV.TCP.Socket

/-- The production runner loop and store, with a gated in-memory channel
instead of sockets. No substitute for Node.onWrite or its SQLite writes. -/
def node (path : String) (consume : IO.Ref Bool) : IO Runner := do
  let db ← openDb path
  let x : Sync SF (SqlM SF) := { fam, cfg := {}, hooks := Connection.hooks fam Connection.sodium .empty }
  let node := Node.boot fam (← (dumpOps (F := SF)).run db) 0
  let cfg : RunConfig := { queue := 1 }
  let ch ← eventChannel cfg
  let writes ← Std.CloseableChannel.Sync.new (some cfg.queue)
  let slots ← Std.Mutex.new []
  let done ← IO.asTask (prio := .dedicated) do
    while !(← consume.get) do IO.sleep 1
    runLoop x ch (fun _ => pure ()) cfg writes { db, node, slots }
  return {
    events := ch, writes, port := 0, done, slots
    stopped := ← IO.mkRef false, listening := Task.pure (.ok ()),
    listener := ← listener, closing := ← Std.Mutex.new false }

def stored (s : St) : IO Nat := do
  let ((v, _), _) ← (Reader.eval (.count s.me.c none)).run { rd := s.rd }
  match v with
  | .count a b => return a + b
  | _ => throw (IO.userError "expected count")

def advance (ms : Nat) (p : St → IO Bool) : M Bool := do
  let end_ := (← IO.monoMsNow) + ms
  while (← IO.monoMsNow) < end_ do
    steps 1
    if ← p (← get) then return true
    IO.sleep 2
  return false

def run (dir : String) (ck : Checks) : IO Unit := do
  IO.FS.createDirAll dir
  let path := dir ++ "/node.db"
  for suffix in ["", "-wal", "-shm"] do
    if ← System.FilePath.pathExists (path ++ suffix) then IO.FS.removeFile (path ++ suffix)
  let sm ← Sim.new
  let s ← App.start sm.io (← sm.viewport.get) path
  let boot ← IO.mkRef false
  let consume ← IO.mkRef false
  let (_, _) ← (show M Unit from do
    found "Node" "Ann"
    waitIdle sm
    openPage .chat
    discard <| sendText "before chaos"
    waitIdle sm
    let message := (← get).ids[0]!.2
    switchToAcc (← get).cur
    let task ← IO.asTask (prio := .dedicated) do
      while !(← boot.get) do IO.sleep 1
      node path consume
    modify fun s => { s with netCfg := some (0, true), netBoot := some task }
    sm.cmds.modify (·.push "chaos 30")
    let parked ← advance 5000 fun s => pure (s.chaos.isNone && !s.toNode.isEmpty)
    ck.ok "chaos parks while netBoot is pending" parked
    let issued := (← get).toNode.toList.flatten
    ck.ok "pending boot has not written chaos to the store" ((← stored (← get)) == 1)
    boot.set true
    discard <| advance 5000 fun s => pure s.net.isSome
    discard <| reactTo message "👋"
    ck.ok "full node channel retains unoffered writes" (!(← get).toNode.isEmpty)
    consume.set true
    let delivered ← advance 5000 fun s => return (← stored s) == 31 && s.toNode.isEmpty
    ck.ok "chaos reaches the actual node store after boot and backpressure" delivered
    let mut allStored := !issued.isEmpty
    for op in issued do
      if (← (Q.op op.id).run (← get).rd #[]) != .bytes (some op.bytes) then allStored := false
    ck.ok s!"all {issued.length} parked chaos ops are stored byte for byte" allStored
    steps 5
    ck.ok "Home's count follows the stored chaos messages" ((← get).page == .home && (← get).total == 31)
    ck.ok "Home never remounts the hidden conversation" ((← get).rows.isEmpty && (← get).reader.isNone)
    let old := (← get).live.reads
    steps 3
    ck.ok "Home's stable subscriptions do not reread" ((← get).live.reads == old)
    discard <| step [.background]).run s

/-- A full channel, a late boot, a scheduled reader and a slow producer
all outlive the deadline. Their work stays owned and is reaped later. -/
def bounded (dir : String) (ck : Checks) : IO Unit := do
  let path := dir ++ "/bounded.db"
  for suffix in ["", "-wal", "-shm"] do
    if ← System.FilePath.pathExists (path ++ suffix) then IO.FS.removeFile (path ++ suffix)
  let sm ← Sim.new
  let s ← App.start sm.io (← sm.viewport.get) path
  let (_, _) ← (show M Unit from do
    found "Bounded" "Ann"
    waitIdle sm
    openPage .chat
    discard <| sendText "anchor"
    waitIdle sm
    let before ← get
    let message := before.ids[0]!.2
    let consume ← IO.mkRef false
    let old ← node path consume
    discard <| old.writes.trySend []
    modify fun s => { s with net := some old }
    let release ← IO.asTask (prio := .dedicated) do IO.sleep 400; consume.set true
    let begin ← IO.monoMsNow
    suspend 150
    ck.ok "suspend returns within its deadline with a full stop channel" ((← IO.monoMsNow) ≤ begin + 150)
    ck.ok "timed-out runner remains owned" (← pure (← get).netStop.isSome)
    modify fun s => { s with active := false }
    let first := Community.react before.me.c before.me.adm message before.me.dev "1".toUTF8 1
    let second := Community.react before.me.c before.me.adm message before.me.dev "2".toUTF8 2
    submit ⟨[first], true⟩
    submit ⟨[second], true⟩
    flushNode
    ck.ok "timeout preserves parked writes in order" ((← get).toNode.toList.flatten.map (·.id) == [first.id, second.id])
    let frames ← sm.frames.get
    let begin ← IO.monoMsNow
    discard <| step [.foreground]
    ck.ok "resume does not join the stopping runner" ((← IO.monoMsNow) < begin + 100)
    ck.ok "resume neither starts a second runner nor offers parked writes early"
      ((← get).net.isNone && (← get).netBoot.isNone && (← get).toNode.size == 2 && (← sm.frames.get) == frames)
    let third := Community.react before.me.c before.me.adm message before.me.dev "4".toUTF8 4
    submit ⟨[third], true⟩
    flushNode
    ck.ok "foreground writes also park while teardown is pending"
      ((← get).toNode.toList.flatten.map (·.id) == [first.id, second.id, third.id] && (← Data.status before.rd third.id).isNone)
    discard <| IO.wait release
    if let some t := (← get).netStop then discard <| IO.wait t
    reap
    let next ← node path (← IO.mkRef true)
    modify fun s => { s with active := false, netCfg := some (0, true), netBoot := some (Task.pure (.ok next)) }
    discard <| step [.foreground]
    let arrived ← advance 3000 fun s => do
      let valid (o : Op) : IO Bool := do
        return match ← Data.status s.rd o.id with | some (.valid _) => true | _ => false
      return s.toNode.isEmpty && (← valid first) && (← valid second) && (← valid third)
    ck.ok "parked writes reach the replacement node's store" arrived
    let (_, revoked) ← (Reader.read (Q.op first.id)).run { rd := before.rd, enabled := pure false }
    ck.ok "revoked reader issues no query" (revoked.live.reads == 0 && revoked.live.entries.isEmpty)
    let sh ← Reader.Shared.new (← IO.mkRef 0)
    let want := Reader.Want.window before.me.c none 0 0
    sh.setWants #[want]
    let checks ← IO.mkRef (0 : Nat)
    let enabled : IO Bool := checks.modifyGet fun n => (decide (n < 3), n + 1)
    let (_, cancelled) ← (Reader.pass sh).run { rd := before.rd, enabled }
    ck.ok "revocation during a real pass prevents later queries" (cancelled.live.reads == 1 && (← checks.get) > 3)
    ck.ok "revoked pass cannot publish its answer" (((← sh.board.get).get? want).isNone)
    ck.ok "old runner rejects offers after teardown" (!(← old.writes.trySend []))
    discard <| step [.background]
    -- A boot that finishes only after suspension must still be stopped.
    let late ← IO.mkRef (none : Option Runner)
    let boot ← IO.asTask (prio := .dedicated) do
      IO.sleep 400
      let r ← node path (← IO.mkRef true)
      late.set (some r)
      return r
    modify fun s => { s with active := true, netBoot := some boot }
    let begin ← IO.monoMsNow
    suspend 150
    ck.ok "late boot cannot extend the suspend deadline" ((← IO.monoMsNow) ≤ begin + 150)
    ck.ok "late boot teardown remains owned" (← pure (← get).netStop.isSome)
    discard <| IO.wait boot
    if let some t := (← get).netStop then discard <| IO.wait t
    reap
    ck.ok "a runner born after timeout is stopped" (← match ← late.get with
      | some r => r.stopped.get | none => pure false)
    -- A reader scheduled before unmount, and a producer/decoder that
    -- finish afterwards. No future can publish into the detached page.
    modify fun s => { s with active := true, netCfg := none }
    mountPage
    let sh := (← get).sh
    let stopped ← IO.mkRef false
    let rd ← openDb path
    let reader ← IO.asTask (prio := .dedicated) do
      IO.sleep 400
      Reader.work sh stopped { rd }
    let produced := Community.react before.me.c before.me.adm message before.me.dev "3".toUTF8 3
    let producer ← IO.asTask (prio := .dedicated) do
      IO.sleep 400
      return #[({ ops := [produced], mine := true } : Job)]
    let decoding ← IO.asTask (prio := .dedicated) do IO.sleep 400; return (none : Option String)
    (← get).wr.busy.modify (· + 1)
    modify fun s => { s with
      active := true, netCfg := none, reader := some ⟨stopped, reader⟩, rst := none,
      chaos := some (producer.map fun r => r.toOption.getD #[]),
      decoding := some (decoding.map fun r => r.toOption.getD none) }
    let begin ← IO.monoMsNow
    suspend 150
    ck.ok "reader, decoder and producer share one suspend deadline" ((← IO.monoMsNow) ≤ begin + 150)
    ck.ok "timed-out work remains owned and reader is revoked" ((← stopped.get) &&
      (← get).readerStop.isSome && !(← get).paintStop.isEmpty && (← get).chaos.isSome)
    discard <| IO.wait reader
    discard <| IO.wait producer
    discard <| IO.wait decoding
    -- The mapped futures are scheduled separately from their producers.
    -- Poll the handles owned by the app, just as background steps do.
    let settled ← waitFor ((← IO.monoMsNow) + 1000) do
      reap
      let s ← get
      return s.chaos.isNone && s.readerStop.isNone && s.paintStop.isEmpty && (← s.wr.saveDone)
    ck.ok "retired tasks settle through background polling" settled
    let cp ← Lifecycle.load (← get).rd
    let durable := cp.bind fun cp => (Codec.decode (cp.2.2.2.2.2[10]?.getD .empty) : Option (List ByteArray))
    ck.ok "late producer becomes a durable parked write" ((← get).toNode.toList.flatten.map (·.id) == [produced.id] &&
      (← get).queuedWrites.contains produced.bytes && (durable.getD []).contains produced.bytes &&
      (← (← get).wr.busy.get) == 0)
    ck.ok "late tasks cannot repopulate the unmounted page" ((← get).rows.isEmpty &&
      (← get).decoding.isNone && (← (← get).sh.wants.get).isEmpty)
    let last ← node path (← IO.mkRef true)
    modify fun s => { s with active := false, netCfg := some (0, true), netBoot := some (Task.pure (.ok last)) }
    discard <| step [.foreground]
    let delivered ← advance 3000 fun s => pure (s.toNode.isEmpty && s.queuedWrites.isEmpty)
    ck.ok "late producer is delivered after resume" delivered
    discard <| step [.background]).run s

/-- Main's reader actions retain their ownership through teardown: a
judged write is durable; an intent revoked before judging is cancelled. -/
def acts (dir : String) (ck : Checks) : IO Unit := do
  let path := dir ++ "/acts.db"
  for suffix in ["", "-wal", "-shm"] do
    if ← System.FilePath.pathExists (path ++ suffix) then IO.FS.removeFile (path ++ suffix)
  let sm ← Sim.new
  let s ← App.start sm.io (← sm.viewport.get) path
  let (_, _) ← (show M Unit from do
    found "Actions" "Ann"
    waitIdle sm
    openPage .chat
    discard <| sendText "reader action target"
    waitIdle sm
    let s ← get
    let target := s.ids[0]!.2
    let kept := Community.react s.me.c s.me.adm target s.me.dev "kept".toUTF8 1
    s.sh.act "accepted".toUTF8 (pure ⟨[kept]⟩)
    readerPass
    ck.ok "reader judges an act before the frame takes it" ((← s.sh.done.get).size == 1)
    discard <| step [.background]
    let cp ← Lifecycle.load s.rd
    let bytes := cp.bind fun cp => (Codec.decode (cp.2.2.2.2.2[10]?.getD .empty) : Option (List ByteArray))
    ck.ok "suspend parks and checkpoints a completed reader act"
      ((← get).toNode.toList.flatten.any (·.id == kept.id) && (bytes.getD []).contains kept.bytes)
    discard <| step [.foreground]
    waitIdle sm
    ck.ok "completed reader act reaches the resumed store" (match ← Data.status s.rd kept.id with
      | some (.valid _) => true | _ => false)
    let cancelled := Community.react s.me.c s.me.adm target s.me.dev "cancelled".toUTF8 2
    let sh ← Reader.Shared.new (← IO.mkRef 0)
    let enabled ← IO.mkRef true
    sh.act "cancel".toUTF8 (do enabled.set false; pure ⟨[cancelled]⟩)
    discard <| (Reader.pass sh).run { rd := s.rd, enabled := enabled.get }
    ck.ok "an intent revoked in flight produces no write or pending row"
      ((← sh.done.get).all (fun (_, w) => w.isNone) && (← sh.out.get).isEmpty &&
       (← Data.status s.rd cancelled.id).isNone)
    discard <| step [.background]).run s

/-- A node's purge checkpoints the WAL (`Engine.checkpointSql`:
`wal_checkpoint(TRUNCATE)`), holding SQLite's write lock until every
reader finishes, the frame's read transaction included. A frame that
writes meanwhile returns at once: its checkpoint goes to the writer's
thread. (Committed on the frame, it waited on its own read until the busy
timeout threw out of `step`: cross's hang.) -/
def purge (dir : String) (ck : Checks) : IO Unit := do
  let path := dir ++ "/purge.db"
  for suffix in ["", "-wal", "-shm"] do
    if ← System.FilePath.pathExists (path ++ suffix) then IO.FS.removeFile (path ++ suffix)
  let sm ← Sim.new
  let s ← App.start sm.io (← sm.viewport.get) path
  let (_, _) ← (show M Unit from do
    found "Purge" "Ann"
    waitIdle sm
    openPage .chat
    waitIdle sm
    let total := (← get).total
    -- the node's connection; its checkpoint starts inside the frame's read
    -- (commands are polled after the frame's first read), and the frame
    -- then sends
    let db ← openDb path
    let purging ← IO.mkRef (none : Option (Task (Except IO.Error Unit)))
    let waiting ← IO.mkRef false
    let io := (← get).io
    modify fun s => { s with io := { io with ctlPoll := do
      if (← purging.get).isSome then return #[]
      let t ← IO.asTask (prio := .dedicated) ((checkpointSql (F := SF)).run db)
      purging.set (some t)
      IO.sleep 100
      waiting.set !(← IO.hasFinished t)
      return #["send while a purge checkpoints"] } }
    let begin ← IO.monoMsNow
    let threw ← try discard <| step []; pure false
      catch e => do IO.eprintln s!"step: {e}"; pure true
    let took := (← IO.monoMsNow) - begin
    modify fun s => { s with io }
    ck.ok "a purge's checkpoint waits on the frame's open read" (← waiting.get)
    ck.ok s!"a frame during a purge's checkpoint returns at once ({took} ms)" (!threw && took < 2000)
    let done ← match ← purging.get with
      | some t => do
        let r ← IO.wait t
        if let .error e := r then IO.eprintln s!"purge: {e}"
        pure r.toBool
      | none => pure false
    ck.ok "the purge's checkpoint completes after the frame" done
    let stored ← advance 5000 fun s => do
      return s.total == total + 1 && (← s.wr.busy.get) == 0 && (← s.wr.saveDone)
    let cp ← Lifecycle.load (← get).rd
    ck.ok "the send is stored and the newest checkpoint committed" (stored && cp.isSome && cp == (← get).saved)
    discard <| step [.background]).run s

/-- A real SQLite write lock makes checkpoint saves fail. The writer must
retain the following job until its checkpoint commits, even through
retries; otherwise it also attempts the job under that lock and loses it. -/
def writerRetry (dir : String) (ck : Checks) : IO Unit := do
  let path := dir ++ "/writer-retry.db"
  for suffix in ["", "-wal", "-shm"] do
    if ← System.FilePath.pathExists (path ++ suffix) then IO.FS.removeFile (path ++ suffix)
  let rd ← openDb path
  Lifecycle.init rd
  let attempts ← IO.mkRef 0
  let w ← Writer.start path fun db bytes => do
    attempts.modify (· + 1)
    db.exec "PRAGMA busy_timeout=1"
    Lifecycle.save db bytes
  w.paused.set true
  let lock ← openDb path
  lock.exec "BEGIN IMMEDIATE"
  let cp : Lifecycle.Checkpoint := (1, 0, .empty, .empty, 0, [])
  let op := Op.make 250 [] "a write after the checkpoint".toUTF8
  try
    w.save (Codec.encode cp)
    w.submit ⟨[op], true⟩
    w.paused.set false
    let deadline := (← IO.monoMsNow) + 3000
    while (← attempts.get) < 3 && (← IO.monoMsNow) < deadline do IO.sleep 2
    ck.ok "the held SQLite write lock forces checkpoint retries" ((← attempts.get) ≥ 3)
    ck.ok "a failed checkpoint keeps its following job pending"
      ((← w.busy.get) == 1 && !(← w.saveDone) && (← Data.status rd op.id).isNone)
  finally
    lock.exec "ROLLBACK"
  let deadline := (← IO.monoMsNow) + 3000
  while ((← w.busy.get) != 0 || !(← w.saveDone)) && (← IO.monoMsNow) < deadline do IO.sleep 2
  ck.ok "the retried checkpoint and its following job both reach SQLite"
    ((← w.busy.get) == 0 && (← w.saveDone) && (← Lifecycle.load rd) == some cp &&
      (← (Q.op op.id).run rd #[]) == .bytes (some op.bytes))

end LifecycleNode

def main (args : List String) : IO UInt32 := do
  let ck ← Checks.new
  let dir := args[0]?.getD "out/lifecycle-node"
  LifecycleNode.run dir ck
  LifecycleNode.bounded dir ck
  LifecycleNode.acts dir ck
  LifecycleNode.purge dir ck
  LifecycleNode.writerRetry dir ck
  IO.Process.exit (← ck.finish "lifecycle node").toUInt8
