/- Attachment children of one tall message mount and unmount while their
parent remains visible. Signed ops, SQLite and the real App.step. -/
import platforms.headless.Sim
import tests.engine.Checks

open App Engine Community Data Tests

namespace Components

def run (dir : String) (ck : Checks) : IO Unit := do
  IO.FS.createDirAll dir
  for suffix in ["", "-wal", "-shm"] do
    let p := dir ++ "/quiet.db" ++ suffix
    if ← System.FilePath.pathExists p then IO.FS.removeFile p
  let sm ← Sim.new
  sm.viewport.set #[1080, 1100, 32, 24, 420]
  let initial ← App.start sm.io (← sm.viewport.get) (dir ++ "/quiet.db")
  let ((), final) ← (show M Unit from do
    sm.cmds.modify (·.push "found components|Ann")
    steps 3
    waitIdle sm
    sm.cmds.modify (·.push "channel")
    steps 2
    for _ in [0:4] do sm.cmds.modify (·.push "photo"); steps 2
    let text := String.intercalate " " (List.replicate 150 "A message owns its text.")
    (← get).wr.paused.set true
    sm.cmds.modify (·.push s!"post {text}")
    waitIdle sm
    let s ← get
    let some (_, message) := s.ids[0]? | throw (IO.userError "fixture message missing")
    let some row := s.rows[message]? | throw (IO.userError "fixture row missing")
    ck.ok "fixture is one real message with four attachment ops" (s.ids.size == 1 && row.data.pics.length == 4)
    let rowWant := Reader.Want.row s.me.c s.me.adm message
    let some reader := s.rst | throw (IO.userError "test reader missing")
    ck.ok "attachment bodies arrive with their list, without per-chunk reads or a second want"
      (reader.deps.toList.any (fun (w, qs) => match w with
        | .picture .. => qs.any (fun | .bodies _ => true | _ => false) &&
            !qs.any (fun | .op _ => true | _ => false)
        | _ => false) &&
       !(← s.sh.wants).any (fun | .slices _ => true | _ => false))
    for p in row.data.pics do
      let q := chunk.byAttachment.query [s.me.c, p.attachment] (desc := false)
      let .bodies a pend raw ← (Q.bodies q).run s.rd (← s.sh.out.get)
        | throw (IO.userError "body projection missing")
      let .list metadata pend' ← (Q.list q).run s.rd (← s.sh.out.get)
        | throw (IO.userError "metadata projection missing")
      ck.ok "body projection preserves the list's window, pending status and exact chunk order"
        (a == metadata && !pend.isEmpty && pend == pend' && (Q.bodies q).win (.bodies a pend raw) ==
          (Q.list q).win (.list metadata pend') && raw.map (·.1) == a.rows.map (·.1.2) &&
          raw.all (fun (id, bytes) => (Op.decode bytes).any (·.id == id)))
    s.wr.paused.set false
    waitIdle sm
    for p in row.data.pics do
      let q := chunk.byAttachment.query [s.me.c, p.attachment] (desc := false)
      let .bodies a _ raw ← (Q.bodies q).run s.rd #[]
        | throw (IO.userError "committed body projection missing")
      ck.ok "stored body projection returns every chunk without point reads"
        (!a.rows.isEmpty && raw.map (·.1) == a.rows.map (·.1.2) &&
          raw.all (fun (id, bytes) => (Op.decode bytes).any (·.id == id)))
    let before ← s.sh.plan.get
    let active := s.pictureNeeds.toList
    ck.ok "visible picture components declare their own slice queries" (!active.isEmpty)
    ck.ok "picture ownership names its attachment op type and identity"
      (active.all fun n => row.data.pics.any fun p =>
        n.owner == Raster.pictureOwner s.me.c message p.attachment &&
          (n.key == .slices p.chunks || n.key == .picture s.me.c p.attachment))
    -- Move from the pictures at the bottom to the text at the top, in
    -- the same row. The row cannot unmount to make this test pass.
    sm.b.set (← sm.maxB.get)
    steps 8
    let after ← get
    let plan ← after.sh.plan.get
    ck.ok "scrolling within a tall message retains the message's query ticket"
      (plan.ticket rowWant == before.ticket rowWant && after.rows.contains message)
    ck.ok "offscreen attachment children release every chunk query"
      (after.pictureNeeds.isEmpty && active.all fun n => !plan.held n.key)
    ck.ok "offscreen attachment children retain no queued decode or bitmap handle" after.imgs.isEmpty
    let some reader := after.rst | throw (IO.userError "test reader missing")
    ck.ok "offscreen child subscriptions and reverse-index entries are released"
      (active.all (fun n => !reader.deps.contains n.key) &&
        reader.rev.toList.all (fun (_, wants) => wants.all reader.wantSet.contains))
    sm.b.set 0
    steps 12
    let returned ← get
    ck.ok "returning to pictures remounts their owned queries" (!returned.pictureNeeds.isEmpty)
    ck.ok "the message ticket survives both viewport changes"
      ((← returned.sh.plan.get).ticket rowWant == before.ticket rowWant)
    let mut finished := false
    let deadline := (← IO.monoMsNow) + 5000
    while !finished && (← IO.monoMsNow) < deadline do
      steps 1
      IO.sleep 2
      for (_, h) in (← get).imgs.toList do
        if (← h.value).isSome then finished := true
    ck.ok "returning pictures finish through the shared worker" finished
    sm.b.set 250
    steps 4
    let beforeResize ← get
    resizeContent #[beforeResize.W.toUInt32, (beforeResize.Hs + 50).toUInt32,
      beforeResize.insetTop.toUInt32, beforeResize.insetBot.toUInt32, beforeResize.dim.dpi.toUInt32]
    let afterResize ← get
    ck.ok "height-only resize retains every displayed bitmap and row version"
      (beforeResize.rows.toList.all fun (x, old) => (afterResize.rows[x]?).any fun row =>
        row.ver == old.ver && row.shown.map (·.rows) == old.shown.map (·.rows))
    resizeContent #[beforeResize.W.toUInt32, beforeResize.Hs.toUInt32,
      beforeResize.insetTop.toUInt32, beforeResize.insetBot.toUInt32, beforeResize.dim.dpi.toUInt32]
    openPage .home
    steps 2
    ck.ok "Home releases the message component while owning only destination images"
      ((← get).rows.isEmpty && (← get).rasterNeeds.all (fun n => match n.key with
        | .image .. => n.owner.head? == some "home".toUTF8
        | _ => false))
    let deadline := (← IO.monoMsNow) + 5000
    while !(← (← get).wr.saveDone) && (← IO.monoMsNow) < deadline do IO.sleep 2
    ).run initial
  final.raster.reconcile []
  -- A new App instance starts with no bitmap cache and restores Home's
  -- saved cursor from disk. The visible channel must initiate the reads.
  let cold ← App.start sm.io (← sm.viewport.get) (dir ++ "/quiet.db")
  ck.ok "cold Home starts with no prepared images" (cold.page == .home && cold.imgs.isEmpty && cold.mark.isSome)
  let ((), done) ← (show M Unit from do
    let deadline := (← IO.monoMsNow) + 5000
    let mut ready := false
    while !ready && (← IO.monoMsNow) < deadline do
      steps 1
      IO.sleep 2
      let s ← get
      ready := !s.prepared.isEmpty && s.prepared.all (fun p => p.pic.raw.isSome)
      for p in s.prepared do
        match s.imgs[(p.pic.hash.push 1, p.w, p.h)]? with
        | some h => ready := ready && (← h.value).isSome
        | none => ready := false
    let home ← get
    ck.ok "cold Home preloads complete viewport images before visiting the channel" ready
    let keys := home.prepared.map fun p => (p.pic.hash.push 1, p.w, p.h)
    let tickets := keys.map fun k => home.imgs[k]?.map (·.ticket)
    openPage .chat
    steps 8
    let chat ← get
    ck.ok "entering the channel retains Home's decode tickets without restarting"
      (!keys.isEmpty && (keys.zip tickets).all fun (k, ticket) =>
        ticket.isSome && chat.imgs[k]?.map (·.ticket) == ticket)
    openPage .you
    steps 2
    ck.ok "leaving both Home and channel releases all preload ownership"
      ((← get).prepared.isEmpty && (← get).handoff.isEmpty && (← get).imgs.isEmpty)
    ).run cold
  done.raster.reconcile []

end Components

def main (args : List String) : IO Unit := do
  let code ← try
    let ck ← Checks.new
    Components.run (args.headD "out/components") ck
    ck.finish "op-components"
  catch e => IO.eprintln s!"op-components: {e}"; pure 1
  (← IO.getStdout).flush
  IO.Process.exit code.toUInt8
