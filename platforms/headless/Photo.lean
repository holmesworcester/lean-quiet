/- System-photo completions driven through the real composer, lifecycle,
SQLite writer and attachment components. The OS result packet is the seam. -/
import platforms.headless.Sim
import tests.engine.Checks

open App Engine Community Data Tests

namespace PhotoTest

def rgba : ByteArray := ⟨#[255,0,0,255, 0,255,0,255, 0,0,255,255, 255,255,0,255]⟩

def finish : M Unit := do
  for _ in [0:500] do
    steps 1
    if (← get).photoRequest.isNone then return
    IO.sleep 2
  throw (IO.userError "photo worker did not finish")

def press : M UInt32 := do
  let s ← get
  let some (box, _) := (composerLayout s).deck.find? (·.2 == .addPhotos)
    | throw (IO.userError "no photo button")
  onTap .composer (box.x + box.w / 2) (box.y + box.h / 2) false
  return (← get).photoSerial

def run (dir : String) (ck : Checks) : IO Unit := do
  IO.FS.createDirAll dir
  for suffix in ["", "-wal", "-shm"] do
    let p := dir ++ "/quiet.db" ++ suffix
    if ← System.FilePath.pathExists p then IO.FS.removeFile p
  let sm ← Sim.new
  sm.viewport.set #[390, 844, 0, 0, 160]
  let calls ← IO.mkRef (#[] : Array UInt32)
  let io := { sm.io with pickPhoto := fun token => do calls.modify (·.push token); pure true }
  let initial ← App.start io (← sm.viewport.get) (dir ++ "/quiet.db")
  let (_, final) ← (show M Unit from do
    found "Photos" "Ann"
    waitIdle sm
    openPage .chat
    steps 3
    let a ← press
    ck.ok "drawn photo button starts a native request, without a sample chip"
      (a != 0 && (← get).photoRequest.isSome && (← get).chips.isEmpty && (← calls.get).back? == some a)
    sm.photo.set (#[a - 1, 1, 2, 2], rgba)
    steps 3
    ck.ok "superseded completion cannot attach" ((← get).chips.isEmpty && (← get).photoRequest.isSome)
    sm.photo.set (#[a, 2, 0, 0], .empty)
    steps 2
    ck.ok "OS cancellation leaves the composer unchanged" ((← get).photoRequest.isNone && (← get).chips.isEmpty)
    let b ← press
    sm.photo.set (#[b, 1, 2049, 2], rgba)
    finish
    ck.ok "malformed native dimensions never reach an attachment" ((← get).chips.isEmpty)
    let c ← press
    openPage .you
    ck.ok "leaving the composer revokes native ownership" ((← get).photoRequest.isNone && (← calls.get).back? == some 0)
    sm.photo.set (#[c, 1, 2, 2], rgba)
    back
    steps 3
    ck.ok "late selection after navigation does not edit the new draft" ((← get).chips.isEmpty)
    let d ← press
    discard <| onEvent .background
    ck.ok "picker-induced backgrounding preserves the user's request" ((← get).photoRequest.isSome)
    discard <| onEvent .foreground
    steps 2
    modify fun s => { s with text := "Photo from system picker" }
    sendNow
    ck.ok "send waits until its selected photo is ready" ((← get).total == 0 && !(← get).text.isEmpty)
    sm.photo.set (#[d, 1, 2, 2], rgba)
    finish
    let s ← get
    let some (bytes, w, h, _) := s.chips[0]? | throw (IO.userError "missing selected photo")
    let some image := Image.decode bytes | throw (IO.userError "selected photo is not QOI")
    ck.ok "oriented native RGBA reaches the actual composer chip unchanged"
      (w == 2 && h == 2 && image.px == #[0xff0000ff,0x00ff00ff,0x0000ffff,0xffff00ff])
    -- A duplicate callback cannot add the image twice.
    sm.photo.set (#[d, 1, 2, 2], rgba)
    steps 3
    ck.ok "completion is consumed once" ((← get).chips.size == 1)
    sendNow
    waitIdle sm
    for _ in [0:100] do
      steps 1
      if (← get).rows.toList.any (fun (_, r) => r.data.pics.length == 1) then break
      IO.sleep 2
    let s ← get
    ck.ok "selected photo is a signed attachment queried by its message component"
      (s.chips.isEmpty && s.text.isEmpty && s.rows.toList.any fun (_, r) =>
        r.data.text == "Photo from system picker" && r.data.pics.any fun p =>
          p.w == 2 && p.h == 2 && p.complete && !p.attachment.isEmpty)
    let e ← press
    found "Other photos" "Ann"
    waitIdle sm
    openPage .chat
    sm.photo.set (#[e, 1, 2, 2], rgba)
    steps 5
    ck.ok "switching community drops the previous composer's selection"
      ((← get).photoRequest.isNone && (← get).chips.isEmpty)
    let raw := Photo.pixels #[1,1,2,2] rgba
    ck.ok "truncated RGBA packet is refused" ((Photo.pixels #[1,1,2,2] (rgba.extract 0 15)).isNone && raw.isSome)
    ck.ok "unknown native status is refused" ((Photo.pixels #[1,9,2,2] rgba).isNone)
  ).run initial
  final.raster.reconcile []

end PhotoTest

def main (args : List String) : IO Unit := do
  let ck ← Checks.new
  PhotoTest.run (args[0]?.getD "out/photo/app") ck
  let code ← ck.finish "photo lifecycle"
  (← IO.getStdout).flush
  IO.Process.exit code.toUInt8
