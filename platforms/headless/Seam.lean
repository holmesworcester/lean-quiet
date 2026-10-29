/- Raw-event and placement integration through Session and the C twin.
The script supplies samples; this executable never manufactures app taps. -/
import engine.renderer.Session
open App Input

def row (w r : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for _ in [0:w] do out := out ++ ⟨#[r.toUInt8, (r / 256).toUInt8, 77, 255]⟩
  return out

def check (label : String) (ok : Bool) : IO Unit := do
  if !ok then throw (IO.userError s!"FAIL {label}")

def unit : IO Unit := do
  let g : Geometry.Geom := ⟨800, 20, 300, 80, 60⟩
  let f := Surface.make g false 32 10 10 704
  let c : Context := ⟨f, 160, 100⟩
  let t (phase time x y : Nat) (id : Nat := 1) : Raw := .touch ⟨phase, id, ⟨x, y⟩, time⟩
  let cases : List (String × List Raw × List Event) := [
    ("tap", [t 0 0 100 120, t 2 100 100 120], [.tap .list 100 329]),
    ("jitter at down", [t 0 0 100 120, t 1 10 108 128, t 2 100 104 124], [.tap .list 100 329]),
    ("out and back", [t 0 0 100 120, t 1 10 109 120, t 2 100 100 120], []),
    ("release movement", [t 0 0 100 120, t 2 100 100 129], []),
    ("long boundary", [t 0 0 100 120, .tick 500, t 2 700 100 120], [.long .list 100 329]),
    ("cancel", [t 0 0 100 120, t 3 100 100 120], []),
    ("two fingers", [t 0 0 100 120, t 0 10 200 200 2, t 1 20 400 400 2,
      t 2 100 100 120, t 2 200 200 200 2], [.tap .list 100 329]),
    ("no promotion", [t 0 0 100 120, t 0 10 200 200 2, t 3 30 100 120,
      t 0 40 300 300 3, t 2 80 300 300 3, t 2 100 200 200 2], []),
    ("composer cancel", [t 0 0 100 460, t 3 100 100 460], [.drag 0 100 20, .drag 3 100 20]),
    ("composer jitter", [t 0 0 100 460, t 1 10 105 465, t 2 100 105 465],
      [.drag 0 100 20, .drag 2 100 20, .tap .composer 100 20]),
    ("Enter down", [.key 66 0], [.send]),
    ("Enter up", [.key 66 1], []),
    ("another key", [.key 65 0], []),
    ("Android L", [.key 40 0], []),
    ("USB Enter", [.usbKey 40 0], [.send]),
    ("USB Enter up", [.usbKey 40 1], []),
    ("USB F9", [.usbKey 66 0], []),
    ("IME Send", [.imeAction 4], [.send]),
    ("IME Search", [.imeAction 3], [])]
  for (name, es, expected) in cases do
    check name ((Input.run c {} es).events == expected)
  let other := { c with frame := Surface.make { g with ime := 0 } false 32 10 10 704 }
  let stamped := Input.run other { frames := [(1, c), (2, other)] }
    [.touchOn 1 ⟨0, 1, ⟨100, 120⟩, 1000⟩, .touchOn 2 ⟨2, 1, ⟨100, 120⟩, 1100⟩]
  check "frame at acquisition" (stamped.events == [.tap .list 100 329])
  let burst := [t 0 0 100 120] ++ (List.range 5000).map (fun i => t 1 (i+1) (if i == 4500 then 200 else 100) 120) ++ [t 2 5100 100 120]
  check "overfull queue retains excursion" ((Input.run c {} burst).events.isEmpty)
  for (b, expected) in [(-1000, 0), (-1, 0), (0, 0), (50, 50), (100, 100), (1000000, 100)] do
    let r := Input.run c {} [.sample b]
    check s!"offset {b}" (r.state.offset == expected)
  for pin in [false, true] do
    for ime in [0, 20, 300] do
      let g := { g with ime }
      let f := Surface.make g pin 32 10 10 704
      let list := (Array.range 704).map (row 1)
      let top := Array.replicate 80 (row 1 900)
      let bot := Array.replicate 60 (row 1 901)
      let screen := Surface.compose f.words 800 (row 1 902) list top bot
      for y in [g.top:g.composerTop] do
        let r := (Int.ofNat y - f.origin).toNat
        check "published crop" (screen[y]! == list[r]!)
  IO.println s!"unit: {cases.length + 14} cases, 3280 viewport rows"

partial def loop (pin : Bool) (ime : Nat) (state : Input.State) : IO Unit := do
  let g : Geometry.Geom := ⟨2400, 63, ime, 128, 120⟩
  let sample ← Platform.scroll 10000 g.viewNow.toUInt32
  let b := Surface.offset (10000 - g.viewNow) sample.toInt64.toInt
  let list := (Array.range (g.view + 64)).map (row 1080)
  let top := Array.replicate 128 (row 1080 60000)
  let bot := Array.replicate 120 (row 1080 60001)
  let result ← Session.present Platform.frame Platform.motion g 420 (10000 - g.viewNow)
    state list b 32 top bot pin
  IO.println s!"frame {b} {g.composerTop} {pin}"
  let mut ime := ime
  for e in result.events do
    match e with
    | .close => return
    | .tap r x y => IO.println s!"tap {repr r} {x} {y}"
    | .long r x y => IO.println s!"long {repr r} {x} {y}"
    | .send => IO.println "send"
    | .ime h => ime := h.toNat
    | _ => pure ()
  loop pin ime result.state

def main (args : List String) : IO Unit := do
  unit
  if args == ["unit"] then return
  loop (args == ["page"]) 0 {}
