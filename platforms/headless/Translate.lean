/- Slow Lean publications, fast OS samples: the C twin translates and fills
without re-entering this loop. Frames are resolved through Cover.seen. -/
import engine.renderer.Session
import engine.renderer.TranslateLaws
open App Geometry
namespace Slow

def pixel (p : Nat) : ByteArray := Paint.solid
  ((p % 251).toUInt32 <<< 16 ||| ((p / 251) % 251).toUInt32 <<< 8 ||| 77) 1080

def fixture (g : Geom) (b over : Nat) : Array ByteArray :=
  let rows := [(5000, some 5000), (200000, none)]
  (Array.range (g.view + 2 * over)).map fun r =>
    let p := b + g.view + over - 1 - r
    match Cover.seen 0 0 true rows p with
    | .line _ _ => pixel p
    | .hold _ | .unloaded => Hold.holdLine ⟨Paint.solid Row.bg 1080, ⟨420, 0, .dark⟩, 1080⟩ (p % 48)
    | .blank => Paint.solid 0 1080

def unit : IO Unit := do
  let g : Geom := ⟨800, 20, 300, 80, 60⟩
  let c : Input.Context := ⟨Surface.make g false 32 10 10 704, 160, 1000⟩
  let down : Input.Touch := ⟨0, 1, ⟨100, 120⟩, 1000⟩
  let up := { down with phase := 2, time := 1100 }
  let raw := (down.words.set! 6 1 |>.set! 7 (Slide.delta false 10 60).toUInt32) ++
    (up.words.set! 6 1 |>.set! 7 (Slide.delta false 10 110).toUInt32)
  let r := Input.run c { frames := [(1, c)] } (Input.decode raw)
  if r.events != [.tap .list 100 379] then throw (IO.userError "translated tap lost its down offset")
  let c := { c with frame := Surface.make g true 32 0 0 704 }
  let r := Input.run c { frames := [(1, c)] } [.touchAt 1 50 down, .touchAt 1 100 up]
  if r.events != [.tap .list 100 599] then throw (IO.userError "pinned tap moved with OS offset")
  let f := Surface.make ⟨200, 0, 0, 20, 20⟩ false 8 100 100 176
  if Translate.seen f 176 268 16 300 false [(500, some 500)] 100 20 != .unloaded then
    throw (IO.userError "newer unloaded window was not covered")
  if Translate.seen f 176 268 300 300 true [(500, some 500)] 100 20 != .blank then
    throw (IO.userError "padding lost its Cover meaning")
  IO.println "translate input/coverage: 4 checks passed"

partial def loop (pin : Bool) (state : Input.State) : IO Unit := do
  let g : Geom := ⟨2400, 63, 0, 128, 120⟩
  let sample ← Platform.scroll 205000 g.viewNow.toUInt32
  let b := if pin then 0 else Surface.offset (205000 - g.viewNow) sample.toInt64.toInt
  let fr := fixture g b 32
  let top := Array.replicate g.top (Paint.solid 0x101010 1080)
  let bot := Array.replicate g.bot (Paint.solid 0x202020 1080)
  let result ← Session.present Platform.frame Platform.motion g 420 (205000 - g.viewNow)
    state fr b 32 top bot pin
  if result.events.any (· == .close) then return
  for e in result.events do
    if let .tap _ x y := e then IO.println s!"tap {x} {y}"
  loop pin result.state
end Slow

def main (args : List String) : IO Unit := do
  Slow.unit
  Slow.loop (args == ["pin"]) {}
