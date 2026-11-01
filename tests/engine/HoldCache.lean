import engine.renderer.HoldCache
open Hold
def sample : St := ⟨Paint.solid 0xF8F8F8 1080, ⟨420, 39, .light, none⟩, 1080⟩

def main : IO UInt32 := do
  let cases : List St := [sample,
    { sample with W := 640 },
    { sample with dim := { sample.dim with dpi := 160 } },
    { sample with dim := { sample.dim with theme := .dark } },
    { sample with bgRow := Paint.solid 0x123456 1080 },
    { sample with dim := { sample.dim with cell := 99 } }]
  let mut cache : MessageCache := none
  let mut checks := 0
  for s in cases do
    for height in [0, 800, 2209] do
      let (rows, next) := cachedMessagePlane cache s height
      unless rows == messagePlane s height do
        IO.eprintln "FAIL: cached plane differs from existing pixel generator"
        return 1
      checks := checks + 1
      let some tile := next | return 2
      unless tile.key == MessageKey.ofState s do return 3
      checks := checks + 1
      cache := next
  IO.println s!"hold-cache: {checks} actual pixel/key checks passed"
  return 0
