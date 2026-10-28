/-
The compiled memoization contract, compact layout records and lazy startup.
Compare every bitmap field/byte on misses, hits, eviction, fresh sources,
different sizes and concurrent calls. Invalid headers/outlines return none.
-/
import engine.renderer.Font

private def check (ok : Bool) (label : String) : IO Unit :=
  unless ok do throw (IO.userError label)

private def same : Option Ttf.Bitmap → Option Ttf.Bitmap → Bool
  | none, none => true
  | some a, some b =>
    a.x == b.x && a.y == b.y && a.w == b.w && a.h == b.h &&
    a.advance == b.advance && a.cell == b.cell && a.left == b.left &&
    a.right == b.right && a.top == b.top && a.bottom == b.bottom && a.pixels == b.pixels
  | _, _ => false

private def contract (f : Ttf.Memo.Source) (g : Nat) : IO Unit :=
  check (same (f.bitmap g) (f.uncached g)) "memo contract: every field and byte"

def main : IO Unit := do
  let checks ← Std.Mutex.new (0 : Nat)
  let compare := fun src g => do
    contract src g
    checks.atomically (modify (· + 1))
  let t0 ← IO.monoNanosNow
  let loaded ← Noto.load 48
  let elapsed := ((← IO.monoNanosNow) - t0) / 1000
  IO.println s!"compact Noto load: {elapsed} us"
  check (elapsed < 40000) "Noto loader exceeds 40 ms (eager parse/selection regression)"
  let raw ← IO.FS.readBinFile "assets/noto-index.bin"
  let some index := Ttf.Index.read raw | throw (IO.userError "index")
  let mut refused := 0
  for n in (List.range 64 ++ [raw.size-1]) do
    check ((Ttf.Index.read (raw.extract 0 n)).isNone) "truncated index"
    refused := refused+1
  check ((Ttf.Index.read (raw.set! 6 255)).isNone) "oversized font in index"
  check ((Ttf.Index.read (raw.set! 17 255)).isNone) "index record count"
  check ((Ttf.Index.read (raw.set! 22 255 |>.set! 23 255)).isNone) "index glyph bounds"
  refused := refused+3
  let mut pairs := 0
  let mut faces := #[]
  let mut sources := #[]
  let files := (Noto.names.map (· ++ "-Regular")) ++ Cjk.names
  for i in [0:files.size] do
    let bytes ← IO.FS.readBinFile s!"assets/{files[i]!}.ttf"
    let some f := Ttf.readHeader bytes | throw (IO.userError "font header")
    faces := faces.push f
    let m := index[i]!
    check (m.units == f.units && m.glyphs == f.advances.size && m.bytes == bytes.size) "index header metrics"
    for (cp,g,a) in m.chars do
      check (Ttf.lookup f.cmap cp == some g && f.advances[g]? == some a) "compact cmap/hmtx agrees"
      pairs := pairs+1
    for size in [16,32,48,64] do
      let src ← Ttf.Memo.source bytes size size
      sources := sources.push src
      for (_,g,_) in m.chars.toList.take 16 do
        compare src g
        compare src g
      compare src f.advances.size
  let mut routed := 0
  for (cp,r) in loaded.chars.toList do
    let f := faces[r.face]!
    check (Ttf.lookup f.cmap cp.toNat == some r.glyph && Ttf.advance f r.glyph 48 == r.advance) "running Font metrics"
    if Cjk.supported cp.toNat then
      check (Cjk.choose (faces.extract Noto.names.size faces.size) cp.toNat == some (r.face-Noto.names.size,r.glyph)) "compact routing agrees"
    routed := routed+1
  -- Force eviction, then revisit sources whose glyph numbers overlap.
  let some cjk := loaded.faces[9]? | throw (IO.userError "CJK source")
  for g in [0:1800] do compare cjk g
  for src in sources do
    for g in [0:16] do compare src g
  let mut tasks := #[]
  for i in [0:8] do
    tasks := tasks.push (← IO.asTask do
      for src in sources.toList.drop i |>.take 16 do
        for g in [0:8] do compare src g)
  for t in tasks do
    match t.get with
    | .ok _ => pure ()
    | .error e => throw e
  let broken ← Ttf.Memo.source ByteArray.empty 48 48
  compare broken 1
  check ((broken.bitmap 1).isNone) "invalid source returns none"
  let bad ← IO.FS.readBinFile "out/noto/composite-loop.ttf"
  let loop ← Ttf.Memo.source bad 48 48
  let some f := Ttf.readHeader bad | throw (IO.userError "loop fixture header")
  let mut rejected := false
  for g in [0:f.advances.size] do
    if (Ttf.outline f g).isNone then
      compare loop g
      check ((loop.bitmap g).isNone) "loop refused at first use"
      rejected := true
      break
  check rejected "loop fixture is non-vacuous"
  let (hits,misses,bytes,peak,count) ← Ttf.Memo.stats
  check (hits > 500 && misses > 1800 && bytes ≤ Ttf.Cache.budget && peak ≤ Ttf.Cache.budget && count ≤ Ttf.Cache.capacity) "memo used and bounded"
  IO.println s!"font contract: {pairs} compact pairs; {routed} routed metrics; {refused} invalid indices; {← checks.atomically get} whole-result comparisons, 8 workers; hits {hits}, misses {misses}, peak {peak}"
