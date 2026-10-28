/-
CJK Regular-instance glyphs against fontTools, locale routing, and the
real bounded cache under overflow, eviction, reloads and concurrent paint.
-/
import QTests.Sim
import Quiet.Ttf.Cache

private def check (ok : Bool) (label : String) : IO Unit :=
  unless ok do throw (IO.userError label)

private def numbers (s : String) : Array Nat := (s.splitOn " ").toArray.filterMap String.toNat?

unsafe def main (args : List String) : IO Unit := do
  let dir := args.headD "out/cjk"
  let mut maps := 0
  let mut rasters := 0
  for name in Cjk.names do
    let some f := Ttf.read (← IO.FS.readBinFile s!"assets/{name}.ttf") | throw (IO.userError s!"read {name}")
    for line in (← IO.FS.readFile s!"{dir}/{name}.map").splitOn "\n" do
      let ns := numbers line
      if ns.size != 3 then continue
      check (Ttf.lookup f.cmap ns[0]! == some ns[1]! && f.advances[ns[1]!]! == ns[2]!) s!"mapping {name} {ns[0]!}"
      maps := maps + 1
    for line in (← IO.FS.readFile s!"{dir}/{name}.samples").splitOn "\n" do
      let ns := numbers line
      if ns.size != 2 then continue
      let cp := ns[0]!
      let size := ns[1]!
      let some g := Ttf.lookup f.cmap cp | throw (IO.userError "missing sample")
      let some b := Ttf.raster f g size size | throw (IO.userError s!"raster {name} {cp}")
      check (decide b.Valid) "CJK raster bound"
      let stem := s!"{dir}/{name}-{cp}-{size}"
      IO.FS.writeBinFile (stem ++ ".pgm") (s!"P5\n{b.w} {b.h}\n255\n".toUTF8 ++ b.pixels)
      IO.FS.writeFile (stem ++ ".box") s!"{b.x} {b.y} {b.w} {b.h} {b.advance}\n"
      rasters := rasters + 1
  let font ← Font.load
  for (c,i) in [('中',9),('國',10),('あ',11),('한',12),('ㄅ',10)] do
    check ((font.glyph c.val).noto.map (·.face) == some i) s!"locale {c}"
  check ((font.glyph '龘'.val).noto.isNone && (font.bitmapGlyph? '龘'.val).isSome) "rare Han keeps Unifont"
  let some r := (font.glyph '中'.val).noto | throw (IO.userError "no Han")
  let some b := font.noto.bitmap r | throw (IO.userError "no Han bitmap")
  let mut cache := Ttf.Cache.empty
  for i in [0:2200] do
    cache := Ttf.Cache.put cache ⟨1,i,48,48⟩ b
    check (decide (Ttf.Cache.Valid cache)) "cache budget"
    check ((Ttf.Cache.get? cache ⟨1,i,48,48⟩).isSome) "insertion survives eviction"
  check ((Ttf.Cache.get? cache ⟨1,0,48,48⟩).isNone) "oldest glyph evicted"
  check ((Ttf.Cache.get? cache ⟨1,2199,48,48⟩).isSome) "newest glyph retained"
  for (key,i) in cache.index.toList do
    check ((cache.slots[i]?.getD none).any (·.key == key)) "index follows eviction"
  let huge := { b with pixels := ⟨Array.replicate Ttf.Cache.budget 0⟩ }
  check ((Ttf.Cache.get? (Ttf.Cache.put cache ⟨1,2200,48,48⟩ huge) ⟨1,2200,48,48⟩).isNone) "oversized glyph not retained"
  Ttf.Memo.clear
  let requests := font.noto.chars.toList.filter (fun (_,r) => r.face ≥ 9)
  for (_,r) in requests.take 1800 do
    check ((font.noto.bitmap r).isSome) "runtime cache fill"
  let (hits, misses, bytes, peak, count) ← Ttf.Memo.stats
  check (bytes ≤ Ttf.Cache.budget && peak ≤ Ttf.Cache.budget && count ≤ Ttf.Cache.capacity && misses ≥ 1800) "runtime cache bounded and used"
  -- A cache miss after eviction must reproduce the same glyph exactly.
  check ((font.noto.bitmap r).map (·.pixels) == some b.pixels) "evicted glyph raster matches"
  let mut tasks := #[]
  for _ in [0:8] do
    tasks := tasks.push (← IO.asTask do
      for (_,r) in requests.take 24 do
        let cached := font.noto.bitmap r
        let f := font.noto.faces[r.face]!
        check (cached.map (·.pixels) == (f.uncached r.glyph).map (·.pixels)) "concurrent memo agrees"
      pure ())
  for t in tasks do
    match t.get with
    | .ok _ => pure ()
    | .error e => throw e
  let lines := ((← IO.FS.readFile s!"{dir}/lines.txt").splitOn "\n").filter (!·.isEmpty)
  let allNames := (Noto.names.map (· ++ "-Regular")) ++ Cjk.names
  let mut bmp := Paint.Bitmap.blank 1500 (lines.length*90+30) (Paint.solid 0xFFFFFF 1500)
  let mut layout := ""
  for (text,i) in lines.zipIdx do
    let line := Text.oneLine font 1460 text
    bmp := bmp.line font line 20 (20+i*90) 0x141414
    for g in line do
      let some r := (font.glyph g.c).noto | throw (IO.userError s!"unexpected sample fallback: {g.c}")
      layout := layout ++ s!"{allNames[r.face]!} {r.glyph} {font.cell} {g.x+20} {20+i*90}\n"
  IO.FS.writeFile s!"{dir}/scripts.layout" layout
  writePpm s!"{dir}/scripts.ppm" 1500 bmp.rows
  IO.println s!"CJK: {maps} mappings/metrics; {rasters} bitmaps; 2200 cache insertions; runtime hits {hits}, misses {misses}, bytes {bytes}, peak {peak}, entries {count}; 8 concurrent workers pass"
  (← IO.getStdout).flush
  IO.Process.exit 0
