/-
Real fonts against fontTools' cmap, metrics and independent outline pen;
malformed files, cache sharing, fallback, density and full text painting.
The Python driver supplies references and compares 8-bit coverage pixels.
-/
import engine.renderer.Paint
import engine.renderer.Ttf.Laws
import platforms.headless.Sim

private def require (ok : Bool) (label : String) : IO Unit :=
  if ok then pure () else throw (IO.userError label)

private def nums (line : String) : Array Nat :=
  (line.splitOn " ").toArray.filterMap String.toNat?

unsafe def main (args : List String) : IO Unit := do
  let dir := args.headD "out/noto"
  let mut mapped := 0
  let mut pictures := 0
  for name in Noto.names.push "Transforms" do
    let path := if name == "Transforms" then s!"{dir}/Transforms.ttf" else s!"assets/{name}-Regular.ttf"
    let bytes ← IO.FS.readBinFile path
    let some f := Ttf.read bytes | throw (IO.userError s!"font rejected: {name}")
    for line in (← IO.FS.readFile s!"{dir}/{name}.map").splitOn "\n" do
      let v := nums line
      if v.size != 3 then continue
      let cp := v[0]!
      let glyph := v[1]!
      require (Ttf.lookup f.cmap cp == some glyph) s!"cmap {name} {cp}"
      require (f.advances[glyph]? == some v[2]!) s!"hmtx {name} {cp}"
      mapped := mapped + 1
    for line in (← IO.FS.readFile s!"{dir}/{name}.samples").splitOn "\n" do
      let v := nums line
      if v.size != 2 then continue
      let cp := v[0]!
      let size := v[1]!
      let some glyph := Ttf.lookup f.cmap cp | throw (IO.userError s!"missing {cp}")
      let some b := Ttf.raster f glyph size size | throw (IO.userError s!"raster {name} {cp}")
      require (decide b.Valid) "bitmap bounds"
      let stem := s!"{dir}/{name}-{cp}-{size}"
      IO.FS.writeBinFile (stem ++ ".pgm") (s!"P5\n{b.w} {b.h}\n255\n".toUTF8 ++ b.pixels)
      IO.FS.writeFile (stem ++ ".box") s!"{b.x} {b.y} {b.w} {b.h} {b.advance}\n"
      pictures := pictures + 1
  let mut hostile := 0
  for line in (← IO.FS.readFile s!"{dir}/hostile.txt").splitOn "\n" do
    if line.isEmpty then continue
    let b ← IO.FS.readBinFile s!"{dir}/{line}"
    require (Ttf.read b |>.isNone) s!"hostile accepted: {line}"
    hostile := hostile + 1
  for (name, cases) in [("format4", [(65, some 5), (66, some 0), (64, none)]),
      ("format12", [(65536, some 9), (65538, some 11), (65539, none)])] do
    let some cmap := Ttf.readCmap (← IO.FS.readBinFile s!"{dir}/{name}.cmap")
      | throw (IO.userError s!"{name} rejected")
    for (c, expected) in cases do
      require (Ttf.lookup cmap c == expected) s!"{name} {c}"
  let rows := Array.replicate 3 (Paint.solid 0 3)
  let clipped : Ttf.Bitmap := ⟨-1, 0, 2, 1, 1, 1, 1, 0, 0, 0, ⟨#[255, 0]⟩⟩
  require (Ttf.blit clipped rows 0 0 0xFFFFFF 0 == rows) "left clip does not wrap to zero"
  require (Ttf.blit { clipped with x := 0, y := -1 } rows 0 0 0xFFFFFF 0 == rows) "top clip does not wrap to zero"
  let visible := Ttf.blit { clipped with x := 0 } rows 0 0 0xFFFFFF 1
  require (Paint.getPx visible[0]! 0 == 0xFFFFFF && Paint.getPx visible[0]! 1 == 0xFFFFFF && Paint.getPx visible[0]! 2 == 0) "bold coverage extends once"
  let font ← Font.load
  require (Text.adv font 'i'.val < Text.adv font 'W'.val) "proportional advances"
  require ((font.glyph 'क'.val).noto.isNone && (font.glyph '龘'.val).noto.isNone) "Indic/rare CJK fallback"
  require ((font.glyph 'A'.val).noto.isSome && (font.glyph 'א'.val).noto.isSome) "Noto selection"
  require (Text.adv font 0x301 == 0 && Text.adv font 0x200D == 0) "marks and invisibles"
  let some r := font.noto.chars['A'.val]? | throw (IO.userError "A absent")
  let first := font.noto.bitmap r
  require (first.isSome) "cache witness"
  let zero ← IO.mkRef (0 : Nat)
  let t0 ← IO.monoNanosNow
  for _ in [0:10000] do
    let salt ← zero.get
    let again := font.noto.bitmap { r with glyph := r.glyph + salt }
    require (ptrEq (again.get!).pixels (first.get!).pixels) "cache recomputed a glyph"
  let t1 ← IO.monoNanosNow
  IO.println s!"cache: 10000 repeated lookups in {(t1 - t0) / 1000} us"
  let small ← Font.load (density := 280)
  let big ← Font.load (density := 560)
  require (small.cell == 32 && font.cell == 48 && big.cell == 64) "density cells"
  require (Text.adv small 'W'.val < Text.adv font 'W'.val && Text.adv font 'W'.val < Text.adv big 'W'.val) "density metrics"
  let ink (f : Font.Font) := (f.noto.chars['W'.val]? >>= f.noto.bitmap).map (·.pixels.size) |>.getD 0
  require (ink small < ink font && ink font < ink big) "density raster cache keys"
  let fallback (f : Font.Font) := (List.range f.cell).any fun row => f.row (f.glyph '龘'.val) row != 0
  require (fallback small && fallback big) "density fallback pixels"
  let mobile ← Font.load (density := 160)
  -- Typography variants must equal fresh parsing/metrics at the requested
  -- size. Alternate sizes to catch a cache key that aliases their pixels.
  for size in [14, 24, 14, 56, 12, 16] do
    let resized := mobile.atSize size
    let fresh ← Noto.load size
    require (resized.cell == size) s!"typography size {size} exists"
    for c in "Quiet Wi Å שלום".toList do
      let some actual := resized.noto.chars[c.val]? | throw (IO.userError "missing variant glyph")
      let some expected := fresh.chars[c.val]? | throw (IO.userError "missing fresh glyph")
      require (actual.advance == expected.advance) s!"variant exact hmtx {size}/{c}"
      let a := resized.noto.bitmap actual
      let e := fresh.bitmap expected
      require (a.map (·.pixels) == e.map (·.pixels) && a.map (·.w) == e.map (·.w)) s!"variant actual pixels {size}/{c}"
  let atlas ← IO.FS.readBinFile "assets/ui-glyphs.bin"
  require ((Glyphs.parse (atlas.extract 0 (atlas.size - 1))).isNone) "truncated icon coverage refused"
  require ((Glyphs.parse (atlas ++ ⟨#[0]⟩)).isNone) "trailing icon data refused"
  for size in [12, 16, 20, 24, 63, 96] do
    for name in ["send", "image-plus", "icon-clip", "icon-check", "icon-close"] do
      let some coverage := mobile.icons.coverage name size | throw (IO.userError s!"missing icon {name}/{size}")
      require (coverage.size == size * size && coverage.data.any (· > 0) && coverage.data.any (· == 0)) s!"icon geometry {name}/{size}"
      let ground := 0xf7f7f7
      let ink := 0x7647c7
      let b := (Paint.Bitmap.blank (size + 4) (size + 4) (Paint.solid ground (size + 4))).icon mobile name 2 2 size ink
      for y in [0:size] do
        for x in [0:size] do
          require (Paint.getPx b.rows[y + 2]! (x + 2) == Paint.blendText ink ground coverage[y * size + x]!.toNat) s!"native icon compositing {name}/{size}"
  for f in [mobile, small, font, big] do
    for sample in ["🙂", "👩🏽‍💻", "🇯🇵"] do
      let token := (f.emoji.emojify (sample.toList.map Char.val).toArray)[0]!
      let some pic := f.emoji.picture token | throw (IO.userError "missing density emoji")
      let expectedW := max 1 ((f.emoji.width token * f.cell + f.emoji.size/2) / f.emoji.size)
      require (Text.adv f token == expectedW) s!"emoji layout scales at cell {f.cell}"
      let bitmap := (Paint.Bitmap.blank 160 160 (Paint.solid 0xffffff 160)).glyph f token 4 4 0 false
      let mut ink := 0
      let mut lower := 0
      for y in [0:160] do
        for x in [0:160] do
          if Paint.getPx bitmap.rows[y]! x != 0xffffff then
            ink := ink + 1
            require (4 ≤ x && x < 4+expectedW && 4 ≤ y && y < 4+f.cell)
              s!"emoji painting fits its text cell at {f.cell}px (source {pic.w}x{pic.h})"
            if y ≥ 4+f.cell/2 then lower := lower + 1
      require (ink > 0 && lower > 0) "scaled emoji retains the lower half, not a clipped source"
  IO.println "emoji density: 12 actual glyph renders fit their measured cells, including desktop"
  let samples := (← IO.FS.readFile s!"{dir}/lines.txt").splitOn "\n"
  let mut image := Paint.Bitmap.blank 1100 (samples.length * 90 + 30) (Paint.solid 0xFFFFFF 1100)
  let mut placed := ""
  for (line, i) in samples.zipIdx do
    if i == 11 then writePpm s!"{dir}/scripts-core.ppm" image.w image.rows
    let layout := Text.oneLine font 1060 line
    image := image.line font layout 20 (20 + i * 90) 0x141414
    if i < 11 then
      for g in layout do
        let some ref := (font.glyph g.c).noto | throw (IO.userError s!"sample fallback {g.c}")
        placed := placed ++ s!"{Noto.names[ref.face]!} {ref.glyph} {font.cell} {g.x + 20} {20 + i*90}\n"
  IO.FS.writeFile s!"{dir}/scripts.layout" placed
  let rows := image.rows.map fun row => Id.run do
    let mut rgb := ByteArray.empty
    for x in [0:image.w] do
      for c in [0:3] do rgb := rgb.push row[4*x+c]!
    return rgb
  let body := rows.foldl (· ++ ·) ByteArray.empty
  IO.FS.writeBinFile s!"{dir}/scripts.ppm" (s!"P6\n{image.w} {image.h}\n255\n".toUTF8 ++ body)
  IO.println s!"Noto: {mapped} cmap/metric pairs, {pictures} coverage bitmaps, {hostile} hostile files refused; fallback and cache pass"
