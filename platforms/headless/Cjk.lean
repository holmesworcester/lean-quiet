/-
CJK Regular-instance glyphs against fontTools, locale routing, and the
running glyph memo: kept, equal to the raster, emptied by `fresh`, kept
per size across `atSize`, and under concurrent paint.
-/
import platforms.headless.Sim

private def check (ok : Bool) (label : String) : IO Unit :=
  unless ok do throw (IO.userError label)

private def numbers (s : String) : Array Nat := (s.splitOn " ").toArray.filterMap String.toNat?

private def same : Option Ttf.Bitmap → Option Ttf.Bitmap → Bool
  | none, none => true
  | some a, some b =>
    a.x == b.x && a.y == b.y && a.w == b.w && a.h == b.h &&
    a.advance == b.advance && a.cell == b.cell && a.left == b.left &&
    a.right == b.right && a.top == b.top && a.bottom == b.bottom && a.pixels == b.pixels
  | _, _ => false

/-- Whether two reads of a glyph with ink gave one object: a kept glyph is
the same object at every read; a raster is a new one. -/
private unsafe def kept : Option Ttf.Bitmap → Option Ttf.Bitmap → Bool
  | some a, some b => a.pixels.size > 0 && ptrEq a.pixels b.pixels
  | _, _ => false

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
  check ((font.noto.bitmap r).isSome) "no Han bitmap"
  -- Glyph numbers come through a ref, so no two reads are one expression.
  let key ← IO.mkRef r.glyph
  let read (s : Noto.Set) : IO (Option Ttf.Bitmap) := do
    return s.bitmap { r with glyph := ← key.get }
  let requests := font.noto.chars.toList.filter (fun (_,r) => r.face ≥ 9)
  let mut reads := 0
  for (_,q) in requests.take 1800 do
    key.set q.glyph
    let f := font.noto.faces[q.face]!
    let a := f.bitmap (← key.get)
    let b := f.bitmap (← key.get)
    check (a.isSome && same a (f.uncached q.glyph)) "memo agrees with the raster"
    if a.any (·.pixels.size > 0) then
      check (kept a b) "second read is the kept glyph"
      reads := reads + 1
  check (reads > 1500) "the kept-glyph check is non-vacuous"
  key.set r.glyph
  let face := font.noto.faces[r.face]!
  let u1 := face.uncached (← key.get)
  let u2 := face.uncached (← key.get)
  check (same u1 u2 && u1.any (·.pixels.size > 0) && !kept u1 u2)
    "control: a raster is a new object each time"
  -- `fresh` lets go of kept glyphs: the same bytes, new objects, kept again.
  let before ← read font.noto
  let fresh := font.fresh
  let after ← read fresh.noto
  check (same before after && !kept before after) "fresh empties the memo"
  check (kept after (← read fresh.noto)) "fresh memo keeps again"
  check (kept before (← read font.noto)) "the old font keeps its own"
  -- A size the app never prepared keeps its glyphs across atSize calls.
  let a ← read (font.atSize 23).noto
  let b ← read (font.atSize 23).noto
  check (a.isSome && kept a b) "atSize keeps an unprepared size"
  check (same a ((font.atSize 23).noto.faces[r.face]!.uncached r.glyph)) "sized memo agrees"
  check (!same a before) "sizes do not alias"
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
  IO.println s!"CJK: {maps} mappings/metrics; {rasters} bitmaps; {reads} kept glyphs equal their raster; fresh and atSize memos pass; 8 concurrent workers pass"
  (← IO.getStdout).flush
  IO.Process.exit 0
