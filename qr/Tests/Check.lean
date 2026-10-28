/-
qr_check: the deterministic suite (the laws are checked when the library
builds; this runs the code).

- data streams: random segment lists of every mode round trip through
  `dataStream`/`parse`; random bit strings either fail to parse or parse
  to segments that round trip again
- Reed–Solomon: every block shape QR uses, errors up to capacity
  corrected, beyond it refused or (rarely) corrected to another codeword,
  never anything else
- format and version information with up to 3 wrong bits, exhaustively
- matrices: versions 1–40 × levels L M Q H × masks 0–7, encoded and read
  back, as drawn and mirrored, and with module damage within capacity
- frames: rendered symbols of every version and level, and exact
  rotations and mirror images, decoded from pixels
- hostile frames (empty, inconsistent sizes, flat, noise, checkerboards,
  finder wallpaper, stripes, damaged symbols) give `none`, quickly
- fuzzing: damaged matrices and frames decode to the right payload or to
  nothing, never to a wrong one
-/
import Qr
import Tests.Pgm

open Qr

/-- A deterministic xorshift generator. -/
structure Rng where
  s : UInt64

def Rng.next (r : Rng) : UInt64 × Rng :=
  let x := r.s
  let x := x ^^^ (x <<< 13)
  let x := x ^^^ (x >>> 7)
  let x := x ^^^ (x <<< 17)
  (x, ⟨x⟩)

def Rng.below (r : Rng) (n : Nat) : Nat × Rng :=
  let (x, r) := r.next
  (if n == 0 then 0 else x.toNat % n, r)

def Rng.bytes (r : Rng) (n : Nat) : ByteArray × Rng := Id.run do
  let mut r := r
  let mut out := ByteArray.emptyWithCapacity n
  for _ in [0:n] do
    let (x, r') := r.below 256
    r := r'
    out := out.push x.toUInt8
  return (out, r)

structure Tally where
  pass : Nat := 0
  fail : Nat := 0
  notes : Array String := #[]

def Tally.check (t : Tally) (ok : Bool) (what : String) : Tally :=
  if ok then { t with pass := t.pass + 1 }
  else { t with fail := t.fail + 1, notes := if t.notes.size < 20 then t.notes.push what else t.notes }

def invite (r : Rng) (n : Nat) : String × Rng := Id.run do
  let abc := "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz".toList
  let mut s := "quiet://join/"
  let mut r := r
  for _ in [0:n] do
    let (i, r') := r.below 62
    r := r'
    s := s.push (abc.getD i 'x')
  return (s, r)

def hex (b : ByteArray) : String :=
  b.foldl (fun s x => s ++ (if x < 16 then "0" else "") ++ String.ofList (Nat.toDigits 16 x.toNat)) ""

/-! ## Images: exact transforms -/

def Qr.Image.rot90 (img : Image) : Image := Id.run do
  let mut px := ByteArray.emptyWithCapacity (img.w * img.h)
  for y in [0:img.w] do
    for x in [0:img.h] do
      px := px.push (bget img.px ((img.h - 1 - x) * img.stride + y))
  return { w := img.h, h := img.w, stride := img.h, px }

def Qr.Image.mirror (img : Image) : Image := Id.run do
  let mut px := ByteArray.emptyWithCapacity (img.w * img.h)
  for y in [0:img.h] do
    for x in [0:img.w] do
      px := px.push (bget img.px (y * img.stride + (img.w - 1 - x)))
  return { img with stride := img.w, px }

def gen (w h : Nat) (f : Nat → Nat → Nat) : Image := Id.run do
  let mut px := ByteArray.emptyWithCapacity (w * h)
  for y in [0:h] do
    for x in [0:w] do
      px := px.push (f x y).toUInt8
  return { w, h, stride := w, px }

/-! ## The sections -/

def randomSeg (r : Rng) (v : Nat) : Seg × Rng := Id.run do
  let (k, r) := r.below 4
  let (len, r) := r.below 40
  let mut r := r
  match k with
  | 0 =>
    let mut ds := #[]
    for _ in [0:len] do
      let (d, r') := r.below 10; r := r'; ds := ds.push (d + 48).toUInt8
    return (.numeric ds.toList, r)
  | 1 =>
    let mut cs := #[]
    for _ in [0:len] do
      let (d, r') := r.below 45; r := r'; cs := cs.push (alnumChr d)
    return (.alnum cs.toList, r)
  | 2 =>
    let (b, r') := r.bytes len
    return (.bytes b.toList, r')
  | _ =>
    let (n, r') := r.below 1000000
    let (sz, r') := r'.below 3
    let n := match sz with | 0 => n % 128 | 1 => n % 16384 | _ => n
    let _ := v
    return (.eci n, r')

def streams (t : Tally) : Tally := Id.run do
  let mut t := t
  let mut r : Rng := ⟨0x5eed1⟩
  -- segments round trip through the codewords
  for i in [0:3000] do
    let (v, r1) := r.below 40
    let v := v + 1
    let (ns, r2) := r1.below 5
    r := r2
    let mut ss := #[]
    for _ in [0:ns] do
      let (s, r') := randomSeg r v; r := r'; ss := ss.push s
    let e := Ecc.all.getD (i % 4) .M
    match dataStream v (dataCodewords v e) ss.toList with
    | none => pure ()
    | some cw => t := t.check (parse v (bytesBits cw) == some ss.toList) s!"stream {i}"
  -- random bits: whatever parses round trips
  for i in [0:3000] do
    let (v, r1) := r.below 40
    let v := v + 1
    let (len, r2) := r1.below 400
    let (b, r3) := r2.bytes (len / 8 + 1)
    r := r3
    -- a plausible mode in front, so that segments are actually read
    let (m, r4) := r.below 4
    r := r4
    let mode := [1, 2, 4, 7].getD m 4
    let bits := bitsOf mode 4 ++ bytesBits b.toList
    match parse v bits with
    | none => t := t.check true ""
    | some ss =>
      let ok := ss.all (Seg.valid v) &&
        (match dataStream v (segsBits v ss).length ss with
         | some cw => parse v (bytesBits cw) == some ss
         | none => true)
      t := t.check ok s!"random stream {i}"
  return t

def reedSolomon (t : Tally) : Tally × Nat × Nat := Id.run do
  let mut t := t
  let mut r : Rng := ⟨0xc0ffee⟩
  let mut shapes : Array (Nat × Nat) := #[]
  for v in [1:41] do
    for e in Ecc.all do
      let l := layout v e
      for len in [l.short, l.short + 1] do
        if !shapes.contains (len + l.ecLen, l.ecLen) then shapes := shapes.push (len + l.ecLen, l.ecLen)
  let mut miscorrected := 0
  for (n, k) in shapes do
    for trial in [0:12] do
      let (d, r1) := r.bytes (n - k); r := r1
      let cw := d.toList.toArray ++ RS.encode k d.toList.toArray
      t := t.check (RS.allZero (RS.syndromes k cw)) s!"rs encode {n} {k}"
      -- errors: within capacity for trials < 8, beyond it after
      let ne := if trial < 8 then trial * (k / 2) / 7 else k / 2 + trial - 7
      let mut bad := cw
      let mut used : Array Nat := #[]
      for _ in [0:ne] do
        let (p, r1) := r.below n
        let (x, r2) := r1.below 255
        r := r2
        if !used.contains p then
          used := used.push p
          bad := bad.setIfInBounds p ((bad[p]?.getD 0) ^^^ (x + 1).toUInt8)
      let errs := used.size
      match RS.correct k bad with
      | some c =>
        if errs ≤ k / 2 then t := t.check (c == cw) s!"rs {n} {k} {errs}"
        else
          t := t.check (RS.allZero (RS.syndromes k c) && RS.dist bad c ≤ k / 2) s!"rs beyond {n} {k}"
          if c != cw then miscorrected := miscorrected + 1
      | none => t := t.check (errs > k / 2) s!"rs refused {n} {k} {errs}"
  return (t, shapes.size, miscorrected)

def formats (t : Tally) : Tally := Id.run do
  let mut t := t
  for e in Ecc.all do
    for k in [0:8] do
      let f := formatBits e k
      for a in [0:15] do
        for b in [a:15] do
          for c in [b:15] do
            let x := f ^^^ (1 <<< a) ^^^ (if b > a then 1 <<< b else 0) ^^^ (if c > b then 1 <<< c else 0)
            t := t.check (decodeFormat x == some (e, k)) s!"format {e.name} {k}"
  for v in [7:41] do
    for a in [0:18] do
      for b in [a:18] do
        let x := bchVersion v ^^^ (1 <<< a) ^^^ (if b > a then 1 <<< b else 0)
        t := t.check (decodeVersion x == some v) s!"version {v}"
  return t

/-- Payload bytes that fill most of a version's byte capacity. -/
def fill (r : Rng) (v : Nat) (e : Ecc) : ByteArray × Rng :=
  let cap := (dataBits v e - 4 - countWidth v 2) / 8
  let (k, r) := r.below (cap / 4 + 1)
  r.bytes (cap - k)

def grids (t : Tally) : IO Tally := do
  let mut t := t
  let mut r : Rng := ⟨0xabcdef⟩
  for v in [1:41] do
    for e in Ecc.all do
      for k in [0:8] do
        let (p, r1) := fill r v e; r := r1
        match encode p e v (some k) with
        | none => t := t.check false s!"encode v{v} {e.name} mask {k}"
        | some s =>
          t := t.check (s.version == v && s.mask == k) s!"version/mask v{v}"
          let ok := (decodeGrid s.grid).map (·.payload.data) == some p.data
          t := t.check ok s!"grid v{v} {e.name} mask {k}"
          if k == v % 8 then
            let m := (decodeGridAny s.grid.transpose)
            t := t.check (m.map (fun d => (d.payload.data, d.mirrored)) == some (p.data, true))
              s!"mirrored grid v{v} {e.name}"
            -- damage: flip a quarter of what the level corrects, spread over the matrix
            let l := layout v e
            let flips := (l.ecLen / 2) * l.nb / 4
            let mut g := s.grid
            let mut r2 := r
            for _ in [0:flips] do
              let (x, r3) := r2.below g.n
              let (y, r4) := r3.below g.n
              r2 := r4
              -- leave the format information alone
              if !(x ≤ 8 && y ≤ 8) && !(x ≤ 8 && y + 8 ≥ g.n) && !(y ≤ 8 && x + 8 ≥ g.n) then
                g := g.set x y (!g.get x y)
            r := r2
            t := t.check ((decodeGrid g).map (·.payload.data) == some p.data) s!"damaged grid v{v} {e.name}"
  return t

def frames (t : Tally) : IO Tally := do
  let mut t := t
  let mut r : Rng := ⟨0x7777⟩
  for v in [1:41] do
    for e in Ecc.all do
      let (p, r1) := fill r v e; r := r1
      match encode p e v with
      | none => t := t.check false s!"encode v{v}"
      | some s =>
        let img := render s (if v ≤ 10 then 3 else 2) 4
        let ok := (decode img.w img.h img.px).map (·.data) == some p.data
        t := t.check ok s!"frame v{v} {e.name}"
  -- every mask, and exact rotations and mirror images
  for v in [1, 2, 7, 10, 14] do
    for k in [0:8] do
      let (p, r1) := fill r v .M; r := r1
      if let some s := encode p .M v (some k) then
        let img := render s 3 4
        let mut im := img
        for turn in [0:4] do
          for mirrored in [false, true] do
            let x := if mirrored then im.mirror else im
            let d := decodeImage x
            t := t.check ((d.map (·.payload.data)) == some p.data && (d.map (·.mirrored)) == some mirrored)
              s!"frame v{v} mask {k} turn {turn} mirrored {mirrored}"
          im := im.rot90
  return t

/-- Frames that hold no symbol: each must give `none`, quickly. -/
def hostile (t : Tally) : IO (Tally × Nat) := do
  let mut t := t
  let mut worst := 0
  let mut cases : Array (String × Image) := #[
    ("empty", { w := 0, h := 0, stride := 0, px := .empty }),
    ("short buffer", { w := 640, h := 480, stride := 640, px := ByteArray.mk (Array.replicate 1000 0) }),
    ("stride below width", { w := 100, h := 100, stride := 50, px := ByteArray.mk (Array.replicate 10000 0) }),
    ("huge size", { w := 1000000, h := 1000000, stride := 1000000, px := ByteArray.mk (Array.replicate 100 0) }),
    ("one pixel", gen 1 1 fun _ _ => 0),
    ("one row", gen 640 1 fun x _ => if x % 3 == 0 then 0 else 255),
    ("black", gen 320 240 fun _ _ => 0),
    ("white", gen 320 240 fun _ _ => 255),
    ("grey", gen 320 240 fun _ _ => 128),
    ("vertical stripes", gen 320 240 fun x _ => if x / 3 % 2 == 0 then 0 else 255),
    ("horizontal stripes", gen 320 240 fun _ y => if y / 4 % 2 == 0 then 0 else 255),
    ("gradient", gen 320 240 fun x y => (x + y) % 256),
    ("rings", gen 320 240 fun x y =>
      let d := max (if x ≥ 160 then x - 160 else 160 - x) (if y ≥ 120 then y - 120 else 120 - y)
      if d / 5 % 2 == 0 then 0 else 255)]
  for s in [1, 2, 3, 4, 5, 7, 9, 12] do
    cases := cases.push (s!"checkerboard {s}", gen 320 240 fun x y => if (x / s + y / s) % 2 == 0 then 0 else 255)
  -- finder wallpaper: finder patterns everywhere, at many sizes
  for s in [2, 3, 5] do
    let f := fun x y =>
      let cx := x / s % 9
      let cy := y / s % 9
      let d := max (if cx ≥ 4 then cx - 4 else 4 - cx) (if cy ≥ 4 then cy - 4 else 4 - cy)
      if d == 2 || d == 4 then 255 else 0
    cases := cases.push (s!"finder wallpaper {s}", gen 400 300 f)
  let mut r : Rng := ⟨0x51⟩
  for i in [0:6] do
    let (b, r1) := r.bytes (320 * 240); r := r1
    let b := if i % 2 == 0 then b else ⟨b.data.map fun x => if x < 128 then 0 else 255⟩
    cases := cases.push (s!"noise {i}", { w := 320, h := 240, stride := 320, px := b })
  -- three finders and nothing decodable between them
  if let some s := encode "x".toUTF8 .L 3 then
    let g := Id.run do
      let mut g := s.grid
      for y in [0:g.n] do
        for x in [0:g.n] do
          if !(functionCanvas 3).fn.get x y then g := g.set x y ((x * 7 + y * 3) % 5 == 0)
      return g
    cases := cases.push ("finders around garbage", render { s with grid := g } 4 4)
  for (name, img) in cases do
    let t0 ← IO.monoMsNow
    let d ← IO.lazyPure fun _ => decodeImage img
    let t1 ← IO.monoMsNow
    worst := max worst (t1 - t0)
    if t1 - t0 > 300 then IO.println s!"  slow hostile frame: {name} {t1 - t0} ms"
    t := t.check d.isNone s!"hostile frame decoded: {name}"
  return (t, worst)

/-- Damaged frames and matrices: the right payload or nothing. -/
def fuzz (t : Tally) : IO (Tally × Nat × Nat) := do
  let mut t := t
  let mut right := 0
  let mut nothing := 0
  let mut r : Rng := ⟨0xf022⟩
  for i in [0:1500] do
    let (v, r1) := r.below 12; r := r1
    let v := v + 1
    let e := Ecc.all.getD (i % 4) .M
    let (p, r1) := fill r v e; r := r1
    let some s := encode p e v | continue
    let (rate, r1) := r.below 30; r := r1
    let mut g := s.grid
    for y in [0:g.n] do
      for x in [0:g.n] do
        let (z, r1) := r.below 100; r := r1
        if z < rate then g := g.set x y (!g.get x y)
    match decodeGridAny g with
    | some d =>
      t := t.check (d.payload.data == p.data) s!"fuzzed grid decoded wrongly ({i})"
      right := right + 1
    | none => nothing := nothing + 1
  for i in [0:300] do
    let (v, r1) := r.below 10; r := r1
    let v := v + 1
    let (p, r1) := fill r v .M; r := r1
    let some s := encode p .M v | continue
    let img := render s 3 4
    let (rate, r1) := r.below 25; r := r1
    let mut px := img.px
    for j in [0:px.size] do
      let (z, r1) := r.below 100; r := r1
      if z < rate then
        let (x, r2) := r.below 256; r := r2
        px := bset px j x.toUInt8
    match decodeImage { img with px } with
    | some d =>
      t := t.check (d.payload.data == p.data) s!"fuzzed frame decoded wrongly ({i})"
      right := right + 1
    | none => nothing := nothing + 1
  return (t, right, nothing)

/-- Matrices qrencode drew (tests/fixtures/qrencode, one for each version
1–40, levels and data kinds by turns): decoded as matrices, and as frames
drawn from them, turned a quarter. -/
def fixtures (t : Tally) : IO Tally := do
  let mut t := t
  for line in (← IO.FS.lines "tests/fixtures/qrencode/manifest.tsv") do
    let [path, want] := line.splitOn "\t" | continue
    let rows := ((← IO.FS.readFile path).splitOn "\n").filter (· ≠ "")
    let n := rows.length
    let mut g := Grid.blank n
    for y in [0:n] do
      let r := (rows.getD y "").toList
      for x in [0:n] do
        if r.getD x '.' == '#' then g := g.set x y true
    t := t.check ((decodeGrid g).map (hex ·.payload) == some want) s!"qrencode matrix {path}"
    let img := render { version := (n - 17) / 4, ecc := .M, mask := 0, grid := g } 3 4
    t := t.check ((decodeImage img.rot90).map (hex ·.payload) == some want) s!"qrencode frame {path}"
  return t

def main (args : List String) : IO UInt32 := do
  let mut t : Tally := {}
  t ← fixtures t
  IO.println s!"qrencode's matrices (tests/fixtures), as matrices and frames: {t.pass} passed, {t.fail} failed"
  let t0 := t
  t := streams t
  IO.println s!"data streams: {t.pass - t0.pass} passed, {t.fail - t0.fail} failed"
  let t0 := t
  let (t1, shapes, mis) := reedSolomon t
  t := t1
  IO.println s!"reed-solomon ({shapes} block shapes): {t.pass - t0.pass} passed, {t.fail - t0.fail} failed; beyond capacity, {mis} blocks corrected to another codeword (allowed)"
  let t0 := t
  t := formats t
  IO.println s!"format/version information: {t.pass - t0.pass} passed, {t.fail - t0.fail} failed"
  let t0 := t
  t ← grids t
  IO.println s!"matrices (v1-40 x L,M,Q,H x masks 0-7, mirrored, damaged): {t.pass - t0.pass} passed, {t.fail - t0.fail} failed"
  let t0 := t
  t ← frames t
  IO.println s!"frames (v1-40 x levels, masks, rotations, mirror images): {t.pass - t0.pass} passed, {t.fail - t0.fail} failed"
  let t0 := t
  let (t1, worst) ← hostile t
  t := t1
  IO.println s!"hostile frames: {t.pass - t0.pass} gave none, {t.fail - t0.fail} decoded; slowest {worst} ms"
  let t0 := t
  let (t1, right, nothing) ← fuzz t
  t := t1
  IO.println s!"fuzzing: {right} decoded right, {nothing} gave none, {t.fail - t0.fail} decoded wrongly"
  -- frames listed in a manifest (the camera suite): NAME<TAB>PATH<TAB>HEX
  if let [manifest] := args then
    let t0 := t
    let mut slow := 0
    let mut total := 0
    for line in (← IO.FS.lines manifest) do
      match line.splitOn "\t" with
      | [name, path, want] =>
        let img ← Pgm.read path
        let a ← IO.monoMsNow
        let d ← IO.lazyPure fun _ => decodeImage img
        let b ← IO.monoMsNow
        slow := max slow (b - a)
        total := total + (b - a)
        let got := d.map fun d => hex d.payload
        t := t.check (got == some want) s!"camera frame {name}"
      | _ => pure ()
    let n := t.pass + t.fail - t0.pass - t0.fail
    IO.println s!"camera frames: {t.pass - t0.pass} decoded, {t.fail - t0.fail} failed; mean {total / n.max 1} ms, slowest {slow} ms"
  for n in t.notes do IO.println s!"  FAIL {n}"
  IO.println s!"total: {t.pass} passed, {t.fail} failed"
  return if t.fail == 0 then 0 else 1
