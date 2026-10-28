/-
qr_tool: the codec from the command line, for the scripts in tests/ and
tools/.

  qr_tool render OUT.pgm ECC SCALE QUIET MINVERSION MASK PAYLOAD_FILE
      encode the file's bytes (byte mode); MASK is 0-7 or auto.
      Prints "version mask size".
  qr_tool decode FILE.pgm...
      one line per file: "FILE ok HEX version ecc mask mirrored corrected ms" or "FILE none ms"
  qr_tool matrix ECC VERSION MASK PAYLOAD_FILE
      the module matrix at exactly that version and mask, one character a
      module ('#' dark, '.' light)
  qr_tool qoi-encode RAW W H OUT.qoi / qoi-decode IN.qoi OUT.raw
      Lean's QOI codec on raw RGBA files (for the Pillow cross-check)
  qr_tool ascii FILE
      decode a module matrix drawn with '#' (dark) and ' ' or '.' (light),
      two characters a module as qrencode -t ASCII prints it: "ok HEX" or "none"
-/
import engine.renderer.qr.Qr
import engine.renderer.pic.Pic
import tests.qr.Pgm

open Qr

def hex (b : ByteArray) : String :=
  b.foldl (fun s x => s ++ (if x < 16 then "0" else "") ++ String.ofList (Nat.toDigits 16 x.toNat)) ""

def eccOf : String → Option Ecc
  | "L" => some .L | "M" => some .M | "Q" => some .Q | "H" => some .H | _ => none

def describe (d : Decoded) : String :=
  s!"{hex d.payload} {d.version} {d.ecc.name} {d.mask} {d.mirrored} {d.corrected}"

def asciiGrid (s : String) (cell : Nat) : Option Grid := Id.run do
  let rows := (s.splitOn "\n").filter (· ≠ "")
  let n := rows.length
  if n == 0 then return none
  let mut g := Grid.blank n
  for y in [0:n] do
    let r := (rows.getD y "").toList
    for x in [0:n] do
      if r.getD (x * cell) ' ' == '#' then g := g.set x y true
  return some g

def main (args : List String) : IO UInt32 := do
  match args with
  | ["render", out, ecc, scale, quiet, minv, mask, file] =>
    let some e := eccOf ecc | throw (IO.userError "ECC is L, M, Q or H")
    let data ← IO.FS.readBinFile file
    let mask := if mask == "auto" then none else mask.toNat?
    match encode data e minv.toNat! mask with
    | none => IO.println "too long"; return 1
    | some s =>
      Pgm.write out (render s scale.toNat! quiet.toNat!)
      IO.println s!"{s.version} {s.mask} {s.size}"
      return 0
  | "decode" :: files =>
    for f in files do
      let img ← Pgm.read f
      let t0 ← IO.monoMsNow
      let r := decodeImage img
      let t1 ← IO.monoMsNow
      match r with
      | some d => IO.println s!"{f} ok {describe d} {t1 - t0}"
      | none => IO.println s!"{f} none {t1 - t0}"
    return 0
  | ["debug", file] =>
    let img ← Pgm.read file
    let m := hybridBits img
    let fs := findFinders m
    for f in fs do IO.println s!"finder {f.c.x} {f.c.y} size {f.size} count {f.count}"
    for (tl, tr, bl) in triangles fs do
      let q := Tri.of m tl tr bl
      IO.println s!"tri tl {q.tl.x},{q.tl.y} tr {q.tr.x},{q.tr.y} bl {q.bl.x},{q.bl.y} ms {q.ms} corners {q.corners.isSome}"
      for n in sizeCandidates q.tl q.tr q.bl q.ms do
        let t0 := finderMap q n
        IO.println s!"  n {n}: first-map timing {t0.map (timingAt m · n)}"
        match mapFor m q n with
        | none => IO.println s!"  n {n}: no map"
        | some t =>
          let g := sampleGrid m t n
          let (a, b) := readFormat g
          IO.println s!"  n {n}: timing {timingScore g} fmt {decodeFormat a |>.map (fun (e, k) => (e.name, k))} {decodeFormat b |>.map (fun (e, k) => (e.name, k))} version {readVersion g} ok {(decodeGridAny g).isSome}"
    return 0
  | ["matrix", ecc, ver, mask, file] =>
    let some e := eccOf ecc | throw (IO.userError "ECC is L, M, Q or H")
    let data ← IO.FS.readBinFile file
    match encode data e ver.toNat! (some mask.toNat!) with
    | some s =>
      if s.version != ver.toNat! then IO.println "too long"; return 1
      for y in [0:s.size] do
        IO.println (String.ofList ((List.range s.size).map fun x => if s.grid.get x y then '#' else '.'))
      return 0
    | none => IO.println "too long"; return 1
  | ["qoi-encode", raw, w, h, out] =>
    -- raw RGBA (4 bytes a pixel) to QOI with Lean's encoder
    let px ← IO.FS.readBinFile raw
    IO.FS.writeBinFile out (Pic.encode { w := w.toNat!, h := h.toNat!, px })
    return 0
  | ["qoi-decode", qoi, out] =>
    -- QOI to raw RGBA with Lean's decoder; prints "w h" or "none"
    match Pic.decode (← IO.FS.readBinFile qoi) with
    | some p => IO.FS.writeBinFile out p.px; IO.println s!"{p.w} {p.h}"; return 0
    | none => IO.println "none"; return 1
  | ["ascii", file] =>
    let s ← IO.FS.readFile file
    let rows := (s.splitOn "\n").filter (· ≠ "")
    let cell := if (rows.headD "").length > rows.length then 2 else 1
    match (asciiGrid s cell).bind decodeGridAny with
    | some d => IO.println s!"ok {describe d}"
    | none => IO.println "none"
    return 0
  | _ =>
    IO.eprintln "usage: see tests/qr/Tool.lean"
    return 2
