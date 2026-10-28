/-
The symbol's tables (ISO/IEC 18004:2015): sizes, block structure per
version and error-correction level, alignment pattern positions and the
widths of segment count fields. Versions run from 1 to 40; a version `v`
symbol is `4v + 17` modules on a side.
-/
namespace Qr

/-- Error-correction level: L (7%), M (15%), Q (25%), H (30%). -/
inductive Ecc where
  | L | M | Q | H
  deriving Repr, DecidableEq, Inhabited

namespace Ecc

def all : List Ecc := [.L, .M, .Q, .H]

def ord : Ecc → Nat
  | .L => 0 | .M => 1 | .Q => 2 | .H => 3

/-- The two bits format information gives each level. -/
def bits : Ecc → Nat
  | .L => 1 | .M => 0 | .Q => 3 | .H => 2

def ofBits : Nat → Ecc
  | 1 => .L | 0 => .M | 3 => .Q | _ => .H

def name : Ecc → String
  | .L => "L" | .M => "M" | .Q => "Q" | .H => "H"

end Ecc

/-- Modules on a side. -/
def sizeOf (v : Nat) : Nat := 4 * v + 17

/-- Error-correction codewords per block, by level then version (index 0 unused). -/
def eccPerBlock : List (List Nat) := [
  [0, 7, 10, 15, 20, 26, 18, 20, 24, 30, 18, 20, 24, 26, 30, 22, 24, 28, 30, 28, 28, 28, 28, 30, 30, 26, 28, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30],
  [0, 10, 16, 26, 18, 24, 16, 18, 22, 22, 26, 30, 22, 22, 24, 24, 28, 28, 26, 26, 26, 26, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28],
  [0, 13, 22, 18, 26, 18, 24, 18, 22, 20, 24, 28, 26, 24, 20, 30, 24, 28, 28, 26, 30, 28, 30, 30, 30, 30, 28, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30],
  [0, 17, 28, 22, 16, 22, 28, 26, 26, 24, 28, 24, 28, 22, 24, 24, 30, 28, 28, 26, 28, 30, 24, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30]]

/-- Error-correction blocks, by level then version (index 0 unused). -/
def numBlocks : List (List Nat) := [
  [0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 4, 4, 4, 4, 6, 6, 6, 6, 7, 8, 8, 9, 9, 10, 12, 12, 12, 13, 14, 15, 16, 17, 18, 19, 19, 20, 21, 22, 24, 25],
  [0, 1, 1, 1, 2, 2, 4, 4, 4, 5, 5, 5, 8, 9, 9, 10, 10, 11, 13, 14, 16, 17, 17, 18, 20, 21, 23, 25, 26, 28, 29, 31, 33, 35, 37, 38, 40, 43, 45, 47, 49],
  [0, 1, 1, 2, 2, 4, 4, 6, 6, 8, 8, 8, 10, 12, 16, 12, 17, 16, 18, 21, 20, 23, 23, 25, 27, 29, 34, 34, 35, 38, 40, 43, 45, 48, 51, 53, 56, 59, 62, 65, 68],
  [0, 1, 1, 2, 4, 4, 4, 5, 6, 8, 8, 11, 11, 16, 16, 18, 16, 19, 21, 25, 25, 25, 34, 30, 32, 35, 37, 40, 42, 45, 48, 51, 54, 57, 60, 63, 66, 70, 74, 77, 81]]

/-- Modules left for data and error correction once the function patterns
(finders, separators, timing, alignment, format and version information)
are drawn. -/
def rawModules (v : Nat) : Nat :=
  let r := (16 * v + 128) * v + 64
  if v < 2 then r
  else
    let n := v / 7 + 2
    let r := r - ((25 * n - 10) * n - 55)
    if v < 7 then r else r - 36

/-- All codewords of a version: data and error correction. -/
def rawCodewords (v : Nat) : Nat := rawModules v / 8

/-- The block structure of a version at a level. -/
structure Layout where
  /-- blocks -/
  nb : Nat
  /-- error-correction codewords per block -/
  ecLen : Nat
  /-- data codewords of a short block; long blocks have one more -/
  short : Nat
  /-- short blocks, which come first -/
  nShort : Nat
  deriving Repr

def layout (v : Nat) (e : Ecc) : Layout :=
  let nb := ((numBlocks.getD e.ord []).getD v 1).max 1
  let ec := (eccPerBlock.getD e.ord []).getD v 0
  let raw := rawCodewords v
  { nb, ecLen := ec, short := raw / nb - ec, nShort := nb - raw % nb }

/-- Data codewords of a version at a level. -/
def dataCodewords (v : Nat) (e : Ecc) : Nat :=
  let l := layout v e
  rawCodewords v - l.ecLen * l.nb

/-- Data bits of a version at a level. -/
def dataBits (v : Nat) (e : Ecc) : Nat := 8 * dataCodewords v e

/-- Centres of the alignment patterns along each axis. -/
def alignPos (v : Nat) : List Nat :=
  if v < 2 then []
  else
    let n := v / 7 + 2
    let step := if v = 32 then 26 else (v * 4 + n * 2 + 1) / (n * 2 - 2) * 2
    6 :: ((List.range (n - 1)).map (fun i => sizeOf v - 7 - i * step)).reverse

/-- Width of a segment's count field: mode index 0 numeric, 1
alphanumeric, 2 byte, 3 kanji. -/
def countWidth (v : Nat) (mode : Nat) : Nat :=
  let w := match mode with
    | 0 => [10, 12, 14] | 1 => [9, 11, 13] | 2 => [8, 16, 16] | _ => [8, 10, 12]
  w.getD (if v ≤ 9 then 0 else if v ≤ 26 then 1 else 2) 0

end Qr
