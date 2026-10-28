/-
Unicode 16 conformance through L2, on the renderer's actual display path.
Checks levels, indexed order (so repeated characters cannot hide a bug),
code-point order, and the shared EN/AN run definition. Exclusions depend
only on input features, never on expected output or whether a case fails.
Also checks issue #3 and weak/neutral boundary regressions. No laws here.
-/
import engine.renderer.Text
import tests.app.BidiScope

namespace BidiTest
open Text Text.Bidi

def words (s : String) : List String := (s.splitOn " ").filter (· != "")
def trim (s : String) : String := s.trimAscii.toString
def nums (s : String) : List Nat := (words (trim s)).map (fun s => s.toNat!)

def hex (s : String) : Nat := s.toList.foldl (fun n c =>
  n * 16 + if c ≤ '9' then c.toNat - 48 else c.toNat - 55) 0

def cp (s : String) : List UInt32 := s.toList.map (·.val)

def representative (s : String) : UInt32 :=
  match s with
  | "L" => 0x61 | "R" => 0x5D0 | "AL" => 0x627 | "EN" => 0x31 | "AN" => 0x661
  | "ES" => 0x2B | "ET" => 0x23 | "CS" => 0x2C | "NSM" => 0x300 | "BN" => 0xAD
  | "B" => 0x2029 | "S" => 0x9 | "WS" => 0x20 | "ON" => 0x21
  | "LRE" => 0x202A | "RLE" => 0x202B | "PDF" => 0x202C | "LRO" => 0x202D
  | "RLO" => 0x202E | "LRI" => 0x2066 | "RLI" => 0x2067 | "FSI" => 0x2068 | "PDI" => 0x2069
  | _ => 0xFFFFFFFF

/-- Disjoint exclusions, in this precedence order. -/
def excluded (cs : List UInt32) : Option Nat :=
  if cs.any (fun c => 0x202A ≤ c && c ≤ 0x202E) then some 0
  else if cs.any (fun c => 0x2066 ≤ c && c ≤ 0x2069) then some 1
  else if cs.any (fun c => classOf c == .bn) then some 2
  else if cs.any control then some 3
  else if cs.any bracket then some 4
  else if cs.any Emoji.isEmoji then some 5 else none

def exclusionNames : Array String := #["X1-X9 embeddings/overrides/PDF", "X5a-X10 isolates",
  "X9 boundary neutrals", "Quiet neutral LRM/RLM/ALM policy", "N0 paired-bracket characters", "Quiet internal emoji tokens (plane 15+)"]

structure Counts where
  records : Nat := 0
  pass : Nat := 0
  fail : Nat := 0
  runs : Nat := 0
  excluded : Array Nat := Array.replicate 6 0
  deriving Inhabited

def contiguous [BEq α] (needle haystack : List α) : Bool :=
  (List.range (haystack.length + 1)).any (fun i => needle == (haystack.drop i).take needle.length)

def checkCase (cs : List UInt32) (mode para : Nat) (expectedLv expectedOrder : List Nat)
    (label : String) (n : Counts) : IO Counts := do
  if let some k := excluded cs then
    return { n with excluded := n.excluded.modify k (· + 1) }
  let rtl := if mode == 2 then rtlPara cs else mode == 1
  let input := cs.mapIdx (fun i c => (i, Text.dirOf c))
  let lv := Text.Bidi.levels rtl input
  let order := display rtl input
  let chars := visualIn rtl cs
  let runs := numberRuns .en rtl input ++ numberRuns .an rtl input
  let ok := (if rtl then 1 else 0) == para && lv == expectedLv && order == expectedOrder &&
    chars == expectedOrder.map (fun i => cs[i]!) && runs.all (fun r => contiguous r order)
  if !ok && n.fail < 12 then
    IO.println s!"FAIL {label} mode={mode} input={cs.map (·.toNat)}\n  levels={lv}, want={expectedLv}\n  order={order}, want={expectedOrder}"
  return { n with
    pass := n.pass + (if ok then 1 else 0)
    fail := n.fail + (if ok then 0 else 1)
    runs := n.runs + runs.length }

def report (name : String) (n : Counts) : IO Unit := do
  IO.println s!"{name}: records={n.records} pass={n.pass} fail={n.fail} number-runs={n.runs}"
  for i in [:exclusionNames.size] do
    IO.println s!"  excluded {exclusionNames[i]!}: {n.excluded[i]!}"
  IO.println s!"  total paragraph cases={n.pass + n.fail + n.excluded.foldl (· + ·) 0}"

def types (path : String) : IO Counts := do
  let mut n : Counts := {}
  let mut lv : List Nat := []
  let mut order : List Nat := []
  let lines ← IO.FS.lines path
  for i in [:lines.size] do
    let line := trim ((lines[i]!.splitOn "#").head!)
    if line.isEmpty then continue
    if line.startsWith "@Levels:" then
      lv := (words (trim ((line.splitOn ":")[1]!))).map (fun s => s.toNat?.getD 999)
    else if line.startsWith "@Reorder:" then
      order := nums ((line.splitOn ":")[1]!)
    else if !line.startsWith "@" then
      let fields := line.splitOn ";"
      let cs := (words (trim fields[0]!)).map representative
      if cs.contains 0xFFFFFFFF then throw (IO.userError s!"unknown class: {line}")
      let bits := hex (trim fields[1]!)
      n := { n with records := n.records + 1 }
      for (bit, mode) in [(1, 2), (2, 0), (4, 1)] do
        if bits &&& bit != 0 then
          let para := if mode == 2 then (if rtlPara cs then 1 else 0) else mode
          n ← checkCase cs mode para lv order s!"BidiTest:{i+1}" n
  if n.records != 490846 then throw (IO.userError "BidiTest: incomplete corpus")
  report "BidiTest" n
  return n

def characters (path : String) : IO Counts := do
  let mut n : Counts := {}
  let lines ← IO.FS.lines path
  for i in [:lines.size] do
    let line := trim ((lines[i]!.splitOn "#").head!)
    if line.isEmpty then continue
    let fields := line.splitOn ";"
    let cs := (words (trim fields[0]!)).map (fun s => (hex s).toUInt32)
    let mode := (trim fields[1]!).toNat!
    let para := (trim fields[2]!).toNat!
    let lv := (words (trim fields[3]!)).map (fun s => s.toNat?.getD 999)
    n ← checkCase cs mode para lv (nums fields[4]!) s!"BidiCharacterTest:{i+1}" { n with records := n.records + 1 }
  if n.records != 91707 then throw (IO.userError "BidiCharacterTest: incomplete corpus")
  report "BidiCharacterTest" n
  return n

def regressions : IO Nat := do
  let mut pass := 0
  let mut fail := 0
  -- W2 converts EN to AN after AL: ES/ET then remain neutral in W6.
  for (left, right, arabic) in [("א", "ב", false), ("ا", "ب", true)] do
    for (s, ar) in [("2.0", "2.0"), ("1,000", "1,000"), ("12:30", "12:30"),
                    ("50%", "%50"), ("3-4", "4-3")] do
      let input := cp s!"{left} {s} {right}"
      let want := cp s!"{right} {if arabic then ar else s} {left}"
      for rtl in [false, true, rtlPara input] do
        if visualIn rtl input == want then pass := pass + 1
        else fail := fail + 1; IO.println s!"FAIL issue #3 {left} {s} {right}, rtl={rtl}"
  for (s, want) in [("א $12:30%% ב", "ב $12:30%% א"), ("ا ١,٢ ب", "ب ١,٢ ا"),
                    ("א 1++2 ב", "ב 2++1 א"), ("א 1,,2 ב", "ב 2,,1 א"),
                    ("ا a50% ب", "ب a50% ا"), ("א 1#2 ב", "ב 1#2 א"),
                    ("א 1́:2 ב", "ב 1́:2 א"), ("א 12:30   ", "   12:30 א")] do
    if (visualL (cp s)).1 == cp want then pass := pass + 1
    else fail := fail + 1; IO.println s!"FAIL regression {s}"
  -- Corpus-discovered L1 regression: NSM inherited S, but is not itself S.
  for rtl in [false, true] do
    let cs : List UInt32 := [0x5D0, 0x9, 0x300, 0x661]
    let lv := Text.Bidi.levels rtl (cs.map fun c => (c, Text.dirOf c))
    let want := if rtl then [1, 1, 1, 2] else [1, 0, 1, 2]
    if lv == want then pass := pass + 1 else fail := fail + 1
  IO.println s!"regressions: pass={pass} fail={fail}"
  return fail
end BidiTest

def main (args : List String) : IO UInt32 := do
  let dir := args[0]?.getD "tests/app/unicode-bidi-16.0.0"
  let r ← BidiTest.regressions
  let a ← BidiTest.types (dir ++ "/BidiTest.txt")
  let b ← BidiTest.characters (dir ++ "/BidiCharacterTest.txt")
  return if r + a.fail + b.fail == 0 then 0 else 1
