/-
The codec that runs against its specification. The compiler runs
`encodeFast` and `decodeFast` for `encode` and `decode` (the `@[csimp]`
laws `encode_eq_fast` and `decode_eq_fast`); here the specification runs
too, as `encodeSpec` and `decodeSpec`, which are `encode` and `decode`
by rfl but are other constants, so the compiler leaves them on lists.

On random values of every codec the engine has (numbers, from one
byte long to 4 KiB, which are read and written by halves past 8 bytes;
byte strings of 0 to 200 KiB; booleans, bytes, lists, tuples, options, sums, ops,
verdicts, Community's and Connection's bodies and facts, sync's keys,
ranges and claims):
- `encode` gives the specification's bytes, and so does `encInto` after
  a buffer that is already there;
- `decode` of them gives the value back, and `decFrom` reads the value
  at an offset, between other bytes;
- `decode` and `decodeSpec` agree on mutants of those bytes: cut short,
  grown, a byte flipped, inserted, deleted or set to 0x80 or 0xFF, a
  number's first or last byte padded to a longer LEB128 form, the tag followed
  by garbage, and garbage alone.

A number 64 KiB long is checked against the specification too.

Negative controls: decoding as `decFrom` alone (no end check, no
re-encoding) and with the end check but no re-encoding must each take
some mutant the specification refuses, so the mutants reach the checks
that make `decodeFast` strict.
-/
import tests.engine.Lib
import ops.connection.All

open Engine Engine.Sync Tests Codec

/-! ## The specification, run -/

def encodeSpec {α} [Codec α] (a : α) : ByteArray := ⟨(enc a).toArray⟩

def decodeSpec {α} [Codec α] (b : ByteArray) : Option α :=
  match dec b.data.toList with
  | some (a, []) => if enc a = b.data.toList then some a else none
  | _ => none

example : @encodeSpec = @encode := rfl
example : @decodeSpec = @decode := rfl

/-- `decFrom` at 0, taken as is. -/
def decodeLenient {α} [Codec α] (b : ByteArray) : Option α :=
  (decFrom b 0 : Option (α × Nat)).map (·.1)

/-- `decFrom` at 0, taken if it ends at the end, without re-encoding. -/
def decodeNoReencode {α} [Codec α] (b : ByteArray) : Option α :=
  match (decFrom b 0 : Option (α × Nat)) with
  | some (a, j) => if j = b.size then some a else none
  | none => none

/-! ## Random values -/

abbrev Gen := StateM Rng

def below (n : Nat) : Gen Nat := modifyGet fun g => g.below n
def word : Gen UInt64 := modifyGet fun g => g.next

def nat : Gen Nat := do
  match ← below 8 with
  | 0 => pure #[0, 1, 127, 128, 255, 16383, 16384, 2 ^ 21 - 1, 2 ^ 21, 2 ^ 63, 2 ^ 64 - 1, 2 ^ 64][← below 12]!
  | 1 => below 128
  | 2 => below 16384
  | 3 => return (← word).toNat
  | 4 => return (← word).toNat * 2 ^ 64 + (← word).toNat
  | 5 => return 2 ^ (← below 300) + (← word).toNat
  | _ => below 2000000

def bytesOf (n : Nat) : Gen ByteArray := do
  let mut b := ByteArray.emptyWithCapacity n
  while b.size < n do
    let w ← word
    for k in [0:8] do
      if b.size < n then b := b.push (w >>> (8 * k).toUInt64).toUInt8
  return b

/-- A field's bytes: mostly short, now and then a chunk's size, rarely
up to 200 KiB. -/
def bytes : Gen ByteArray := do
  match ← below 200 with
  | 0 => bytesOf (← below 204801)
  | 1 | 2 | 3 | 4 => bytesOf (← below 70000)
  | k => if k < 40 then bytesOf #[0, 1, 32, 64, 127, 128, 129][k % 7]! else bytesOf (← below 300)

/-- A byte string for the byte-string codec itself: the LEB128 length
boundaries, then sizes up to 200 KiB. -/
def byteString (i : Nat) : Gen ByteArray := do
  let edges := #[0, 1, 2, 127, 128, 129, 255, 256, 16383, 16384, 16385, 65535, 65536, 65537, 204800]
  if h : i < edges.size then bytesOf edges[i] else bytesOf (← below 204801)

/-- The number bytes b[i, i + L) spell, little-endian, built by halves
(independently of the codec). -/
def ofBytes (b : ByteArray) (i L : Nat) : Nat :=
  if L ≤ 8 then (List.range L).foldr (fun k acc => acc * 256 + (b.get! (i + k)).toNat) 0
  else ofBytes b i (L / 2) + (ofBytes b (i + L / 2) (L - L / 2) <<< (8 * (L / 2)))
termination_by L
decreasing_by all_goals omega

/-- A number whose encoding is exactly L bytes long (L ≥ 1). -/
def longNat (L : Nat) : Gen Nat := do
  let r ← bytesOf L
  let top := 7 * L - 1
  return 2 ^ top + (ofBytes r 0 L &&& (2 ^ top - 1))

def coin : Gen Bool := return (← below 2) == 1
def byte : Gen UInt8 := return (← word).toUInt8
def id32 : Gen ByteArray := bytesOf 32

def list {α} (g : Gen α) : Gen (List α) := do
  let n ← if (← below 10) == 0 then below 40 else below 5
  let mut l := []
  for _ in [0:n] do l := (← g) :: l
  return l

def op : Gen Op := return Op.make (← byte) (← list id32) (← bytes)

def cBody : Gen Community.Body := do
  match ← below 20 with
  | 0 => return .root (← bytes) (← bytes) (← bytes)
  | 1 => return .invite (← bytes) (← coin) (← nat) (← bytes)
  | 2 => return .request (← bytes) (← bytes) (← bytes) (← bytes)
  | 3 => return .grant (← bytes)
  | 4 => return .remove (← bytes)
  | 5 => return .post (← bytes) (← bytes) (← nat) (← bytes)
  | 6 => return .wrap (← bytes) (← bytes) (← bytes)
  | 7 => return .profile (← bytes) (← nat) (← bytes)
  | 8 => return .attach (← bytes) (← nat) (← bytes) (← bytes) (← bytes)
  | 9 => return .react (← bytes) (← nat) (← bytes)
  | 10 => return .approve (← bytes)
  | 11 => return .admit
  | 12 => return .accept (← id32) (← bytes)
  | 13 => return .joining (← id32) (← bytes) (← list bytes) (← id32) (← bytes) (← bytes) (← nat)
  | 14 => return .secret (← bytes) (← bytes)
  | 15 => return .name (← nat) (← bytes) (← bytes)
  | 16 => return .abandon
  | 17 => return .key (← bytes) (← bytes)
  | 18 => return .endpoint (← bytes)
  | _ => return .chunk (← bytes) (← nat) (← nat) (← bytes) (← list id32)

def cFact : Gen Community.Fact := do
  match ← below 19 with
  | 0 => return .admission (← id32) (← id32) (← bytes) (← bytes)
  | 1 => return .invitation (← id32) (← id32) (← bytes) (← coin) (← nat)
  | 2 => return .admin (← id32) (← id32)
  | 3 => return .removal (← id32) (← id32) (← id32)
  | 4 => return .message (← id32) (← id32) (← bytes) (← bytes) (← bytes) (← nat)
  | 5 => return .wrap (← id32) (← bytes) (← bytes) (← bytes)
  | 6 => return .profile (← id32) (← id32) (← bytes) (← nat)
  | 7 => return .attachment (← id32) (← id32) (← id32) (← id32) (← nat) (← bytes) (← bytes)
  | 8 => return .react (← id32) (← id32) (← id32) (← bytes) (← nat)
  | 9 => return .request (← id32) (← id32) (← bytes) (← bytes) (← coin) (← nat)
  | 10 => return .approval (← id32) (← id32) (← id32)
  | 11 => return .secret (← bytes) (← bytes)
  | 12 => return .accepted (← id32) (← bytes)
  | 13 => return .joining (← id32) (← bytes) (← list bytes) (← id32) (← bytes) (← bytes) (← nat)
  | 14 => return .named (← id32) (← id32) (← bytes) (← nat)
  | 15 => return .abandoned (← id32) (← id32) (← id32)
  | 16 => return .key (← bytes) (← bytes) (← bytes)
  | 17 => return .endpoint (← bytes) (← bytes)
  | _ => return .chunk (← id32) (← id32) (← id32) (← nat) (← nat)

def kBody : Gen Connection.Body := do
  match ← below 8 with
  | 0 => return .eph (← bytes)
  | 1 => return .request (← bytes) (← bytes) (← bytes)
  | 2 => return .opened
  | 3 => return .connection (← bytes)
  | 4 => return .established
  | 5 => return .send (← bytes)
  | 6 => return .given (← bytes)
  | _ => return .recv (← coin) (← bytes) (← bytes) (← nat)

def kFact : Gen Connection.Fact := do
  match ← below 8 with
  | 0 => return .eph (← bytes) (← bytes) (← bytes)
  | 1 => return .request (← bytes) (← bytes) (← bytes)
  | 2 => return .opened (← id32) (← id32) (← bytes) (← bytes) (← list id32)
  | 3 => return .connection (← id32) (← bytes)
  | 4 => return .established (← id32) (← id32) (← bytes) (← bytes) (← bytes) (← bytes) (← coin)
  | 5 => return .send (← id32) (← bytes)
  | 6 => return .given (← id32) (← bytes)
  | _ => return .recv (← id32) (← coin) (← bytes) (← bytes) (← nat)

def option {α} (g : Gen α) : Gen (Option α) := do
  if (← below 3) == 0 then return none else return some (← g)

def sum {α β} (a : Gen α) (b : Gen β) : Gen (α ⊕ β) := do
  if (← below 2) == 0 then return .inl (← a) else return .inr (← b)

def verdict {α} (g : Gen α) : Gen (Verdict α) := do
  if (← below 4) == 0 then return .invalid else return .valid (← g)

def key : Gen Key := return ⟨← nat, ← nat⟩
def range : Gen Range := return ⟨← key, ← option key⟩
def claim : Gen Claim := do
  if (← below 2) == 0 then return .fp (← range) (← nat) (← bytes)
  else return .ids (← range) (← list id32)

/-! ## Mutants -/

def setAt (b : ByteArray) (i : Nat) (x : UInt8) : ByteArray := if i < b.size then b.set! i x else b
def insertAt (b : ByteArray) (i : Nat) (x : UInt8) : ByteArray :=
  (b.extract 0 i).push x ++ b.extract i b.size
def deleteAt (b : ByteArray) (i : Nat) : ByteArray := b.extract 0 i ++ b.extract (i + 1) b.size

/-- A position: half the time in the first 16 bytes, where tags and
lengths are. -/
def pos (n : Nat) : Gen Nat := do
  if n == 0 then return 0
  if (← below 2) == 0 then below (min n 16) else below n

def mutants (e : ByteArray) : Gen (List ByteArray) := do
  let n := e.size
  let mut ms : List ByteArray := [.empty, e.extract 0 1, e.extract 0 (n - 1), e.extract 0 (← below (n + 1)),
    e.push (← byte), e ++ (← bytesOf (← below 40))]
  for _ in [0:3] do
    let i ← pos n
    ms := setAt e i (e.get! i ^^^ ((← below 255) + 1).toUInt8) :: ms
  ms := setAt e (← pos n) 0x80 :: setAt e (← pos n) 0xFF :: ms
  ms := insertAt e (← pos (n + 1)) (← byte) :: deleteAt e (← pos n) :: ms
  -- A number's first or last byte as a longer LEB128 form: x becomes
  -- 0x80 | x, 0.
  for i in List.range (min n 4) ++ (if n > 0 then [n - 1] else []) do
    let x := e.get! i
    if x < 128 then ms := insertAt (setAt e i (x ||| 0x80)) (i + 1) 0 :: ms
  ms := (ByteArray.empty.push (e.get! 0) ++ (← bytesOf (← below 64))) :: (← bytesOf (← below 300)) :: ms
  return ms

/-! ## The comparison -/

structure Tally where
  values : Nat := 0
  mutants : Nat := 0
  lenient : Nat := 0
  noReencode : Nat := 0

def same {α} [Codec α] (x y : Option α) : Bool := x.map encodeSpec == y.map encodeSpec

/-- Every check on one value. -/
def one {α} [Codec α] (t : Checks) (tally : IO.Ref Tally) (name : String) (v : α) (g : Rng) : IO Rng := do
  let e := encodeSpec v
  t.ok s!"{name}: encode is the specification's bytes ({e.size} bytes)" (encode v == e)
  let buf := Id.run ((bytesOf 5).run' g)
  t.ok s!"{name}: encInto after a buffer appends exactly them" (encInto buf v == buf ++ e)
  t.ok s!"{name}: decode of them is the value" (same (decode e) (some v))
  t.ok s!"{name}: decodeSpec agrees" (same (decodeSpec e) (some v))
  let pre := ByteArray.empty.push 1 |>.push 2 |>.push 3
  let mid := pre ++ e ++ (ByteArray.empty.push 9)
  t.ok s!"{name}: decFrom reads it between other bytes"
    (match (decFrom mid pre.size : Option (α × Nat)) with
      | some (a, j) => encodeSpec a == e && j == pre.size + e.size
      | none => false)
  let (ms, g) := Id.run ((mutants e).run g)
  let mut lenient := 0
  let mut noRe := 0
  for m in ms do
    let s := (decodeSpec m : Option α)
    t.ok s!"{name}: decode = decodeSpec on a mutant of {m.size} bytes" (same (decode m) s)
    if !same (decodeLenient m) s then lenient := lenient + 1
    if !same (decodeNoReencode m) s then noRe := noRe + 1
  tally.modify fun x =>
    ⟨x.values + 1, x.mutants + ms.length, x.lenient + lenient, x.noReencode + noRe⟩
  return g

/-- n random values of one codec, with their mutants. A codec with a
number or a length in it (`numbers`) has mutants that only re-encoding
refuses. -/
def suite {α} [Codec α] (t : Checks) (name : String) (n : Nat) (gen : Nat → Gen α) (seed : Nat)
    (numbers := true) : IO Unit := do
  let tally ← IO.mkRef ({} : Tally)
  let mut g : Rng := ⟨seed.toUInt64 * 0x9E3779B97F4A7C15 + 1⟩
  for i in [0:n] do
    let (v, g') := Id.run ((gen i).run g)
    g ← one t tally name v g'
  let x ← tally.get
  IO.println s!"{name}: {x.values} values, {x.mutants} mutants; decFrom alone takes {x.lenient} the spec refuses, without re-encoding {x.noReencode}"
  t.ok s!"{name}: some mutant is taken by decFrom alone (negative control)" (x.lenient > 0)
  if numbers then
    t.ok s!"{name}: some mutant is taken without re-encoding (negative control)" (x.noReencode > 0)

def main (args : List String) : IO UInt32 := do
  let n := (args.headD "200").toNat!
  let t ← Checks.new
  suite t "Nat" n (fun _ => nat) 1
  suite t "long Nat (up to 4 KiB)" (n / 5) (fun _ => do longNat ((← below 4096) + 1)) 21
  suite t "ByteArray" n byteString 2
  suite t "Bool" 4 (fun _ => coin) 3 (numbers := false)
  suite t "UInt8" n (fun _ => byte) 4 (numbers := false)
  suite t "List ByteArray" n (fun _ => list bytes) 5
  suite t "List Nat" n (fun _ => list nat) 6
  suite t "ByteArray × Nat × List ByteArray" n (fun _ => return (← bytes, ← nat, ← list bytes)) 7
  suite t "Option ByteArray" n (fun _ => option bytes) 8
  suite t "Op" n (fun _ => op) 9
  suite t "Community.Body" (3 * n) (fun _ => cBody) 10
  suite t "Community.Fact" (3 * n) (fun _ => cFact) 11
  suite t "Verdict Community.Fact" n (fun _ => verdict cFact) 12
  suite t "Connection.Body" n (fun _ => kBody) 13
  suite t "Connection.Fact" n (fun _ => kFact) 14
  suite t "Community.Fact ⊕ Connection.Fact" n (fun _ => sum cFact kFact) 15
  suite t "Verdict (Community.Fact ⊕ Connection.Fact)" n (fun _ => verdict (sum cFact kFact)) 16
  suite t "Key" n (fun _ => key) 17
  suite t "Range" n (fun _ => range) 18
  suite t "Claim" n (fun _ => claim) 19
  suite t "List Claim" n (fun _ => list claim) 20
  -- A number 64 KiB long, against the specification (no mutants: the
  -- specification takes a second on each).
  let big := Id.run ((longNat 65536).run' ⟨22⟩)
  let e := encodeSpec big
  t.ok s!"a 64 KiB number: encode is the specification's bytes ({e.size} bytes)" (encode big == e)
  t.ok "a 64 KiB number: decode gives it back, and so does decodeSpec"
    ((decode e : Option Nat) == some big && (decodeSpec e : Option Nat) == some big)
  t.ok "a 64 KiB number without its last byte decodes to nothing"
    ((decode (e.extract 0 (e.size - 1)) : Option Nat) == none)
  -- Without the re-encoding, a longer LEB128 form of a number is taken.
  let tally ← IO.mkRef ({} : Tally)
  let _ ← one t tally "Nat 5 padded" (5 : Nat) ⟨7⟩
  t.ok "without re-encoding, a padded number is taken (negative control)"
    ((decodeNoReencode (ByteArray.mk #[0x85, 0]) : Option Nat) == some 5 &&
      (decode (ByteArray.mk #[0x85, 0]) : Option Nat) == none &&
      (decodeSpec (ByteArray.mk #[0x85, 0]) : Option Nat) == none)
  t.finish "codecdiff"
