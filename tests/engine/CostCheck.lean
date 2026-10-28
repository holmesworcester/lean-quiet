/-
The cost laws, on the code that runs (docs/PERF.md). Each pilot's code
is run `Counted` on real inputs, with the real hash: what it computes is
what the compiled code computes, and what it charges is within the
budget its law states. Each negative control, run the same way,
computes the same thing and is over the budget: that is the law's
teeth.

- Merkle (ops/community/MerkleCost.lean): files of 0 to 33 chunks under
  SHA-256. `rootAndProofsM` hashes 2·2^d times and its bytes are within
  the file's size + 112·2^d; `rootAndProofsSlowM`, the way before the
  levels, hashes 2^(d+1) + n·(2^(d+1) − 2 − d) times.
- The codec (engine/core/CodecCost.lean): numbers of 1 to 65536 bytes,
  at offsets in random bytes too, within N·(log₂ N + 3); the digits a
  byte at a time, over L·(log₂ L + 2) from 16 bytes on. Byte strings of
  0 to 64 KiB: their length's bytes read, their bytes copied once; the
  list codec's way reads every byte.
- A frame's pictures (ops/app/Pics.lean), over 240 frames of a world as
  data with real tasks: a picture costs its spawns and reads in its
  first frame, then nothing; a file whose chunk ops are missing reads
  them again every 120 frames and at no other frame. The old `decoded`
  (`imageV`) spawns a preview decode every frame.
-/
import tests.engine.Lib
import ops.community.MerkleCost
import engine.core.CodecCost
import ops.app.Pics

open Engine Engine.Counted Tests

/-- n bytes from a seeded generator. -/
def randomBytes (seed n : Nat) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity n
  let mut g : Rng := ⟨seed.toUInt64⟩
  for _ in [0:n] do
    let (x, g') := g.next
    g := g'
    b := b.push x.toUInt8
  return b

section Merkle
open Community.Merkle

def merkle (t : Checks) : IO Unit := do
  for len in [0, 1, 65535, 65536, 65537, 3 * 65536 + 5, 1048576 + 1000, 33 * 65536] do
    let ct := randomBytes len len
    let n := nChunks len
    let d := depthOf n
    let fast := rootAndProofsM (m := Counted) sha256 ct
    let slow := rootAndProofsSlowM (m := Counted) sha256 ct
    let runs := rootAndProofs sha256 ct
    t.ok s!"merkle {len}: counted, what runs computes the same root and proofs" (val fast == runs)
    t.ok s!"merkle {len}: 2·2^d hashes" ((cost fast).hashes == 2 * 2 ^ d)
    t.ok s!"merkle {len}: under 4n hashes" ((cost fast).hashes < 4 * n)
    t.ok s!"merkle {len}: bytes hashed within the file + 112·2^d"
      ((cost fast).hashed ≤ len + 112 * 2 ^ d)
    t.ok s!"merkle {len}: every byte of the file hashed" (len ≤ (cost fast).hashed)
    t.ok s!"merkle {len}: the negative control computes the same" (val slow == runs)
    t.ok s!"merkle {len}: the negative control's hashes as counted"
      ((cost slow).hashes == 2 ^ (d + 1) + n * (2 ^ (d + 1) - 2 - d))
    if 2 ≤ n then
      t.ok s!"merkle {len}: the negative control is over the budget" (2 * 2 ^ d < (cost slow).hashes)
    IO.println s!"merkle {len} B, {n} chunks: levels {(cost fast).hashes} hashes of {(cost fast).hashed} B; rebuilt siblings {(cost slow).hashes} hashes of {(cost slow).hashed} B"

end Merkle

section Codec
open Codec

/-- A number L bytes long: L - 1 continuation bytes, then one under 128. -/
def longNumber (seed L : Nat) : ByteArray := Id.run do
  let r := randomBytes seed L
  let mut b := ByteArray.emptyWithCapacity L
  for i in [0:L] do
    let x := r.get! i
    b := b.push (if i + 1 < L then x ||| 0x80 else x &&& 0x7F)
  return b

def codec (t : Checks) : IO Unit := do
  for L in [1, 8, 9, 16, 17, 64, 1000, 4096, 65536] do
    let b := longNumber L L
    let c := decNatFromM (m := Counted) b 0
    t.ok s!"number {L} B: counted, the reader computes what runs" (val c == decNatFrom b 0)
    t.ok s!"number {L} B: within N·(log₂ N + 3)" ((cost c).work ≤ L * (Nat.log2 L + 3))
    t.ok s!"number {L} B: the digits within L·(log₂ L + 2)"
      ((cost (digitsM (m := Counted) b 0 L)).work ≤ L * (Nat.log2 L + 2))
    let slow := digitsSlowM (m := Counted) b 0 L
    t.ok s!"number {L} B: the byte-at-a-time control computes the same"
      (val slow == digitsFast b 0 L)
    t.ok s!"number {L} B: the byte-at-a-time control costs L·(L+1)/2"
      (2 * (cost slow).work == L * (L + 1))
    if 16 ≤ L then
      t.ok s!"number {L} B: the byte-at-a-time control is over the budget"
        (L * (Nat.log2 L + 2) < (cost slow).work)
    IO.println s!"number {L} B: halves {(cost c).work} word ops; byte at a time {(cost slow).work}"
  -- any bytes, any offset: a number is within the budget whatever a peer sends
  for seed in [0:40] do
    let b := randomBytes (1000 + seed) (seed * 37 % 300)
    for i in [0:b.size + 1] do
      let c := decNatFromM (m := Counted) b i
      if !(val c == decNatFrom b i && (cost c).work ≤ (b.size - i) * (Nat.log2 (b.size - i) + 3)) then
        t.ok s!"number at {i} of random bytes {seed}: within the budget" false
      let s := decBytesFromM (m := Counted) b i
      if !(val s == decBytesFrom b i && (cost s).work ≤ Nat.log2 b.size / 7 + 1) then
        t.ok s!"byte string at {i} of random bytes {seed}: within the budget" false
  t.ok "random bytes: every number and byte string read within its budget" true
  for n in [0, 1, 127, 128, 16383, 16384, 65536] do
    let x := randomBytes n n
    let b := Codec.encode x
    let c := decBytesFromM (m := Counted) b 0
    t.ok s!"bytes {n}: counted, the reader computes what runs" (val c == decBytesFrom b 0)
    t.ok s!"bytes {n}: decoded" (val c == some (x, b.size))
    t.ok s!"bytes {n}: the length's bytes read, the bytes copied once"
      ((cost c).work == (encNat n).length && (cost c).copied == n)
    t.ok s!"bytes {n}: within log₂|b|/7 + 1 reads" ((cost c).work ≤ Nat.log2 b.size / 7 + 1)
    let slow := decBytesListM (m := Counted) b 0
    t.ok s!"bytes {n}: the list codec's way decodes the same" (val slow == val c)
    if 2 ≤ b.size then
      t.ok s!"bytes {n}: the list codec's way is over the budget"
        (Nat.log2 b.size / 7 + 1 < (cost slow).work)
    IO.println s!"bytes {n}: {(cost c).work} read, {(cost c).copied} copied; list codec {(cost slow).work} read"

end Codec

section Pics
open Pics

def pics (t : Checks) : IO Unit := do
  let pic (complete : Bool) (preview : Bool) : Row.Pic :=
    { hash := ⟨#[7, 7, 7]⟩, w := 96, h := 64, preview := if preview then randomBytes 1 40 else .empty,
      got := if complete then 3 else 1, total := 3, chunks := [⟨#[1]⟩, ⟨#[2]⟩, ⟨#[3]⟩] }
  let world (stored : Bool) : World :=
    { imgs := fun _ => none, retry := fun _ => none, frames := 0, done := fun _ => true,
      store := fun _ => if stored then some [randomBytes 2 10] else none }
  -- 240 frames of each picture: what each frame costs
  for (complete, preview, stored) in [(true, true, true), (true, true, false), (false, true, true),
      (true, false, true), (false, false, false)] do
    let p := pic complete preview
    let name := s!"pics (complete {complete}, preview {preview}, stored {stored})"
    let mut w := world stored
    let mut spawns : Array Nat := #[]
    let mut reads : Array Nat := #[]
    let mut spawnsV : Array Nat := #[]
    let mut wV := world stored
    for f in [0:240] do
      w := { w with frames := f }
      let c := costIn (image p 96 64) w
      spawns := spawns.push c.spawns
      reads := reads.push c.reads
      w := after (image p 96 64) w
      wV := { wV with frames := f }
      spawnsV := spawnsV.push (costIn (imageV p 96 64) wV).spawns
      wV := after (imageV p 96 64) wV
    let first := (if preview then 1 else 0) + (if complete && stored then 1 else 0)
    t.ok s!"{name}: the first frame spawns each decode once" (spawns[0]! == first)
    t.ok s!"{name}: no later frame spawns" (spawns.extract 1 240 |>.all (· == 0))
    let readAt := fun (f : Nat) => if complete && (f == 0 || (!stored && f % 120 == 0)) then 3 else 0
    t.ok s!"{name}: the store is read only in the first frame, and every 120 frames while chunks are missing"
      ((List.range 240).all fun f => reads[f]! == readAt f)
    t.ok s!"{name}: the second frame costs nothing (image_twice)"
      (costIn (image p 96 64) (after (image p 96 64) (world stored)) == 0)
    if preview then
      t.ok s!"{name}: the old decoded spawns a preview decode every frame"
        (spawnsV.extract 1 240 |>.all (· == 1))
    IO.println s!"{name}: spawns {spawns.foldl (· + ·) 0} in 240 frames, reads {reads.foldl (· + ·) 0}; old decoded spawns {spawnsV.foldl (· + ·) 0}"

end Pics

def main : IO UInt32 := do
  let t ← Checks.new
  merkle t
  codec t
  pics t
  t.finish "costcheck"
