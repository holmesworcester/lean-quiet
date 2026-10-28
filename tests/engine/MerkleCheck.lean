/-
Community.Merkle with the hash that runs (SHA-256), on files of 0, 1,
65535, 65536, 65537, 3×65536+5 and 1 MiB + 1000 bytes: the slices put
together are the file, every chunk verifies against the file's root with
its proof, and the chunks that verify put together are the file again.
Known roots, and one proof, from an independent rendering of the
module's docstring pin the bytes (the tags, be64 big-endian, the tree's
shape, the empty file's one empty slice); it builds the tree bottom up
by pairing, where the module builds it top down:

  S = 65536; H = sha256; n = max(1, ceil(len/S)); d = least, 2^d >= n
  level = [H(b"quiet/merkle/leaf/v1" + be64(i) + ct[i*S:(i+1)*S]) for i < n]
          + [H(b"quiet/merkle/empty/v1")] * (2^d - n)
  while len(level) > 1: level = [H(b"quiet/merkle/node/v1" + l + r) for pairs]
  root = H(b"quiet/merkle/root/v1" + be64(len) + level[0])

Then forgeries against each file's root, which must all be refused:
every slice with a byte flipped (sampled), cut or grown by a byte; the
wrong index (a neighbour, the chunk count, 2^d, i + 2^d, i + 2^64);
siblings too few, too many, flipped, or not 32 bytes; the wrong length
(±1, +64 KiB, +2^64, 0); a neighbour's slice under this proof; and
chunks of another file, of the same size and of other sizes.

Negative controls: `verify` with one check dropped at a time
(`verifyWithout`, which drops nothing for k = 99 and is then `verify`,
by rfl), on the same forgeries; the run prints what each lets through.
- The index check: the empty file's chunk at index 2^64 (its be64 is
  0's) passes, and the examples below show `verify_sound` and
  `index_bound` false without it, under `witness`, a hash that meets
  their assumptions.
- The sibling count: a sibling past the depth is never climbed, so an
  extra one passes; `verify_sound` (the siblings are the proof) is false
  without it.
- The slice size: nothing passes here (the leaf binds the slice), but
  `index_bound`, which assumes nothing of the hash, is false without it.
- The length guard: matters only for files of 2^64 bytes or more, where
  be64 gives two lengths one root; `verify_sound` needs it there.
- The sibling sizes: nothing passes, and no law needs it (a sibling of
  another size changes the node's input); an early refusal.
-/
import Tests.Lib
import Community.Merkle

open Engine Tests Community.Merkle

def H : B → B := sha256

def unhex (s : String) : B :=
  let d (c : Char) : UInt8 := (if c.isDigit then c.toNat - 48 else c.toNat - 87).toUInt8
  let cs := s.toList
  ⟨((List.range (cs.length / 2)).map fun i => d cs[2*i]! * 16 + d cs[2*i+1]!).toArray⟩

/-- Flip the bits m of byte i. -/
def flipAt (b : B) (i : Nat) (m : UInt8 := 1) : B := b.set! i (b.get! i ^^^ m)

/-- n bytes from a seeded generator. -/
def randomFile (seed n : Nat) : B := Id.run do
  let mut b := ByteArray.emptyWithCapacity n
  let mut g : Rng := ⟨seed.toUInt64⟩
  for _ in [0:n] do
    let (x, g') := g.next
    g := g'
    b := b.push x.toUInt8
  return b

/-- The known-answer files: byte k is (31k + 7) mod 251. -/
def pattern (n : Nat) : B := ⟨(Array.range n).map fun k => ((k * 31 + 7) % 251).toUInt8⟩

abbrev Verifier := B → Nat → Nat → B → List B → Bool

/-- `verify` with check k dropped: 0 the length guard, 1 the index, 2 the
sibling count, 3 the sibling sizes, 4 the slice size. Any other k drops
nothing, and is `verify`. -/
def verifyWithout (H : B → B) (k : Nat) : Verifier := fun root len i s sibs =>
  let n := nChunks len
  let d := depthOf n
  (k == 0 || decide (len < 2 ^ 64)) && (k == 1 || decide (i < n)) && (k == 2 || decide (sibs.length = d)) &&
    (k == 3 || sibs.all (·.size == 32)) && (k == 4 || decide (s.size = sliceLen len i)) &&
    rootOf H len (climb H d i (leaf H i s) sibs) == root

theorem verifyWithout_none (H : B → B) : verifyWithout H 99 = verify H := rfl

/-! The laws catch the mutants: each example is a chunk `verify` refuses
and a mutant passes, against which a law is false. -/

/-- Without the index check, the empty file's chunk passes at index 2^64
(its be64 is 0's), and it is no chunk of the file: `verify_sound` and
`index_bound` are false. -/
example : verify witness (fileRoot witness .empty) 0 (2 ^ 64) .empty [] = false ∧
    verifyWithout witness 1 (fileRoot witness .empty) 0 (2 ^ 64) .empty [] = true ∧
    (slices .empty)[2 ^ 64]? = none ∧ ¬ 2 ^ 64 < nChunks 0 := by decide

/-- Without the sibling count, the empty file's chunk passes with a
sibling it does not have: `verify_sound` is false. -/
example : verify witness (fileRoot witness .empty) 0 0 .empty [bytes32 0] = false ∧
    verifyWithout witness 2 (fileRoot witness .empty) 0 0 .empty [bytes32 0] = true ∧
    proof witness .empty 0 = [] := by decide

/-- Without the slice size check, under a hash that is constant, a 2-byte
slice passes as a 1-byte file's chunk: `index_bound` (which assumes
nothing of the hash) is false. -/
example : verify (fun _ => bytes32 0) (bytes32 0) 1 0 (bytes32 0 |>.extract 0 2) [] = false ∧
    verifyWithout (fun _ => bytes32 0) 4 (bytes32 0) 1 0 (bytes32 0 |>.extract 0 2) [] = true ∧
    (bytes32 0 |>.extract 0 2).size ≠ sliceLen 1 0 := by decide

def dropped : List (Nat × String) :=
  [(0, "the length guard"), (1, "the index check"), (2, "the sibling count"), (3, "the sibling sizes"),
    (4, "the slice size")]

structure Forgery where
  name : String
  root : B
  len : Nat
  i : Nat
  s : B
  sibs : List B

def z32 : B := ⟨Array.replicate 32 0⟩

/-- Forged chunks against ct's root; `others` are other files. -/
def forgeries (ct : B) (others : List B) (seed : Nat) : Array Forgery := Id.run do
  let r := fileRoot H ct
  let len := ct.size
  let n := nChunks len
  let d := depthOf n
  let mut out := #[]
  let mut g : Rng := ⟨seed.toUInt64⟩
  for i in [0:n] do
    let s := slice ct i
    let p := proof H ct i
    let mk (what : String) (len' i' : Nat) (s' : B) (p' : List B) : Forgery :=
      ⟨s!"{len}-byte file, chunk {i}: {what}", r, len', i', s', p'⟩
    -- The slice tampered.
    if s.size > 0 then
      let mut at' := [0, s.size / 2, s.size - 1]
      for _ in [0:13] do
        let (k, g') := g.below s.size
        g := g'
        at' := k :: at'
      for k in at' do
        out := out.push (mk s!"byte {k} flipped" len i (flipAt s k) p)
        out := out.push (mk s!"byte {k}'s high bit flipped" len i (flipAt s k 0x80) p)
      out := out.push (mk "the slice cut by a byte" len i (s.extract 0 (s.size - 1)) p)
    out := out.push (mk "the slice grown by a byte" len i (s.push 0) p)
    -- The wrong index.
    for i' in [i + 1, i - 1, n, 2 ^ d, i + 2 ^ d, i + 2 ^ 64] do
      if i' != i then out := out.push (mk s!"index {i'}" len i' s p)
    -- The siblings.
    out := out.push (mk "an extra sibling last" len i s (p ++ [z32]))
    out := out.push (mk "an extra sibling first" len i s (z32 :: p))
    if !p.isEmpty then
      out := out.push (mk "the last sibling dropped" len i s p.dropLast)
      out := out.push (mk "the first sibling dropped" len i s p.tail)
    for k in [0:p.length] do
      let q := p[k]!
      out := out.push (mk s!"sibling {k} flipped" len i s (p.set k (flipAt q 0)))
      out := out.push (mk s!"sibling {k} cut to 31 bytes" len i s (p.set k (q.extract 0 31)))
      out := out.push (mk s!"sibling {k} grown to 33 bytes" len i s (p.set k (q.push 0)))
    -- The wrong length.
    for len' in [len + 1, len - 1, len + sliceSize, len + 2 ^ 64, 0] do
      if len' != len then out := out.push (mk s!"length {len'}" len' i s p)
    -- A neighbour's slice under this proof.
    if n > 1 then
      let j := (i + 1) % n
      out := out.push (mk s!"slice {j} at index {i}" len i (slice ct j) p)
    -- Another file's chunk, and this chunk against another file's root.
    for o in others do
      if i < nChunks o.size then
        let so := slice o i
        let po := proof H o i
        out := out.push (mk s!"a {o.size}-byte file's chunk and proof" o.size i so po)
        out := out.push (mk s!"a {o.size}-byte file's chunk and proof, at this length" len i so po)
        out := out.push (mk s!"a {o.size}-byte file's slice under this proof" len i so p)
      out := out.push { mk s!"this chunk against a {o.size}-byte file's root" len i s p with root := fileRoot H o }
  return out

def sizes : List Nat := [0, 1, 65535, 65536, 65537, 3 * 65536 + 5, 1048576 + 1000]

def kats : List (Nat × String) :=
  [(0, "97742eced29ec984ad0bffa9e324b6e71733fa1f553af70b2d0bf2644e5691ad"),
   (3, "0d67c88d26df6e977c311d277a93036a9d1ba46ba0b9fb18f66a62274a6d59de"),
   (65536, "be42095cb9cb669b44b65ab99bada7fc14e03541122f177a69bddd93d87ac9fe"),
   (65537, "71860dfe2ac05419097c2c988199c0f2c1bd0484d8f2e9766b866e0ba82b343b"),
   (200000, "0e750194070109067caf22238cb3a4d16f5282ba46eafc3cfd14bf0cc48d2ce7")]

/-- Chunk 2's proof for the 200000-byte known-answer file, siblings top down. -/
def katProof : String :=
  "991675c3aef742f50dc2c583de0c3ed52412553df02d17c7995ccbd07e73e5fe" ++
  "2c38a7d578e68a939154c2934aae371c6dff0844b7d0f62572f98967e48bd295"

/-- The least d with 2^d ≥ n, by counting. -/
def depthByCount (n : Nat) : Nat := Id.run do
  let mut d := 0
  while 2 ^ d < n do d := d + 1
  return d

def main : IO UInt32 := do
  let t ← Checks.new
  -- Known answers.
  for (n, root) in kats do
    t.ok s!"the {n}-byte known-answer file's root" (fileRoot H (pattern n) == unhex root)
  t.ok "the 200000-byte known-answer file's chunk 2 proof"
    ((proof H (pattern 200000) 2).foldl (· ++ ·) .empty == unhex katProof)
  let depths := (List.range 5000) ++ ((List.range 71).flatMap fun k => [2 ^ k - 1, 2 ^ k, 2 ^ k + 1])
  t.ok "depthOf is the least depth that holds n leaves" (depths.all fun n => depthOf n == depthByCount n)
  -- Every file: its chunks verify and put together are it; forgeries are refused.
  let files := sizes.zipIdx.map fun (n, k) => randomFile (k + 1) n
  let mut chunks := 0
  let mut forged := 0
  let mut accepted : Array (Array String) := #[#[], #[], #[], #[], #[]]
  for ct in files do
    let len := ct.size
    let n := nChunks len
    let r := fileRoot H ct
    let ss := slices ct
    t.ok s!"the {len}-byte file has {n} slices" (ss.length == n)
    t.ok s!"the {len}-byte file's slices have their sizes"
      ((List.range n).all fun i => (ss[i]!).size == sliceLen len i)
    t.ok s!"the {len}-byte file's slices put together are it" (assemble ss == ct)
    let mut got : Array B := #[]
    for i in [0:n] do
      let p := proof H ct i
      t.ok s!"the {len}-byte file's chunk {i} has {depthOf n} siblings" (p.length == depthOf n)
      if verify H r len i ss[i]! p then got := got.push ss[i]!
      t.ok s!"the {len}-byte file's chunk {i} verifies" (verify H r len i ss[i]! p)
      t.ok s!"the {len}-byte file's chunk {i} verifies under every mutant"
        ((List.range 5).all fun k => verifyWithout H k r len i ss[i]! p)
      chunks := chunks + 1
    t.ok s!"the {len}-byte file's verified chunks put together are it"
      (got.size == n && assemble got.toList == ct)
    let others := [randomFile (len + 1000) (max len 1)] ++ (files.filter (·.size != len)).take 2
    for f in forgeries ct others len do
      let refused := !verify H f.root f.len f.i f.s f.sibs
      t.ok s!"{f.name} is refused" refused
      t.ok s!"{f.name}: the copy with nothing dropped agrees"
        (verifyWithout H 99 f.root f.len f.i f.s f.sibs == !refused)
      for k in [0:5] do
        if verifyWithout H k f.root f.len f.i f.s f.sibs then accepted := accepted.modify k (·.push f.name)
      forged := forged + 1
  IO.println s!"merkle_check: {files.length} files, {chunks} chunks verified, {forged} forgeries refused"
  for (k, what) in dropped do
    let a := accepted[k]!
    IO.println s!"merkle_check: without {what}, {a.size} forgeries pass"
    for name in a.toList.take 3 do IO.println s!"  e.g. {name}"
  t.ok "a verifier without the index check is caught" (accepted[1]!.size > 0)
  t.ok "a verifier without the sibling count is caught" (accepted[2]!.size > 0)
  t.finish "merkle_check"
