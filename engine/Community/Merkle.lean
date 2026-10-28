/-
An attachment's integrity: a Merkle tree over SHA-256, written here so
the verifier that runs is the one the laws are about.

A file is sealed once under its own key. Its CIPHERTEXT is cut into
64 KiB slices, and the tree is over the ciphertext, so a relay verifies
a chunk without any key, and nothing confirms a guessed plaintext.
- leaf i = H(tagLeaf ‖ be64 i ‖ slice);
- node = H(tagNode ‖ left ‖ right);
- the tree has 2^d leaves (d the least depth that holds them all); the
  missing ones are the empty leaf H(tagEmpty);
- the root is H(tagRoot ‖ be64 len ‖ tree root), so it commits the
  length too, and so the number of chunks and the last one's size.

A chunk carries its slice and its siblings, top down. It verifies iff
its index is below the chunk count, its slice has the size its index
calls for, every sibling is 32 bytes, and climbing from its leaf through
the siblings reaches the root.

Laws (`H` collision-resistant as a hypothesis, as unforgeability is for
signatures):
- `encode_verify`: every chunk of a file verifies against its root;
- `verify_sound`: a chunk that verifies against a file's root is that
  file's chunk;
- `index_bound`: a verifying chunk's index is below the chunk count;
- `complete_assembles`: verifying chunks for every index put together
  are the file.
-/
import Engine.Core

namespace Community.Merkle
open Engine

abbrev B := ByteArray

/-- A slice's size: 64 KiB, as poc-17 chose it (past a frame bundle's
48 KiB, so one chunk to a frame). -/
def sliceSize : Nat := 65536

def be64 (n : Nat) : B := ByteArray.mk ((List.range 8).reverse.map fun i => (n >>> (8 * i)).toUInt8).toArray

def tagLeaf : B := "quiet/merkle/leaf/v1".toUTF8
def tagNode : B := "quiet/merkle/node/v1".toUTF8
def tagEmpty : B := "quiet/merkle/empty/v1".toUTF8
def tagRoot : B := "quiet/merkle/root/v1".toUTF8

section
variable (H : B → B)

def leaf (i : Nat) (s : B) : B := H (tagLeaf ++ be64 i ++ s)
def node (l r : B) : B := H (tagNode ++ l ++ r)
def empty : B := H tagEmpty

/-- How many chunks a file of `len` bytes has. -/
def nChunks (len : Nat) : Nat := (len + sliceSize - 1) / sliceSize

/-- The least depth whose tree holds n leaves. -/
def depthOf (n : Nat) : Nat := Id.run do
  let mut d := 0
  for _ in [0:64] do
    if 2 ^ d ≥ n then break
    d := d + 1
  return d

/-- The size chunk i of a `len`-byte file has. -/
def sliceLen (len i : Nat) : Nat := min sliceSize (len - i * sliceSize)

/-- A file's ciphertext cut into its slices. -/
def slices (ct : B) : List B :=
  (List.range (nChunks ct.size)).map fun i => ct.extract (i * sliceSize) ((i + 1) * sliceSize)

/-- The subtree of depth d over leaves f s … f (s + 2^d - 1). -/
def sub (f : Nat → B) : Nat → Nat → B
  | 0, s => f s
  | d + 1, s => node H (sub f d s) (sub f d (s + 2 ^ d))

/-- The siblings of leaf s + i in that subtree, top down. -/
def path (f : Nat → B) : Nat → Nat → Nat → List B
  | 0, _, _ => []
  | d + 1, s, i =>
    if i < 2 ^ d then sub H f d (s + 2 ^ d) :: path f d s i
    else sub H f d s :: path f d (s + 2 ^ d) (i - 2 ^ d)

/-- From leaf hash x at index i of a depth-d subtree, through its
siblings (top down), to the subtree's root. -/
def climb : Nat → Nat → B → List B → B
  | 0, _, x, _ => x
  | d + 1, i, x, sib :: rest =>
    if i < 2 ^ d then node H (climb d i x rest) sib else node H sib (climb d (i - 2 ^ d) x rest)
  | _ + 1, _, x, [] => x

/-- The leaves of a file: its chunks' leaves, then empty ones. -/
def leaves (ct : B) (j : Nat) : B :=
  match (slices ct)[j]? with
  | some s => leaf H j s
  | none => empty H

def rootOf (len : Nat) (tree : B) : B := H (tagRoot ++ be64 len ++ tree)

/-- A file's root: what an attachment commits. -/
def fileRoot (ct : B) : B := rootOf H ct.size (sub H (leaves H ct) (depthOf (nChunks ct.size)) 0)

/-- Chunk i's siblings, for the file's ciphertext. -/
def proof (ct : B) (i : Nat) : List B := path H (leaves H ct) (depthOf (nChunks ct.size)) 0 i

/-- Whether chunk i of a `len`-byte file, with these siblings, belongs
under `root`. -/
def verify (root : B) (len i : Nat) (s : B) (sibs : List B) : Bool :=
  let n := nChunks len
  let d := depthOf n
  decide (i < n) && decide (sibs.length = d) && sibs.all (·.size == 32) &&
    decide (s.size = sliceLen len i) && rootOf H len (climb H d i (leaf H i s) sibs) == root

end

/-- Slices put together, in order. -/
def assemble (ss : List B) : B := ss.foldl (· ++ ·) .empty

end Community.Merkle
