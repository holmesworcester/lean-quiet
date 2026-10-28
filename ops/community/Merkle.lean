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
- the empty file is one empty slice, so every file has a chunk, and a
  receiver always checks one against the root (with no chunk, nothing
  would tie the root to the file).

A chunk carries its slice and its siblings, top down. It verifies iff
the length is below 2^64 (be64 names a length only below that: past it,
two lengths share a root), its index is below the chunk count, its slice
has the size its index calls for, every sibling is 32 bytes, and
climbing from its leaf through the siblings reaches the root.

Laws (`H` has 32-byte outputs and, where a law needs it, no second
preimage of anything the file's root hashes: collision resistance as a
hypothesis, as unforgeability is for signatures; injectivity cannot be
the hypothesis, see `no_injective_hash`):
- `encode_verify`: every chunk of a file (under 2^64 bytes) verifies
  against its root;
- `verify_sound`: a chunk that verifies against a file's root is that
  file's chunk: its length, its slice, and its siblings are the file's;
- `index_bound`: a verifying chunk's index is below the chunk count, and
  its slice has its index's size;
- `complete_assembles`: verifying chunks for every index put together
  are the file;
- `assumptions_hold`: for every file under 2^64 bytes, some hash with
  32-byte outputs meets the laws' assumption.

What runs builds the tree once, level by level, and reads the root and
every proof off the levels; `fileRoot_eq_fast`, `proof_eq_fast` and
`rootAndProofs_eq_fast` (`@[csimp]`) prove it equal to `fileRoot` and
`proof`, so the laws are about it.
-/
import engine.core.Core

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

/-- How many chunks a file of `len` bytes has: one per 64 KiB begun, and
one (empty) for the empty file. -/
def nChunks (len : Nat) : Nat := max 1 ((len + sliceSize - 1) / sliceSize)

/-- The least depth whose tree holds n leaves. -/
def depthOf (n : Nat) : Nat := if n ≤ 1 then 0 else (n - 1).log2 + 1

/-- The size chunk i of a `len`-byte file has. -/
def sliceLen (len i : Nat) : Nat := min sliceSize (len - i * sliceSize)

/-- Slice i of a file's ciphertext. -/
def slice (ct : B) (i : Nat) : B := ct.extract (i * sliceSize) ((i + 1) * sliceSize)

/-- A file's ciphertext cut into its slices. -/
def slices (ct : B) : List B := (List.range (nChunks ct.size)).map (slice ct)

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

/-- The leaves of a file: its chunks' leaves, then empty ones. (Slice j
alone, not `slices`, so a root costs one pass over the file.) -/
def leaves (ct : B) (j : Nat) : B :=
  if j < nChunks ct.size then leaf H j (slice ct j) else empty H

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
  decide (len < 2 ^ 64) && decide (i < n) && decide (sibs.length = d) && sibs.all (·.size == 32) &&
    decide (s.size = sliceLen len i) && rootOf H len (climb H d i (leaf H i s) sibs) == root

end

/-- Slices put together, in order. -/
def assemble (ss : List B) : B := ss.foldl (· ++ ·) .empty

/-! ## What the laws assume

Collision resistance cannot be stated as injectivity: no hash with
32-byte outputs is injective (`no_injective_hash`), so a law assuming
both would hold of any verifier. The laws assume instead that none of
the inputs a file's root hashes has a second preimage. Some 32-byte
hash meets that for every file under 2^64 bytes (`assumptions_hold`),
and a chunk that verifies but is not the file's yields a SHA-256 second
preimage. -/

section
variable (H : B → B)

/-- No second preimage, under H, of any of xs. -/
def NoSecondPreimage (xs : List B) : Prop := ∀ x ∈ xs, ∀ y, H y = H x → y = x

/-- What leaf j of a file hashes. -/
def leafIn (ct : B) (j : Nat) : B :=
  if j < nChunks ct.size then tagLeaf ++ be64 j ++ slice ct j else tagEmpty

/-- What `sub` hashes over the leaves H (g j): each node, then its
children. -/
def subInputs (g : Nat → B) : Nat → Nat → List B
  | 0, s => [g s]
  | d + 1, s => (tagNode ++ sub H (fun j => H (g j)) d s ++ sub H (fun j => H (g j)) d (s + 2 ^ d)) ::
      (subInputs g d s ++ subInputs g d (s + 2 ^ d))

/-- What a file's root hashes: the root, then the tree. -/
def treeInputs (ct : B) : List B :=
  (tagRoot ++ be64 ct.size ++ sub H (leaves H ct) (depthOf (nChunks ct.size)) 0) ::
    subInputs H (leafIn ct) (depthOf (nChunks ct.size)) 0

end

/-! ## Laws -/

section
variable {H : B → B}

theorem beq_eq (a b : B) : (a == b) = decide (a = b) := by
  show (a.data == b.data) = _
  by_cases h : a = b
  · subst h; simp
  · have : a.data ≠ b.data := fun e => h (ByteArray.ext e)
    simp [h, this]

theorem size_tagLeaf : tagLeaf.size = 20 := by decide
theorem size_tagNode : tagNode.size = 20 := by decide
theorem size_tagEmpty : tagEmpty.size = 21 := by decide
theorem tagLeaf_ne_tagNode : tagLeaf ≠ tagNode := by decide
theorem size_be64 (n : Nat) : (be64 n).size = 8 := by simp [be64, ByteArray.size]

/-- Numbers whose base-b digits below k agree agree mod b^k. -/
theorem mod_pow_eq {n m b : Nat} : ∀ k, (∀ j < k, n / b ^ j % b = m / b ^ j % b) → n % b ^ k = m % b ^ k
  | 0, _ => by simp [Nat.mod_one]
  | k + 1, h => by
    rw [Nat.pow_succ, Nat.mod_mul, Nat.mod_mul, mod_pow_eq k (fun j hj => h j (by omega)), h k (by omega)]

/-- be64 names n mod 2^64. -/
theorem be64_mod {n m : Nat} (h : be64 n = be64 m) : n % 2 ^ 64 = m % 2 ^ 64 := by
  have h' : ∀ j < 8, (n >>> (8 * j)).toUInt8 = (m >>> (8 * j)).toUInt8 := by
    have := congrArg (fun b : B => b.data.toList) h
    simp only [be64, List.toList_toArray, List.map_inj_left, List.mem_reverse, List.mem_range] at this
    exact this
  rw [show (2 : Nat) ^ 64 = 256 ^ 8 by rfl]
  apply mod_pow_eq 8
  intro j hj
  have := congrArg UInt8.toNat (h' j hj)
  simpa [Nat.shiftRight_eq_div_pow, Nat.pow_mul] using this

theorem nodeIn_inj {a b c d : B} (hb : b.size = d.size) (h : tagNode ++ a ++ b = tagNode ++ c ++ d) :
    a = c ∧ b = d := by
  rw [ByteArray.append_eq_append_iff_of_size_eq_right hb] at h
  exact ⟨(ByteArray.append_right_inj _).1 h.1, h.2⟩

theorem leafIn_ne_nodeIn (i : Nat) (s a b : B) : tagLeaf ++ be64 i ++ s ≠ tagNode ++ a ++ b := by
  intro h
  rw [ByteArray.append_assoc, ByteArray.append_assoc,
    ByteArray.append_eq_append_iff_of_size_eq_left (by rw [size_tagLeaf, size_tagNode])] at h
  exact tagLeaf_ne_tagNode h.1

theorem tagEmpty_ne_nodeIn {a b : B} (ha : a.size = 32) (hb : b.size = 32) : tagEmpty ≠ tagNode ++ a ++ b := by
  intro h
  have := congrArg ByteArray.size h
  simp [ByteArray.size_append, size_tagEmpty, size_tagNode, ha, hb] at this

theorem leafIn_ne_tagEmpty (i : Nat) (s : B) : tagLeaf ++ be64 i ++ s ≠ tagEmpty := by
  intro h
  have := congrArg ByteArray.size h
  simp [ByteArray.size_append, size_tagLeaf, size_be64, size_tagEmpty] at this
  omega

theorem rootIn_inj {l m : Nat} {t u : B} (h : tagRoot ++ be64 l ++ t = tagRoot ++ be64 m ++ u) :
    be64 l = be64 m ∧ t = u := by
  rw [ByteArray.append_eq_append_iff_of_size_eq_left (by simp [ByteArray.size_append, size_be64])] at h
  exact ⟨(ByteArray.append_right_inj _).1 h.1, h.2⟩

/-- Every list of k bytes. -/
def allBytes : Nat → List (List UInt8)
  | 0 => [[]]
  | k + 1 => (allBytes k).flatMap fun l => (List.range 256).map fun x => x.toUInt8 :: l

theorem length_allBytes : ∀ k, (allBytes k).length = 256 ^ k
  | 0 => rfl
  | k + 1 => by simp [allBytes, List.length_flatMap, List.map_const', length_allBytes k, Nat.pow_succ, Nat.mul_comm]

theorem mem_allBytes : ∀ l : List UInt8, l ∈ allBytes l.length
  | [] => by simp [allBytes]
  | x :: l => by
    simp only [allBytes, List.length_cons, List.mem_flatMap, List.mem_map, List.mem_range]
    exact ⟨l, mem_allBytes l, x.toNat, x.toNat_lt, by simp⟩

/-- **No hash with 32-byte outputs is injective** (there are 256^32 of
them, and more inputs), so the laws cannot assume injectivity. -/
theorem no_injective_hash (hsize : ∀ x, (H x).size = 32) : ¬ ∀ x y, H x = H y → x = y := by
  intro hcr
  let f (n : Nat) : List UInt8 := (H ⟨Array.replicate n 0⟩).data.toList
  have hnd : ((List.range (256 ^ 32 + 1)).map f).Nodup := by
    refine List.Pairwise.map f (fun a b hab e => hab ?_) List.nodup_range
    have := congrArg ByteArray.size (hcr _ _ (ByteArray.ext (Array.toList_inj.1 e)))
    simpa [ByteArray.size] using this
  have hsub : (List.range (256 ^ 32 + 1)).map f ⊆ allBytes 32 := by
    intro l hl
    obtain ⟨n, -, rfl⟩ := List.mem_map.1 hl
    have := mem_allBytes (f n)
    simpa [f, hsize] using this
  have := hnd.length_le_of_subset hsub
  simp [length_allBytes] at this

theorem le_pow_depthOf (n : Nat) : n ≤ 2 ^ depthOf n := by
  unfold depthOf
  split
  · simp; omega
  · have := Nat.lt_log2_self (n := n - 1)
    omega

/-- `depthOf n` is the least depth whose tree holds n leaves. -/
theorem depthOf_le_iff {n k : Nat} : depthOf n ≤ k ↔ n ≤ 2 ^ k := by
  unfold depthOf
  split
  · have := Nat.two_pow_pos k
    simp; omega
  · rw [Nat.add_one_le_iff, Nat.log2_lt (by omega)]
    omega

theorem one_le_nChunks (len : Nat) : 1 ≤ nChunks len := Nat.le_max_left _ _

theorem size_slice (ct : B) (i : Nat) : (slice ct i).size = sliceLen ct.size i := by
  simp only [slice, sliceLen, ByteArray.size_extract, sliceSize]
  omega

theorem length_slices (ct : B) : (slices ct).length = nChunks ct.size := by simp [slices]

theorem getElem?_slices (ct : B) (i : Nat) :
    (slices ct)[i]? = if i < nChunks ct.size then some (slice ct i) else none := by
  split <;> simp [slices, *]

theorem getElem_slices (ct : B) (i : Nat) (h : i < (slices ct).length) : (slices ct)[i] = slice ct i := by
  simp [slices]

theorem assemble_range (ct : B) : ∀ k, assemble ((List.range k).map (slice ct)) = ct.extract 0 (k * sliceSize)
  | 0 => by simp [assemble]
  | k + 1 => by
    have := assemble_range ct k
    simp only [assemble] at this ⊢
    rw [List.range_succ, List.map_append, List.foldl_append, this]
    simp [slice, Nat.max_eq_right (Nat.mul_le_mul_right sliceSize (Nat.le_succ k))]

/-- **The slices put together are the file.** -/
theorem assemble_slices (ct : B) : assemble (slices ct) = ct := by
  have h : ct.size ≤ nChunks ct.size * sliceSize := by
    simp only [nChunks, sliceSize]
    omega
  rw [slices, assemble_range, ← Nat.max_eq_left h, ByteArray.extract_zero_max_size]

theorem size_sub (hsize : ∀ x, (H x).size = 32) {f : Nat → B} (hf : ∀ j, (f j).size = 32) :
    ∀ d s, (sub H f d s).size = 32
  | 0, s => hf s
  | _ + 1, _ => hsize _

theorem size_climb (hsize : ∀ x, (H x).size = 32) {x : B} (hx : x.size = 32) :
    ∀ d i sibs, (climb H d i x sibs).size = 32
  | 0, _, _ => by simpa [climb] using hx
  | _ + 1, i, _ :: _ => by simp only [climb]; split <;> exact hsize _
  | _ + 1, _, [] => by simpa [climb] using hx

theorem length_path (f : Nat → B) : ∀ d s i, (path H f d s i).length = d
  | 0, _, _ => rfl
  | d + 1, s, i => by unfold path; split <;> simp [length_path f d]

theorem size_path (hsize : ∀ x, (H x).size = 32) {f : Nat → B} (hf : ∀ j, (f j).size = 32) :
    ∀ d s i, ∀ y ∈ path H f d s i, y.size = 32
  | 0, _, _ => by simp [path]
  | d + 1, s, i => by
    unfold path
    split <;>
    · intro y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact size_sub hsize hf _ _
      · exact size_path hsize hf d _ _ y hy

/-- **Climbing the path from the true leaf reaches the subtree's root.** -/
theorem climb_path (f : Nat → B) : ∀ d s i, i < 2 ^ d → climb H d i (f (s + i)) (path H f d s i) = sub H f d s
  | 0, s, i, hi => by
    have : i = 0 := by simp at hi; omega
    subst this
    simp [climb, sub]
  | d + 1, s, i, hi => by
    unfold path
    split
    · rename_i h
      simp only [climb, h, ↓reduceIte, climb_path f d s i h, sub]
    · rename_i h
      have h' : i - 2 ^ d < 2 ^ d := by rw [Nat.pow_succ] at hi; omega
      have e : s + i = s + 2 ^ d + (i - 2 ^ d) := by omega
      simp only [climb, h, ↓reduceIte]
      rw [e, climb_path f d (s + 2 ^ d) (i - 2 ^ d) h', sub]

/-- **A climb that reaches a subtree's root came from that subtree's
leaf, at that depth, through its path**, unless something the subtree
hashes has a second preimage. The leaves and the start hash inputs that
are not nodes', so the climb cannot stop short or run past the leaves. -/
theorem climb_sub (hsize : ∀ x, (H x).size = 32) {g : Nat → B}
    (hg : ∀ j a b, a.size = 32 → b.size = 32 → g j ≠ tagNode ++ a ++ b)
    {xin : B} (hx : ∀ a b, a.size = 32 → b.size = 32 → xin ≠ tagNode ++ a ++ b) :
    ∀ e i sibs d s, NoSecondPreimage H (subInputs H g d s) → sibs.length = e → (∀ y ∈ sibs, y.size = 32) →
      i < 2 ^ e → climb H e i (H xin) sibs = sub H (fun j => H (g j)) d s →
      e = d ∧ xin = g (s + i) ∧ sibs = path H (fun j => H (g j)) d s i
  | 0, i, sibs, d, s, hn, hl, _, hi, h => by
    have : i = 0 := by simp at hi; omega
    subst this
    obtain rfl : sibs = [] := List.length_eq_zero_iff.1 hl
    cases d with
    | zero =>
      simp only [climb, sub] at h
      exact ⟨rfl, hn _ (by simp [subInputs]) _ h, rfl⟩
    | succ d =>
      simp only [climb, sub, node] at h
      exact absurd (hn _ (by simp [subInputs]) _ h)
        (hx _ _ (size_sub hsize (fun _ => hsize _) _ _) (size_sub hsize (fun _ => hsize _) _ _))
  | e + 1, i, sib :: rest, d, s, hn, hl, hs, hi, h => by
    have hsib : sib.size = 32 := hs sib (by simp)
    have hrest : ∀ y ∈ rest, y.size = 32 := fun y hy => hs y (by simp [hy])
    have hl' : rest.length = e := by simpa using hl
    have hc := size_climb hsize (hsize xin)
    have hsub := size_sub hsize (fun j => hsize (g j))
    cases d with
    | zero =>
      simp only [climb, sub, node] at h
      split at h
      · exact (hg _ _ _ (hc _ _ _) hsib (hn (g s) (by simp [subInputs]) _ h).symm).elim
      · exact (hg _ _ _ hsib (hc _ _ _) (hn (g s) (by simp [subInputs]) _ h).symm).elim
    | succ d =>
      have hL : NoSecondPreimage H (subInputs H g d s) := fun x hx => hn x (by simp [subInputs, hx])
      have hR : NoSecondPreimage H (subInputs H g d (s + 2 ^ d)) := fun x hx => hn x (by simp [subInputs, hx])
      have hN := hn (tagNode ++ sub H (fun j => H (g j)) d s ++ sub H (fun j => H (g j)) d (s + 2 ^ d))
        (by simp [subInputs])
      simp only [climb, sub, node] at h
      split at h
      · rename_i hlt
        obtain ⟨h1, h3⟩ := nodeIn_inj (by rw [hsib, hsub]) (hN _ h)
        obtain ⟨rfl, h2, h4⟩ := climb_sub hsize hg hx e i rest d s hL hl' hrest hlt h1
        exact ⟨rfl, h2, by simp only [path, hlt, ↓reduceIte, h3, h4]⟩
      · rename_i hge
        obtain ⟨h3, h1⟩ := nodeIn_inj (by rw [hc, hsub]) (hN _ h)
        have hlt : i - 2 ^ e < 2 ^ e := by rw [Nat.pow_succ] at hi; omega
        obtain ⟨rfl, h2, h4⟩ := climb_sub hsize hg hx e (i - 2 ^ e) rest d (s + 2 ^ d) hR hl' hrest hlt h1
        refine ⟨rfl, ?_, by simp only [path, hge, ↓reduceIte, h3, h4]⟩
        rw [h2]
        congr 1
        omega
  | _ + 1, _, [], _, _, _, hl, _, _, _ => by simp at hl

theorem verify_iff {root : B} {len i : Nat} {s : B} {sibs : List B} :
    verify H root len i s sibs = true ↔
      len < 2 ^ 64 ∧ i < nChunks len ∧ sibs.length = depthOf (nChunks len) ∧ (∀ y ∈ sibs, y.size = 32) ∧
      s.size = sliceLen len i ∧ rootOf H len (climb H (depthOf (nChunks len)) i (leaf H i s) sibs) = root := by
  simp [verify, beq_eq, and_assoc]

theorem leaves_eq (ct : B) (j : Nat) :
    leaves H ct j = if j < nChunks ct.size then leaf H j (slice ct j) else empty H := rfl

/-- **Every chunk of a file verifies against its root** (a file under
2^64 bytes, the most be64 names). -/
theorem encode_verify (hsize : ∀ x, (H x).size = 32) {ct : B} (hct : ct.size < 2 ^ 64) {i : Nat}
    (hi : i < nChunks ct.size) :
    verify H (fileRoot H ct) ct.size i ((slices ct)[i]'(by rw [length_slices]; exact hi)) (proof H ct i)
      = true := by
  have hfs : ∀ j, (leaves H ct j).size = 32 := fun j => by rw [leaves_eq]; split <;> exact hsize _
  have hd : i < 2 ^ depthOf (nChunks ct.size) := Nat.lt_of_lt_of_le hi (le_pow_depthOf _)
  have hl : leaf H i ((slices ct)[i]'(by rw [length_slices]; exact hi)) = leaves H ct (0 + i) := by
    simp only [getElem_slices, Nat.zero_add, leaves_eq, hi, ↓reduceIte]
  rw [verify_iff, hl, getElem_slices]
  exact ⟨hct, hi, length_path _ _ _ _, size_path hsize hfs _ _ _, size_slice ct i,
    by rw [proof, climb_path _ _ _ _ hd, fileRoot]⟩

theorem leaves_hash (ct : B) : leaves H ct = fun j => H (leafIn ct j) := by
  funext j
  unfold leaves leafIn leaf empty
  split <;> rfl

/-- **A chunk that verifies against a file's root is that file's chunk**:
the length is the file's, the index is in it, the slice is its slice
there, and the siblings are its proof (no other siblings verify),
unless SHA-256 has a second preimage of something the root hashes. -/
theorem verify_sound (hsize : ∀ x, (H x).size = 32) {ct : B} (hspr : NoSecondPreimage H (treeInputs H ct))
    {len i : Nat} {s : B} {sibs : List B} (h : verify H (fileRoot H ct) len i s sibs = true) :
    len = ct.size ∧ (slices ct)[i]? = some s ∧ sibs = proof H ct i := by
  obtain ⟨hlen, hi, hl, hs, -, hr⟩ := verify_iff.1 h
  obtain ⟨hb, ht⟩ := rootIn_inj (hspr _ (List.mem_cons_self ..) _ hr)
  have hsub : NoSecondPreimage H (subInputs H (leafIn ct) (depthOf (nChunks ct.size)) 0) :=
    fun x hx => hspr x (List.mem_cons_of_mem _ hx)
  have hg : ∀ j a b, a.size = 32 → b.size = 32 → leafIn ct j ≠ tagNode ++ a ++ b := by
    intro j a b ha hb
    unfold leafIn
    split
    · exact leafIn_ne_nodeIn _ _ _ _
    · exact tagEmpty_ne_nodeIn ha hb
  rw [leaves_hash] at ht
  obtain ⟨hd, hx, hp⟩ := climb_sub hsize hg (fun a b _ _ => leafIn_ne_nodeIn i s a b)
    _ i sibs _ 0 hsub hl hs (Nat.lt_of_lt_of_le hi (le_pow_depthOf _)) ht
  rw [Nat.zero_add] at hx
  unfold leafIn at hx
  split at hx
  · rename_i hi'
    refine ⟨?_, ?_, by rw [proof, leaves_hash, hp]⟩
    · -- The trees have one depth, and be64 agrees: below 2^64 that is
      -- one length, and a file past it has a deeper tree.
      have hm := be64_mod hb
      have h48 : depthOf (nChunks ct.size) ≤ 48 := hd ▸ depthOf_le_iff.2 (by simp only [nChunks, sliceSize]; omega)
      have hc := depthOf_le_iff.1 h48
      have hc' := depthOf_le_iff.1 (Nat.le_of_eq hd.symm)
      rcases Nat.eq_zero_or_pos len with rfl | hpos
      · rw [show depthOf (nChunks 0) = 0 by decide] at hc'
        simp only [nChunks, sliceSize] at hc hc'
        omega
      · simp only [nChunks, sliceSize] at hc
        omega
    · simp only [getElem?_slices, hi', ↓reduceIte, (ByteArray.append_right_inj _).1 hx]
  · exact absurd hx (leafIn_ne_tagEmpty _ _)

/-- **A verifying chunk's index is below the chunk count, and its slice
has the size that index calls for.** -/
theorem index_bound {root : B} {len i : Nat} {s : B} {sibs : List B} (h : verify H root len i s sibs = true) :
    i < nChunks len ∧ s.size = sliceLen len i := by
  obtain ⟨-, hi, -, -, hs, -⟩ := verify_iff.1 h
  exact ⟨hi, hs⟩

/-- **Verifying chunks for every index, put together, are the file**,
unless SHA-256 has a second preimage of something its root hashes.
Every file has a chunk, so the first one pins the length. -/
theorem complete_assembles (hsize : ∀ x, (H x).size = 32) {ct : B}
    (hspr : NoSecondPreimage H (treeInputs H ct)) {len : Nat} (s : Nat → B) (sibs : Nat → List B)
    (h : ∀ i < nChunks len, verify H (fileRoot H ct) len i (s i) (sibs i) = true) :
    assemble ((List.range (nChunks len)).map s) = ct := by
  obtain rfl := (verify_sound hsize hspr (h 0 (one_le_nChunks len))).1
  have : (List.range (nChunks ct.size)).map s = slices ct := by
    apply List.ext_getElem?
    intro i
    by_cases hi : i < nChunks ct.size
    · rw [(verify_sound hsize hspr (h i hi)).2.1]
      simp [hi]
    · simp [getElem?_slices, hi]
  rw [this, assemble_slices]

/-! ### The assumptions hold for every file

For every file under 2^64 bytes, some hash with 32-byte outputs has no
second preimage of anything its root hashes (`assumptions_hold`). The
hash is a table of the file's tree inputs (`tableOf`): each input is
hashed to its first place in the table, and everything else to 0. An
input holds the hashes of the inputs below it, so the table is gathered
children first, in the order `sub` hashes (`gather`), each input hashed
by the table so far; growing the table at its end never changes what it
hashes an input it holds to (`tableHash_prefix`). A file under 2^64
bytes has fewer than 2^49 inputs, so 8 bytes of place tell them apart
(`tableHash_spr`). -/

/-- x's first place in L, from 0. -/
def place (x : B) : List B → Option Nat
  | [] => none
  | a :: t => if x = a then some 0 else (place x t).map (· + 1)

/-- A table as a hash: an input's first place in it, counted from 1, as
32 bytes; 0 for an input it does not hold. -/
def tableHash (L : List B) (x : B) : B :=
  ⟨Array.replicate 24 0⟩ ++ be64 ((place x L).elim 0 (· + 1))

/-- L with x at its end. -/
def put (x : B) (L : List B) : List B := L ++ [x]

/-- L with the inputs of the depth-d subtree over leaves g from leaf s,
in the order `sub` hashes them, each hashed by the table so far. -/
def gather (g : Nat → B) : Nat → Nat → List B → List B
  | 0, s, L => put (g s) L
  | d + 1, s, L =>
    let L2 := gather g d (s + 2 ^ d) (gather g d s L)
    let H := tableHash L2
    put (tagNode ++ sub H (fun j => H (g j)) d s ++ sub H (fun j => H (g j)) d (s + 2 ^ d)) L2

/-- The table of a file's tree inputs: the tree's, then the root's. -/
def tableOf (ct : B) : List B :=
  let L := gather (leafIn ct) (depthOf (nChunks ct.size)) 0 []
  put (tagRoot ++ be64 ct.size ++
    sub (tableHash L) (fun j => tableHash L (leafIn ct j)) (depthOf (nChunks ct.size)) 0) L

theorem place_of_mem {x : B} : ∀ {L : List B}, x ∈ L → ∃ i, place x L = some i ∧ i < L.length
  | [], h => absurd h List.not_mem_nil
  | a :: t, h => by
    by_cases hx : x = a
    · exact ⟨0, by simp [place, hx], by simp⟩
    · obtain ⟨i, hi, hl⟩ := place_of_mem ((List.mem_cons.1 h).resolve_left hx)
      exact ⟨i + 1, by simp [place, hx, hi], by simp; omega⟩

theorem place_get {x : B} : ∀ {L : List B} {i : Nat}, place x L = some i → L[i]? = some x
  | [], _, h => by simp [place] at h
  | a :: t, i, h => by
    by_cases hx : x = a
    · simp [place, hx] at h; subst h; simp [hx]
    · simp only [place, hx, ↓reduceIte, Option.map_eq_some_iff] at h
      obtain ⟨j, hj, rfl⟩ := h
      simpa using place_get hj

theorem place_append {x : B} {M : List B} : ∀ {L : List B}, x ∈ L → place x (L ++ M) = place x L
  | [], h => absurd h List.not_mem_nil
  | a :: t, h => by
    by_cases hx : x = a
    · simp [place, hx]
    · simp only [List.cons_append, place, hx, ↓reduceIte, place_append ((List.mem_cons.1 h).resolve_left hx)]

theorem size_tableHash (L : List B) (x : B) : (tableHash L x).size = 32 := by
  rw [tableHash, ByteArray.size_append, size_be64]; rfl

/-- Growing a table at its end never changes what it hashes an input it
held to. -/
theorem tableHash_prefix {L L' : List B} (hp : L <+: L') {x : B} (hx : x ∈ L) :
    tableHash L' x = tableHash L x := by
  obtain ⟨M, rfl⟩ := hp
  rw [tableHash, tableHash, place_append hx]

/-- **A table shorter than 2^64, read as a hash, has no second preimage
of anything it holds.** -/
theorem tableHash_spr {L : List B} (hl : L.length < 2 ^ 64) {x y : B} (hx : x ∈ L)
    (hy : tableHash L y = tableHash L x) : y = x := by
  have hb := be64_mod ((ByteArray.append_right_inj _).1 hy)
  obtain ⟨i, hi, hil⟩ := place_of_mem hx
  rw [hi] at hb
  simp only [Option.elim] at hb
  cases hp : place y L with
  | none =>
    rw [hp] at hb
    simp only [Nat.zero_mod] at hb
    rw [Nat.mod_eq_of_lt (by omega)] at hb; omega
  | some j =>
    rw [hp] at hb
    simp only at hb
    have hjl : j < L.length := by
      have := place_get hp
      exact (List.getElem?_eq_some_iff.1 this).1
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hb
    have e : j = i := by omega
    subst e
    have := (place_get hp).symm.trans (place_get hi)
    simpa using this

theorem prefix_put (x : B) (L : List B) : L <+: put x L := List.prefix_append L [x]

theorem mem_put (x : B) (L : List B) : x ∈ put x L := by simp [put]

theorem length_put (x : B) (L : List B) : (put x L).length = L.length + 1 := by simp [put]

/-- **Gathering a subtree's inputs**: it grows the table at its end, by
fewer inputs than the subtree has leaves twice over; and for any table
that grows it further, the subtree's root is the one it hashed, and
every input of the subtree is in it. -/
theorem gather_spec (g : Nat → B) : ∀ d s L,
    L <+: gather g d s L ∧ (gather g d s L).length + 1 ≤ L.length + 2 ^ (d + 1) ∧
    ∀ L', gather g d s L <+: L' →
      sub (tableHash L') (fun j => tableHash L' (g j)) d s =
        sub (tableHash (gather g d s L)) (fun j => tableHash (gather g d s L) (g j)) d s ∧
      ∀ x ∈ subInputs (tableHash L') g d s, x ∈ gather g d s L
  | 0, s, L => by
    refine ⟨prefix_put _ _, by simp only [gather, length_put]; omega, fun L' hp => ?_⟩
    have hm := mem_put (g s) L
    refine ⟨by simp only [sub, gather]; exact tableHash_prefix hp hm, fun x hx => ?_⟩
    simp only [subInputs, List.mem_singleton] at hx
    subst hx; exact hm
  | d + 1, s, L => by
    obtain ⟨p1, n1, h1⟩ := gather_spec g d s L
    obtain ⟨p2, n2, h2⟩ := gather_spec g d (s + 2 ^ d) (gather g d s L)
    let L1 := gather g d s L
    let L2 := gather g d (s + 2 ^ d) L1
    let H2 := tableHash L2
    let x := tagNode ++ sub H2 (fun j => H2 (g j)) d s ++ sub H2 (fun j => H2 (g j)) d (s + 2 ^ d)
    have e3 : gather g (d + 1) s L = put x L2 := rfl
    rw [e3]
    have p3 := prefix_put x L2
    have n3 : (put x L2).length = L2.length + 1 := length_put x L2
    have e2 : L2.length = (gather g d (s + 2 ^ d) (gather g d s L)).length := rfl
    have e1 : L1.length = (gather g d s L).length := rfl
    refine ⟨p1.trans (p2.trans p3), by rw [Nat.pow_succ]; omega, fun L' hp => ?_⟩
    -- under any table past L3, the children's roots are the ones hashed
    have kids : ∀ L'', L2 <+: L'' →
        sub (tableHash L'') (fun j => tableHash L'' (g j)) d s = sub H2 (fun j => H2 (g j)) d s ∧
        sub (tableHash L'') (fun j => tableHash L'' (g j)) d (s + 2 ^ d) =
          sub H2 (fun j => H2 (g j)) d (s + 2 ^ d) := fun L'' h =>
      ⟨((h1 L'' (p2.trans h)).1).trans ((h1 L2 p2).1).symm, (h2 L'' h).1.trans ((h2 L2 (List.prefix_refl _)).1).symm⟩
    have root : ∀ L'', put x L2 <+: L'' →
        sub (tableHash L'') (fun j => tableHash L'' (g j)) (d + 1) s = tableHash (put x L2) x := by
      intro L'' h
      obtain ⟨kl, kr⟩ := kids L'' (p3.trans h)
      simp only [sub, node]
      rw [kl, kr]
      exact tableHash_prefix h (mem_put x L2)
    refine ⟨(root L' hp).trans (root _ (List.prefix_refl _)).symm, fun y hy => ?_⟩
    obtain ⟨kl, kr⟩ := kids L' (p3.trans hp)
    simp only [subInputs, List.mem_cons, List.mem_append] at hy
    rcases hy with rfl | hy | hy
    · rw [kl, kr]; exact mem_put x L2
    · exact (p2.trans p3).subset ((h1 L' (p2.trans (p3.trans hp))).2 y hy)
    · exact p3.subset ((h2 L' (p3.trans hp)).2 y hy)

/-- **A file's table, read as a hash, has no second preimage of
anything the file's root hashes**, for every file under 2^64 bytes. -/
theorem tableOf_spr (ct : B) (hct : ct.size < 2 ^ 64) :
    NoSecondPreimage (tableHash (tableOf ct)) (treeInputs (tableHash (tableOf ct)) ct) := by
  let D := depthOf (nChunks ct.size)
  let L := gather (leafIn ct) D 0 []
  let r := tagRoot ++ be64 ct.size ++ sub (tableHash L) (fun j => tableHash L (leafIn ct j)) D 0
  have et : tableOf ct = put r L := rfl
  obtain ⟨-, hn, hs⟩ := gather_spec (leafIn ct) D 0 []
  obtain ⟨hsub, hin⟩ := hs (put r L) (prefix_put r L)
  have hD : D ≤ 48 := depthOf_le_iff.2 (by simp only [nChunks, sliceSize]; omega)
  have hlen : (tableOf ct).length < 2 ^ 64 := by
    rw [et]
    have := length_put r L
    have eL : L.length = (gather (leafIn ct) D 0 []).length := rfl
    have := Nat.pow_le_pow_right (n := 2) (by decide) (Nat.succ_le_succ hD)
    simp only [List.length_nil] at hn
    omega
  refine fun x hx y hy => tableHash_spr hlen ?_ hy
  rw [et] at hx ⊢
  unfold treeInputs at hx
  rw [leaves_hash] at hx
  simp only [List.mem_cons] at hx
  rcases hx with rfl | hx
  · rw [hsub]; exact mem_put r L
  · exact (prefix_put r L).subset (hin x hx)

/-- **The laws' assumptions hold for every file**: for every file under
2^64 bytes, a hash with 32-byte outputs has no second preimage of
anything the file's root hashes (where injectivity cannot,
`no_injective_hash`), so `verify_sound`, `complete_assembles` and the
attachment laws are not vacuous for any attachment. The hash is the
file's table (`tableOf_spr`). -/
theorem assumptions_hold (ct : B) (hct : ct.size < 2 ^ 64) :
    ∃ H : B → B, (∀ x, (H x).size = 32) ∧ NoSecondPreimage H (treeInputs H ct) :=
  ⟨tableHash (tableOf ct), size_tableHash _, tableOf_spr ct hct⟩

end

/-! ## What runs: the levels, built once

`sub` and `path` say what a root and a proof are, and the laws are about
them. They are not what runs: `path` rebuilds every sibling's subtree,
so one proof hashes the whole file again, and a file's n proofs hash
n² slices. What runs hashes each leaf once into a table, builds each
level above it once, and reads the root and the proofs off the levels.
`fileRoot`, `proof` and `rootAndProofs` (what an attachment writes) are
compiled as their `Fast` twins through `@[csimp]` equalities, proven,
so `encode_verify`, `verify_sound` and `complete_assembles` are about
the code that runs. -/

section
variable (H : B → B)

/-- A file's root and every chunk's proof: what an attachment writes. -/
def rootAndProofs (ct : B) : B × List (List B) :=
  (fileRoot H ct, (List.range (nChunks ct.size)).map (proof H ct))

/-- The level above a: each pair hashed into its node. -/
def up (a : Array B) : Array B :=
  Array.ofFn (n := a.size / 2) fun j => node H (a.getD (2 * j) .empty) (a.getD (2 * j + 1) .empty)

/-- Level k above a, a's own being 0. -/
def level (a : Array B) : Nat → Array B
  | 0 => a
  | k + 1 => up H (level a k)

/-- Levels 0 to d above a, each built once from the one below. -/
def levels (a : Array B) : Nat → List (Array B)
  | 0 => [a]
  | d + 1 => a :: levels (up H a) d

/-- A file's leaves, each slice hashed once. -/
def leafArray (ct : B) : Array B :=
  Array.ofFn (n := 2 ^ depthOf (nChunks ct.size)) fun j => leaves H ct j

/-- A file's levels, its leaves first. -/
def fileLevels (ct : B) : List (Array B) :=
  levels H (leafArray H ct) (depthOf (nChunks ct.size))

/-- `sub` of depth k at leaf s, read off the levels. -/
def look (ls : List (Array B)) (k s : Nat) : B := (ls.getD k #[]).getD (s / 2 ^ k) .empty

/-- `path`, with each subtree's root read from g. -/
def pathOf (g : Nat → Nat → B) : Nat → Nat → Nat → List B
  | 0, _, _ => []
  | d + 1, s, i =>
    if i < 2 ^ d then g d (s + 2 ^ d) :: pathOf g d s i
    else g d s :: pathOf g d (s + 2 ^ d) (i - 2 ^ d)

def fileRootFast (ct : B) : B :=
  rootOf H ct.size (look (fileLevels H ct) (depthOf (nChunks ct.size)) 0)

def proofFast (ct : B) (i : Nat) : List B :=
  pathOf (look (fileLevels H ct)) (depthOf (nChunks ct.size)) 0 i

def rootAndProofsFast (ct : B) : B × List (List B) :=
  let ls := fileLevels H ct
  let d := depthOf (nChunks ct.size)
  (rootOf H ct.size (look ls d 0), (List.range (nChunks ct.size)).map (pathOf (look ls) d 0))

theorem getD_ofFn {n : Nat} (f : Fin n → B) {j : Nat} (h : j < n) :
    (Array.ofFn f).getD j .empty = f ⟨j, h⟩ := by
  simp [Array.getD, h]

theorem size_up (a : Array B) : (up H a).size = a.size / 2 := by simp [up]

theorem level_up (a : Array B) : ∀ k, level H (up H a) k = level H a (k + 1)
  | 0 => rfl
  | k + 1 => by rw [level, level_up a k]; rfl

theorem getD_levels (a : Array B) : ∀ d k, k ≤ d → (levels H a d).getD k #[] = level H a k
  | 0, k, hk => by rw [show k = 0 by omega]; rfl
  | d + 1, 0, _ => rfl
  | d + 1, k + 1, hk => by
    simp only [levels, List.getD_cons_succ]
    rw [getD_levels (up H a) d k (by omega), level_up]

/-- **Level k holds the roots of the depth-k subtrees**, left to right. -/
theorem level_sub {f : Nat → B} {D : Nat} {a : Array B} (hs : a.size = 2 ^ D)
    (ha : ∀ j < 2 ^ D, a.getD j .empty = f j) :
    ∀ k, k ≤ D → (level H a k).size = 2 ^ (D - k) ∧
      ∀ j < 2 ^ (D - k), (level H a k).getD j .empty = sub H f k (j * 2 ^ k)
  | 0, _ => ⟨by simp only [level, Nat.sub_zero]; exact hs,
      fun j hj => by simp only [level, sub, Nat.pow_zero, Nat.mul_one]; exact ha j (by simpa using hj)⟩
  | k + 1, hk => by
    obtain ⟨ihs, ihg⟩ := level_sub hs ha k (by omega)
    have e : 2 ^ (D - k) = 2 ^ (D - (k + 1)) * 2 := by
      rw [← Nat.pow_succ]; congr 1; omega
    refine ⟨by rw [level, size_up, ihs, e, Nat.mul_div_cancel _ (by decide)], fun j hj => ?_⟩
    have hj' : j < (level H a k).size / 2 := by rw [ihs, e, Nat.mul_div_cancel _ (by decide)]; exact hj
    rw [level, up, getD_ofFn _ hj', sub, ihg (2 * j) (by rw [e]; omega), ihg (2 * j + 1) (by rw [e]; omega)]
    have p : j * 2 ^ (k + 1) = 2 * j * 2 ^ k := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, ← Nat.mul_assoc, Nat.mul_comm j 2]
    rw [p, Nat.add_mul, Nat.one_mul]

/-- **`pathOf` is `path`** wherever g gives `sub`'s roots of whole
subtrees inside a tree of depth D. -/
theorem pathOf_eq (f : Nat → B) (g : Nat → Nat → B) (D : Nat)
    (hg : ∀ k m, k ≤ D → (m + 1) * 2 ^ k ≤ 2 ^ D → g k (m * 2 ^ k) = sub H f k (m * 2 ^ k)) :
    ∀ d m i, d ≤ D → (m + 1) * 2 ^ d ≤ 2 ^ D → pathOf g d (m * 2 ^ d) i = path H f d (m * 2 ^ d) i
  | 0, _, _, _, _ => rfl
  | d + 1, m, i, hd, hm => by
    have p : m * 2 ^ (d + 1) = 2 * m * 2 ^ d := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ d) 2, ← Nat.mul_assoc, Nat.mul_comm m 2]
    have p1 : 2 * m * 2 ^ d + 2 ^ d = (2 * m + 1) * 2 ^ d := by rw [Nat.add_mul, Nat.one_mul]
    have hm' : (2 * m + 1 + 1) * 2 ^ d ≤ 2 ^ D := by
      rw [Nat.pow_succ] at hm
      rw [show 2 * m + 1 + 1 = (m + 1) * 2 by omega, Nat.mul_assoc, Nat.mul_comm 2 (2 ^ d)]
      exact hm
    have hm2 : (2 * m + 1) * 2 ^ d ≤ 2 ^ D := Nat.le_trans (Nat.mul_le_mul_right _ (by omega)) hm'
    rw [p]
    unfold pathOf path
    rw [p1, hg d (2 * m + 1) (by omega) hm', hg d (2 * m) (by omega) hm2,
      pathOf_eq f g D hg d (2 * m) _ (by omega) hm2, pathOf_eq f g D hg d (2 * m + 1) _ (by omega) hm']

theorem look_sub (ct : B) : ∀ k m, k ≤ depthOf (nChunks ct.size) →
    (m + 1) * 2 ^ k ≤ 2 ^ depthOf (nChunks ct.size) →
      look (fileLevels H ct) k (m * 2 ^ k) = sub H (leaves H ct) k (m * 2 ^ k) := by
  intro k m hk hm
  have hs : (leafArray H ct).size = 2 ^ depthOf (nChunks ct.size) := by simp [leafArray]
  have ha : ∀ j < 2 ^ depthOf (nChunks ct.size), (leafArray H ct).getD j .empty = leaves H ct j :=
    fun j hj => getD_ofFn _ hj
  obtain ⟨-, hg⟩ := level_sub H hs ha k hk
  have hm' : m < 2 ^ (depthOf (nChunks ct.size) - k) := by
    have e : 2 ^ depthOf (nChunks ct.size) = 2 ^ (depthOf (nChunks ct.size) - k) * 2 ^ k := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [e] at hm
    exact Nat.lt_of_succ_le (Nat.le_of_mul_le_mul_right hm (Nat.two_pow_pos k))
  rw [look, fileLevels, getD_levels _ _ _ _ hk, Nat.mul_div_cancel _ (Nat.two_pow_pos k), hg m hm']

/-- **The root, as it runs, is `fileRoot`.** -/
@[csimp] theorem fileRoot_eq_fast : @fileRoot = @fileRootFast := by
  funext H ct
  rw [fileRoot, fileRootFast]
  congr 1
  have := look_sub H ct (depthOf (nChunks ct.size)) 0 (Nat.le_refl _) (by simp)
  simpa using this.symm

/-- **A proof, as it runs, is `proof`.** -/
@[csimp] theorem proof_eq_fast : @proof = @proofFast := by
  funext H ct i
  have := pathOf_eq H (leaves H ct) (look (fileLevels H ct)) _ (look_sub H ct)
    (depthOf (nChunks ct.size)) 0 i (Nat.le_refl _) (by simp)
  simp only [Nat.zero_mul] at this
  rw [proof, proofFast, this]

/-- **The root and all the proofs, from one set of levels, are
`rootAndProofs`.** -/
@[csimp] theorem rootAndProofs_eq_fast : @rootAndProofs = @rootAndProofsFast := by
  funext H ct
  have hr : fileRootFast H ct = fileRoot H ct := by rw [fileRoot_eq_fast]
  have hp : proofFast H ct = proof H ct := by rw [proof_eq_fast]
  rw [rootAndProofs, ← hr, ← hp]
  rfl

end

end Community.Merkle
