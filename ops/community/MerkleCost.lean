/-
What an attachment's Merkle tree costs, as it runs (docs/PERF.md).

`rootAndProofs`, what an attachment writes, runs as `rootAndProofsM` at
`Id`, and hashes only through its door, `hashM`. Run `Counted`, the
same code computes the same root and proofs (`val_rootAndProofsM`) and
charges each hash with its input's size. The budget:
- `rootAndProofs_hashes`: for a tree of depth d, 2·2^d hashes: each leaf
  slot once, each node once, and the root once. That is fewer than 4n
  for n chunks (`rootAndProofs_hashes_lt`).
- `rootAndProofs_hashed`: the bytes hashed are the file's, once, and at
  most 112 more per leaf slot (fewer than 224 per chunk).

The negative control is `rootAndProofsSlowM`, the way that ran before
the levels: the root from `sub`, and each proof from `path`, which
rebuilds every sibling's subtree, through the same door.
`slow_hashes` counts its hashes: 2^(d+1) + n·(2^(d+1) − 2 − d), about
2n² for n chunks. `slow_over_budget` shows that it breaks the budget for
every file of two chunks or more.
-/
import ops.community.Merkle

namespace Community.Merkle
open Engine Engine.Counted

section
variable (H : B → B)

@[simp] theorem val_hashM (x : B) : val (hashM (m := Counted) H x) = H x := rfl

@[simp] theorem cost_hashM (x : B) :
    cost (hashM (m := Counted) H x) = { hashes := 1, hashed := x.size } :=
  Meter.add_zero _

/-! ## The value: the meter changes nothing -/

theorem val_upM (a : Array B) : val (upM (m := Counted) H a) = up H a := by
  rw [upM, val_ofFnM]; rfl

theorem val_levelsM (a : Array B) : ∀ d, val (levelsM (m := Counted) H a d) = levels H a d
  | 0 => rfl
  | d + 1 => by
    show a :: val (levelsM (m := Counted) H (val (upM (m := Counted) H a)) d) = _
    rw [val_upM, val_levelsM _ d]; rfl

theorem val_leafM (ct : B) (j : Nat) : val (leafM (m := Counted) H ct j) = leaves H ct j := by
  unfold leafM leaves leaf empty; split <;> rfl

theorem val_leafArrayM (ct : B) : val (leafArrayM (m := Counted) H ct) = leafArray H ct := by
  rw [leafArrayM, val_ofFnM, leafArray]; simp only [val_leafM]

/-- **Counted, what runs computes what an attachment writes**: the root
and every proof are `rootAndProofs`'s. -/
theorem val_rootAndProofsM (ct : B) :
    val (rootAndProofsM (m := Counted) H ct) = rootAndProofs H ct := by
  have e : val (levelsM (m := Counted) H (val (leafArrayM (m := Counted) H ct))
      (depthOf (nChunks ct.size))) = fileLevels H ct := by
    rw [val_leafArrayM, val_levelsM]; rfl
  rw [show rootAndProofs H ct = rootAndProofsFast H ct by rw [rootAndProofs_eq_fast],
    rootAndProofsFast_eq, ← e]
  rfl

/-! ## Hashes -/

theorem hashes_upM (a : Array B) : (cost (upM (m := Counted) H a)).hashes = a.size / 2 := by
  rw [upM, field_ofFnM Meter.hashes rfl (fun _ _ => rfl) _ (fun _ => 1) (fun _ => by simp)]
  simp [List.map_const']

theorem size_two_pow_up {a : Array B} {d : Nat} (ha : a.size = 2 ^ (d + 1)) : (up H a).size = 2 ^ d := by
  rw [size_up, ha, Nat.pow_succ, Nat.mul_div_cancel _ (by decide)]

theorem hashes_levelsM : ∀ d (a : Array B), a.size = 2 ^ d →
    (cost (levelsM (m := Counted) H a d)).hashes = 2 ^ d - 1
  | 0, _, _ => rfl
  | d + 1, a, ha => by
    simp only [levelsM, cost_bind, cost_pure, Meter.add_zero, Meter.hashes_add]
    rw [hashes_upM, val_upM, hashes_levelsM d _ (size_two_pow_up H ha), ha, Nat.pow_succ,
      Nat.mul_div_cancel _ (by decide)]
    have := Nat.one_le_two_pow (n := d)
    omega

theorem hashes_leafM (ct : B) (j : Nat) : (cost (leafM (m := Counted) H ct j)).hashes = 1 := by
  unfold leafM; split <;> simp

theorem hashes_leafArrayM (ct : B) :
    (cost (leafArrayM (m := Counted) H ct)).hashes = 2 ^ depthOf (nChunks ct.size) := by
  rw [leafArrayM, field_ofFnM Meter.hashes rfl (fun _ _ => rfl) _ (fun _ => 1)
    (fun i => hashes_leafM H ct i)]
  simp [List.map_const']

theorem size_leafArray (ct : B) : (leafArray H ct).size = 2 ^ depthOf (nChunks ct.size) := by
  simp [leafArray]

/-- **An attachment's root and proofs cost 2·2^d hashes**, d the
tree's depth: each leaf slot is hashed once, each node once, and the
root once. Every proof is read off the levels, and hashes nothing. -/
theorem rootAndProofs_hashes (ct : B) :
    (cost (rootAndProofsM (m := Counted) H ct)).hashes = 2 * 2 ^ depthOf (nChunks ct.size) := by
  simp only [rootAndProofsM, cost_bind, cost_pure, Meter.add_zero, Meter.hashes_add]
  rw [hashes_leafArrayM, val_leafArrayM, hashes_levelsM _ _ _ (size_leafArray H ct), cost_hashM]
  have := Nat.one_le_two_pow (n := depthOf (nChunks ct.size))
  simp only; omega

theorem pow_depthOf_lt {n : Nat} (h : 1 ≤ n) : 2 ^ depthOf n < 2 * n := by
  unfold depthOf
  split
  · simp; omega
  · rw [Nat.pow_succ]
    have := Nat.log2_self_le (n := n - 1) (by omega)
    omega

/-- **Fewer than 4n hashes for n chunks.** -/
theorem rootAndProofs_hashes_lt (ct : B) :
    (cost (rootAndProofsM (m := Counted) H ct)).hashes < 4 * nChunks ct.size := by
  rw [rootAndProofs_hashes]
  have := pow_depthOf_lt (one_le_nChunks ct.size)
  omega

/-! ## Bytes: the file's, once -/

/-- Every element of a, as `getD` reads it, is at most 32 bytes. -/
def Small (a : Array B) : Prop := ∀ j, (a.getD j .empty).size ≤ 32

theorem size_node_le {a : Array B} (ha : Small a) (j : Nat) :
    (tagNode ++ a.getD (2 * j) .empty ++ a.getD (2 * j + 1) .empty).size ≤ 84 := by
  simp only [ByteArray.size_append, size_tagNode]
  have := ha (2 * j); have := ha (2 * j + 1)
  omega

theorem small_up (hsize : ∀ x, (H x).size = 32) (a : Array B) : Small (up H a) := by
  intro j
  by_cases hj : j < a.size / 2
  · rw [up, getD_ofFn _ hj, node, hsize]; exact Nat.le_refl _
  · have : (up H a).getD j .empty = .empty := by
      simp [Array.getD, size_up, hj]
    rw [this]; decide

theorem small_level (hsize : ∀ x, (H x).size = 32) {a : Array B} (ha : Small a) :
    ∀ k, Small (level H a k)
  | 0 => ha
  | _ + 1 => small_up H hsize _

theorem hashed_upM {a : Array B} (ha : Small a) :
    (cost (upM (m := Counted) H a)).hashed ≤ 84 * (a.size / 2) := by
  rw [upM]
  refine Nat.le_trans (field_ofFnM_le Meter.hashed rfl (fun _ _ => rfl) _ (fun _ => 84)
    (fun i => by rw [cost_hashM]; exact size_node_le ha i)) ?_
  simp [List.map_const', Nat.mul_comm]

theorem hashed_levelsM (hsize : ∀ x, (H x).size = 32) : ∀ d (a : Array B), a.size = 2 ^ d → Small a →
    (cost (levelsM (m := Counted) H a d)).hashed ≤ 84 * (2 ^ d - 1)
  | 0, _, _, _ => Nat.zero_le _
  | d + 1, a, ha, hs => by
    simp only [levelsM, cost_bind, cost_pure, Meter.add_zero, Meter.hashed_add]
    have h1 := hashed_upM H hs
    rw [val_upM]
    have h2 := hashed_levelsM hsize d _ (size_two_pow_up H ha) (small_up H hsize a)
    rw [ha, Nat.pow_succ, Nat.mul_div_cancel _ (by decide)] at h1
    have := Nat.one_le_two_pow (n := d)
    rw [Nat.pow_succ]
    omega

theorem hashed_leafM (ct : B) (j : Nat) :
    (cost (leafM (m := Counted) H ct j)).hashed ≤ 28 + (slice ct j).size := by
  unfold leafM
  split
  · simp [ByteArray.size_append, size_tagLeaf, size_be64]
  · simp [size_tagEmpty]; omega

/-- The first k slices hold the file's first k · 64 KiB bytes. -/
theorem sum_slices (ct : B) (k : Nat) :
    ((List.range k).map fun j => (slice ct j).size).sum = min ct.size (k * sliceSize) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, size_slice, sliceLen,
      sliceSize, Nat.min_def]
    split <;> split <;> split <;> omega

theorem sum_map_add_const {α : Type} (c : Nat) (f : α → Nat) (l : List α) :
    (l.map fun j => c + f j).sum = c * l.length + (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; rw [Nat.mul_succ]; omega

theorem hashed_leafArrayM (ct : B) :
    (cost (leafArrayM (m := Counted) H ct)).hashed ≤ ct.size + 28 * 2 ^ depthOf (nChunks ct.size) := by
  rw [leafArrayM]
  refine Nat.le_trans (field_ofFnM_le Meter.hashed rfl (fun _ _ => rfl) _
    (fun j => 28 + (slice ct j).size) (fun i => hashed_leafM H ct i)) ?_
  rw [sum_map_add_const, sum_slices]
  simp only [List.length_range]
  omega

theorem small_leafArray (hsize : ∀ x, (H x).size = 32) (ct : B) : Small (leafArray H ct) := by
  intro j
  by_cases hj : j < 2 ^ depthOf (nChunks ct.size)
  · rw [leafArray, getD_ofFn _ hj, leaves_hash, hsize]; exact Nat.le_refl _
  · have : (leafArray H ct).getD j .empty = .empty := by simp [Array.getD, size_leafArray, hj]
    rw [this]; decide

theorem size_tagRoot : tagRoot.size = 20 := by decide

/-- **An attachment hashes its file's bytes once**, and at most 112
bytes more per leaf slot: its leaves' tags and indices, its nodes, and
its root (H with 32-byte outputs, as SHA-256). -/
theorem rootAndProofs_hashed (hsize : ∀ x, (H x).size = 32) (ct : B) :
    (cost (rootAndProofsM (m := Counted) H ct)).hashed ≤
      ct.size + 112 * 2 ^ depthOf (nChunks ct.size) := by
  simp only [rootAndProofsM, cost_bind, cost_pure, Meter.add_zero, Meter.hashed_add, cost_hashM]
  have h1 := hashed_leafArrayM H ct
  rw [val_leafArrayM]
  have h2 := hashed_levelsM H hsize _ _ (size_leafArray H ct) (small_leafArray H hsize ct)
  have h3 : (look (val (levelsM (m := Counted) H (leafArray H ct) (depthOf (nChunks ct.size))))
      (depthOf (nChunks ct.size)) 0).size ≤ 32 := by
    rw [val_levelsM, look, getD_levels H _ _ _ (Nat.le_refl _)]
    exact small_level H hsize (small_leafArray H hsize ct) _ _
  simp only [ByteArray.size_append, size_tagRoot, size_be64]
  have := Nat.one_le_two_pow (n := depthOf (nChunks ct.size))
  omega

/-- **Fewer than 224 bytes beyond the file's per chunk.** -/
theorem rootAndProofs_hashed_lt (hsize : ∀ x, (H x).size = 32) (ct : B) :
    (cost (rootAndProofsM (m := Counted) H ct)).hashed < ct.size + 224 * nChunks ct.size := by
  have := rootAndProofs_hashed H hsize ct
  have := pow_depthOf_lt (one_le_nChunks ct.size)
  omega

end

/-! ## The negative control: every proof rebuilding its siblings

What ran before the levels (`fileRoot` and `proof` as written, which
`path` makes rebuild every sibling's subtree), through the same door.
It computes the same root and proofs (`val_rootAndProofsSlowM`), so no
law about values can tell it from what runs; the budget does. -/

section
variable {m : Type → Type} [Monad m] [Tick m] (H : B → B)

/-- `sub`, through the door. -/
def subM (f : Nat → m B) : Nat → Nat → m B
  | 0, s => f s
  | d + 1, s => do
    let l ← subM f d s
    let r ← subM f d (s + 2 ^ d)
    hashM H (tagNode ++ l ++ r)

/-- `path`, through the door: each sibling's subtree built again. -/
def pathM (f : Nat → m B) : Nat → Nat → Nat → m (List B)
  | 0, _, _ => pure []
  | d + 1, s, i =>
    if i < 2 ^ d then do
      let x ← subM H f d (s + 2 ^ d)
      let rest ← pathM f d s i
      pure (x :: rest)
    else do
      let x ← subM H f d s
      let rest ← pathM f d (s + 2 ^ d) (i - 2 ^ d)
      pure (x :: rest)

/-- The root from `sub`, and each proof from `path`. -/
def rootAndProofsSlowM (ct : B) : m (B × List (List B)) := do
  let d := depthOf (nChunks ct.size)
  let t ← subM H (leafM H ct) d 0
  let r ← hashM H (tagRoot ++ be64 ct.size ++ t)
  let ps ← (List.range (nChunks ct.size)).mapM (pathM H (leafM H ct) d 0)
  pure (r, ps)

end

section
variable (H : B → B)

theorem val_mapM {α β : Type} (f : α → Counted β) :
    ∀ l : List α, val (l.mapM f) = l.map fun a => val (f a)
  | [] => rfl
  | a :: t => by rw [List.mapM_cons, val_bind, val_bind, val_pure, val_mapM f t]; rfl

theorem field_mapM {α β : Type} (g : Meter → Nat) (hg0 : g 0 = 0) (hga : ∀ a b, g (a + b) = g a + g b)
    (f : α → Counted β) (b : Nat) (hb : ∀ a, g (cost (f a)) = b) :
    ∀ l : List α, g (cost (l.mapM f)) = l.length * b
  | [] => by rw [List.mapM_nil, cost_pure, hg0]; simp
  | a :: t => by
    rw [List.mapM_cons, cost_bind, cost_bind, cost_pure, hga, hga, hg0, hb,
      field_mapM g hg0 hga f b hb t, List.length_cons]
    rw [Nat.add_one_mul]; omega

theorem val_subM (ct : B) : ∀ d s, val (subM H (leafM (m := Counted) H ct) d s) = sub H (leaves H ct) d s
  | 0, s => val_leafM H ct s
  | d + 1, s => by
    show H (tagNode ++ val (subM H (leafM (m := Counted) H ct) d s) ++
      val (subM H (leafM (m := Counted) H ct) d (s + 2 ^ d))) = _
    rw [val_subM ct d s, val_subM ct d]; rfl

theorem val_pathM (ct : B) : ∀ d s i,
    val (pathM H (leafM (m := Counted) H ct) d s i) = path H (leaves H ct) d s i
  | 0, _, _ => rfl
  | d + 1, s, i => by
    unfold pathM path
    split
    · show val (subM H _ d (s + 2 ^ d)) :: val (pathM H _ d s i) = _
      rw [val_subM, val_pathM ct d]
    · show val (subM H _ d s) :: val (pathM H _ d (s + 2 ^ d) (i - 2 ^ d)) = _
      rw [val_subM, val_pathM ct d]

/-- The negative control computes what runs: the same root and proofs. -/
theorem val_rootAndProofsSlowM (ct : B) :
    val (rootAndProofsSlowM (m := Counted) H ct) = rootAndProofs H ct := by
  show (H (tagRoot ++ be64 ct.size ++ val (subM H (leafM (m := Counted) H ct) _ 0)),
    val ((List.range (nChunks ct.size)).mapM (pathM H (leafM (m := Counted) H ct) _ 0))) = _
  rw [val_subM, val_mapM]
  simp only [val_pathM]
  rfl

theorem hashes_subM (ct : B) : ∀ d s,
    (cost (subM H (leafM (m := Counted) H ct) d s)).hashes = 2 ^ (d + 1) - 1
  | 0, s => hashes_leafM H ct s
  | d + 1, s => by
    simp only [subM, cost_bind, Meter.hashes_add, cost_hashM]
    rw [hashes_subM ct d, hashes_subM ct d, Nat.pow_succ 2 (d + 1)]
    have := Nat.one_le_two_pow (n := d + 1)
    omega

theorem hashes_pathM (ct : B) : ∀ d s i,
    (cost (pathM H (leafM (m := Counted) H ct) d s i)).hashes = 2 ^ (d + 1) - 2 - d
  | 0, _, _ => rfl
  | d + 1, s, i => by
    unfold pathM
    have := Nat.one_le_two_pow (n := d + 1)
    have hd : d + 2 ≤ 2 ^ (d + 1) := by
      have := Nat.lt_two_pow_self (n := d); rw [Nat.pow_succ]; omega
    split <;>
    · simp only [cost_bind, cost_pure, Meter.add_zero, Meter.hashes_add]
      rw [hashes_subM, hashes_pathM ct d, Nat.pow_succ 2 (d + 1)]
      omega

/-- **The negative control's hashes**: 2^(d+1) for the root, and
2^(d+1) − 2 − d for each of the n proofs. -/
theorem slow_hashes (ct : B) :
    (cost (rootAndProofsSlowM (m := Counted) H ct)).hashes =
      2 ^ (depthOf (nChunks ct.size) + 1) +
        nChunks ct.size * (2 ^ (depthOf (nChunks ct.size) + 1) - 2 - depthOf (nChunks ct.size)) := by
  simp only [rootAndProofsSlowM, cost_bind, cost_pure, Meter.add_zero, Meter.hashes_add, cost_hashM]
  rw [hashes_subM, field_mapM Meter.hashes rfl (fun _ _ => rfl) _ _ (fun i => hashes_pathM H ct _ 0 i),
    List.length_range]
  have := Nat.one_le_two_pow (n := depthOf (nChunks ct.size) + 1)
  omega

/-- **The budget catches the negative control**: for every file of two
chunks or more, rebuilding the siblings breaks `rootAndProofs_hashes`. -/
theorem slow_over_budget (ct : B) (h : 2 ≤ nChunks ct.size) :
    2 * 2 ^ depthOf (nChunks ct.size) < (cost (rootAndProofsSlowM (m := Counted) H ct)).hashes := by
  rw [slow_hashes]
  have hd : 1 ≤ depthOf (nChunks ct.size) := by unfold depthOf; split <;> omega
  generalize depthOf (nChunks ct.size) = d at hd
  have := Nat.lt_two_pow_self (n := d)
  rw [Nat.pow_succ]
  have : 1 ≤ 2 ^ d * 2 - 2 - d := by omega
  have := Nat.le_mul_of_pos_right (nChunks ct.size) this
  omega

end

end Community.Merkle
