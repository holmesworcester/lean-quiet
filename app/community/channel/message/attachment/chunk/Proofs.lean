import app.community.Family
import app.community.channel.message.attachment.chunk.Commands

namespace Community
open Engine Codec
variable {C : Crypto} {ops : Id → Option Op}

/-- **A chunk is Valid only if its Merkle path verifies** against the
root and length it names (`Merkle.verify_sound` then makes it that
file's slice). -/
theorem check_chunk {C : Crypto} {o : Op} {b : Body} {fs : List Fact} {c att root : Id} {len i : Nat}
    (h : check C o b fs = some (.chunk c att root len i)) :
    ∃ tm slice sibs, b = .chunk root len tm i slice sibs ∧ o.reqs.head? = some c ∧ att = o.reqs.getD 1 .empty ∧
      Merkle.verify sha256 root len i slice sibs = true ∧
      ∃ d e m u k x, fs = [.admission c c d e, .attachment c m u root len tm k x] := by
  unfold check at h
  split at h <;> (try (simp at h; done))
  rename_i b r t
  rcases b with ⟨r', l, tm, i', x, p⟩; rcases r with ⟨c0, u0, d0, e0⟩; rcases t with ⟨c2, m, u, r2, l2, tm2, k, x2⟩
  simp only [Chunk.check] at h
  split at h
  · rename_i hc
    simp only [Option.map_some, Option.some.injEq, Fact.ofChunk.injEq, Chunk.Fact.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    obtain ⟨h1, rfl, rfl, rfl, rfl, rfl, h6⟩ := hc
    exact ⟨_, _, _, rfl, h1, rfl, h6, _, _, _, _, _, _, rfl⟩
  · simp at h

/-- No SHA-256 collision between what file ct's root hashes and what
checking chunk body b hashed (`Merkle.NoCollision` over the bytes b
carries); nothing for a body that is not a chunk. Two finite lists of
bytes at hand, so it fails only if b carries a real collision, and a
node can test it. -/
def ChunkSound (ct : ByteArray) : Body → Prop
  | .chunk _ len _ i s sibs =>
    Merkle.NoCollision sha256 (Merkle.treeInputs sha256 ct) (Merkle.verifyInputs sha256 len i s sibs)
  | _ => True

instance (ct : ByteArray) (b : Body) : Decidable (ChunkSound ct b) := by
  unfold ChunkSound; split <;> infer_instance

/-- `ChunkSound` of every op a store holds: no chunk in it carries a
SHA-256 collision with file ct's tree. -/
def ChunksSound (ops : Id → Option Op) (ct : ByteArray) : Prop :=
  ∀ x o b, ops x = some o → (decode o.body : Option Body) = some b → ChunkSound ct b

/-- **A Valid chunk is its file's slice.** If its root is a file's root
(SHA-256 32 bytes wide, and nothing checking the chunk hashed colliding
with what the root hashes), its length is the file's, its slice is the
file's slice at its index, and its siblings are that slice's proof. -/
theorem chunk_is_slice {C : Crypto} {o : Op} {b : Body} {fs : List Fact} {c att : Id} {len i : Nat}
    {ct : ByteArray} (hsize : ∀ x, (sha256 x).size = 32) (hspr : ChunkSound ct b)
    (h : check C o b fs = some (.chunk c att (Merkle.fileRoot sha256 ct) len i)) :
    ∃ tm slice, b = .chunk (Merkle.fileRoot sha256 ct) len tm i slice (Merkle.proof sha256 ct i) ∧
      len = ct.size ∧ (Merkle.slices ct)[i]? = some slice := by
  obtain ⟨tm, slice, sibs, rfl, _, _, hv, _⟩ := check_chunk h
  obtain ⟨hl, hs, rfl⟩ := Merkle.verify_sound hsize hspr hv
  exact ⟨tm, slice, rfl, hl, hs⟩

/-- **A chunk is its attachment's.** A Valid chunk cites an attachment
of its community whose root and length are the chunk's, and claims that
attachment's time; and that attachment cites its message: so a
message's dependents reach every chunk of its attachments. -/
theorem chunk_of_attachment {x c att root : Id} {len i : Nat}
    (h : V C ops x (.chunk c att root len i)) :
    ∃ o tm m u k s, ops x = some o ∧ o.reqs = [c, att] ∧ orderOf o = tm ∧
      V C ops att (.attachment c m u root len tm k s) := by
  obtain ⟨o, b, fs, hx, hb, hr, hv⟩ := valid_inv h
  obtain ⟨tm, _, _, rfl, hhead, hatt, _, d, e, m, u, k, s, rfl⟩ := check_chunk hv
  obtain ⟨r0, r1, rest, hreq, _, hav, hrest⟩ := all2_cons2 hr
  cases hrest
  rw [hreq] at hhead hatt; simp at hhead hatt; subst hhead; subst hatt
  exact ⟨o, tm, m, u, k, s, hx, hreq, by simp [orderOf, hb], hav⟩

/-- Chunk i of file ct, of attachment att in community c, claimed at
time tm (its attachment's): the one op it can be. -/
def fileChunk (c att : Id) (tm : Nat) (ct : ByteArray) (i : Nat) : Op :=
  let b := Body.chunk (Merkle.fileRoot sha256 ct) ct.size tm i ((Merkle.slices ct).getD i .empty)
    (Merkle.proof sha256 ct i)
  Op.make b.tag [c, att] (encode b)

/-- **A Valid chunk under a file's root is that file's chunk op** for
its attachment, at the attachment's time: the slice and siblings are the
file's (`chunk_is_slice`), the op cites c and the attachment, its time
is the attachment's, and its type is its body's (`op_of_valid`). -/
theorem chunk_id (hk : Keyed ops) (hsize : ∀ x, (sha256 x).size = 32) {ct : ByteArray}
    (hspr : ChunksSound ops ct) {c att z m u : Id} {l l2 i tm : Nat} {k s : ByteArray}
    (hz : V C ops z (.chunk c att (Merkle.fileRoot sha256 ct) l i))
    (ha : V C ops att (.attachment c m u (Merkle.fileRoot sha256 ct) l2 tm k s)) :
    z = (fileChunk c att tm ct i).id := by
  obtain ⟨o, b, hzo, hmk, hb⟩ := op_of_valid hz
  obtain ⟨o', b', fs, hzo', hb', hr, hc⟩ := valid_inv hz
  rw [hzo] at hzo'; cases hzo'
  rw [hb] at hb'; cases hb'
  obtain ⟨tm', slice, rfl, rfl, hs⟩ := chunk_is_slice hsize (hspr z o b hzo hb) hc
  obtain ⟨o2, tm2, _, _, _, _, hzo2, hreqs, hord, hav⟩ := chunk_of_attachment hz
  rw [hzo] at hzo2; cases hzo2
  have := spec_det hav ha
  simp only [Verdict.valid.injEq, Fact.attachment.injEq] at this
  obtain ⟨_, _, _, _, _, rfl, _, _⟩ := this
  have htm : tm' = tm2 := by simp [orderOf, hb] at hord; exact hord
  subst htm
  have hsl : (Merkle.slices ct).getD i .empty = slice := by simp [List.getD, hs]
  rw [← hk z o hzo, hmk, hreqs]; unfold fileChunk; rw [hsl]

/-- **An attachment's chunk at an index is one op**, so no chunk is
counted twice; and two attachments never share a chunk op, since each
cites its own. -/
theorem chunk_unique (hk : Keyed ops) (hsize : ∀ x, (sha256 x).size = 32) {ct : ByteArray}
    (hspr : ChunksSound ops ct) {c att x y m u : Id} {l l' l2 i tm : Nat} {k s : ByteArray}
    (ha : V C ops att (.attachment c m u (Merkle.fileRoot sha256 ct) l2 tm k s))
    (hx : V C ops x (.chunk c att (Merkle.fileRoot sha256 ct) l i))
    (hy : V C ops y (.chunk c att (Merkle.fileRoot sha256 ct) l' i)) : x = y := by
  rw [chunk_id hk hsize hspr hx ha, chunk_id hk hsize hspr hy ha]

theorem chunk_own {x c att att' root root' : Id} {len len' i i' : Nat}
    (hx : V C ops x (.chunk c att root len i)) (hy : V C ops x (.chunk c att' root' len' i')) :
    att = att' := by
  have := spec_det hx hy
  simp only [Verdict.valid.injEq, Fact.chunk.injEq] at this
  exact this.2.1
open Engine
section
variable {s : DB Fact} {C : Crypto}

/-- **What an attachment writes are its file's chunk ops**: chunk i of
`attach` is `fileChunk` of the file at i, for every i below the chunk
count, so the progress laws count the ops `send` writes. -/
theorem attach_chunks (c adm msg : Id) (tm : Nat) (d : Device) (k : Key32) (f : NewFile) :
    (attach c adm msg tm d k f).2 = (List.range (Merkle.nChunks (fileCipher f).size)).map
      (fileChunk c (attach c adm msg tm d k f).1.id tm (fileCipher f)) := by
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  have hs : (Merkle.slices (fileCipher f)).getD i .empty = Merkle.slice (fileCipher f) i := by
    simp [List.getD, Merkle.getElem?_slices, hi]
  have hp : ((List.range (Merkle.nChunks (fileCipher f).size)).map
      (Merkle.proof sha256 (fileCipher f))).getD i [] = Merkle.proof sha256 (fileCipher f) i := by
    simp [List.getD, hi]
  simp only [fileChunk, mkOp, Merkle.rootAndProofs, hs, hp, attach]

end
end Community
