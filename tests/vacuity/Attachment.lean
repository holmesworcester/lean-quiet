import tests.vacuity.IdentityTrust
import engine.sync.WindowLaws

/-! Real SHA-256/Ed25519/XChaCha20 attachment fixture. Finite validation and
progress checks run natively. The laws' no-collision premise (`ChunkSound`,
`ChunksSound`) is about the bytes at hand, so it is decided here on the real
SHA-256 of this file's tree and its chunks; the three README theorem
applications retain only SHA-256's 32-byte output size as an assumption. -/
namespace Vacuity.Attachment
open Engine Community Codec Tests Vacuity.Identity Vacuity.IdentityTrust
set_option linter.defProp false

def contentKey : Key32 := Bytes.digest "vacuity/attachment/content-key".toUTF8
def file : NewFile := {
  info := { name := "meeting-notes.bin".toUTF8, kind := "application/octet-stream".toUTF8, w := 0, h := 0, preview := .empty }
  bytes := ⟨((List.range 70000).map fun i => (i % 251).toUInt8).toArray⟩
  key := Bytes.digest "vacuity/attachment/file-key".toUTF8
  nonce := ⟨⟨Array.replicate 24 7⟩, rfl⟩
  metaNonce := ⟨⟨Array.replicate 24 9⟩, rfl⟩ }

def cipher := fileCipher file
def rootHash := Merkle.fileRoot sha256 cipher
def msgTime : Nat := 29880000
def composed := attach c admission.id message.id msgTime bob contentKey file
def attachment := composed.1
def kid := kidOf cryptoSeal contentKey
def sealedMeta : ByteArray := match (decode attachment.body : Option Body) with
  | some (.attach _ _ _ _ sealed _) => sealed
  | _ => .empty

def attachmentFact : Fact := .attachment c message.id requestB.id rootHash cipher.size msgTime kid sealedMeta
def chunkBody (i : Nat) : Body :=
  .chunk rootHash cipher.size msgTime i (Merkle.slice cipher i) (Merkle.proof sha256 cipher i)
def chunk0 := fileChunk c attachment.id msgTime cipher 0
def chunk1 := fileChunk c attachment.id msgTime cipher 1
-- Another relay independently constructs the canonical bytes for index0.
def relayed0 := mkOp [c, attachment.id] (chunkBody 0)
def chunkFact (i : Nat) : Fact := .chunk c attachment.id rootHash cipher.size i

def full := before ++ [attachment, chunk0, chunk1]
def incomplete := before ++ [attachment, chunk1]
def duplicated := before ++ [attachment, chunk1, chunk1]

/-- Op o, if it is a chunk, is `ChunkSound` for this file. -/
def SoundOp (o : Op) : Prop := match (decode o.body : Option Body) with
  | some b => ChunkSound cipher b
  | none => True

instance (o : Op) : Decidable (SoundOp o) := by unfold SoundOp; split <;> infer_instance

/-- A store whose ops are among L, each sound, is `ChunksSound`. -/
theorem sound_of_list {L : List Op} {ops : Id → Option Op}
    (hl : ∀ x o, ops x = some o → o ∈ L) (h : ∀ o ∈ L, SoundOp o) : ChunksSound ops cipher := by
  intro x o b hx hb
  have := h o (hl x o hx)
  unfold SoundOp at this
  rw [hb] at this
  exact this

def sliceCertificate :=
  if hv : check ed25519 chunk0 (chunkBody 0) [rootFact, attachmentFact] = some (chunkFact 0) then
    if hp : ChunkSound cipher (chunkBody 0) then
      some (PLift.up (fun (hs : ∀ x, (sha256 x).size = 32) => chunk_is_slice hs hp hv))
    else none
  else none

def uniqueCertificate := do
  let ⟨ha⟩ ← certify full attachment attachmentFact
  let ⟨hx⟩ ← certify full chunk0 (chunkFact 0)
  let ⟨hy⟩ ← certify full relayed0 (chunkFact 0)
  if hp : ∀ o ∈ full, SoundOp o then
    return PLift.up (fun (hs : ∀ x, (sha256 x).size = 32) =>
      chunk_unique (keyed full) hs (sound_of_list (fun _ _ h => List.mem_of_find?_eq_some h) hp) ha hx hy)
  else none

/-- The fixture's stored ops give a round the same set S in either order
(`window_set_canonical`), at a floor below its message. -/
def canonicalCertificate :=
  if hu : ∀ o ∈ full, ∀ p ∈ full, o.id = p.id → o = p then
    some (PLift.up (fun a : Engine.Sync.Item =>
      Engine.Sync.window_set_canonical (family ed25519) full full.reverse (fun _ => List.mem_reverse.symm) hu
        4 c (msgTime + 1) a))
  else none

/-- A real timed chain from a Valid chunk: chunk 0 cites its attachment,
which claims its message's time; it is within four steps (`timed_chain_le`). -/
def chainCertificate := do
  let ⟨hv⟩ ← certify full chunk0 (chunkFact 0)
  if h1 : table full chunk0.id = some chunk0 then
    if h2 : chunk0.reqs.any (fun i => decide (i = attachment.id)) = true then
      have h2' : attachment.id ∈ chunk0.reqs := by
        obtain ⟨i, hi, e⟩ := List.any_eq_true.1 h2
        simp only [decide_eq_true_eq] at e
        exact e ▸ hi
      if h3 : table full attachment.id = some attachment then
        if h4 : orderOf attachment ≠ 0 then
          return PLift.up (timed_chain_le hv (TimedChain.cons h1 h2' h3 h4 (TimedChain.nil _)))
        else none
      else none
    else none
  else none

/-- The real Valid chunk 0 sorts with its message (`chunks_in_window`). -/
def windowCertificate := do
  let ⟨hx⟩ ← certify full chunk0 (chunkFact 0)
  return PLift.up (chunks_in_window hx)

def progressCertificate := do
  let ⟨ha⟩ ← certifyDB incomplete attachment attachmentFact
  if hq : (run incomplete).queue = [] then
    if hp : ∀ o ∈ incomplete, SoundOp o then
      return PLift.up (fun (hs : ∀ x, (sha256 x).size = 32) =>
        progress_exact hs (sound_of_list (fun x o h => (reach_stored (runReach incomplete) x o h).1) hp)
          (runInv incomplete) hq ha)
    else none
  else none

def tamperedSlice : ByteArray :=
  let s := Merkle.slice cipher 1
  s.set! 0 (s.get! 0 ^^^ 1)
def tampered : Op := mkOp [c, attachment.id]
  (.chunk rootHash cipher.size msgTime 1 tamperedSlice (Merkle.proof sha256 cipher 1))
def wrongIndex : Op := mkOp [c, attachment.id]
  (.chunk rootHash cipher.size msgTime 2 (Merkle.slice cipher 1) (Merkle.proof sha256 cipher 1))
def wrongSibling : Op := mkOp [c, attachment.id]
  (.chunk rootHash cipher.size msgTime 1 (Merkle.slice cipher 1) [sha256 "wrong sibling".toUTF8])
/-- Chunk 1 with a true slice and path, claimed at time 0 (where every
chunk sorted before `chunks_in_window`): not its attachment's time. -/
def timeZero : Op := mkOp [c, attachment.id]
  (.chunk rootHash cipher.size 0 1 (Merkle.slice cipher 1) (Merkle.proof sha256 cipher 1))
/-- The same file attached by its message's author, signed, but claimed
at time 0 instead of the message's. -/
def attachedAtZero := (attach c admission.id message.id 0 bob contentKey file).1

def main : IO UInt32 := do
  let t ← Checks.new
  t.ok "nonempty encrypted attachment spans exactly two chunks"
    (file.bytes.size == 70000 && cipher.size == 70016 && Merkle.nChunks cipher.size == 2)
  t.ok "real signed attachment is Valid" (certify full attachment attachmentFact).isSome
  t.ok "both actual chunk validity premises" ((certify full chunk0 (chunkFact 0)).isSome &&
    (certify full chunk1 (chunkFact 1)).isSome)
  t.ok "chunk_is_slice validator and no-collision premises under real SHA-256" sliceCertificate.isSome
  t.ok "chunk_unique relay validity and no-collision premises under real SHA-256" uniqueCertificate.isSome
  t.ok "progress_exact settled store and no-collision premises under real SHA-256" progressCertificate.isSome
  t.ok "checking a two-chunk file's chunk hashes a node: the climb runs"
    ((Merkle.verifyInputs sha256 cipher.size 1 (Merkle.slice cipher 1) (Merkle.proof sha256 cipher 1)).length == 3)
  t.ok "attachment composer emits the canonical chunk ops" (composed.2 == [chunk0, chunk1])
  t.ok "independent relay reconstructs identical canonical op" (relayed0 == chunk0)
  t.ok "incomplete store actually holds chunk index1" (certifyDB incomplete chunk1 (chunkFact 1)).isSome
  t.ok "out-of-order one-chunk progress is exactly 1 of 2" ((progress c attachment.id cipher.size).eval (run incomplete) == (1,2))
  t.ok "duplicate relay cannot increase progress" ((progress c attachment.id cipher.size).eval (run duplicated) == (1,2))
  t.ok "complete progress is exactly 2 of 2" ((progress c attachment.id cipher.size).eval (run full) == (2,2))
  t.ok "actual Merkle tree inputs each hash to32 bytes"
    ((Merkle.treeInputs sha256 cipher).all fun x => (sha256 x).size == 32)
  t.ok "valid chunks verify under actual SHA256"
    ((List.range 2).all fun i => Merkle.verify sha256 rootHash cipher.size i
      (Merkle.slice cipher i) (Merkle.proof sha256 cipher i))
  t.ok "tampering preserves length but changes payload"
    (tamperedSlice.size == (Merkle.slice cipher 1).size && tamperedSlice != Merkle.slice cipher 1)
  t.ok "tampered slice is rejected" ((run (incomplete ++ [tampered])).status tampered.id == some .invalid)
  t.ok "out-of-range index is rejected" ((run (incomplete ++ [wrongIndex])).status wrongIndex.id == some .invalid)
  t.ok "wrong sibling is rejected" ((run (incomplete ++ [wrongSibling])).status wrongSibling.id == some .invalid)
  t.ok "a chunk at time 0 is rejected" ((run (incomplete ++ [timeZero])).status timeZero.id == some .invalid)
  t.ok "an attachment at another time than its message is rejected"
    ((run (before ++ [attachedAtZero])).status attachedAtZero.id == some .invalid)
  t.ok "chunks_in_window applies to a real Valid chunk" windowCertificate.isSome
  t.ok "window_set_canonical applies to the fixture's ops in either order" canonicalCertificate.isSome
  t.ok "timed_chain_le applies to a real chunk's chain to its attachment" chainCertificate.isSome
  t.ok "the attachment and its chunks sort at the message's time (chunks_in_window)"
    (orderOf message == msgTime && orderOf attachment == msgTime && orderOf chunk0 == msgTime &&
      orderOf chunk1 == msgTime)
  t.ok "missing attachment leaves chunk unresolved"
    ((run (before ++ [chunk0])).status chunk0.id == none)
  t.ok "tamper cannot increase progress"
    ((progress c attachment.id cipher.size).eval (run (incomplete ++ [tampered, wrongIndex, wrongSibling])) == (1,2))
  t.finish "attachment vacuity (real crypto; no-collision premises decided on real SHA-256)"

end Vacuity.Attachment
