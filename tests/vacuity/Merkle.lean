import engine.core.Merkle

namespace Vacuity.Merkle
open _root_.Merkle
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.defProp false
-- A nonempty attachment and an explicit hash model. This is NOT SHA-256.
-- It gives unique outputs to this file's leaf/root inputs and a third output
-- to other inputs, so nothing collides with what the root hashes: the laws'
-- no-collision premise is proved, not assumed, for every list of checked
-- inputs. One chunk: the real two-chunk climb under SHA-256 is exercised in
-- tests/vacuity/Attachment.lean.
def file : B := "A small attachment from Alice to Bob.".toUTF8
def hash (y : B) : B :=
  if y = leafIn file 0 then bytes32 1 else if y = tagRoot ++ be64 file.size ++ bytes32 1 then bytes32 2 else bytes32 0

theorem outputSize (x : B) : (hash x).size = 32 := by
  unfold hash
  split
  · rfl
  · split <;> rfl

theorem preimage : ∀ x ∈ treeInputs hash file, ∀ y, hash y = hash x → y = x := by
  have hra : tagRoot ++ be64 file.size ++ bytes32 1 ≠ leafIn file 0 := by decide
  have h01 : bytes32 0 ≠ bytes32 1 := by decide
  have h02 : bytes32 0 ≠ bytes32 2 := by decide
  have h12 : bytes32 1 ≠ bytes32 2 := by decide
  have hHa : hash (leafIn file 0) = bytes32 1 := by simp [hash]
  have hHr : hash (tagRoot ++ be64 file.size ++ bytes32 1) = bytes32 2 := by simp [hash, hra]
  have ht : treeInputs hash file = [tagRoot ++ be64 file.size ++ bytes32 1, leafIn file 0] := by
    have hd : depthOf (nChunks file.size) = 0 := by decide
    simp only [treeInputs, hd, subInputs, sub, leaves_hash]
    rw [hHa]
  rw [ht]
  intro x hx y hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · rw [hHr] at hy
    unfold hash at hy
    split at hy
    · exact absurd hy h12
    · split at hy
      · assumption
      · exact absurd hy h02
  · rw [hHa] at hy
    unfold hash at hy
    split at hy
    · assumption
    · split at hy
      · exact absurd hy.symm h12
      · exact absurd hy h01


theorem verifies : verify hash (fileRoot hash file) file.size 0 file [] = true := by decide +kernel

theorem noCollision (ys : List B) : NoCollision hash (treeInputs hash file) ys :=
  fun x hx y _ h => preimage x hx y h

def verifiedSlice := verify_sound (ct := file) (len := file.size) (i := 0) (s := file) (sibs := []) outputSize
  (noCollision _) verifies

theorem everyChunk : ∀ i < nChunks file.size,
    verify hash (fileRoot hash file) file.size i file [] = true := by
  intro i hi
  have count : nChunks file.size = 1 := by decide
  rw [count] at hi
  have : i = 0 := by omega
  subst i
  exact verifies

def assembled := complete_assembles (ct := file) outputSize (len := file.size) (fun _ => file) (fun _ => [])
  (fun _ _ => noCollision _) everyChunk

def notInjective := no_injective_hash outputSize

-- The existing empty-file satisfiability theorem and this nonempty extension.
theorem assumptions :
    (∃ H : B → B, (∀ x, (H x).size = 32) ∧ ∀ ys, NoCollision H (treeInputs H .empty) ys) ∧
    ((∀ ys, NoCollision hash (treeInputs hash file) ys) ∧ file.size > 0) :=
  ⟨assumptions_hold, noCollision, by decide⟩
-- Tampered content of the same size at a valid index: the size and index
-- checks pass, and only the hash comparison rejects it.
theorem tamperedSize : "A small attachment from Alice to Eve.".toUTF8.size = file.size := by decide
example : verify hash (fileRoot hash file) file.size 0 "A small attachment from Alice to Eve.".toUTF8 [] = false := by
  decide +kernel
-- An index past the chunk count is rejected by the range check.
example : verify hash (fileRoot hash file) file.size 1 file [] = false := by decide +kernel
end Vacuity.Merkle
