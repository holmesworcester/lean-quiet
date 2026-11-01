import engine.core.Merkle

namespace Vacuity.Merkle
open _root_.Merkle
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option linter.defProp false
-- A nonempty attachment and an explicit hash model. This is NOT SHA-256.
-- It gives unique outputs to this file's leaf/root inputs and a third output
-- to other inputs. The universal second-preimage premise is proved, not assumed.
def file : B := "A small attachment from Alice to Bob.".toUTF8
def hash (y : B) : B :=
  if y = leafIn file 0 then bytes32 1 else if y = tagRoot ++ be64 file.size ++ bytes32 1 then bytes32 2 else bytes32 0

theorem outputSize (x : B) : (hash x).size = 32 := by
  unfold hash
  split
  · rfl
  · split <;> rfl

theorem preimage : NoSecondPreimage hash (treeInputs hash file) := by
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

def verifiedSlice := verify_sound (ct := file) (len := file.size) (i := 0) (s := file) (sibs := []) outputSize preimage verifies

theorem everyChunk : ∀ i < nChunks file.size,
    verify hash (fileRoot hash file) file.size i file [] = true := by
  intro i hi
  have count : nChunks file.size = 1 := by decide
  rw [count] at hi
  have : i = 0 := by omega
  subst i
  exact verifies

def assembled := complete_assembles (ct := file) outputSize preimage (len := file.size) (fun _ => file) (fun _ => []) everyChunk

def notInjective := no_injective_hash outputSize

-- The existing empty-file satisfiability theorem and this nonempty extension.
theorem assumptions :
    (∃ H : B → B, (∀ x, (H x).size = 32) ∧ NoSecondPreimage H (treeInputs H .empty)) ∧
    (NoSecondPreimage hash (treeInputs hash file) ∧ file.size > 0) :=
  ⟨assumptions_hold, preimage, by decide⟩
example : verify hash (fileRoot hash file) file.size 0 "tampered attachment".toUTF8 [] = false := by decide +kernel
example : verify hash (fileRoot hash file) file.size 1 file [] = false := by decide +kernel
end Vacuity.Merkle
