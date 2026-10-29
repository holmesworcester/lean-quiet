/- Run the RBSR answer/exchange code used by Conn.onRbsr on non-leaf
histories at the proved logarithmic depth. This is a one-round check,
not a claim of delivery or many-node liveness. -/
import ops.sync.Round
import tests.engine.Checks

open Engine Engine.Sync Tests

namespace ClaimTree

def key (n : Nat) : Key := ⟨n, n⟩
def ident (n : Nat) : ByteArray := (toString n).toUTF8

def check (ck : Checks) (P : Params) (n depth : Nat) : IO Unit := do
  let xs := (List.range n).map (· * 2)
  let ys := (List.range n).map (· * 3)
  let r : Range := ⟨⟨0, 0⟩, none⟩
  let claim := opening key ident sha256 P ys r
  let (give, want) := exchange key ident sha256 P depth xs ys claim
  let missingY := (xs.filter fun x => !ys.contains x).map ident
  let missingX := (ys.filter fun y => !xs.contains y).map ident
  let same := fun (a b : List ByteArray) => a.length == b.length && a.all b.contains && b.all a.contains
  ck.ok s!"non-leaf {n}: logarithmic depth gives exactly the missing ids" (same give missingY && same want missingX)
  let deeper := exchange key ident sha256 P (depth + 3) xs ys claim
  ck.ok s!"non-leaf {n}: deeper exchange is stable" (deeper == (give, want))
  ck.ok s!"non-leaf {n}: opening really is a fingerprint" (match claim with | .fp .. => true | _ => false)

end ClaimTree

def main : IO UInt32 := do
  let ck ← Checks.new
  ClaimTree.check ck { leaf := 4, fan := 4 } 64 6
  ClaimTree.check ck { leaf := 4, fan := 4 } 256 8
  ClaimTree.check ck {} 512 4
  ck.finish "claim-tree"
