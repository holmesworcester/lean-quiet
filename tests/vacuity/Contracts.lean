import tests.vacuity.SealAudit
import tests.vacuity.Session
import tests.vacuity.Merkle

namespace Vacuity.Contracts
open Engine Connection.Noise
set_option linter.defProp false

def noiseBadKey : Option (PLift (¬ suite.Good)) :=
  if h : suite.dec .empty 0 "ad".toUTF8 (suite.enc .empty 0 "ad".toUTF8 "nonempty".toUTF8) = none then
    some ⟨fun g => by
      have good := g.dec_enc .empty 0 "ad".toUTF8 "nonempty".toUTF8
      rw [h] at good
      cases good⟩
  else none

-- The symbolic suite does satisfy its contract. The separate Session fixtures
-- exercise it with four distinct roles and nonempty payloads.
def symbolicGood : Symbolic.sym.Good := Symbolic.good

def main : IO UInt32 := do
  let t ← Tests.Checks.new
  t.ok "actual Noise suite violates unrestricted Good on empty key" noiseBadKey.isSome
  let key : ByteArray := ⟨Array.replicate 32 3⟩
  t.ok "correct-size Noise key opens what it seals"
    (suite.dec key 0 "ad".toUTF8 (suite.enc key 0 "ad".toUTF8 "nonempty".toUTF8) == some "nonempty".toUTF8)
  return ← t.finish "contract vacuity"
end Vacuity.Contracts
