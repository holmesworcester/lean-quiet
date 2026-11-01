import app.connection.Family
import engine.sync.NoticeLaws

namespace Connection
open Engine Engine.Sync Codec
section
variable [fr : Fresh (Model F)]

/-- A receipt is a Community op: no Connection body decodes from it. -/
theorem receipt_not_send (m : Id) (j : Nat) (a : B) :
    (decode (Community.receipt m j).body : Option Body) ≠ some (.send a) := by
  intro h
  rw [decode_some] at h
  have : (Community.receipt m j).body.data.toList = 24 :: Codec.enc j := by
    simp [Community.receipt, Community.mkOp, Op.make, encode, Codec.enc, Community.Body.enc]
  rw [this] at h
  simp [Codec.enc, Body.enc] at h

end
end Connection
