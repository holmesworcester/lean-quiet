import app.community.Op

/-
A user's private notification state, for that user's own devices: the
messages read (exact ids) and the notification level. Signed by one of
the user's admitted devices and sealed to one device's X25519 key; the
ciphertext syncs in the community like any op, and only that device
opens it (the payload is the app's: app/community/notice/Commands.lean).
After libquiet's notification preferences and read receipts (#844).
Body tag 20, fact tag 18.
-/

namespace Community
open Engine Codec

namespace Notice

/-- What its author writes and signs: the device it is sealed to, the
sealed payload, and the writer's revision (newer settings win). -/
structure Body where
  recipient : ByteArray
  box : ByteArray
  time : Nat
  sig : ByteArray
  deriving DecidableEq, Inhabited

instance : Codec Body := Codec.tagged 20 (fun x => (x.recipient, x.box, x.time, x.sig))
  (fun (p : B × B × Nat × B) => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩) (fun _ => rfl)

@[simp] theorem Body.enc_tag (x : Body) : Codec.enc x = 20 :: Codec.enc (x.recipient, x.box, x.time, x.sig) := rfl

/-- The body with its signature blanked: what the signature covers. -/
def Body.unsigned (b : Body) : Body := { b with sig := .empty }

/-- Its fact, `notice`: whose state it is (the user of the writer's
admission), for which device, sealed. -/
structure Fact where
  c : Id
  u : Id
  recipient : ByteArray
  box : ByteArray
  time : Nat
  deriving DecidableEq, Inhabited

instance : Codec Fact := Codec.tagged 18 (fun x => (x.c, x.u, x.recipient, x.box, x.time))
  (fun (p : B × B × B × B × Nat) => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩) (fun _ => rfl)

@[simp] theorem Fact.enc_tag (x : Fact) : Codec.enc x = 18 :: Codec.enc (x.c, x.u, x.recipient, x.box, x.time) := rfl

/-- Where its fact sorts under its keys: by revision, newest first. -/
@[simp] def sortKey (f : Fact) : ByteArray := be64 f.time

/-! ## The lists its fact is filed in (`notice.*`) -/
/-- What is sealed to one device in c: the only list a device reads. -/
def byRecipient : Rel Fact := ⟨"notice", "byRecipient", fun f => some [f.c, f.recipient]⟩
@[simp] theorem byRecipient_args (f : Fact) : byRecipient.args f = (some [f.c, f.recipient]) := rfl

end Notice

end Community
