import app.community.Op

/-
A user's private notification state, for that user's own devices: the
messages read (exact ids) and the notification level. Signed by one of
the user's admitted devices and sealed to one device's X25519 key (the
payload is the app's: app/community/Commands.lean). Local for now: it
never leaves this device, so no member learns when this user reads or
changes a setting. With device linking it travels only between the
user's own devices (docs/NOTIFICATIONS.md). After libquiet's
notification preferences and read receipts (#844). Body tag 20, fact
tag 18.
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

/-! ## The sealed payload (the app's; validators never open it) -/

/-- A notification level (libquiet's): every message, only mentions and
direct messages, or none. -/
inductive Level where
  | all | mentions | off
  deriving BEq, DecidableEq, Inhabited, Repr

/-- A level's code in a payload; 0 is "inherit". -/
def Level.code : Option Level → Nat
  | none => 0 | some .all => 1 | some .mentions => 2 | some .off => 3

def Level.ofCode : Nat → Option Level
  | 1 => some .all | 2 => some .mentions | 3 => some .off | _ => none

theorem Level.ofCode_code (l : Option Level) : Level.ofCode (Level.code l) = l := by
  cases l with
  | none => rfl
  | some l => cases l <;> rfl

/-- A user's notification settings: the community's level, a
conversation's (it outranks the community's, even Off), and whether
thread replies notify (conversation, then community). -/
structure Settings where
  community : Option Level := none
  conversation : Option Level := none
  replies : Option Bool := none
  communityReplies : Option Bool := none
  deriving BEq, DecidableEq, Inhabited, Repr

/-- What a notice seals: the exact messages newly read; the writer's
current levels (community, conversation; 0 inherits); and the revision
those levels were set at. Every notice carries the settings it knew, so
the newest few notices hold the newest settings, and a read written
concurrently with a settings change cannot undo it (the higher settings
revision wins). -/
abbrev Payload := List Id × Nat × Nat × Nat

/-- The associated data a payload is sealed under: it binds the box to
its community and its user, so a box cannot be moved to another. -/
def binding (c u : Id) : ByteArray := Codec.encode ("quiet/notify/v1".toUTF8, c, u)

end Notice

end Community
