import app.community.Op

/-
This device's receipt of a saturated post: where it orders past the
counter cap. Local.

`community.channel.message.receipt`: this op's body and fact, their bytes, and the lists its fact
is filed in. Its validator is Validate.lean; the family's registry, which
sums every op's body and fact, is app/community/Family.lean.
-/

namespace Community
open Engine Codec

/-- A receipt's sort key: after every counter below the cap, then by
this device's receipt counter, then by the message. -/
def recKey (k : Nat) (m : Id) : ByteArray := be64 countCap ++ be64 k ++ m

namespace Receive

/-- What its author writes. -/
structure Body where
  k : Nat
  deriving DecidableEq, Inhabited

instance : Codec Body := Codec.tagged 24 (fun x => x.k) (fun (p : Nat) => ⟨p⟩) (fun _ => rfl)

@[simp] theorem Body.enc_tag (x : Body) : Codec.enc x = 24 :: Codec.enc x.k := rfl

/-- Nothing to blank: the body is unsigned. -/
def Body.unsigned (b : Body) : Body := b


/-- Its fact, `received`. -/
structure Fact where
  c : Id
  kid : Id
  msg : Id
  k : Nat
  clump : Option Id := none
  deriving DecidableEq, Inhabited

/-- Its bytes: tag 22, or 24 with a clump root. -/
def Fact.enc : Fact → List UInt8
  | ⟨c, kid, msg, k, none⟩ => 22 :: Codec.enc (c, kid, msg, k)
  | ⟨c, kid, msg, k, (some root)⟩ => 24 :: Codec.enc (c, kid, msg, k, root)

def Fact.dec : List UInt8 → Option (Fact × List UInt8)
  | 22 :: r => decAs (fun (p : B × B × B × Nat) => (⟨p.1, p.2.1, p.2.2.1, p.2.2.2, none⟩ : Fact)) r
  | 24 :: r => decAs (fun (p : B × B × B × Nat × B) => (⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, some p.2.2.2.2⟩ : Fact)) r
  | _ => none

def Fact.encInto (buf : ByteArray) : Fact → ByteArray
  | ⟨c, kid, msg, k, none⟩ => Codec.encInto (buf.push 22) (c, kid, msg, k)
  | ⟨c, kid, msg, k, (some root)⟩ => Codec.encInto (buf.push 24) (c, kid, msg, k, root)

def Fact.decFrom (b : ByteArray) (i : Nat) : Option (Fact × Nat) :=
  match b[i]? with
  | some 22 => decFromAs (fun (p : B × B × B × Nat) => (⟨p.1, p.2.1, p.2.2.1, p.2.2.2, none⟩ : Fact)) b (i + 1)
  | some 24 => decFromAs (fun (p : B × B × B × Nat × B) => (⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, some p.2.2.2.2⟩ : Fact)) b (i + 1)
  | _ => none

instance : Codec Fact where
  enc := Fact.enc
  dec := Fact.dec
  round f rest := by
    rcases f with ⟨c, kid, msg, k, _ | root⟩ <;> simp only [Fact.enc, Fact.dec, List.cons_append] <;> exact decAs_enc _ _ _
  encInto := Fact.encInto
  encInto_eq buf x := by
    rcases x with ⟨c, kid, msg, k, _ | root⟩ <;> simp only [Fact.encInto, Fact.enc] <;> exact encInto_tag ..
  decFrom := Fact.decFrom
  decFrom_at x h := by
    rcases x with ⟨c, kid, msg, k, _ | root⟩ <;> simp only [Fact.enc] at h <;> simp only [Fact.decFrom, h.tag] <;>
      exact decFromAs_tag _ h

theorem Fact.enc_tag (x : Fact) : ∃ t l, Codec.enc x = t :: l ∧ (t = 22 ∨ t = 24) := by
  rcases x with ⟨c, kid, msg, k, _ | root⟩ <;> exact ⟨_, _, rfl, by simp⟩

/-- Where its fact sorts under its keys. -/
@[simp] def sortKey (f : Fact) : ByteArray := recKey f.k f.msg

/-! ## The lists its fact is filed in (`received.*`) -/
/-- This device's receipts of c's saturated messages under content key
kid, in the order it received them: where `readable` lists them. -/
def byKey : Rel Fact := ⟨"received", "byKey", fun f => some [f.c, f.kid]⟩
@[simp] theorem byKey_args (f : Fact) : byKey.args f = (some [f.c, f.kid]) := rfl
/-- This device's receipts in c: the newest one's counter is the next
one's less one (`topReceived`). -/
def all : Rel Fact := ⟨"received", "all", fun f => some [f.c]⟩
@[simp] theorem all_args (f : Fact) : all.args f = (some [f.c]) := rfl
/-- Whether this device has received message m. -/
def byMsg : Rel Fact := ⟨"received", "byMsg", fun f => some [f.msg]⟩
@[simp] theorem byMsg_args (f : Fact) : byMsg.args f = (some [f.msg]) := rfl
def rootsByKey : Rel Fact := ⟨"received", "rootsByKey", fun f => match f.clump with | none => some [f.c, f.kid] | some _ => none⟩
@[simp] theorem rootsByKey_args (f : Fact) : rootsByKey.args f = (match f.clump with | none => some [f.c, f.kid] | some _ => none) := rfl
def childrenByKey : Rel Fact := ⟨"received", "childrenByKey", fun f => match f.clump with | some root => some [f.c, root, f.kid] | none => none⟩
@[simp] theorem childrenByKey_args (f : Fact) : childrenByKey.args f = (match f.clump with | some root => some [f.c, root, f.kid] | none => none) := rfl

end Receive

end Community
