import ops.community.Op

/-
A post: a message by an admitted device. Its header is clear (the key id,
the counter, the time, the signature, which covers the sealed bytes) and
its body sealed, so a keyless node judges a post as a member does. It
claims a counter, which orders its channel, and a time, which is shown.
Body tag 23, fact tags 21 and 23 (with a clump root).

`community.channel.message`: this op's body and fact, their bytes, and the lists its fact
is filed in. Its validator is Validate.lean; the family's registry, which
sums every op's body and fact, is ops/community/Family.lean.
-/

namespace Community
open Engine Codec

/-- A message's sort key: its counter, then its time, each capped, so
the order is (counter, time, id) (`msg_cmp`). -/
def msgKey (n tm : Nat) : ByteArray := be64 (min n countCap) ++ be64 (min tm timeCap)

namespace Post

/-- What its author writes and signs. -/
structure Body where
  ckey : ByteArray
  text : ByteArray
  n : Nat
  time : Nat
  sig : ByteArray
  deriving DecidableEq, Inhabited

instance : Codec Body := Codec.tagged 23 (fun x => (x.ckey, x.text, x.n, x.time, x.sig)) (fun (p : B × B × Nat × Nat × B) => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩) (fun _ => rfl)

@[simp] theorem Body.enc_tag (x : Body) : Codec.enc x = 23 :: Codec.enc (x.ckey, x.text, x.n, x.time, x.sig) := rfl

/-- The body with its signatures blanked: what the signatures cover. -/
def Body.unsigned (b : Body) : Body := { b with sig := .empty }



/-- Its fact, `message`. -/
structure Fact where
  c : Id
  u : Id
  device : ByteArray
  ckey : ByteArray
  text : ByteArray
  n : Nat
  time : Nat
  clump : Option Id := none
  deriving DecidableEq, Inhabited

/-- Its bytes: tag 21, or 23 with a clump root. -/
def Fact.enc : Fact → List UInt8
  | ⟨c, u, device, ckey, text, n, time, none⟩ => 21 :: Codec.enc (c, u, device, ckey, text, n, time)
  | ⟨c, u, device, ckey, text, n, time, (some root)⟩ => 23 :: Codec.enc (c, u, device, ckey, text, n, time, root)

def Fact.dec : List UInt8 → Option (Fact × List UInt8)
  | 21 :: r => decAs (fun (p : B × B × B × B × B × Nat × Nat) => (⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2, none⟩ : Fact)) r
  | 23 :: r => decAs (fun (p : B × B × B × B × B × Nat × Nat × B) => (⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1, some p.2.2.2.2.2.2.2⟩ : Fact)) r
  | _ => none

def Fact.encInto (buf : ByteArray) : Fact → ByteArray
  | ⟨c, u, device, ckey, text, n, time, none⟩ => Codec.encInto (buf.push 21) (c, u, device, ckey, text, n, time)
  | ⟨c, u, device, ckey, text, n, time, (some root)⟩ => Codec.encInto (buf.push 23) (c, u, device, ckey, text, n, time, root)

def Fact.decFrom (b : ByteArray) (i : Nat) : Option (Fact × Nat) :=
  match b[i]? with
  | some 21 => decFromAs (fun (p : B × B × B × B × B × Nat × Nat) => (⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2, none⟩ : Fact)) b (i + 1)
  | some 23 => decFromAs (fun (p : B × B × B × B × B × Nat × Nat × B) => (⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1, some p.2.2.2.2.2.2.2⟩ : Fact)) b (i + 1)
  | _ => none

instance : Codec Fact where
  enc := Fact.enc
  dec := Fact.dec
  round f rest := by
    rcases f with ⟨c, u, device, ckey, text, n, time, _ | root⟩ <;> simp only [Fact.enc, Fact.dec, List.cons_append] <;> exact decAs_enc _ _ _
  encInto := Fact.encInto
  encInto_eq buf x := by
    rcases x with ⟨c, u, device, ckey, text, n, time, _ | root⟩ <;> simp only [Fact.encInto, Fact.enc] <;> exact encInto_tag ..
  decFrom := Fact.decFrom
  decFrom_at x h := by
    rcases x with ⟨c, u, device, ckey, text, n, time, _ | root⟩ <;> simp only [Fact.enc] at h <;> simp only [Fact.decFrom, h.tag] <;>
      exact decFromAs_tag _ h

theorem Fact.enc_tag (x : Fact) : ∃ t l, Codec.enc x = t :: l ∧ (t = 21 ∨ t = 23) := by
  rcases x with ⟨c, u, device, ckey, text, n, time, _ | root⟩ <;> exact ⟨_, _, rfl, by simp⟩

/-- Where its fact sorts under its keys. -/
@[simp] def sortKey (f : Fact) : ByteArray := msgKey f.n f.time

/-! ## The lists its fact is filed in (`message.*`) -/
/-- A channel's messages, saturated ones included: the first, newest
first, has the highest counter (`topCount`). -/
def all : Rel Fact := ⟨"message", "all", fun f => some [f.c]⟩
@[simp] theorem all_args (f : Fact) : all.args f = (some [f.c]) := rfl
def byAuthor : Rel Fact := ⟨"message", "byAuthor", fun f => some [f.c, f.u]⟩
@[simp] theorem byAuthor_args (f : Fact) : byAuthor.args f = (some [f.c, f.u]) := rfl
/-- A community's messages sealed under content key kid, below the
counter cap: a device lists the ones it can read as the union over the
keys it holds, its receipts of saturated ones after them (`readable`). -/
def byKey : Rel Fact := ⟨"message", "byKey", fun f => if f.n < countCap then some [f.c, f.ckey] else none⟩
@[simp] theorem byKey_args (f : Fact) : byKey.args f = (if f.n < countCap then some [f.c, f.ckey] else none) := rfl
/-- Roots under an available key, for the conversation's outer list. -/
def rootsByKey : Rel Fact := ⟨"message", "rootsByKey", fun f => match f.clump with | none => if f.n < countCap then some [f.c, f.ckey] else none | some _ => none⟩
@[simp] theorem rootsByKey_args (f : Fact) : rootsByKey.args f = (match f.clump with | none => if f.n < countCap then some [f.c, f.ckey] else none | some _ => none) := rfl
/-- Each clump component owns its bounded child list. -/
def childrenByKey : Rel Fact := ⟨"message", "childrenByKey", fun f => match f.clump with | some root => if f.n < countCap then some [f.c, root, f.ckey] else none | none => none⟩
@[simp] theorem childrenByKey_args (f : Fact) : childrenByKey.args f = (match f.clump with | some root => if f.n < countCap then some [f.c, root, f.ckey] else none | none => none) := rfl

end Post

end Community
