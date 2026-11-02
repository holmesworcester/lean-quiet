import tests.vacuity.IdentityTrust
import app.community.Proofs

/-! The community key's laws applied to real signed ops (Ed25519, X25519,
XChaCha20-Poly1305), over Reach-built stores; and the refusals they
stand for: a wrap without its author's signature, a post under another
key id, and a member's wrap of another key under the community's id. -/
namespace Vacuity.CommunityKey
open Engine Community Codec Tests Vacuity.Identity Vacuity.IdentityTrust

/-- A store's verdict on an op, with its proof, when it is Valid. -/
def validFact (ops : List Op) (o : Op) : Option (Σ' f : Fact, PLift (V ed25519 (run ops).ops o.id f)) :=
  match h : (run ops).status o.id with
  | some (.valid f) => some ⟨f, ⟨(runInv ops).sound _ _ h⟩⟩
  | _ => none

def valid (ops : List Op) (o : Op) : Bool := (validFact ops o).isSome
def invalid (ops : List Op) (o : Op) : Bool := (run ops).status o.id == some .invalid

/-! ## The ops -/

/-- Bob's node: the X25519 secret whose public key his request named. -/
def bobSecret : ByteArray := (Bytes.digest ("test node ".toUTF8 ++ bob.pk)).1
def bobNode := endpoint bobSecret

/-- Alice's wrap of the community key to Bob's node, citing his admission,
and the box it carries. -/
def honestEsk := Bytes.digest "vacuity-wrap-esk".toUTF8
def honest := wrapKey c c admission.id alice communityKey honestEsk (keyOf bob)
def honestBox := box cryptoSeal honestEsk (keyOf bob) keyId communityKey
def honestFact := Fact.wrap c keyId (keyOf bob) honestBox

/-- Another 32-byte key, sealed to Bob under the community's key id: what a
member who wants to read Bob's later posts would plant. The box opens at
Bob's node; only the key inside is wrong. -/
def otherKey : Key32 := ⟨⟨Array.replicate 32 99⟩, rfl⟩
def plantBox := box cryptoSeal (Bytes.digest "vacuity-plant-esk".toUTF8) (keyOf bob) keyId otherKey
def plant := wrap c c admission.id alice plantBox

/-- The same box with its signature blanked, and signed by Mallory (no
admission of hers is cited) while citing Alice's. -/
def unsigned := mkOp [c, c, admission.id] (.wrap plantBox .empty)
def forged := wrap c c admission.id mallory plantBox

/-- Bob's post under another key id than the root names. -/
def foreignPost := post c admission.id bob "another-key".toUTF8 "Under another key".toUTF8 2 29880003

def bobStore := before ++ [bobNode]
def planted := bobStore ++ [plant]
def wrapped := planted ++ [honest]

/-! ## The laws, applied -/

def rootKid := do
  let ⟨h⟩ ← certifyDB before r rootFact
  return PLift.up (show RootKid ed25519 (run before).ops c keyId from ⟨_, _, h⟩)

def rootKidUnique := do
  let ⟨h⟩ ← rootKid
  return PLift.up (rootKid_unique h h)

def postKey := applyLaw (certifyDB before message messageFact) post_community_key

def file : NewFile :=
  { info := { name := "a.qoi".toUTF8, kind := "image/qoi".toUTF8, w := 1, h := 1, preview := .empty },
    bytes := "one pixel".toUTF8, key := Bytes.digest "vacuity-file-key".toUTF8,
    nonce := Bytes.fit 24 "vacuity-file-nonce".toUTF8, metaNonce := Bytes.fit 24 "vacuity-meta-nonce".toUTF8 }
def attached := attach c admission.id message.id 29880000 bob communityKey file
def attachOps := before ++ [attached.1]

def attachKey : Option (PLift (∃ c' kid, RootKid ed25519 (run attachOps).ops c' kid)) := do
  let ⟨f, ⟨h⟩⟩ ← validFact attachOps attached.1
  match f, h with
  | .attachment c' _ _ _ _ _ kid _, h => return PLift.up ⟨c', kid, attach_community_key h⟩
  | _, _ => none

def keyKid := applyLaw
  (certifyDB keyed (contentKey c communityKey.1) (.key c keyId communityKey.1)) key_kid

def communityKidRoot :=
  if hq : (run before).queue = [] then
    if hk : (communityKid c).eval (run before) = some keyId then
      some (PLift.up (communityKid_root (runInv before) hq hk))
    else none
  else none

def currentKeyCommunity :=
  if hq : (run keyed).queue = [] then
    if hk : (currentKey c).eval (run keyed) = some communityKey then
      some (PLift.up (currentKey_community (runInv keyed) hq hk))
    else none
  else none

/-- Alice's store holding her copy of the key and Bob's post. -/
def keyedPosted : List Op := before ++ [contentKey c communityKey.1]

def postSealedCurrent := do
  let ⟨hp⟩ ← certifyDB keyedPosted message messageFact
  if hq : (run keyedPosted).queue = [] then
    if hk : (currentKey c).eval (run keyedPosted) = some communityKey then
      return PLift.up (post_sealed_current (runInv keyedPosted) hq hk hp)
    else none
  else none

def unwrapped (ops : List Op) : Write := (unwrap c).eval (run ops)

def unwrapCommunity : Option (PLift (∃ k : Key32, (communityKid c).eval (run wrapped) = some (kidOf cryptoSeal k) ∧
    (unwrapped wrapped).ops = [contentKey c k.1])) :=
  if h : (unwrapped wrapped).ops = [] then none
  else some ⟨(unwrap_community (run wrapped) c).resolve_left h⟩

def sendNonce : Nonce24 := Bytes.fit 24 "vacuity-send-nonce".toUTF8

def sendCommunity :=
  if hq : (run keyed).queue = [] then
    if hk : (currentKey c).eval (run keyed) = some communityKey then
      some (PLift.up (send_community_key (runInv keyed) hq hk (myAdm := c) (d := alice) sendNonce
        "Sealed by the sender's current key".toUTF8 29880005 []))
    else none
  else none

def wrapSigned := applyLaw (certifyDB wrapped honest honestFact) wrap_signed

def noWrapForgery (Signed : Key → ByteArray → Prop) := applyLaw (certifyDB wrapped honest honestFact)
  (fun h => fun hU : Unforgeable ed25519 _ Signed => no_wrap_forgery hU h)

/-- The shipped `unwrap` (before this change): every wrap to this node
that opens becomes a key, filed under the id of what it holds, and the
shipped `currentKey` took the first key row of c. Kept here to show the
plant it let in. -/
def unwrapShipped (c : Id) : View Fact Write := do
  let some (pk, sk) ← nodeKey | pure ⟨[]⟩
  let ws ← wrap.byRecipient.read [c, pk]
  let mut out : List Op := []
  for (_, f) in ws.rows do
    let .wrap _ kid _ bx := f | continue
    let held ← key.byId.read [kid] (limit := some 0)
    if held.total ≠ 0 then continue
    match unbox cryptoSeal sk kid bx with
    | some k => if !out.any (fun o => o.body == (contentKey c k.1).body) then
        out := out ++ [contentKey c k.1]
    | none => pure ()
  pure ⟨out⟩

def main : IO UInt32 := do
  let t ← Checks.new
  t.ok "rootKid_unique: Alice's root names the community key id" rootKidUnique.isSome
  t.ok "post_community_key: Bob's Valid post is under the root's key id" postKey.isSome
  t.ok "attach_community_key: Bob's Valid attachment is under the root's key id" attachKey.isSome
  t.ok "key_kid: Alice's local copy of the key is filed under its own hash" keyKid.isSome
  t.ok "communityKid_root: the store reads the root's key id" communityKidRoot.isSome
  t.ok "currentKey_community: Alice's currentKey is the community key" currentKeyCommunity.isSome
  t.ok "send_community_key: Alice's send seals under the root's key id" sendCommunity.isSome
  t.ok "post_sealed_current: Bob's post in Alice's store is under her current key" postSealedCurrent.isSome
  t.ok "unwrap_community: Bob takes the community key from Alice's wrap" unwrapCommunity.isSome
  t.ok "wrap_signed: Alice's signed wrap to Bob is Valid" wrapSigned.isSome
  t.ok "no_wrap_forgery: applies to Alice's actual wrap" (noWrapForgery (fun _ _ => True)).isSome
  -- the refusals the laws stand for, on real ops
  t.ok "a wrap with its signature blanked is Invalid" (invalid (bobStore ++ [unsigned]) unsigned)
  t.ok "a wrap signed by a device other than the admission it cites is Invalid"
    (invalid (bobStore ++ [forged]) forged)
  t.ok "the planted wrap itself is Valid: a member signed it, and its box is opaque" (valid planted plant)
  t.ok "the plant opens at Bob's node to a key of another id"
    ((unbox cryptoSeal (Bytes.fit 32 bobSecret) keyId plantBox).map (kidOf cryptoSeal ·) ==
      some (kidOf cryptoSeal otherKey) && kidOf cryptoSeal otherKey != keyId)
  t.ok "unwrap takes nothing from the plant" ((unwrapped planted).ops.isEmpty)
  t.ok "and takes the community key once Alice's wrap arrives"
    ((unwrapped wrapped).ops == [contentKey c communityKey.1])
  t.ok "the shipped unwrap took the planted key" (((unwrapShipped c).eval (run planted)).ops ==
    [contentKey c otherKey.1])
  t.ok "a post under another key id is Invalid" (invalid (before ++ [foreignPost]) foreignPost)
  t.ok "the same author's post under the root's key id is Valid" (valid before message)
  t.ok "currentKey answers nothing before the key is held" ((currentKey c).eval (run before) == none)
  t.finish "community key vacuity (real ops)"

end Vacuity.CommunityKey
