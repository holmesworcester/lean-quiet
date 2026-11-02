import tests.vacuity.IdentityTrust
import app.community.Screen
import app.community.channel.message.View
import app.community.key.View
import app.community.profile.View
import app.community.Proofs

namespace Vacuity.IdentityMessages
open Engine Community Codec Tests Kinds Vacuity.Identity Vacuity.IdentityTrust
set_option linter.defProp false

def content : Key32 := communityKey
def nonce : Nonce24 := ⟨⟨Array.replicate 24 43⟩, rfl⟩
def plaintext := "Hello Alice — a sealed message from Bob."
def kid := kidOf cryptoSeal content
def post1 := sealedPost c admission.id bob content nonce plaintext.toUTF8 1 29880000
def post2 := sealedPost c admission.id bob content ⟨⟨Array.replicate 24 44⟩, rfl⟩ "Second message".toUTF8 2 1
def localKey := contentKey c content.1
def bobName := profile c admission.id bob "Bob".toUTF8 29880001
def scene := before ++ [post1,post2,localKey,bobName]
def cipher1 := nonce.1 ++ sealBody cryptoSeal content nonce c kid plaintext.toUTF8
def cipher2 := (⟨Array.replicate 24 44⟩ : ByteArray) ++
  sealBody cryptoSeal content ⟨⟨Array.replicate 24 44⟩, rfl⟩ c kid "Second message".toUTF8
def fact1 := Fact.message c requestB.id bob.pk kid cipher1 1 29880000
def fact2 := Fact.message c requestB.id bob.pk kid cipher2 2 1

def Shown (db : DB Fact) (msg : Id) : Prop :=
  ∃ c' u dev kid' sealed n tm clump,
    ViewLaws.factIn db msg = some (.message c' u dev kid' sealed n tm clump)

def messageOwn : Option (PLift (Shown (run scene) post1.id)) :=
  match h : (Message.readOwn (m := ViewLaws.Model) post1.id).run (run scene) with
  | none => none
  | some (d,deps) => some ⟨by
      obtain ⟨c',u,dev,kid',sealed,n,tm,clump,hf,_⟩ := ViewLaws.message_own (run scene) post1.id d deps h
      exact ⟨c',u,dev,kid',sealed,n,tm,clump,hf⟩⟩

def profileRead := ViewLaws.profile_read (run scene) c requestB.id #[]

def readableComplete := do
  let ⟨hm⟩ ← certifyDB scene post1 fact1
  let ⟨hk⟩ ← certifyDB scene localKey (.key c kid content)
  if hq : (run scene).queue = [] then
    return PLift.up (readable_complete (runInv scene) hq c false hm hk)
  else none

def row1 := ((msgKey 1 29880000,post1.id),fact1)
def visible := ((readable c none false).eval (run scene)).rows

def readableHeld :=
  if hq : (run scene).queue = [] then
    if hp : visible.any (fun p => decide (p = row1)) = true then
      some (PLift.up (readable_held (runInv scene) hq c none false none none (by
        obtain ⟨p,hp,he⟩ := List.any_eq_true.1 hp
        have he' : p = row1 := of_decide_eq_true he
        exact he' ▸ hp)))
    else none
  else none

def orderTotal := if hq : (run scene).queue = [] then
  some (PLift.up (order_total (runInv scene) hq c none false none none)) else none

def messageCompare := msg_cmp (c := c) (u := requestB.id) (d := bob.pk) (kid := kid)
  (sealed := cipher1) (n := 1) (tm := 29880000) (clump := none)
  (c' := c) (u' := requestB.id) (d' := bob.pk) (kid' := kid)
  (sealed' := cipher2) (n' := 2) (tm' := 1) (clump' := none) post1.id post2.id

def timeIsDisplay := time_is_display (c := c) (u := requestB.id) (d := bob.pk) (kid := kid)
  (sealed := cipher1) (n := 1) (clump := none)
  (c' := c) (u' := requestB.id) (d' := bob.pk) (kid' := kid)
  (sealed' := cipher2) (n' := 2) (clump' := none)
  (by decide +kernel) 29880000 1 post1.id post2.id

-- One local secret written by this node, then a peer job attempting to plant
-- another secret alongside a shared message. Fed records the actual intake.
def mySecret := secret (sha256 "vacuity-bob".toUTF8)
def peerSecret := secret (sha256 "vacuity-mallory".toUTF8)
def ownStore : DB Fact := (intake (family ed25519) true [mySecret]).foldl (fun s o => ingestS o s) DB.empty
def fedStore : DB Fact := (intake (family ed25519) false [peerSecret,post1]).foldl (fun s o => ingestS o s) ownStore

theorem fed : Fed (family ed25519) [mySecret] fedStore :=
  Fed.job false [peerSecret,post1] (Fed.job true [mySecret] Fed.empty)

/-- A Community op is never ephemeral, so this node's own job keeps it. -/
theorem mySecretDurable : (family ed25519).durable mySecret = true := by
  simp [Family.durable, Community.family, Community.scopeOf, mySecret, secret, body_mkOp,
    Community.Body.isEphemeral, Community.Body.isLocal]

def intakeLocal := if hl : (family ed25519).room mySecret = none then
  some (PLift.up (intake_local (family ed25519) (mine := true) (ops := [mySecret])
    (List.mem_filter.2 ⟨List.mem_filter.2 ⟨List.mem_singleton.2 rfl, mySecretDurable⟩,
      by simp [Op.capped, mySecret, secret, maxReqs]⟩) hl)) else none

def storedLocal := if hx : fedStore.ops mySecret.id = some mySecret then
  if hl : (family ed25519).room mySecret = none then
    some (PLift.up (stored_local fed hx hl))
  else none
else none

def localFactMine :=
  if hv : specAt (family ed25519) fedStore.ops 1 mySecret.id =
      some (.valid (.secret bob.pk (sha256 "vacuity-bob".toUTF8))) then
    some (PLift.up (local_fact_mine fed (show V ed25519 fedStore.ops mySecret.id
      (.secret bob.pk (sha256 "vacuity-bob".toUTF8)) from ⟨1,hv⟩) rfl))
  else none

def main : IO UInt32 := do
  let t ← Checks.new
  t.ok "message_own actual decrypted row" messageOwn.isSome
  t.ok "readable_complete actual message and local key" readableComplete.isSome
  t.ok "readable_held actual nonempty row" readableHeld.isSome
  t.ok "order_total on two signed sealed messages" orderTotal.isSome
  let own := (Message.readOwn (m := ViewLaws.Model) post1.id).run (run scene)
  t.ok "exact plaintext, author name and time" (own.any fun (d,_) =>
    d.text == plaintext && d.time == 29880000 &&
    ((Profile.author (m := ViewLaws.Model) c d.author).run (run scene)).1.1 == "Bob")
  t.ok "owned row exact author, plaintext and time" (own.any fun (d,deps) =>
    d.author == requestB.id && d.text == plaintext && d.time == 29880000 && deps.size == 2)
  -- the fixture's own post (counter 1) is under the community key too
  t.ok "readable includes both posts in counter order despite reverse times"
    (visible.length == 3 && (visible.map (fun pf => pf.1.2)).filter (· != message.id) == [post1.id,post2.id])
  t.ok "message comparator prioritizes counter" (Pos.cmp (sortOf fact1,post1.id) (sortOf fact2,post2.id) == .lt)
  t.ok "profile view names Bob" (((Profile.read (m := ViewLaws.Model) c requestB.id #[]).run (run scene)).1.name == "Bob")
  let noKey := run (before ++ [post1,bobName])
  t.ok "without key no row is shown" (((Message.readOwn (m := ViewLaws.Model) post1.id).run noKey).isNone)
  t.ok "without key no message is listed" (((readable c none false).eval noKey).rows.isEmpty)
  let wrongKey := contentKey c ⟨Array.replicate 32 42⟩
  t.ok "different content key cannot reveal row"
    (((Message.readOwn (m := ViewLaws.Model) post1.id).run (run (before ++ [post1,wrongKey]))).isNone)
  t.ok "intake_local accepts actual own local secret" intakeLocal.isSome
  t.ok "stored_local after own and hostile peer jobs" storedLocal.isSome
  t.ok "local_fact_mine actual valid secret" localFactMine.isSome
  t.ok "peer cannot plant its secret" (fedStore.ops peerSecret.id == none)
  t.ok "peer shared op still received" (fedStore.ops post1.id == some post1)
  t.finish "message views vacuity (real sealed messages)"

end Vacuity.IdentityMessages
