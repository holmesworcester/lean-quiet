import tests.vacuity.IdentityLifecycle

namespace Vacuity.IdentityFrames
open Engine Engine.Sync Codec Tests Connection Vacuity.Identity Vacuity.IdentityConnection
open Vacuity.IdentityLifecycle (addr endpointB)
set_option linter.defProp false

def nonce := (sha256 "vacuity-frame-nonce".toUTF8).extract 0 24
def payload := message.bytes
def incoming (s : IdentityConnection.Session) := Frame.seal sodium s.reply.id s.recvKey nonce payload
def damaged (s : IdentityConnection.Session) : ByteArray := ⟨(incoming s).data.modify 57 fun b => b ^^^ 1⟩
def held (s : IdentityConnection.Session) : Held F := ⟨activeOps s,run (activeOps s)⟩
instance : Fresh (HeldM F) := ⟨pure eA⟩
def sync : Sync F (HeldM F) := {fam,cfg := {},hooks := Connection.hooks fam sodium addr}
def nodeState (s : IdentityConnection.Session) := Node.boot fam (activeOps s) 0

def initiatorEstablished (s : IdentityConnection.Session) := Established.op s.reply.id s.req.id (Eph.op eB s.req.id).id endpointB.id

-- The endpoint validation premises are checked here. The size-aware suite.Good
-- contract remains a universal native-crypto assumption, not a finite test result.
def establishedAgrees (s : IdentityConnection.Session) :=
  if hn : pkA ≠ pkB then
    if hr : check sodium (established s) .established
      [.inr (.connection s.req.id s.m2), .inr (.request pkA pkB s.m1),
       .inr (.eph s.reply.id (sodium.suite.pub eA) eA), .inl (.endpoint pkA staticA)] =
      some (.established s.reply.id c pkB s.hash s.sendKey s.recvKey false) then
      if hi : check sodium (initiatorEstablished s) .established
        [.inr (.connection s.req.id s.m2), .inr (.request pkA pkB s.m1),
         .inr (.eph s.req.id (sodium.suite.pub eB) eB), .inl (.endpoint pkB staticB)] =
        some (.established s.reply.id c pkA s.hash s.recvKey s.sendKey true) then
        some (PLift.up (fun hg : sodium.suite.Good => established_agrees sodium hg rfl rfl hn hr hi))
      else none
    else none
  else none

-- Each premise is checked for the actual session key, nonce, signed payload and
-- associated session ID, then the production theorem is applied without any
-- remaining universal crypto premise.
def openSeal (s : IdentityConnection.Session) :=
  if hc : s.reply.id.size = 32 then
    if hn : nonce.size = 24 then
      if hd : sodium.fdec s.recvKey nonce (Frame.ad s.reply.id)
          (sodium.fenc s.recvKey nonce (Frame.ad s.reply.id) payload) = some payload then
        if he : (sodium.fenc s.recvKey nonce (Frame.ad s.reply.id) payload).size = payload.size + 16 then
          some (PLift.up (open_seal hd he hc hn))
        else none
      else none
    else none
  else none

def cidSeal (s : IdentityConnection.Session) :=
  if hc : s.reply.id.size = 32 then
    if hn : nonce.size = 24 then
      if he : (sodium.fenc s.recvKey nonce (Frame.ad s.reply.id) payload).size = payload.size + 16 then
        some (PLift.up (cid_seal he hc hn))
      else none
    else none
  else none

/-- `established_agrees_sodium`: the same real session; the one premise left
is the crypto trust file. -/
def establishedAgreesSodium (s : IdentityConnection.Session) :=
  if hn : pkA ≠ pkB then
    if hr : check sodium (established s) .established
      [.inr (.connection s.req.id s.m2), .inr (.request pkA pkB s.m1),
       .inr (.eph s.reply.id (sodium.suite.pub eA) eA), .inl (.endpoint pkA staticA)] =
      some (.established s.reply.id c pkB s.hash s.sendKey s.recvKey false) then
      if hi : check sodium (initiatorEstablished s) .established
        [.inr (.connection s.req.id s.m2), .inr (.request pkA pkB s.m1),
         .inr (.eph s.req.id (sodium.suite.pub eB) eB), .inl (.endpoint pkB staticB)] =
        some (.established s.reply.id c pkA s.hash s.recvKey s.sendKey true) then
        some (PLift.up (fun t : Trust.NativeCrypto => established_agrees_sodium t rfl rfl hn hr hi))
      else none
    else none
  else none

/-- `open_seal_sodium`: the real session's id, receive key and nonce, sized
once (`Bytes.of?`, as `sealFor` does); the trust file is the one premise. -/
def openSealSodium (s : IdentityConnection.Session) :
    Option (PLift (Trust.NativeCrypto → Frame.open sodium s.recvKey (incoming s) = some (s.reply.id, payload))) :=
  match hc : Bytes.of? (n := 32) s.reply.id, hk : Bytes.of? (n := 32) s.recvKey,
      hn : Bytes.of? (n := 24) nonce with
  | some cid, some k, some n =>
    if hp : payload.size < Crypto.maxPlaintext then
      some (PLift.up (fun t => by
        have := open_seal_sodium t cid k n hp
        rwa [Bytes.of?_eq_some hc, Bytes.of?_eq_some hk, Bytes.of?_eq_some hn] at this))
    else none
  | _, _, _ => none

def cidSealSodium (s : IdentityConnection.Session) :
    Option (PLift (Trust.NativeCrypto → Frame.cid (incoming s) = some s.reply.id)) :=
  match hc : Bytes.of? (n := 32) s.reply.id, hk : Bytes.of? (n := 32) s.recvKey,
      hn : Bytes.of? (n := 24) nonce with
  | some cid, some k, some n =>
    if hp : payload.size < Crypto.maxPlaintext then
      some (PLift.up (fun t => by
        have := cid_seal_sodium t cid k n hp
        rwa [Bytes.of?_eq_some hc, Bytes.of?_eq_some hk, Bytes.of?_eq_some hn] at this))
    else none
  | _, _, _ => none

/-- `sealFor_opens`: the running `sealFor`, on the real session's held keys. -/
def sealed (s : IdentityConnection.Session) := ((sealFor sodium s.reply.id payload : HeldM F _) (held s)).1

def sealForOpens (s : IdentityConnection.Session) :
    Option (PLift (Trust.NativeCrypto → ∃ f, sealed s = some f ∧ ∃ sk rk,
      ((sessionKeys s.reply.id : HeldM F _) (held s)).1 = some (sk, rk) ∧
        Frame.open sodium sk f = some (s.reply.id, payload))) :=
  match h : sealed s with
  | some f =>
    if hp : payload.size < Crypto.maxPlaintext then
      some (PLift.up (fun t => ⟨f, rfl, sealFor_opens t hp h⟩))
    else none
  | none => none

def openFrameAuth (s : IdentityConnection.Session) :=
  if ho : ((openFrame sodium (incoming s) : HeldM F _) (held s)).1 = some (s.reply.id,payload) then
    some (PLift.up (openFrame_auth ho))
  else none

def sealedAuth (s : IdentityConnection.Session) :=
  let f := damaged s
  if hc : Frame.cid f = some s.reply.id then
    if hk : ((sessionKeys s.reply.id : HeldM F _) (held s)).1 = some (s.sendKey,s.recvKey) then
      if hd : sodium.fdec s.recvKey (f.extract 33 57) (Frame.ad s.reply.id) (f.extract 57 f.size) = none then
        some (PLift.up (sealed_auth sync rfl (nodeState s) addr f 100 (held s) (by
          intro cid sk rk hcid hkey
          rw [hc] at hcid; cases hcid
          rw [hk] at hkey; cases hkey
          exact hd)))
      else none
    else none
  else none

def main : IO UInt32 := do
  let t ← Checks.new
  let some s := session | IO.eprintln "Could not construct real Noise session"; return 1
  t.ok "both real endpoint validations (Good assumption remains)" (establishedAgrees s).isSome
  t.ok "open_seal checks every premise for the real session" (openSeal s).isSome
  t.ok "cid_seal checks every premise for the real session" (cidSeal s).isSome
  for len in [0, 31, 33] do
    let badKey : ByteArray := ⟨Array.replicate len 7⟩
    t.ok s!"{len}-byte frame key cannot discharge open_seal premises"
      (!(openSeal {s with recvKey := badKey}).isSome)
    t.ok s!"{len}-byte frame key cannot discharge cid_seal premise"
      (!(cidSeal {s with recvKey := badKey}).isSome)
    t.ok s!"{len}-byte receive key rejects valid frame"
      (Frame.open sodium badKey (incoming s) == none)
  for len in [0, 23, 25] do
    let badNonce : ByteArray := ⟨Array.replicate len 9⟩
    t.ok s!"{len}-byte nonce produces rejected frame"
      (Frame.open sodium s.recvKey (Frame.seal sodium s.reply.id s.recvKey badNonce payload) == none)
  t.ok "established_agrees_sodium receives every premise of the real session" (establishedAgreesSodium s).isSome
  t.ok "open_seal_sodium receives every premise of the real session" (openSealSodium s).isSome
  t.ok "cid_seal_sodium receives every premise of the real session" (cidSealSodium s).isSome
  t.ok "the running sealFor seals for the real session" (sealForOpens s).isSome
  t.ok "what the running sealFor sealed opens under the session's key"
    ((sealed s).bind (Frame.open sodium s.sendKey) == some (s.reply.id, payload))
  t.ok "and not under the other direction's key"
    ((sealed s).bind (Frame.open sodium s.recvKey) == none)
  t.ok "a session this node holds no keys for seals nothing"
    (((sealFor sodium (sha256 "no such session".toUTF8) payload : HeldM F _) (held s)).1.isNone)
  t.ok "real authenticated frame applies openFrame_auth" (openFrameAuth s).isSome
  t.ok "damaged real frame applies sealed_auth" (sealedAuth s).isSome
  t.ok "valid sized frame roundtrips actual signed message bytes"
    (Frame.open sodium s.recvKey (incoming s) == some (s.reply.id,payload))
  t.ok "header names actual session" (Frame.cid (incoming s) == some s.reply.id)
  t.ok "wrong directional key rejected" (Frame.open sodium s.sendKey (incoming s) == none)
  t.ok "damaged ciphertext rejected" (Frame.open sodium s.recvKey (damaged s) == none)
  let headerDamage : ByteArray := ⟨(incoming s).data.modify 5 fun b => b ^^^ 1⟩
  t.ok "damaged associated session ID rejected" (Frame.open sodium s.recvKey headerDamage == none)
  let out := (nodeState s).onFrame sync addr (tagged sealedTag (damaged s)) 100 (held s)
  t.ok "rejected frame emits no sends/drops/stores" (out.1.2.send.isEmpty && out.1.2.drop.isEmpty && out.1.2.stored.isEmpty)
  t.ok "rejected frame preserves actual database/log" (out.2.db.stored == (held s).db.stored && out.2.log == (held s).log)
  t.finish "real handshake and authenticated frame premise checks"

end Vacuity.IdentityFrames
