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

-- The finite validation premises can be checked, but the theorem's suite.Good
-- assumption cannot: its unqualified AEAD law is false for malformed keys.
def establishedAgrees (s : IdentityConnection.Session) :=
  if hn : pkA ≠ pkB then
    if hr : Established.check sodium (established s)
      [.inr (.connection s.req.id s.m2), .inr (.request pkA pkB s.m1),
       .inr (.eph s.reply.id (sodium.suite.pub eA) eA), .inl (.endpoint pkA staticA)] =
      some (.established s.reply.id c pkB s.hash s.sendKey s.recvKey false) then
      if hi : Established.check sodium (initiatorEstablished s)
        [.inr (.connection s.req.id s.m2), .inr (.request pkA pkB s.m1),
         .inr (.eph s.req.id (sodium.suite.pub eB) eB), .inl (.endpoint pkB staticB)] =
        some (.established s.reply.id c pkA s.hash s.recvKey s.sendKey true) then
        some (PLift.up (fun hg : sodium.suite.Good => established_agrees sodium hg rfl rfl hn hr hi))
      else none
    else none
  else none

def frameDecrypts := ∀ k n ad p, sodium.fdec k n ad (sodium.fenc k n ad p) = some p
def frameSize := ∀ k n ad p, (sodium.fenc k n ad p).size = p.size + 16

def openSeal (s : IdentityConnection.Session) :=
  if hc : s.reply.id.size = 32 then
    if hn : nonce.size = 24 then
      some (PLift.up (fun hd : frameDecrypts => fun he : frameSize =>
        open_seal (K := sodium) (sk := s.recvKey) (p := payload) hd he hc hn))
    else none
  else none

def cidSeal (s : IdentityConnection.Session) :=
  if hc : s.reply.id.size = 32 then
    if hn : nonce.size = 24 then
      some (PLift.up (fun he : frameSize => cid_seal (K := sodium) (sk := s.recvKey) (p := payload) he hc hn))
    else none
  else none

def frameDecryptFalse : Option (PLift (¬ frameDecrypts)) :=
  if h : sodium.fdec .empty nonce .empty (sodium.fenc .empty nonce .empty payload) ≠ some payload then
    some ⟨fun hg => h (hg .empty nonce .empty payload)⟩
  else none

def frameSizeFalse : Option (PLift (¬ frameSize)) :=
  if h : (sodium.fenc .empty nonce .empty payload).size ≠ payload.size + 16 then
    some ⟨fun hg => h (hg .empty nonce .empty payload)⟩
  else none

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
  t.ok "open_seal finite dimensional premises (universal AEAD assumptions remain)" (openSeal s).isSome
  t.ok "cid_seal finite dimensional premises (universal AEAD size remains)" (cidSeal s).isSome
  t.ok "empty key refutes universal frame decrypt premise" frameDecryptFalse.isSome
  t.ok "empty key refutes universal frame size premise" frameSizeFalse.isSome
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
