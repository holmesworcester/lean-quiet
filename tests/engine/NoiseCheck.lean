/-
Connection's handshake against the published test vector for
Noise_KK_25519_ChaChaPoly_SHA256 (cacophony's vectors, the one KK
vector; cacophony is the Haskell Noise implementation): libsodium's
suite, run through Connection.Noise's four calls, must write the
vector's exact handshake bytes, read back its payloads, reach its
handshake hash, and seal and open the four transport messages after it.
Then tampered messages, a wrong static key and a wrong ephemeral key
must all fail, and a device's Ed25519 key must convert to the X25519 key
of its secret. The suite must meet what the laws assume of it
(`Suite.Good`) on the vector's keys.
-/
import tests.engine.Lib
import ops.connection.Noise
import ops.connection.Frame

open Engine Community Tests Connection.Noise

def unhex (s : String) : ByteArray :=
  let d (c : Char) : UInt8 := (if c.isDigit then c.toNat - 48 else c.toNat - 87).toUInt8
  let cs := s.toList
  ⟨((List.range (cs.length / 2)).map fun i => d cs[2*i]! * 16 + d cs[2*i+1]!).toArray⟩

/-- Flip one bit of byte i. -/
def flipBit (b : ByteArray) (i : Nat) : ByteArray := b.set! i (b.get! i ^^^ 1)

def prologue := unhex "4a6f686e2047616c74"
def sI := unhex "e61ef9919cde45dd5f82166404bd08e38bceb5dfdfded0a34c8df7ed542214d1"
def sR := unhex "4a3acbfdb163dec651dfa3194dece676d437029c62a408b4c5ea9114246e4893"
def e := unhex "893e28b9dc6ca8d611ab664754b8ceb7bac5117349a4439a6b0569da977c464a"
def f := unhex "bbdb4cdbd309f1a1f2e1456967fe288cadd6f712d65dc7b7793d5e63da6b375b"
def rsOfI := unhex "31e0303fd6418d2f8c0e78b91f22e8caed0fbe48656dcf4767e4834f701b8f62"  -- the responder static the initiator holds
def rsOfR := unhex "6bc3822a2aa7f4e6981d6538692b3cdf3e6df9eea6ed269eb41d93c22757b75a"  -- the initiator static the responder holds
def hh := unhex "24c6b51ecb76277140ca018b5985bc9f03de321dae2d34dcae433dafef0131d9"
def payloads : List ByteArray := [unhex "4c756477696720766f6e204d69736573", unhex "4d757272617920526f746862617264", unhex "462e20412e20486179656b", unhex "4361726c204d656e676572", unhex "4a65616e2d426170746973746520536179", unhex "457567656e2042f6686d20766f6e2042617765726b"]
def cts : List ByteArray := [unhex "ca35def5ae56cec33dc2036731ab14896bc4c75dbb07a61f879f8e3afa4c79440177015efc1fe7a37c629af7120a96274e6ab7afcc9261901d0e09ae32a5bb96",
  unhex "95ebc60d2b1fa672c1f46a8aa265ef51bfe38e7ccb39ec5be34069f144808843b274d3429adc47ca093ba63ef90f8da89fda108db471dccfa4894aa7b00003",
  unhex "966b05bc69ec01b8454d3160a214e6f24a3d884eb31ec2408af63f",
  unhex "0ad887fba4f611bbb4afe44ba3556b8164332ca7d5934634d63d80",
  unhex "012b28ae646ae7830e2c5472cb023eab071c1db3d8413ec69b513b83832f974c2d",
  unhex "bb3e6a48160d9c5971d37f975727294e0d868342db31832e54d07191ab0ca3c3703b5ed3d9"]

def S := suite

def main : IO UInt32 := do
  let t ← Checks.new
  let p := payloads.toArray
  let c := cts.toArray
  t.ok "the initiator's static key is the one the responder holds" (S.pub sI == rsOfR)
  t.ok "the responder's static key is the one the initiator holds" (S.pub sR == rsOfI)
  -- What the laws assume of the suite (Suite.Good), on the vector's keys.
  t.ok "DH commutes" (S.dh sI (S.pub sR) == S.dh sR (S.pub sI) && S.dh e (S.pub f) == S.dh f (S.pub e))
  -- A wrong-sized key is refused both ways: no fallback key on seal.
  let short := ByteArray.mk #[1, 2, 3]
  let msg := "secret".toUTF8
  t.ok "ChaCha20-Poly1305 seal refuses a key that is not 32 bytes"
    ((Engine.Crypto.chachaSeal short 0 .empty msg).size == 0)
  t.ok "and nothing sealed under a 32-byte zero key opens with a short key"
    ((Engine.Crypto.chachaOpen short 0 .empty (Engine.Crypto.chachaSeal (ByteArray.mk (Array.replicate 32 0)) 0 .empty msg)).isNone)
  t.ok "XChaCha20-Poly1305 seal refuses a short key or nonce"
    ((Engine.Crypto.xchachaSeal short (ByteArray.mk (Array.replicate 24 0)) .empty msg).size == 0 &&
     (Engine.Crypto.xchachaSeal (ByteArray.mk (Array.replicate 32 0)) short .empty msg).size == 0)
  t.ok "a message splits into its key and the rest"
    (S.split (S.pair (S.pub e) p[0]!) == some (S.pub e, p[0]!))
  -- Message 1: the request.
  let some (st, m1) := write1 S prologue sI e rsOfI p[0]! | t.ok "message 1 is written" false; return 1
  t.ok "message 1 is the vector's" (m1 == c[0]!)
  let some (st', re, q1) := read1 S prologue sR rsOfR m1 | t.ok "message 1 is read" false; return 1
  t.ok "the responder reads payload 1" (q1 == p[0]!)
  t.ok "and the initiator's ephemeral" (re == S.pub e)
  t.ok "both ends hold one state" (st' == st)
  -- Message 2: the connection.
  let some (sr, m2) := write2 S st' f rsOfR re p[1]! | t.ok "message 2 is written" false; return 1
  t.ok "message 2 is the vector's" (m2 == c[1]!)
  let some (si, q2) := read2 S st sI e m2 | t.ok "message 2 is read" false; return 1
  t.ok "the initiator reads payload 2" (q2 == p[1]!)
  t.ok "the handshake hash is the vector's, at both ends" (si.h == hh && sr.h == hh)
  t.ok "the keys cross" (si.send == sr.recv && si.recv == sr.send)
  -- The guarded assumptions (Suite.Good, Keys.Good, Seal.Good) on the
  -- vector's keys, and the unguarded ones failing at a wrong size: the
  -- negative control that shows why the guard is there.
  t.ok "the transport keys are HKDF outputs the AEAD takes (keyOk, hkdf_ok)"
    (S.keyOk si.send.k && S.keyOk si.recv.k && S.keyOk (S.hkdf sI e).1 && S.keyOk (S.hkdf sI e).2)
  t.ok "the AEAD opens what it sealed under a key it takes (dec_enc, guarded)"
    (S.dec si.send.k 7 hh (S.enc si.send.k 7 hh p[2]!) == some p[2]!)
  t.ok "negative control: unguarded, dec_enc fails at a 3-byte key, which keyOk refuses"
    (!S.keyOk short && S.dec short 7 hh (S.enc short 7 hh p[2]!) != some p[2]!)
  let K := Connection.sodium
  let n24 := sha256 "n24".toUTF8 |>.extract 0 24
  t.ok "the frames' AEAD opens what it sealed under a 32-byte key and a 24-byte nonce"
    (K.fdec si.send.k n24 hh (K.fenc si.send.k n24 hh p[2]!) == some p[2]!)
  t.ok "negative control: unguarded, it fails at a 23-byte nonce"
    (K.fdec si.send.k (n24.extract 0 23) hh (K.fenc si.send.k (n24.extract 0 23) hh p[2]!) != some p[2]!)
  let C := Community.cryptoSeal
  t.ok "the content seal opens what it sealed under a 32-byte key and a 24-byte nonce; its hash is 32 bytes"
    (C.dec si.send.k n24 hh (C.enc si.send.k n24 hh p[2]!) == some p[2]! && (C.hash p[2]!).size == 32)
  t.ok "negative control: unguarded, it fails at a 3-byte key"
    (C.dec short n24 hh (C.enc short n24 hh p[2]!) != some p[2]!)
  -- Transport: the initiator sends 3 and 5, the responder 4 and 6.
  let mut a := si
  let mut b := sr
  for i in [2:6] do
    let (x, y) := if i % 2 == 0 then (a, b) else (b, a)
    let (x', ct) := x.send.enc S p[i]!
    t.ok s!"transport message {i + 1} is the vector's" (ct == c[i]!)
    match y.recv.dec S ct with
    | some (y', q) =>
      t.ok s!"transport message {i + 1} opens" (q == p[i]!)
      if i % 2 == 0 then a := { a with send := x' }; b := { b with recv := y' }
      else b := { b with send := x' }; a := { a with recv := y' }
    | none => t.ok s!"transport message {i + 1} opens" false
  -- What must fail.
  let bad1 := (List.range m1.size).filter (· % 7 == 0) |>.all fun i =>
    (read1 S prologue sR rsOfR (flipBit m1 i)).isNone
  t.ok "every tampered message 1 is refused" bad1
  let bad2 := (List.range m2.size).filter (· % 7 == 0) |>.all fun i =>
    (read2 S st sI e (flipBit m2 i)).isNone
  t.ok "every tampered message 2 is refused" bad2
  t.ok "a responder with another static key cannot read message 1"
    (read1 S prologue (sha256 "other".toUTF8) rsOfR m1).isNone
  t.ok "a responder that takes the request for another initiator's cannot read it"
    (read1 S prologue sR (S.pub (sha256 "mallory".toUTF8)) m1).isNone
  t.ok "an initiator without its ephemeral secret cannot read message 2"
    (read2 S st sI (sha256 "guess".toUTF8) m2).isNone
  t.ok "a short message is refused" ((read1 S prologue sR rsOfR (m1.extract 0 31)).isNone)
  -- Device keys: the X25519 key of a device's Ed25519 key is the public
  -- key of the X25519 secret of its secret key.
  for name in ["founder", "joiner", "member"] do
    let d := Device.named name
    t.ok s!"{name}'s Ed25519 key converts to its X25519 key" (S.pub (staticOf d.sk) == staticPubOf d.pk)
  t.ok "a non-point is refused" ((staticPubOf (ByteArray.mk (Array.replicate 32 0xFF))).size == 0)
  -- Ephemeral secrets come from the OS.
  let r1 ← randomBytes 32
  let r2 ← randomBytes 32
  t.ok "random ephemerals are 32 bytes and differ" (r1.size == 32 && r2.size == 32 && r1 != r2)
  -- Session frames (XChaCha20-Poly1305, connection id in the header and
  -- the associated data, random nonce).
  let K := Connection.sodium
  let cid := sha256 "connection".toUTF8
  let cid2 := sha256 "other connection".toUTF8
  let k := sha256 "send key".toUTF8
  let n ← randomBytes 24
  let body := "a sync message, and some ops".toUTF8
  let fr := Connection.Frame.seal K cid k n body
  t.ok "a frame names its connection" (Connection.Frame.cid fr == some cid)
  t.ok "a frame opens under its key" (Connection.Frame.open K k fr == some (cid, body))
  t.ok "a frame never opens under another key" ((Connection.Frame.open K (sha256 "x".toUTF8) fr).isNone)
  let moved := Connection.Frame.seal K cid2 k n body
  let spliced := (moved.extract 0 33) ++ fr.extract 33 fr.size
  t.ok "a frame moved to another connection's header never opens" ((Connection.Frame.open K k spliced).isNone)
  let bad := (List.range fr.size).filter (· % 5 == 0) |>.all fun i => (Connection.Frame.open K k (flipBit fr i)).isNone
  t.ok "every tampered frame is refused" bad
  let n2 ← randomBytes 24
  t.ok "two seals of the same bytes differ" (Connection.Frame.seal K cid k n2 body != fr)
  -- Counters: the nonce is the frame's counter, then random bytes.
  let rnd ← randomBytes 32
  let ctr := 0x0102030405060708
  let fc := Connection.Frame.seal K cid k (Connection.Frame.nonce ctr rnd) body
  t.ok "a frame opens to the counter it was sealed with" (Connection.Frame.openAt K k fc == some (cid, ctr, body))
  let bumped := fc.set! 40 (fc.get! 40 + 1)
  t.ok "a frame whose counter was changed never opens" ((Connection.Frame.openAt K k bumped).isNone)
  let fc2 := Connection.Frame.seal K cid k (Connection.Frame.nonce (ctr + 1) rnd) body
  t.ok "the next counter is fresh after this one, and this one is not again"
    (match Connection.Frame.openAt K k fc, Connection.Frame.openAt K k fc2 with
      | some (_, c1, _), some (_, c2, _) => Connection.Frame.fresh c1 c2 && !Connection.Frame.fresh c1 c1
      | _, _ => false)
  t.ok "the same counter with another random tail is another nonce"
    (Connection.Frame.nonce ctr rnd != Connection.Frame.nonce ctr (sha256 rnd))
  t.finish "noise_check"
