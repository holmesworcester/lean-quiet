/-
Connection's handshake against the published test vector for
Noise_KK_25519_ChaChaPoly_SHA256 (cacophony's vectors, the one KK
vector; cacophony is the Haskell Noise implementation): libsodium's
suite, run through Connection.Noise's four calls, must write the
vector's exact handshake bytes, read back its payloads, reach its
handshake hash, and seal and open the four transport messages after it.
Then tampered messages, a wrong static key and a wrong ephemeral key
must all fail, and a device's Ed25519 key must convert to the X25519 key
of its secret.
-/
import Tests.Lib
import Connection.Noise

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
  t.finish "noise_check"
