/-
The handshake's cryptography: Noise_KK_25519_ChaChaPoly_SHA256 (Noise
revision 34). Its two messages are the connection family's two wire
ops, the request and the connection, as in poc-17 and tiny.

    -> s
    <- s
    ...
    -> e, es, ss
    <- e, ee, se

Each end knows the other's static key before a message is read. The
initiator dials a key it knows: the invite link's inviter, or a member
device. The responder reads the initiator's key from the request op,
where it travels in the clear, as poc-17's does. The request's payload
is sealed under `es` and `ss`. It carries the joiner's request, which
every member sees anyway, so it needs no forward secrecy.

The transport keys depend on `ee`, so once both ephemeral secrets are
gone, nothing on disk opens the traffic. The ephemeral secrets are
local `eph` ops, and a close purges them.

These are pure functions over a `Suite`. The family's validators call
them, and `suite` is libsodium's (native/noise.c); cacophony's test
vectors check it (Tests/NoiseCheck.lean).

Law: `handshake_agrees`. For any suite whose DH commutes and whose AEAD
opens what it seals, an honest run whose four DHs succeed succeeds. The
responder reads the initiator's payload, the initiator reads the
responder's, both ends hold the same handshake hash, and each end's
sending key is the other's receiving key.
-/
import Engine.Core

namespace Connection.Noise

/-- What a handshake is built from. -/
structure Suite where
  /-- A secret key and a public key to their shared secret; none for a bad point. -/
  dh : ByteArray → ByteArray → Option ByteArray
  /-- A secret key's public key. -/
  pub : ByteArray → ByteArray
  /-- AEAD: key, nonce, associated data, plaintext to ciphertext. -/
  enc : ByteArray → UInt64 → ByteArray → ByteArray → ByteArray
  /-- AEAD: key, nonce, associated data, ciphertext to plaintext; none if forged. -/
  dec : ByteArray → UInt64 → ByteArray → ByteArray → Option ByteArray
  hash : ByteArray → ByteArray

/-- What the law assumes of a suite. -/
structure Suite.Good (S : Suite) : Prop where
  dh_comm : ∀ a b, S.dh a (S.pub b) = S.dh b (S.pub a)
  dec_enc : ∀ k n ad p, S.dec k n ad (S.enc k n ad p) = some p
  pub_size : ∀ a, (S.pub a).size = 32

/-! ## Keys from a chaining key -/

def hmac (S : Suite) (key data : ByteArray) : ByteArray :=
  let k := if key.size > 64 then S.hash key else key
  let k := k ++ ⟨Array.replicate (64 - k.size) 0⟩
  let pad (c : UInt8) : ByteArray := ⟨k.data.map (· ^^^ c)⟩
  S.hash (pad 0x5c ++ S.hash (pad 0x36 ++ data))

/-- Noise's HKDF, two outputs. -/
def hkdf (S : Suite) (ck ikm : ByteArray) : ByteArray × ByteArray :=
  let t := hmac S ck ikm
  let o1 := hmac S t ⟨#[1]⟩
  (o1, hmac S t (o1 ++ ⟨#[2]⟩))

/-! ## The symmetric state -/

/-- The chaining key, the handshake hash, and the key and nonce payloads
are sealed under. In KK every payload follows a DH, so there is always a
key when one is sealed. -/
structure Sym where
  ck : ByteArray
  h : ByteArray
  k : ByteArray
  n : UInt64
  deriving DecidableEq

def Sym.mixHash (S : Suite) (st : Sym) (d : ByteArray) : Sym := { st with h := S.hash (st.h ++ d) }

def Sym.mixKey (S : Suite) (st : Sym) (ikm : ByteArray) : Sym :=
  let o := hkdf S st.ck ikm
  { st with ck := o.1, k := o.2, n := 0 }

def Sym.encHash (S : Suite) (st : Sym) (p : ByteArray) : Sym × ByteArray :=
  let c := S.enc st.k st.n st.h p
  ({ st.mixHash S c with n := st.n + 1 }, c)

def Sym.decHash (S : Suite) (st : Sym) (c : ByteArray) : Option (Sym × ByteArray) :=
  (S.dec st.k st.n st.h c).map fun p => ({ st.mixHash S c with n := st.n + 1 }, p)

/-- The name is 32 bytes, so it is the first `h` as it stands. -/
def protocol : ByteArray := "Noise_KK_25519_ChaChaPoly_SHA256".toUTF8

/-- Both ends start from the name, the prologue and the two static keys,
the initiator's first. -/
def Sym.start (S : Suite) (prologue si sr : ByteArray) : Sym :=
  (((⟨protocol, protocol, .empty, 0⟩ : Sym).mixHash S prologue).mixHash S si).mixHash S sr

/-! ## After the handshake -/

/-- One direction's key and its next nonce. -/
structure Cipher where
  k : ByteArray
  n : UInt64
  deriving DecidableEq

def Cipher.enc (S : Suite) (c : Cipher) (p : ByteArray) : Cipher × ByteArray :=
  ({ c with n := c.n + 1 }, S.enc c.k c.n .empty p)

def Cipher.dec (S : Suite) (c : Cipher) (m : ByteArray) : Option (Cipher × ByteArray) :=
  (S.dec c.k c.n .empty m).map ({ c with n := c.n + 1 }, ·)

/-- A session: the handshake hash, and the two directions' keys. -/
structure Session where
  h : ByteArray
  send : Cipher
  recv : Cipher
  deriving DecidableEq

/-- The two transport keys: the initiator sends under the first. -/
def Sym.split (S : Suite) (st : Sym) : Cipher × Cipher :=
  let o := hkdf S st.ck .empty
  (⟨o.1, 0⟩, ⟨o.2, 0⟩)

/-! ## The two messages -/

/-- Before the payload of message 1 (`e, es, ss`). -/
def Sym.one (S : Suite) (prologue si sr epub es ss : ByteArray) : Sym :=
  (((Sym.start S prologue si sr).mixHash S epub).mixKey S es).mixKey S ss

/-- Before the payload of message 2 (`e, ee, se`). -/
def Sym.two (S : Suite) (st : Sym) (fpub ee se : ByteArray) : Sym :=
  ((st.mixHash S fpub).mixKey S ee).mixKey S se

/-- Initiator, message 1, with static secret `s` and ephemeral secret `e`,
to responder static `rs`: its state, and the message. -/
def write1 (S : Suite) (prologue s e rs payload : ByteArray) : Option (Sym × ByteArray) := do
  let es ← S.dh e rs
  let ss ← S.dh s rs
  let r := (Sym.one S prologue (S.pub s) rs (S.pub e) es ss).encHash S payload
  return (r.1, S.pub e ++ r.2)

/-- Responder, message 1, with static secret `s`, from initiator static
`rs`: its state, the initiator's ephemeral, the payload. -/
def read1 (S : Suite) (prologue s rs msg : ByteArray) : Option (Sym × ByteArray × ByteArray) :=
  if msg.size < 32 then none else do
  let re := msg.extract 0 32
  let es ← S.dh s re
  let ss ← S.dh s rs
  let r ← (Sym.one S prologue rs (S.pub s) re es ss).decHash S (msg.extract 32 msg.size)
  return (r.1, re, r.2)

/-- Initiator, after message 1, from the message alone: its state and
the payload it sealed, recovered with its static secret `s` and
ephemeral secret `e`. The message must begin with `e`'s key, so it is
this initiator's. The state need never be stored. -/
def sent1 (S : Suite) (prologue s e rs msg : ByteArray) : Option (Sym × ByteArray) :=
  if msg.size < 32 then none else
  if msg.extract 0 32 ≠ S.pub e then none else do
  let es ← S.dh e rs
  let ss ← S.dh s rs
  (Sym.one S prologue (S.pub s) rs (S.pub e) es ss).decHash S (msg.extract 32 msg.size)

/-- Responder, message 2, with ephemeral secret `f`, to the initiator's
static `rs` and ephemeral `re`: its session, and the message. -/
def write2 (S : Suite) (st : Sym) (f rs re payload : ByteArray) : Option (Session × ByteArray) := do
  let ee ← S.dh f re
  let se ← S.dh f rs
  let r := (Sym.two S st (S.pub f) ee se).encHash S payload
  let ks := r.1.split S
  return (⟨r.1.h, ks.2, ks.1⟩, S.pub f ++ r.2)

/-- Initiator, message 2, with static secret `s` and ephemeral secret
`e`: its session, and the payload. -/
def read2 (S : Suite) (st : Sym) (s e msg : ByteArray) : Option (Session × ByteArray) :=
  if msg.size < 32 then none else do
  let rf := msg.extract 0 32
  let ee ← S.dh e rf
  let se ← S.dh s rf
  let r ← (Sym.two S st rf ee se).decHash S (msg.extract 32 msg.size)
  let ks := r.1.split S
  return (⟨r.1.h, ks.1, ks.2⟩, r.2)

/-! ## The law -/

section
variable {S : Suite}

theorem decHash_encHash (G : S.Good) (st : Sym) (p : ByteArray) :
    st.decHash S (st.encHash S p).2 = some ((st.encHash S p).1, p) := by
  simp [Sym.decHash, Sym.encHash, G.dec_enc]

theorem size_ge (G : S.Good) (a : ByteArray) (c : ByteArray) : ¬ (S.pub a ++ c).size < 32 := by
  rw [ByteArray.size_append, G.pub_size]; omega

theorem front (G : S.Good) (a c : ByteArray) : (S.pub a ++ c).extract 0 32 = S.pub a :=
  ByteArray.extract_append_eq_left (G.pub_size a).symm

theorem back (G : S.Good) (a c : ByteArray) : (S.pub a ++ c).extract 32 (S.pub a ++ c).size = c := by
  rw [ByteArray.size_append]
  exact ByteArray.extract_append_eq_right (G.pub_size a).symm (by rw [G.pub_size])

/-- The responder reads what the initiator wrote, and holds its state. -/
theorem read1_write1 (G : S.Good) {prologue sI sR e p es ss : ByteArray}
    (hes : S.dh e (S.pub sR) = some es) (hss : S.dh sI (S.pub sR) = some ss) :
    ∃ st m, write1 S prologue sI e (S.pub sR) p = some (st, m) ∧
      read1 S prologue sR (S.pub sI) m = some (st, S.pub e, p) := by
  have hes' : S.dh sR (S.pub e) = some es := by rw [← G.dh_comm]; exact hes
  have hss' : S.dh sR (S.pub sI) = some ss := by rw [← G.dh_comm]; exact hss
  let r := (Sym.one S prologue (S.pub sI) (S.pub sR) (S.pub e) es ss).encHash S p
  refine ⟨r.1, S.pub e ++ r.2, by simp [write1, hes, hss, r], ?_⟩
  simp only [read1, size_ge G, ↓reduceIte]
  rw [front G, back G]
  simp [hes', hss', r, decHash_encHash G]

/-- The initiator recovers, from its own message 1, the state and
payload it wrote. -/
theorem sent1_write1 (G : S.Good) {prologue sI e rs p : ByteArray} {st : Sym} {m : ByteArray}
    (h : write1 S prologue sI e rs p = some (st, m)) : sent1 S prologue sI e rs m = some (st, p) := by
  simp only [write1] at h
  cases hes : S.dh e rs with
  | none => simp [hes] at h
  | some es =>
    cases hss : S.dh sI rs with
    | none => simp [hes, hss] at h
    | some ss =>
      simp only [hes, hss] at h
      injection h with h; injection h with h1 h2; subst h1 h2
      simp only [sent1, size_ge G, ↓reduceIte, front G, back G, ne_eq, not_true_eq_false, hes, hss]
      simp [decHash_encHash G]

/-- The initiator reads what the responder wrote, and the sessions match. -/
theorem read2_write2 (G : S.Good) (st : Sym) {sI e f p ee se : ByteArray}
    (hee : S.dh f (S.pub e) = some ee) (hse : S.dh f (S.pub sI) = some se) :
    ∃ sr m, write2 S st f (S.pub sI) (S.pub e) p = some (sr, m) ∧
      ∃ si, read2 S st sI e m = some (si, p) ∧
        si.h = sr.h ∧ si.send = sr.recv ∧ si.recv = sr.send := by
  have hee' : S.dh e (S.pub f) = some ee := by rw [G.dh_comm]; exact hee
  have hse' : S.dh sI (S.pub f) = some se := by rw [G.dh_comm]; exact hse
  let r := (Sym.two S st (S.pub f) ee se).encHash S p
  let ks := r.1.split S
  refine ⟨⟨r.1.h, ks.2, ks.1⟩, S.pub f ++ r.2, by simp [write2, hee, hse, r, ks],
    ⟨r.1.h, ks.1, ks.2⟩, ?_, rfl, rfl, rfl⟩
  simp only [read2, size_ge G, ↓reduceIte]
  rw [front G, back G]
  simp [hee', hse', r, ks, decHash_encHash G]

/-- **An honest handshake agrees.** If its four DHs succeed: the
initiator's message 1 succeeds and the responder reads its payload and
ephemeral; the responder's message 2 succeeds and the initiator reads
its payload; both hold the same handshake hash; each one's sending key
is the other's receiving key. -/
theorem handshake_agrees (G : S.Good) (prologue sI sR e f p1 p2 : ByteArray)
    {es ss ee se : ByteArray} (hes : S.dh e (S.pub sR) = some es) (hss : S.dh sI (S.pub sR) = some ss)
    (hee : S.dh f (S.pub e) = some ee) (hse : S.dh f (S.pub sI) = some se) :
    ∃ st m1, write1 S prologue sI e (S.pub sR) p1 = some (st, m1) ∧
      read1 S prologue sR (S.pub sI) m1 = some (st, S.pub e, p1) ∧
      ∃ sr m2, write2 S st f (S.pub sI) (S.pub e) p2 = some (sr, m2) ∧
        ∃ si, read2 S st sI e m2 = some (si, p2) ∧
          si.h = sr.h ∧ si.send = sr.recv ∧ si.recv = sr.send := by
  obtain ⟨st, m1, h1, h1'⟩ := read1_write1 (p := p1) G hes hss
  exact ⟨st, m1, h1, h1', read2_write2 (p := p2) G st hee hse⟩

end

/-! ## libsodium's suite -/

@[extern "le_x25519"] opaque x25519 (sk pk : @& ByteArray) : ByteArray
@[extern "le_x25519_base"] opaque x25519Base (sk : @& ByteArray) : ByteArray
@[extern "le_chachapoly_seal"] opaque chachaSeal (k : @& ByteArray) (n : UInt64) (ad p : @& ByteArray) :
  ByteArray
@[extern "le_chachapoly_open"] opaque chachaOpen (k : @& ByteArray) (n : UInt64) (ad c : @& ByteArray) :
  Option ByteArray
/-- A device's X25519 static secret, from its Ed25519 secret key (seed ++ pk). -/
@[extern "le_ed_sk_to_x"] opaque staticOf (edSk : @& ByteArray) : ByteArray
/-- A device's X25519 static key, from its Ed25519 key; empty if not a point. -/
@[extern "le_ed_pk_to_x"] opaque staticPubOf (edPk : @& ByteArray) : ByteArray
/-- Random bytes from the OS. -/
@[extern "le_random"] opaque randomBytes (n : UInt32) : IO ByteArray

/-- X25519, ChaCha20-Poly1305 and SHA-256. -/
def suite : Suite where
  dh a b := let r := x25519 a b; if r.size = 32 then some r else none
  pub := x25519Base
  enc := chachaSeal
  dec := chachaOpen
  hash := Engine.sha256

end Connection.Noise
