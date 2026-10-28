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

These are pure functions over a `Suite α`, generic in the carrier `α`.
The family's validators call them at `α := ByteArray` with `suite`,
libsodium's (native/noise.c), which cacophony's test vectors check
(Tests/NoiseCheck.lean). Connection/NoiseSymbolic.lean calls the same
functions at symbolic terms to prove the session keys secret.

Law: `handshake_agrees`. For any suite whose DH commutes, whose AEAD
opens what it seals, and whose messages split back into the public key
and the rest, an honest run whose four DHs succeed succeeds. The
responder reads the initiator's payload, the initiator reads the
responder's, both ends hold the same handshake hash, and each end's
sending key is the other's receiving key.
-/
import engine.core.Crypto

namespace Connection.Noise

/-- What a handshake is built from, over a carrier `α`: bytes when it
runs (`suite`), terms in the secrecy proofs (`Symbolic.sym`). -/
structure Suite (α : Type) where
  /-- A secret key and a public key to their shared secret; none for a bad point. -/
  dh : α → α → Option α
  /-- A secret key's public key. -/
  pub : α → α
  /-- AEAD: key, nonce, associated data, plaintext to ciphertext. -/
  enc : α → Nat → α → α → α
  /-- AEAD: key, nonce, associated data, ciphertext to plaintext; none if forged. -/
  dec : α → Nat → α → α → Option α
  hash : α → α
  /-- Noise's HKDF with two outputs, from a chaining key and input key material. -/
  hkdf : α → α → α × α
  /-- A message: a public key, then the rest. -/
  pair : α → α → α
  /-- A message's public key and the rest; none if it cannot hold one. -/
  split : α → Option (α × α)
  /-- A constant: the protocol name, an empty payload. -/
  lit : ByteArray → α

/-- What the laws assume of a suite. -/
structure Suite.Good {α : Type} (S : Suite α) : Prop where
  dh_comm : ∀ a b, S.dh a (S.pub b) = S.dh b (S.pub a)
  dec_enc : ∀ k n ad p, S.dec k n ad (S.enc k n ad p) = some p
  split_pair : ∀ a c, S.split (S.pair (S.pub a) c) = some (S.pub a, c)

/-! ## Keys from a chaining key, in bytes -/

def hmac (hash : ByteArray → ByteArray) (key data : ByteArray) : ByteArray :=
  let k := if key.size > 64 then hash key else key
  let k := k ++ ⟨Array.replicate (64 - k.size) 0⟩
  let pad (c : UInt8) : ByteArray := ⟨k.data.map (· ^^^ c)⟩
  hash (pad 0x5c ++ hash (pad 0x36 ++ data))

/-- Noise's HKDF, two outputs. -/
def hkdf (hash : ByteArray → ByteArray) (ck ikm : ByteArray) : ByteArray × ByteArray :=
  let t := hmac hash ck ikm
  let o1 := hmac hash t ⟨#[1]⟩
  (o1, hmac hash t (o1 ++ ⟨#[2]⟩))

section
variable {α : Type} (S : Suite α)

/-! ## The symmetric state -/

/-- The chaining key, the handshake hash, and the key and nonce payloads
are sealed under. In KK every payload follows a DH, so there is always a
key when one is sealed. -/
structure Sym (α : Type) where
  ck : α
  h : α
  k : α
  n : Nat
  deriving DecidableEq

def Sym.mixHash (st : Sym α) (d : α) : Sym α := { st with h := S.hash (S.pair st.h d) }

def Sym.mixKey (st : Sym α) (ikm : α) : Sym α :=
  let o := S.hkdf st.ck ikm
  { st with ck := o.1, k := o.2, n := 0 }

def Sym.encHash (st : Sym α) (p : α) : Sym α × α :=
  let c := S.enc st.k st.n st.h p
  ({ st.mixHash S c with n := st.n + 1 }, c)

def Sym.decHash (st : Sym α) (c : α) : Option (Sym α × α) :=
  (S.dec st.k st.n st.h c).map fun p => ({ st.mixHash S c with n := st.n + 1 }, p)

/-- The name is 32 bytes, so it is the first `h` as it stands. -/
def protocol : ByteArray := "Noise_KK_25519_ChaChaPoly_SHA256".toUTF8

/-- Both ends start from the name, the prologue and the two static keys,
the initiator's first. -/
def Sym.start (prologue si sr : α) : Sym α :=
  (((⟨S.lit protocol, S.lit protocol, S.lit .empty, 0⟩ : Sym α).mixHash S prologue).mixHash S si).mixHash S sr

/-! ## After the handshake -/

/-- One direction's key and its next nonce. -/
structure Cipher (α : Type) where
  k : α
  n : Nat
  deriving DecidableEq

def Cipher.enc (c : Cipher α) (p : α) : Cipher α × α :=
  ({ c with n := c.n + 1 }, S.enc c.k c.n (S.lit .empty) p)

def Cipher.dec (c : Cipher α) (m : α) : Option (Cipher α × α) :=
  (S.dec c.k c.n (S.lit .empty) m).map ({ c with n := c.n + 1 }, ·)

/-- A session: the handshake hash, and the two directions' keys. -/
structure Session (α : Type) where
  h : α
  send : Cipher α
  recv : Cipher α
  deriving DecidableEq

/-- The two transport keys: the initiator sends under the first. -/
def Sym.split (st : Sym α) : Cipher α × Cipher α :=
  let o := S.hkdf st.ck (S.lit .empty)
  (⟨o.1, 0⟩, ⟨o.2, 0⟩)

/-! ## The two messages -/

/-- Before the payload of message 1 (`e, es, ss`). -/
def Sym.one (prologue si sr epub es ss : α) : Sym α :=
  (((Sym.start S prologue si sr).mixHash S epub).mixKey S es).mixKey S ss

/-- Before the payload of message 2 (`e, ee, se`). -/
def Sym.two (st : Sym α) (fpub ee se : α) : Sym α :=
  ((st.mixHash S fpub).mixKey S ee).mixKey S se

/-- Initiator, message 1, with static secret `s` and ephemeral secret `e`,
to responder static `rs`: its state, and the message. -/
def write1 (prologue s e rs payload : α) : Option (Sym α × α) := do
  let es ← S.dh e rs
  let ss ← S.dh s rs
  let r := (Sym.one S prologue (S.pub s) rs (S.pub e) es ss).encHash S payload
  return (r.1, S.pair (S.pub e) r.2)

/-- Responder, message 1, with static secret `s`, from initiator static
`rs`: its state, the initiator's ephemeral, the payload. -/
def read1 (prologue s rs msg : α) : Option (Sym α × α × α) := do
  let (re, c) ← S.split msg
  let es ← S.dh s re
  let ss ← S.dh s rs
  let r ← (Sym.one S prologue rs (S.pub s) re es ss).decHash S c
  return (r.1, re, r.2)

/-- Initiator, after message 1, from the message alone: its state and
the payload it sealed, recovered with its static secret `s` and
ephemeral secret `e`. The message must begin with `e`'s key, so it is
this initiator's. The state need never be stored. -/
def sent1 [DecidableEq α] (prologue s e rs msg : α) : Option (Sym α × α) := do
  let (re, c) ← S.split msg
  if re = S.pub e then
    let es ← S.dh e rs
    let ss ← S.dh s rs
    (Sym.one S prologue (S.pub s) rs (S.pub e) es ss).decHash S c
  else none

/-- Responder, message 2, with ephemeral secret `f`, to the initiator's
static `rs` and ephemeral `re`: its session, and the message. -/
def write2 (st : Sym α) (f rs re payload : α) : Option (Session α × α) := do
  let ee ← S.dh f re
  let se ← S.dh f rs
  let r := (Sym.two S st (S.pub f) ee se).encHash S payload
  let ks := r.1.split S
  return (⟨r.1.h, ks.2, ks.1⟩, S.pair (S.pub f) r.2)

/-- Initiator, message 2, with static secret `s` and ephemeral secret
`e`: its session, and the payload. -/
def read2 (st : Sym α) (s e msg : α) : Option (Session α × α) := do
  let (rf, c) ← S.split msg
  let ee ← S.dh e rf
  let se ← S.dh s rf
  let r ← (Sym.two S st rf ee se).decHash S c
  let ks := r.1.split S
  return (⟨r.1.h, ks.1, ks.2⟩, r.2)

end

/-! ## The law -/

section
variable {α : Type} {S : Suite α}

theorem decHash_encHash (G : S.Good) (st : Sym α) (p : α) :
    st.decHash S (st.encHash S p).2 = some ((st.encHash S p).1, p) := by
  simp [Sym.decHash, Sym.encHash, G.dec_enc]

/-- The responder reads what the initiator wrote, and holds its state. -/
theorem read1_write1 (G : S.Good) {prologue sI sR e p es ss : α}
    (hes : S.dh e (S.pub sR) = some es) (hss : S.dh sI (S.pub sR) = some ss) :
    ∃ st m, write1 S prologue sI e (S.pub sR) p = some (st, m) ∧
      read1 S prologue sR (S.pub sI) m = some (st, S.pub e, p) := by
  have hes' : S.dh sR (S.pub e) = some es := by rw [← G.dh_comm]; exact hes
  have hss' : S.dh sR (S.pub sI) = some ss := by rw [← G.dh_comm]; exact hss
  let r := (Sym.one S prologue (S.pub sI) (S.pub sR) (S.pub e) es ss).encHash S p
  refine ⟨r.1, S.pair (S.pub e) r.2, by simp [write1, hes, hss, r], ?_⟩
  simp [read1, G.split_pair, hes', hss', r, decHash_encHash G]

/-- The initiator recovers, from its own message 1, the state and
payload it wrote. -/
theorem sent1_write1 [DecidableEq α] (G : S.Good) {prologue sI e rs p : α} {st : Sym α} {m : α}
    (h : write1 S prologue sI e rs p = some (st, m)) : sent1 S prologue sI e rs m = some (st, p) := by
  simp only [write1] at h
  cases hes : S.dh e rs with
  | none => simp [hes] at h
  | some es =>
    cases hss : S.dh sI rs with
    | none => simp [hes, hss] at h
    | some ss =>
      simp only [hes, hss, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [sent1, G.split_pair, hes, hss, decHash_encHash G]

/-- The initiator reads what the responder wrote, and the sessions match. -/
theorem read2_write2 (G : S.Good) (st : Sym α) {sI e f p ee se : α}
    (hee : S.dh f (S.pub e) = some ee) (hse : S.dh f (S.pub sI) = some se) :
    ∃ sr m, write2 S st f (S.pub sI) (S.pub e) p = some (sr, m) ∧
      ∃ si, read2 S st sI e m = some (si, p) ∧
        si.h = sr.h ∧ si.send = sr.recv ∧ si.recv = sr.send := by
  have hee' : S.dh e (S.pub f) = some ee := by rw [G.dh_comm]; exact hee
  have hse' : S.dh sI (S.pub f) = some se := by rw [G.dh_comm]; exact hse
  let r := (Sym.two S st (S.pub f) ee se).encHash S p
  let ks := r.1.split S
  refine ⟨⟨r.1.h, ks.2, ks.1⟩, S.pair (S.pub f) r.2, by simp [write2, hee, hse, r, ks],
    ⟨r.1.h, ks.1, ks.2⟩, ?_, rfl, rfl, rfl⟩
  simp [read2, G.split_pair, hee', hse', r, ks, decHash_encHash G]

/-- The initiator's state recovered from its message 1 is the
responder's after reading it, and the responder reads the initiator's
ephemeral and payload. -/
theorem sent1_read1 [DecidableEq α] (G : S.Good) {pro sI sR e m1 : α} {st st' : Sym α} {re p p' : α}
    (hs : sent1 S pro sI e (S.pub sR) m1 = some (st', p'))
    (hr : read1 S pro sR (S.pub sI) m1 = some (st, re, p)) :
    st' = st ∧ p' = p ∧ re = S.pub e := by
  unfold sent1 at hs
  unfold read1 at hr
  cases hm : S.split m1 with
  | none => simp [hm] at hs
  | some rc =>
    obtain ⟨re', c⟩ := rc
    simp only [hm, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hs hr
    by_cases he : re' = S.pub e
    · subst he
      simp only [↓reduceIte] at hs
      cases h1 : S.dh e (S.pub sR) with
      | none => simp [h1] at hs
      | some es =>
        cases h2 : S.dh sI (S.pub sR) with
        | none => simp [h1, h2] at hs
        | some ss =>
          have h1' : S.dh sR (S.pub e) = some es := by rw [← G.dh_comm]; exact h1
          have h2' : S.dh sR (S.pub sI) = some ss := by rw [← G.dh_comm]; exact h2
          simp only [h1, h2, h1', h2', Option.bind_some] at hs hr
          rw [hs] at hr
          simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl, rfl⟩ := hr
          exact ⟨rfl, rfl, rfl⟩
    · simp [he] at hs

/-- The initiator's session from the responder's message 2 matches the
responder's: the same hash, crossed keys. -/
theorem read2_write2' (G : S.Good) {st : Sym α} {f sI e pl m2 : α} {sr si : Session α} {p : α}
    (hw : write2 S st f (S.pub sI) (S.pub e) pl = some (sr, m2))
    (hr : read2 S st sI e m2 = some (si, p)) :
    si.h = sr.h ∧ si.send = sr.recv ∧ si.recv = sr.send := by
  unfold write2 at hw
  simp only [Option.bind_eq_bind, Option.pure_def] at hw
  cases h1 : S.dh f (S.pub e) with
  | none => simp [h1] at hw
  | some ee =>
    cases h2 : S.dh f (S.pub sI) with
    | none => simp [h1, h2] at hw
    | some se =>
      have h1' : S.dh e (S.pub f) = some ee := by rw [G.dh_comm]; exact h1
      have h2' : S.dh sI (S.pub f) = some se := by rw [G.dh_comm]; exact h2
      simp only [h1, h2, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      simp only [read2, G.split_pair, h1', h2', Option.bind_eq_bind,
        Option.bind_some, decHash_encHash G, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨rfl, rfl, rfl⟩

/-- **An honest handshake agrees.** If its four DHs succeed: the
initiator's message 1 succeeds and the responder reads its payload and
ephemeral; the responder's message 2 succeeds and the initiator reads
its payload; both hold the same handshake hash; each one's sending key
is the other's receiving key. -/
theorem handshake_agrees (G : S.Good) (prologue sI sR e f p1 p2 : α)
    {es ss ee se : α} (hes : S.dh e (S.pub sR) = some es) (hss : S.dh sI (S.pub sR) = some ss)
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

export Engine.Crypto (x25519 x25519Base chachaSeal chachaOpen staticOf staticPubOf xchachaSeal
  xchachaOpen randomBytes)

/-- X25519, ChaCha20-Poly1305 and SHA-256, on bytes. A message is its
32-byte public key, then the rest; a shorter one does not split. -/
def suite : Suite ByteArray where
  dh a b := let r := x25519 a b; if r.size = 32 then some r else none
  pub := x25519Base
  enc k n := chachaSeal k n.toUInt64
  dec k n := chachaOpen k n.toUInt64
  hash := Engine.sha256
  hkdf := Noise.hkdf Engine.sha256
  pair a b := a ++ b
  split m := if m.size < 32 then none else some (m.extract 0 32, m.extract 32 m.size)
  lit b := b

end Connection.Noise
