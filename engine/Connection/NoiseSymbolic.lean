/-
The handshake's secrecy and authentication, in a symbolic (Dolev-Yao)
model. The functions are Connection/Noise.lean's, the ones the
connection family's validators run (`write1`, `read1`, `sent1`,
`write2`, `read2`), computed at `α := T`, a term algebra, instead of at
bytes. Nothing here restates the protocol.

**The model.** Its assumptions, which are choices, not axioms:
- Cryptography is perfect. `T`'s constructors are free: a hash, an HKDF
  output, a ciphertext or a pair equals only itself, and nothing
  inverts a hash, an HKDF or a public key. A ciphertext opens only
  under its exact key, nonce and associated data, and nothing forges
  one without the key.
- Private exponents are names (`atom i`). Two names' DH value is
  `dh (min i j) (max i j)`, the same from either end. That is the only
  DH equation: `dh` is defined on a name and a name's public key and
  fails on anything else, so an honest party rejects a message whose
  public key is not a name's. X25519 accepts any 32 bytes, so this
  leaves out runs in which the attacker sends as a public key g^(hash
  t), a DH value, or raw bytes. In exchange, every DH value the model
  has is exact: the attacker gets DH(i, j) only if i or j is not
  secret, and does whenever it knows one and the other's public key.
  The keys in the laws below rest on DH values between honest names
  (`es` and `ss`, or `ee`), which an honest party mixes in whatever
  ephemeral key the attacker sends; but the laws say nothing of the runs
  the model leaves out.
- The attacker (`Derivable K`) is Dolev-Yao: it knows `K`, makes
  constants, pairs and unpairs, takes public keys, DHs of names it
  knows with public keys it knows, hashes and HKDFs, seals, and opens
  a ciphertext whose key it has. It is active: it hands honest parties
  any message it can derive and learns what they send back (`Sends`)
  and what they read (`Reveals`). Honest parties may be any names: any
  name serves as a static or an ephemeral, in any number of runs, so
  ephemeral reuse is covered too. They take every input from the
  attacker: prologue, peer static key, messages, and payloads, which
  is how Quiet's are (the hello is public, message 2's is empty). They
  seal session traffic under their transport keys with any payload,
  nonce and associated data the attacker picks; the node's frames
  (XChaCha20-Poly1305 under the same keys) are this free AEAD here.

**The proofs.** `Clean S t`, relative to a set `S` of secret names, is
what the attacker may know: a name outside `S`, any constant or public
key, a DH value with a name outside `S`, a hash, HKDF or pair of clean
terms, a ciphertext with clean associated data and payload. Every
attacker rule and every honest answer keeps it (`derivable_clean`),
because honest parties seal only payloads the attacker chose. The
transport keys are HKDFs over DH values of secret names, so they are
not clean, so they are not derivable. For authentication, `Part x t` is
what unpairing and opening take out of `t`; every ciphertext under a
secret key among the parts of a derivable term was sealed by an honest
party (`derivable_sealed`), and the ciphertext's key and handshake hash
then name the party and the run.

Laws:
- `good`: the symbolic suite is `Suite.Good`, so Noise.lean's
  correctness laws hold over terms too; `kk_runs`: the honest symbolic
  run completes, so the laws below are about runs that happen.
- `derivable_clean`, `derivable_sealed`.
- `kk_secret_init`, `kk_secret_resp`, `kk_secret` (active attacker).
  The initiator's keys, after `sent1` and `read2` on any message 2, are
  not derivable if the responder's static is secret and so is the
  initiator's static or its ephemeral. The responder's, after `read1`
  on any message 1 and `write2`, are not derivable if both statics are.
  `kk_secret` is both, for the four secrets and an attacker that knows
  every other name and every public key. `kk_secret_init_tight`: an
  attacker that knows the initiator's static and ephemeral does derive
  its keys, so that hypothesis is needed and the attacker is not too
  weak to break the handshake.
- `kk_forward_secret_init`, `kk_forward_secret_resp`,
  `kk_forward_secret`: with only the two ephemerals secret, the
  initiator that reads an honest message 2 and the responder that
  answers an honest message 1 hold keys that are not derivable. In
  `kk_forward_secret` the attacker also knows both statics and both
  messages.
- `kk_authentic`: an initiator accepts a derivable message 2 only if it
  is exactly what the honest responder wrote answering this
  initiator's message 1, and then both hold one session.
  `kk_authentic_resp`: a responder accepts a derivable message 1 as
  from `sI` only if it is exactly what `sI` wrote to it. Both are
  non-injective: a replayed message is accepted again.
  `exposed_parts`: the attackers of `kk_secret` and
  `kk_forward_secret` meet their hypothesis.

What it does not cover:
- Computational security: no reduction to X25519's gap-DH,
  ChaCha20-Poly1305's IND-CPA and INT-CTXT, or SHA-256 and HMAC as
  PRFs. A symbolic proof says the protocol has no logical flaw, not
  that the primitives are strong.
- Side channels and bugs below these functions: libsodium's code,
  constant time, the FFI, memory that held secrets.
- The DH equations it leaves out: exponents other than names, low-order
  and non-canonical points, X25519's clamping, the Ed25519 to X25519
  conversion of static keys.
- Nonce reuse, which a free AEAD cannot express; and secrecy of
  payloads, which the honest parties here take from the attacker.
- Replay and freshness (agreement is non-injective), and other
  sessions' keys handed to the attacker (session-key reveal).
- The node around the handshake: which ops are stored and when a close
  purges the ephemerals (`closing`, Engine/Purge.lean), which is what
  makes "once the ephemerals are gone" true.
-/
import Connection.Noise

namespace Connection.Noise

/-! ## What a run is made of, over any suite -/

section
variable {α : Type} {S : Suite α}

theorem decHash_some {st r : Sym α} {c p : α} (h : st.decHash S c = some (r, p)) :
    S.dec st.k st.n st.h c = some p ∧ r = { st.mixHash S c with n := st.n + 1 } := by
  unfold Sym.decHash at h
  cases hd : S.dec st.k st.n st.h c with
  | none => simp [hd] at h
  | some p' =>
    simp only [hd, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩

theorem write1_some {pro s e rs p m : α} {st : Sym α} (h : write1 S pro s e rs p = some (st, m)) :
    ∃ es ss, S.dh e rs = some es ∧ S.dh s rs = some ss ∧
      st = ((Sym.one S pro (S.pub s) rs (S.pub e) es ss).encHash S p).1 ∧
      m = S.pair (S.pub e) ((Sym.one S pro (S.pub s) rs (S.pub e) es ss).encHash S p).2 := by
  simp only [write1, Option.bind_eq_bind, Option.pure_def] at h
  cases hes : S.dh e rs with
  | none => simp [hes] at h
  | some es =>
    cases hss : S.dh s rs with
    | none => simp [hes, hss] at h
    | some ss =>
      simp only [hes, hss, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨es, ss, rfl, rfl, h.1.symm, h.2.symm⟩

theorem read1_some {pro s rs m re p : α} {st : Sym α} (h : read1 S pro s rs m = some (st, re, p)) :
    ∃ c es ss, S.split m = some (re, c) ∧ S.dh s re = some es ∧ S.dh s rs = some ss ∧
      (Sym.one S pro rs (S.pub s) re es ss).decHash S c = some (st, p) := by
  simp only [read1, Option.bind_eq_bind, Option.pure_def] at h
  cases hm : S.split m with
  | none => simp [hm] at h
  | some rc =>
    obtain ⟨re', c⟩ := rc
    simp only [hm, Option.bind_some] at h
    cases hes : S.dh s re' with
    | none => simp [hes] at h
    | some es =>
      cases hss : S.dh s rs with
      | none => simp [hes, hss] at h
      | some ss =>
        simp only [hes, hss, Option.bind_some] at h
        cases hd : (Sym.one S pro rs (S.pub s) re' es ss).decHash S c with
        | none => simp [hd] at h
        | some r =>
          simp only [hd, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact ⟨c, es, ss, rfl, hes, rfl, hd⟩

theorem sent1_some [DecidableEq α] {pro s e rs m p : α} {st : Sym α}
    (h : sent1 S pro s e rs m = some (st, p)) :
    ∃ c es ss, S.split m = some (S.pub e, c) ∧ S.dh e rs = some es ∧ S.dh s rs = some ss ∧
      (Sym.one S pro (S.pub s) rs (S.pub e) es ss).decHash S c = some (st, p) := by
  simp only [sent1, Option.bind_eq_bind] at h
  cases hm : S.split m with
  | none => simp [hm] at h
  | some rc =>
    obtain ⟨re, c⟩ := rc
    simp only [hm, Option.bind_some] at h
    by_cases he : re = S.pub e
    · subst he
      simp only [↓reduceIte] at h
      cases hes : S.dh e rs with
      | none => simp [hes] at h
      | some es =>
        cases hss : S.dh s rs with
        | none => simp [hes, hss] at h
        | some ss =>
          simp only [hes, hss, Option.bind_some] at h
          exact ⟨c, es, ss, rfl, rfl, rfl, h⟩
    · simp [he] at h

theorem write2_some {st : Sym α} {f rs re p m : α} {ses : Session α}
    (h : write2 S st f rs re p = some (ses, m)) :
    ∃ ee se, S.dh f re = some ee ∧ S.dh f rs = some se ∧
      ses = ⟨((Sym.two S st (S.pub f) ee se).encHash S p).1.h,
        (((Sym.two S st (S.pub f) ee se).encHash S p).1.split S).2,
        (((Sym.two S st (S.pub f) ee se).encHash S p).1.split S).1⟩ ∧
      m = S.pair (S.pub f) ((Sym.two S st (S.pub f) ee se).encHash S p).2 := by
  simp only [write2, Option.bind_eq_bind, Option.pure_def] at h
  cases hee : S.dh f re with
  | none => simp [hee] at h
  | some ee =>
    cases hse : S.dh f rs with
    | none => simp [hee, hse] at h
    | some se =>
      simp only [hee, hse, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨ee, se, rfl, rfl, h.1.symm, h.2.symm⟩

theorem read2_some {st : Sym α} {s e m p : α} {ses : Session α}
    (h : read2 S st s e m = some (ses, p)) :
    ∃ rf c ee se r, S.split m = some (rf, c) ∧ S.dh e rf = some ee ∧ S.dh s rf = some se ∧
      (Sym.two S st rf ee se).decHash S c = some (r, p) ∧
      ses = ⟨r.h, (r.split S).1, (r.split S).2⟩ := by
  simp only [read2, Option.bind_eq_bind, Option.pure_def] at h
  cases hm : S.split m with
  | none => simp [hm] at h
  | some rc =>
    obtain ⟨rf, c⟩ := rc
    simp only [hm, Option.bind_some] at h
    cases hee : S.dh e rf with
    | none => simp [hee] at h
    | some ee =>
      cases hse : S.dh s rf with
      | none => simp [hee, hse] at h
      | some se =>
        simp only [hee, hse, Option.bind_some] at h
        cases hd : (Sym.two S st rf ee se).decHash S c with
        | none => simp [hd] at h
        | some r =>
          obtain ⟨r, p'⟩ := r
          simp only [hd, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨rf, c, ee, se, r, rfl, hee, hse, hd, rfl⟩

end

namespace Symbolic

/-! ## Terms, and the suite over them -/

/-- Symbolic values. `atom i` is a name: a secret exponent, or anything
fresh. `dh i j` is the DH value of names `i ≤ j`. -/
inductive T where
  | atom (i : Nat)
  | lit (b : ByteArray)
  | pub (x : T)
  | dh (i j : Nat)
  | hash (x : T)
  | hk1 (ck ikm : T)
  | hk2 (ck ikm : T)
  | aead (k : T) (n : Nat) (ad p : T)
  | pair (a b : T)
  /-- A session frame's AEAD (XChaCha20-Poly1305, `Keys.fenc`): key,
  nonce, associated data, payload. -/
  | xaead (k n ad p : T)
  deriving DecidableEq

/-- DH over names: a name and a name's public key give their shared
value, the same from either end. Any other shape fails. -/
def dh : T → T → Option T
  | .atom i, .pub (.atom j) => some (.dh (min i j) (max i j))
  | _, _ => none

/-- A ciphertext opens under its exact key, nonce and associated data. -/
def dec (k : T) (n : Nat) (ad : T) : T → Option T
  | .aead k' n' ad' p => if k' = k ∧ n' = n ∧ ad' = ad then some p else none
  | _ => none

def unpair : T → Option (T × T)
  | .pair a b => some (a, b)
  | _ => none

/-- The symbolic suite: every operation a free constructor, but DH. -/
def sym : Suite T where
  dh := dh
  pub := .pub
  enc := .aead
  dec := dec
  hash := .hash
  hkdf ck ikm := (.hk1 ck ikm, .hk2 ck ikm)
  pair := .pair
  split := unpair
  lit := .lit

theorem dh_atom (i j : Nat) : dh (.atom i) (.pub (.atom j)) = some (.dh (min i j) (max i j)) := rfl

theorem dh_some {x y z : T} (h : dh x y = some z) :
    ∃ i j, x = .atom i ∧ y = .pub (.atom j) ∧ z = .dh (min i j) (max i j) := by
  unfold dh at h
  split at h
  · cases h; exact ⟨_, _, rfl, rfl, rfl⟩
  · cases h

theorem dec_some {k ad c p : T} {n : Nat} (h : dec k n ad c = some p) : c = .aead k n ad p := by
  unfold dec at h
  split at h
  · split at h
    · rename_i hk
      obtain ⟨rfl, rfl, rfl⟩ := hk
      cases h; rfl
    · cases h
  · cases h

theorem unpair_some {m a b : T} (h : unpair m = some (a, b)) : m = .pair a b := by
  unfold unpair at h
  split at h
  · cases h; rfl
  · cases h

/-- **The symbolic suite is good**, so every correctness law of
Noise.lean holds over terms too. -/
theorem good : sym.Good where
  dh_comm a b := by
    cases a <;> cases b <;> simp [sym, dh, Nat.min_comm, Nat.max_comm]
  dec_enc k n ad p := by simp [sym, dec]
  split_pair _ _ := rfl

/-- **The honest symbolic run completes**: for any names and payloads,
the four calls succeed and the sessions match. So the secrecy laws are
about runs that happen. -/
theorem kk_runs (pro : T) (sI sR e f : Nat) (p1 p2 : T) :
    ∃ st m1, write1 sym pro (.atom sI) (.atom e) (.pub (.atom sR)) p1 = some (st, m1) ∧
      read1 sym pro (.atom sR) (.pub (.atom sI)) m1 = some (st, .pub (.atom e), p1) ∧
      ∃ sr m2, write2 sym st (.atom f) (.pub (.atom sI)) (.pub (.atom e)) p2 = some (sr, m2) ∧
        ∃ si, read2 sym st (.atom sI) (.atom e) m2 = some (si, p2) ∧
          si.h = sr.h ∧ si.send = sr.recv ∧ si.recv = sr.send :=
  handshake_agrees good pro _ _ _ _ p1 p2 (dh_atom _ _) (dh_atom _ _) (dh_atom _ _) (dh_atom _ _)

/-! ## The attacker -/

/-- What honest parties send, as `Sends q m`: an honest party handed
`q` by the attacker sends `m`. Its secrets are any names. -/
inductive Sends : T → T → Prop
  /-- Message 1, by an initiator with static `s` and ephemeral `e`, to any static key. -/
  | request (s e : Nat) {pro rs p m1 : T} {st : Sym T} :
      write1 sym pro (.atom s) (.atom e) rs p = some (st, m1) →
      Sends (.pair pro (.pair rs p)) m1
  /-- Message 2, by a responder with static `s` and ephemeral `f`, to any message 1 it reads. -/
  | answer (s f : Nat) {pro rs m1 re p1 p m2 : T} {st : Sym T} {ses : Session T} :
      read1 sym pro (.atom s) rs m1 = some (st, re, p1) →
      write2 sym st (.atom f) rs re p = some (ses, m2) →
      Sends (.pair pro (.pair rs (.pair m1 p))) m2
  /-- Traffic from an initiator's session, as `sent1` and `read2` give it. -/
  | initSeals (s e n : Nat) {pro rs m1 m2 p1 p2 ad q : T} {st : Sym T} {ses : Session T} :
      sent1 sym pro (.atom s) (.atom e) rs m1 = some (st, p1) →
      read2 sym st (.atom s) (.atom e) m2 = some (ses, p2) →
      Sends (.pair pro (.pair rs (.pair m1 (.pair m2 (.pair ad q))))) (.aead ses.send.k n ad q)
  /-- Traffic from a responder's session, as `read1` and `write2` give it. -/
  | respSeals (s f n : Nat) {pro rs m1 re p1 p m2 ad q : T} {st : Sym T} {ses : Session T} :
      read1 sym pro (.atom s) rs m1 = some (st, re, p1) →
      write2 sym st (.atom f) rs re p = some (ses, m2) →
      Sends (.pair pro (.pair rs (.pair m1 (.pair p (.pair ad q))))) (.aead ses.send.k n ad q)

/-- What honest parties let out of what they read: the payloads. -/
inductive Reveals : T → T → Prop
  /-- Message 1's payload, as a responder with static `s` reads it. -/
  | opened (s : Nat) {pro rs m1 re p1 : T} {st : Sym T} :
      read1 sym pro (.atom s) rs m1 = some (st, re, p1) →
      Reveals (.pair pro (.pair rs m1)) p1
  /-- Message 2's payload, as an initiator with static `s` and ephemeral `e` reads it. -/
  | accepted (s e : Nat) {pro rs m1 m2 p1 p2 : T} {st : Sym T} {ses : Session T} :
      sent1 sym pro (.atom s) (.atom e) rs m1 = some (st, p1) →
      read2 sym st (.atom s) (.atom e) m2 = some (ses, p2) →
      Reveals (.pair pro (.pair rs (.pair m1 m2))) p2

/-- **The attacker**: what it derives from `K`, by the Dolev-Yao rules
and by asking honest parties. -/
inductive Derivable (K : T → Prop) : T → Prop
  | know {t} : K t → Derivable K t
  | lit (b : ByteArray) : Derivable K (.lit b)
  | pair {a b} : Derivable K a → Derivable K b → Derivable K (.pair a b)
  | fst {a b} : Derivable K (.pair a b) → Derivable K a
  | snd {a b} : Derivable K (.pair a b) → Derivable K b
  | pub {x} : Derivable K x → Derivable K (.pub x)
  | dh {x y z} : Derivable K x → Derivable K y → sym.dh x y = some z → Derivable K z
  | hash {x} : Derivable K x → Derivable K (.hash x)
  | hk1 {a b} : Derivable K a → Derivable K b → Derivable K (.hk1 a b)
  | hk2 {a b} : Derivable K a → Derivable K b → Derivable K (.hk2 a b)
  | encrypt {k ad p} (n : Nat) : Derivable K k → Derivable K ad → Derivable K p →
      Derivable K (.aead k n ad p)
  | decrypt {k n ad p} : Derivable K (.aead k n ad p) → Derivable K k → Derivable K p
  | sent {q m} : Derivable K q → Sends q m → Derivable K m
  | revealed {q m} : Derivable K q → Reveals q m → Derivable K m

/-! ## What the attacker may know -/

/-- What may be known when the names in `S` are secret. -/
def Clean (S : Nat → Prop) : T → Prop
  | .atom i => ¬ S i
  | .lit _ => True
  | .pub _ => True
  | .dh i j => ¬ S i ∨ ¬ S j
  | .hash x => Clean S x
  | .hk1 a b => Clean S a ∧ Clean S b
  | .hk2 a b => Clean S a ∧ Clean S b
  | .aead _ _ ad p => Clean S ad ∧ Clean S p
  | .pair a b => Clean S a ∧ Clean S b
  | .xaead _ n ad p => Clean S n ∧ Clean S ad ∧ Clean S p

section
variable {S : Nat → Prop}

theorem clean_dh {i j : Nat} : Clean S (.dh (min i j) (max i j)) ↔ ¬ S i ∨ ¬ S j := by
  by_cases hij : i ≤ j
  · simp [Clean, Nat.min_eq_left hij, Nat.max_eq_right hij]
  · have hji : j ≤ i := by omega
    simp only [Clean, Nat.min_eq_right hji, Nat.max_eq_left hji]
    exact Or.comm

theorem clean_one {pro si sr epub es ss : T} (h1 : Clean S pro) (h2 : Clean S si) (h3 : Clean S sr)
    (h4 : Clean S epub) : Clean S (Sym.one sym pro si sr epub es ss).h := by
  simp [Sym.one, Sym.mixKey, Sym.mixHash, Sym.start, sym, Clean, *]

theorem clean_two {st : Sym T} {fpub ee se : T} (h1 : Clean S st.h) (h2 : Clean S fpub) :
    Clean S (Sym.two sym st fpub ee se).h := by
  simp [Sym.two, Sym.mixKey, Sym.mixHash, sym, Clean, *]

theorem clean_encHash {st : Sym T} {p : T} (hs : Clean S st.h) (hp : Clean S p) :
    Clean S (st.encHash sym p).2 := by
  simp [Sym.encHash, sym, Clean, *]

theorem clean_decHash {st r : Sym T} {c p : T} (h : st.decHash sym c = some (r, p))
    (hs : Clean S st.h) (hc : Clean S c) : Clean S r.h ∧ Clean S p := by
  obtain ⟨hd, rfl⟩ := decHash_some h
  have hc' := dec_some hd
  subst hc'
  exact ⟨⟨hs, hc⟩, hc.2⟩

/-- Honest parties send only clean messages when handed clean ones. -/
theorem sends_clean {q m : T} (h : Sends q m) (hq : Clean S q) : Clean S m := by
  cases h with
  | request s e h =>
    obtain ⟨es, ss, -, -, -, rfl⟩ := write1_some h
    obtain ⟨hpro, hrs, hp⟩ := hq
    exact ⟨trivial, clean_encHash (clean_one hpro trivial hrs trivial) hp⟩
  | answer s f h1 h2 =>
    obtain ⟨c, es, ss, hm, -, -, hd⟩ := read1_some h1
    obtain ⟨hpro, hrs, hm1, hp⟩ := hq
    rw [unpair_some hm] at hm1
    have hst := (clean_decHash hd (clean_one hpro hrs trivial hm1.1) hm1.2).1
    obtain ⟨ee, se, -, -, -, rfl⟩ := write2_some h2
    exact ⟨trivial, clean_encHash (clean_two hst trivial) hp⟩
  | initSeals s e n h1 h2 => exact hq.2.2.2.2
  | respSeals s f n h1 h2 => exact hq.2.2.2.2

/-- What honest parties read from clean messages is clean. -/
theorem reveals_clean {q m : T} (h : Reveals q m) (hq : Clean S q) : Clean S m := by
  cases h with
  | opened s h =>
    obtain ⟨c, es, ss, hm, -, -, hd⟩ := read1_some h
    obtain ⟨hpro, hrs, hm1⟩ := hq
    rw [unpair_some hm] at hm1
    exact (clean_decHash hd (clean_one hpro hrs trivial hm1.1) hm1.2).2
  | accepted s e h1 h2 =>
    obtain ⟨c, es, ss, hm, -, -, hd⟩ := sent1_some h1
    obtain ⟨hpro, hrs, hm1, hm2⟩ := hq
    rw [unpair_some hm] at hm1
    have hst := (clean_decHash hd (clean_one hpro trivial hrs trivial) hm1.2).1
    obtain ⟨rf, c', ee, se, r, hm', -, -, hd', -⟩ := read2_some h2
    rw [unpair_some hm'] at hm2
    exact (clean_decHash hd' (clean_two hst hm2.1) hm2.2).2

/-- **The attacker derives only clean terms**, if it starts from clean ones. -/
theorem derivable_clean {K : T → Prop} (hK : ∀ t, K t → Clean S t) {t : T} (h : Derivable K t) :
    Clean S t := by
  induction h with
  | know h => exact hK _ h
  | lit => trivial
  | pair _ _ ha hb => exact ⟨ha, hb⟩
  | fst _ ih => exact ih.1
  | snd _ ih => exact ih.2
  | pub => trivial
  | dh _ _ hz hx _ =>
    obtain ⟨i, j, rfl, rfl, rfl⟩ := dh_some hz
    exact clean_dh.2 (Or.inl hx)
  | hash _ ih => exact ih
  | hk1 _ _ ha hb => exact ⟨ha, hb⟩
  | hk2 _ _ ha hb => exact ⟨ha, hb⟩
  | encrypt _ _ _ _ _ had hp => exact ⟨had, hp⟩
  | decrypt _ _ ih _ => exact ih.2
  | sent _ hs ih => exact sends_clean hs ih
  | revealed _ hr ih => exact reveals_clean hr ih

/-! ## The session keys -/

/-- The handshake hash before message 1's payload. -/
def hOne (pro si sr epub : T) : T :=
  .hash (.pair (.hash (.pair (.hash (.pair (.hash (.pair (.lit protocol) pro)) si)) sr)) epub)

theorem write1_msg {pro s e rs p m : T} {st : Sym T} (h : write1 sym pro s e rs p = some (st, m)) :
    ∃ es ss, m = .pair (.pub e) (.aead (.hk2 (.hk1 (.lit protocol) es) ss) 0 (hOne pro (.pub s) rs (.pub e)) p) := by
  obtain ⟨es, ss, -, -, -, rfl⟩ := write1_some h
  exact ⟨es, ss, rfl⟩

theorem sent1_ck {pro s e rs m p : T} {st : Sym T} (h : sent1 sym pro s e rs m = some (st, p)) :
    ∃ es ss c, m = .pair (.pub e) c ∧ dh e rs = some es ∧ dh s rs = some ss ∧
      st.ck = .hk1 (.hk1 (.lit protocol) es) ss ∧ st.h = .hash (.pair (hOne pro (.pub s) rs (.pub e)) c) := by
  obtain ⟨c, es, ss, hm, hes, hss, hd⟩ := sent1_some h
  obtain ⟨-, rfl⟩ := decHash_some hd
  exact ⟨es, ss, c, unpair_some hm, hes, hss, rfl, rfl⟩

theorem read1_ck {pro s rs m re p : T} {st : Sym T} (h : read1 sym pro s rs m = some (st, re, p)) :
    ∃ es ss c, m = .pair re c ∧ dh s re = some es ∧ dh s rs = some ss ∧
      st.ck = .hk1 (.hk1 (.lit protocol) es) ss ∧ st.h = .hash (.pair (hOne pro rs (.pub s) re) c) ∧
      c = .aead (.hk2 (.hk1 (.lit protocol) es) ss) 0 (hOne pro rs (.pub s) re) p := by
  obtain ⟨c, es, ss, hm, hes, hss, hd⟩ := read1_some h
  obtain ⟨hdec, rfl⟩ := decHash_some hd
  exact ⟨es, ss, c, unpair_some hm, hes, hss, rfl, rfl, dec_some hdec⟩

theorem read2_keys {st : Sym T} {s e m p : T} {ses : Session T}
    (h : read2 sym st s e m = some (ses, p)) :
    ∃ rf ee se, m = .pair rf (.aead (.hk2 (.hk1 st.ck ee) se) 0 (.hash (.pair st.h rf)) p) ∧
      dh e rf = some ee ∧ dh s rf = some se ∧
      ses.send.k = .hk1 (.hk1 (.hk1 st.ck ee) se) (.lit .empty) ∧
      ses.recv.k = .hk2 (.hk1 (.hk1 st.ck ee) se) (.lit .empty) := by
  obtain ⟨rf, c, ee, se, r, hm, hee, hse, hd, rfl⟩ := read2_some h
  obtain ⟨hdec, rfl⟩ := decHash_some hd
  refine ⟨rf, ee, se, ?_, hee, hse, rfl, rfl⟩
  rw [unpair_some hm, dec_some hdec]
  rfl

theorem write2_keys {st : Sym T} {f rs re p m : T} {ses : Session T}
    (h : write2 sym st f rs re p = some (ses, m)) :
    ∃ ee se, m = .pair (.pub f) (.aead (.hk2 (.hk1 st.ck ee) se) 0 (.hash (.pair st.h (.pub f))) p) ∧
      dh f re = some ee ∧ dh f rs = some se ∧
      ses.send.k = .hk2 (.hk1 (.hk1 st.ck ee) se) (.lit .empty) ∧
      ses.recv.k = .hk1 (.hk1 (.hk1 st.ck ee) se) (.lit .empty) := by
  obtain ⟨ee, se, hee, hse, rfl, rfl⟩ := write2_some h
  exact ⟨ee, se, rfl, hee, hse, rfl, rfl⟩

/-- Keys over an unclean chaining key or DH value are unclean. -/
theorem keys_unclean {ck ee se : T} (h : ¬ Clean S ck ∨ ¬ Clean S ee) :
    ¬ Clean S (.hk1 (.hk1 (.hk1 ck ee) se) (.lit .empty)) ∧
      ¬ Clean S (.hk2 (.hk1 (.hk1 ck ee) se) (.lit .empty)) := by
  have : ¬ Clean S (.hk1 (.hk1 ck ee) se) := fun hc => h.elim (· hc.1.1) (· hc.1.2)
  exact ⟨fun hc => this hc.1, fun hc => this hc.1⟩

theorem not_derivable {K : T → Prop} (hK : ∀ t, K t → Clean S t) {t : T} (h : ¬ Clean S t) :
    ¬ Derivable K t := fun hd => h (derivable_clean hK hd)

theorem keys_secret {K : T → Prop} (hK : ∀ t, K t → Clean S t) {ck ee se : T}
    (h : ¬ Clean S ck ∨ ¬ Clean S ee) :
    ¬ Derivable K (.hk1 (.hk1 (.hk1 ck ee) se) (.lit .empty)) ∧
      ¬ Derivable K (.hk2 (.hk1 (.hk1 ck ee) se) (.lit .empty)) :=
  ⟨not_derivable hK (keys_unclean h).1, not_derivable hK (keys_unclean h).2⟩

/-! ## Secrecy against an active attacker -/

/-- The initiator's chaining key after message 1 rests on `es` and `ss`. -/
theorem init_unclean {sI sR e : Nat} (hR : S sR) (hIe : S sI ∨ S e) {pro m1 p1 : T} {st : Sym T}
    (h1 : sent1 sym pro (.atom sI) (.atom e) (.pub (.atom sR)) m1 = some (st, p1)) :
    ¬ Clean S st.ck := by
  obtain ⟨es, ss, _, -, hes, hss, hck, -⟩ := sent1_ck h1
  rw [dh_atom] at hes hss
  cases hes; cases hss
  rw [hck]
  rintro ⟨⟨-, hes⟩, hss⟩
  rcases hIe with hI | he
  · exact (clean_dh.1 hss).elim (· hI) (· hR)
  · exact (clean_dh.1 hes).elim (· he) (· hR)

/-- **The initiator's session keys are secret.** An initiator with static
`sI` and ephemeral `e`, dialing `sR`, recovers its state with `sent1`
and accepts any message 2 with `read2`, as `Established` does. If `sR`
is secret, and `sI` or `e` is, its keys are not derivable: they rest on
`es` and on `ss`. -/
theorem kk_secret_init {K : T → Prop} (hK : ∀ t, K t → Clean S t) {sI sR e : Nat}
    (hR : S sR) (hIe : S sI ∨ S e) {pro m1 m2 p1 p2 : T} {st : Sym T} {si : Session T}
    (h1 : sent1 sym pro (.atom sI) (.atom e) (.pub (.atom sR)) m1 = some (st, p1))
    (h2 : read2 sym st (.atom sI) (.atom e) m2 = some (si, p2)) :
    ¬ Derivable K si.send.k ∧ ¬ Derivable K si.recv.k := by
  obtain ⟨_, _, _, -, -, -, hs, hr⟩ := read2_keys h2
  rw [hs, hr]
  exact keys_secret hK (Or.inl (init_unclean hR hIe h1))

/-- **The responder's session keys are secret.** A responder with static
`sR` reads any message 1 as from `sI` with `read1` and answers with
`write2`, as `Established` does. If both statics are secret, its keys
are not derivable: they rest on `ss`. -/
theorem kk_secret_resp {K : T → Prop} (hK : ∀ t, K t → Clean S t) {sI sR f : Nat}
    (hI : S sI) (hR : S sR) {pro m1 m2 re p1 p2 : T} {st : Sym T} {sr : Session T}
    (h1 : read1 sym pro (.atom sR) (.pub (.atom sI)) m1 = some (st, re, p1))
    (h2 : write2 sym st (.atom f) (.pub (.atom sI)) re p2 = some (sr, m2)) :
    ¬ Derivable K sr.send.k ∧ ¬ Derivable K sr.recv.k := by
  obtain ⟨_, ss, _, -, -, hss, hck, -, -⟩ := read1_ck h1
  rw [dh_atom] at hss
  cases hss
  have hc : ¬ Clean S st.ck := by
    rw [hck]
    rintro ⟨-, hss⟩
    exact (clean_dh.1 hss).elim (· hR) (· hI)
  obtain ⟨_, _, -, -, -, hs, hr⟩ := write2_keys h2
  rw [hs, hr]
  exact (keys_secret hK (Or.inl hc)).symm

end

/-- What the attacker starts with when the names in `S` are secret:
every other name, and every public key. -/
def Exposed (S : Nat → Prop) (t : T) : Prop := (∃ i, t = .atom i ∧ ¬ S i) ∨ ∃ x, t = .pub x

theorem exposed_clean {S : Nat → Prop} {t : T} (h : Exposed S t) : Clean S t := by
  rcases h with ⟨i, rfl, hi⟩ | ⟨x, rfl⟩
  · exact hi
  · trivial

/-- A session's four secrets: both statics, both ephemerals. -/
def secrets (sI sR e f : Nat) (i : Nat) : Prop := i = sI ∨ i = sR ∨ i = e ∨ i = f

/-- **KK keeps session keys secret against an active attacker**, which
knows every name but the session's four secrets and every public key,
and talks to honest parties at will: whatever message 2 the initiator
accepts, and whatever message 1 the responder answers, neither side's
keys are derivable. -/
theorem kk_secret {sI sR e f : Nat} {pro pro' m1 m2 m1' m2' re p1 p2 q1 q2 : T} {st st' : Sym T}
    {si sr : Session T}
    (h1 : sent1 sym pro (.atom sI) (.atom e) (.pub (.atom sR)) m1 = some (st, p1))
    (h2 : read2 sym st (.atom sI) (.atom e) m2 = some (si, p2))
    (h3 : read1 sym pro' (.atom sR) (.pub (.atom sI)) m1' = some (st', re, q1))
    (h4 : write2 sym st' (.atom f) (.pub (.atom sI)) re q2 = some (sr, m2')) :
    ¬ Derivable (Exposed (secrets sI sR e f)) si.send.k ∧
      ¬ Derivable (Exposed (secrets sI sR e f)) si.recv.k ∧
      ¬ Derivable (Exposed (secrets sI sR e f)) sr.send.k ∧
      ¬ Derivable (Exposed (secrets sI sR e f)) sr.recv.k :=
  let hK := fun _ => exposed_clean
  ⟨(kk_secret_init hK (by simp [secrets]) (Or.inl (by simp [secrets])) h1 h2).1,
    (kk_secret_init hK (by simp [secrets]) (Or.inl (by simp [secrets])) h1 h2).2,
    (kk_secret_resp hK (by simp [secrets]) (by simp [secrets]) h3 h4).1,
    (kk_secret_resp hK (by simp [secrets]) (by simp [secrets]) h3 h4).2⟩

/-- **The secrets are needed.** An attacker that knows the initiator's
static and ephemeral (and every public key) derives the keys of every
session `kk_secret_init` speaks of: the hypothesis that one of them is
secret cannot be dropped, and `Derivable` is strong enough to break the
handshake when it should. -/
theorem kk_secret_init_tight {S : Nat → Prop} {sI sR e : Nat} (hI : ¬ S sI) (he : ¬ S e)
    {pro m1 m2 p1 p2 : T} {st : Sym T} {si : Session T}
    (h1 : sent1 sym pro (.atom sI) (.atom e) (.pub (.atom sR)) m1 = some (st, p1))
    (h2 : read2 sym st (.atom sI) (.atom e) m2 = some (si, p2)) :
    Derivable (Exposed S) si.send.k ∧ Derivable (Exposed S) si.recv.k := by
  obtain ⟨es, ss, _, -, hes, hss, hck, -⟩ := sent1_ck h1
  obtain ⟨rf, ee, se, -, hee, hse, hs, hr⟩ := read2_keys h2
  obtain ⟨_, j, -, rfl, -⟩ := dh_some hee
  have dI : Derivable (Exposed S) (.atom sI) := .know (.inl ⟨sI, rfl, hI⟩)
  have dE : Derivable (Exposed S) (.atom e) := .know (.inl ⟨e, rfl, he⟩)
  have dP : ∀ x, Derivable (Exposed S) (.pub x) := fun x => .know (.inr ⟨x, rfl⟩)
  have dck : Derivable (Exposed S) st.ck := by
    rw [hck]; exact .hk1 (.hk1 (.lit _) (.dh dE (dP (.atom sR)) hes)) (.dh dI (dP (.atom sR)) hss)
  have dx := Derivable.hk1 (.hk1 dck (.dh dE (dP (.atom j)) hee)) (.dh dI (dP (.atom j)) hse)
  rw [hs, hr]
  exact ⟨.hk1 dx (.lit _), .hk2 dx (.lit _)⟩

/-! ## Forward secrecy -/

section
variable {S : Nat → Prop}

/-- **The initiator's keys survive its static keys.** An initiator with
ephemeral `e` that reads a message 2 written with ephemeral `f` holds
keys that rest on `ee`: if `e` and `f` are secret, they are not
derivable, whatever else is known, both statics included. -/
theorem kk_forward_secret_init {K : T → Prop} (hK : ∀ t, K t → Clean S t) {e f : Nat}
    (he : S e) (hf : S f) {st st' : Sym T} {s rs re q m2 p2 : T} {sr si : Session T}
    (hw : write2 sym st' (.atom f) rs re q = some (sr, m2))
    (hr : read2 sym st s (.atom e) m2 = some (si, p2)) :
    ¬ Derivable K si.send.k ∧ ¬ Derivable K si.recv.k := by
  obtain ⟨_, _, hm2, -⟩ := write2_keys hw
  obtain ⟨rf, ee, se, hm, hee, -, hs, hr⟩ := read2_keys hr
  rw [hm2] at hm
  injection hm with hrf
  subst hrf
  rw [dh_atom] at hee
  cases hee
  rw [hs, hr]
  exact keys_secret hK (Or.inr fun h => (clean_dh.1 h).elim (· he) (· hf))

/-- **The responder's keys survive its static keys.** A responder with
ephemeral `f` that answers a message 1 written with ephemeral `e` holds
keys that rest on `ee`: if `e` and `f` are secret, they are not
derivable, whatever else is known. -/
theorem kk_forward_secret_resp {K : T → Prop} (hK : ∀ t, K t → Clean S t) {e f : Nat}
    (he : S e) (hf : S f) {st0 st : Sym T} {pro0 s0 rs0 p pro s rs m1 re p1 q m2 : T} {sr : Session T}
    (hw : write1 sym pro0 s0 (.atom e) rs0 p = some (st0, m1))
    (hr : read1 sym pro s rs m1 = some (st, re, p1))
    (h2 : write2 sym st (.atom f) rs re q = some (sr, m2)) :
    ¬ Derivable K sr.send.k ∧ ¬ Derivable K sr.recv.k := by
  obtain ⟨_, _, hm1⟩ := write1_msg hw
  obtain ⟨_, _, _, hm, -, -, -, -, -⟩ := read1_ck hr
  rw [hm1] at hm
  injection hm with hre
  subst hre
  obtain ⟨ee, se, -, hee, -, hs, hr⟩ := write2_keys h2
  rw [dh_atom] at hee
  cases hee
  rw [hs, hr]
  exact (keys_secret hK (Or.inr fun h => (clean_dh.1 h).elim (· hf) (· he))).symm

end

/-- **KK is forward secret.** An honest run, with prologue and payloads
in the clear. Afterwards the attacker knows both statics, every other
name but the two ephemerals, every public key, and both messages; it
still derives neither side's keys. So once the ephemerals are purged,
nothing left opens the session. -/
theorem kk_forward_secret {sI sR e f : Nat} (hI : sI ≠ e ∧ sI ≠ f) (hR : sR ≠ e ∧ sR ≠ f)
    {pro b1 b2 : ByteArray} {st st' : Sym T} {m1 m2 re q1 q2 : T} {sr si : Session T}
    (h1 : write1 sym (.lit pro) (.atom sI) (.atom e) (.pub (.atom sR)) (.lit b1) = some (st, m1))
    (h2 : read1 sym (.lit pro) (.atom sR) (.pub (.atom sI)) m1 = some (st', re, q1))
    (h3 : write2 sym st' (.atom f) (.pub (.atom sI)) re (.lit b2) = some (sr, m2))
    (h4 : read2 sym st (.atom sI) (.atom e) m2 = some (si, q2)) :
    let K := Exposed (fun i => i = e ∨ i = f)
    Derivable K (.atom sI) ∧ Derivable K (.atom sR) ∧ Derivable K m1 ∧ Derivable K m2 ∧
      ¬ Derivable K si.send.k ∧ ¬ Derivable K si.recv.k ∧
      ¬ Derivable K sr.send.k ∧ ¬ Derivable K sr.recv.k := by
  intro K
  have hK : ∀ t, K t → Clean (fun i => i = e ∨ i = f) t := fun _ => exposed_clean
  have hsI : Derivable K (.atom sI) := .know (.inl ⟨sI, rfl, by omega⟩)
  have hsR : Derivable K (.atom sR) := .know (.inl ⟨sR, rfl, by omega⟩)
  have hpub : ∀ x, Derivable K (.pub x) := fun x => .know (.inr ⟨x, rfl⟩)
  have hm1 : Derivable K m1 :=
    .sent (.pair (.lit _) (.pair (hpub _) (.lit _))) (.request sI e h1)
  have hm2 : Derivable K m2 :=
    .sent (.pair (.lit _) (.pair (hpub _) (.pair hm1 (.lit _)))) (.answer sR f h2 h3)
  have ⟨i1, i2⟩ := kk_forward_secret_init hK (Or.inl rfl) (Or.inr rfl) h3 h4
  have ⟨r1, r2⟩ := kk_forward_secret_resp hK (Or.inl rfl) (Or.inr rfl) h1 h2 h3
  exact ⟨hsI, hsR, hm1, hm2, i1, i2, r1, r2⟩

/-! ## Authentication -/

/-- `Part x t`: `x` comes out of `t` by unpairing and opening. -/
inductive Part (x : T) : T → Prop
  | refl : Part x x
  | fst {a b : T} : Part x a → Part x (.pair a b)
  | snd {a b : T} : Part x b → Part x (.pair a b)
  | body {k ad p : T} {n : Nat} : Part x p → Part x (.aead k n ad p)

/-- `c` is sealed in a message an honest party sent, handed something
the attacker derived. -/
def Sealed (K : T → Prop) (c : T) : Prop :=
  ∃ q m, Derivable K q ∧ Sends q m ∧ (m = c ∨ ∃ x, m = .pair x c)

section
variable {S : Nat → Prop} {K : T → Prop}

theorem sends_sealed {q m : T} (hq : Derivable K q) (hs : Sends q m)
    (ih : ∀ {k n ad p}, Part (.aead k n ad p) q → ¬ Clean S k → Sealed K (.aead k n ad p))
    {k ad p : T} {n : Nat} (hp : Part (.aead k n ad p) m) (hk : ¬ Clean S k) :
    Sealed K (.aead k n ad p) := by
  cases hs with
  | request s e h =>
    obtain ⟨_, _, rfl⟩ := write1_msg h
    cases hp with
    | fst hp => cases hp
    | snd hp =>
      cases hp with
      | refl => exact ⟨_, _, hq, .request s e h, .inr ⟨_, rfl⟩⟩
      | body hp => exact ih (.snd (.snd hp)) hk
  | answer s f h1 h2 =>
    obtain ⟨_, _, rfl, -⟩ := write2_keys h2
    cases hp with
    | fst hp => cases hp
    | snd hp =>
      cases hp with
      | refl => exact ⟨_, _, hq, .answer s f h1 h2, .inr ⟨_, rfl⟩⟩
      | body hp => exact ih (.snd (.snd (.snd hp))) hk
  | initSeals s e n' h1 h2 =>
    cases hp with
    | refl => exact ⟨_, _, hq, .initSeals s e n h1 h2, .inl rfl⟩
    | body hp => exact ih (.snd (.snd (.snd (.snd (.snd hp))))) hk
  | respSeals s f n' h1 h2 =>
    cases hp with
    | refl => exact ⟨_, _, hq, .respSeals s f n h1 h2, .inl rfl⟩
    | body hp => exact ih (.snd (.snd (.snd (.snd (.snd hp))))) hk

theorem reveals_sealed {q m : T} (hr : Reveals q m)
    (ih : ∀ {k n ad p}, Part (.aead k n ad p) q → ¬ Clean S k → Sealed K (.aead k n ad p))
    {k ad p : T} {n : Nat} (hp : Part (.aead k n ad p) m) (hk : ¬ Clean S k) :
    Sealed K (.aead k n ad p) := by
  cases hr with
  | opened s h =>
    obtain ⟨_, _, _, rfl, -, -, -, -, rfl⟩ := read1_ck h
    exact ih (.snd (.snd (.snd (.body hp)))) hk
  | accepted s e h1 h2 =>
    obtain ⟨_, _, _, rfl, -⟩ := read2_keys h2
    exact ih (.snd (.snd (.snd (.snd (.body hp))))) hk

/-- **Every ciphertext under a secret key that the attacker can take
out of what it derives was sealed by an honest party**, if it starts
with none. -/
theorem derivable_sealed (hK : ∀ t, K t → Clean S t)
    (hK2 : ∀ t, K t → ∀ {k n ad p}, Part (.aead k n ad p) t → Clean S k) {t : T}
    (h : Derivable K t) :
    ∀ {k n ad p}, Part (.aead k n ad p) t → ¬ Clean S k → Sealed K (.aead k n ad p) := by
  induction h with
  | know h => exact fun hp hk => absurd (hK2 _ h hp) hk
  | lit => intro _ _ _ _ hp; cases hp
  | pair _ _ iha ihb =>
    intro _ _ _ _ hp hk
    cases hp with
    | fst hp => exact iha hp hk
    | snd hp => exact ihb hp hk
  | fst _ ih => exact fun hp hk => ih (.fst hp) hk
  | snd _ ih => exact fun hp hk => ih (.snd hp) hk
  | pub => intro _ _ _ _ hp; cases hp
  | dh _ _ hz =>
    intro _ _ _ _ hp
    obtain ⟨i, j, rfl, rfl, rfl⟩ := dh_some hz
    cases hp
  | hash => intro _ _ _ _ hp; cases hp
  | hk1 => intro _ _ _ _ hp; cases hp
  | hk2 => intro _ _ _ _ hp; cases hp
  | encrypt n hk' _ _ _ _ ihp =>
    intro _ _ _ _ hp hk
    cases hp with
    | refl => exact absurd (derivable_clean hK hk') hk
    | body hp => exact ihp hp hk
  | decrypt _ _ ih _ => exact fun hp hk => ih (.body hp) hk
  | sent hq hs ih => exact fun hp hk => sends_sealed hq hs ih hp hk
  | revealed _ hr ih => exact fun hp hk => reveals_sealed hr ih hp hk

/-- **The initiator authenticates the responder.** An initiator with
static `sI` and ephemeral `e` that dialed `sR` accepts a message 2 the
attacker can derive only if it is exactly the message 2 the honest
responder `sR` wrote, with some ephemeral `f`, answering this very
message 1 as from `sI`; and then the two sessions match. As for
secrecy, `sR` must be secret, and `sI` or `e`. The attacker may start
with any clean terms that hold no ciphertext under a secret key. -/
theorem kk_authentic (hK : ∀ t, K t → Clean S t)
    (hK2 : ∀ t, K t → ∀ {k n ad p}, Part (.aead k n ad p) t → Clean S k)
    {sI sR e : Nat} (hR : S sR) (hIe : S sI ∨ S e) {pro m1 m2 p1 p2 : T} {st : Sym T} {si : Session T}
    (h1 : sent1 sym pro (.atom sI) (.atom e) (.pub (.atom sR)) m1 = some (st, p1))
    (h2 : read2 sym st (.atom sI) (.atom e) m2 = some (si, p2)) (hm2 : Derivable K m2) :
    ∃ f p sr, read1 sym pro (.atom sR) (.pub (.atom sI)) m1 = some (st, .pub (.atom e), p1) ∧
      write2 sym st (.atom f) (.pub (.atom sI)) (.pub (.atom e)) p = some (sr, m2) ∧
      si.h = sr.h ∧ si.send = sr.recv ∧ si.recv = sr.send := by
  have hc := init_unclean hR hIe h1
  obtain ⟨es, ss, c1, hm1, -, -, hck, hh⟩ := sent1_ck h1
  obtain ⟨rf, ee, se, hm, -, hse, -, -⟩ := read2_keys h2
  have hk : ¬ Clean S (.hk2 (.hk1 st.ck ee) se) := fun h => hc h.1.1
  have hpart : Part (.aead (.hk2 (.hk1 st.ck ee) se) 0 (.hash (.pair st.h rf)) p2) m2 := by
    rw [hm]; exact .snd .refl
  obtain ⟨q, m, -, hs, hmc⟩ := derivable_sealed hK hK2 hm2 hpart hk
  cases hs with
  | request s' e' hw =>
    obtain ⟨_, _, rfl⟩ := write1_msg hw
    rcases hmc with h | ⟨x, h⟩
    · cases h
    · simp only [T.pair.injEq, T.aead.injEq, T.hk2.injEq, T.hk1.injEq] at h
      have := h.2.1.1.1
      rw [hck] at this
      cases this
  | answer s' f' hr' hw' =>
    obtain ⟨_, _, hM, -⟩ := write2_keys hw'
    rcases hmc with h | ⟨x, h⟩
    · rw [hM] at h; cases h
    · have h' := h
      rw [hM] at h'
      simp only [T.pair.injEq, T.aead.injEq, T.hash.injEq] at h'
      obtain ⟨hx, -, -, ⟨hst, hrf⟩, -⟩ := h'
      have hmm : m = m2 := by rw [h, hm, ← hx, ← hrf]
      obtain ⟨_, _, c1', hm1', -, -, -, hh', -⟩ := read1_ck hr'
      rw [hh', hh] at hst
      simp only [hOne, T.hash.injEq, T.pair.injEq, T.pub.injEq, T.atom.injEq] at hst
      obtain ⟨⟨⟨⟨⟨-, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := hst
      rw [hm1', ← hm1] at hr'
      obtain ⟨rfl, rfl, -⟩ := sent1_read1 good h1 hr'
      rw [hmm] at hw'
      exact ⟨f', _, _, hr', hw', read2_write2' good hw' h2⟩
  | initSeals s' e' n' h1' h2' =>
    obtain ⟨_, _, _, -, -, -, hs1, -⟩ := read2_keys h2'
    rcases hmc with h | ⟨x, h⟩
    · simp only [T.aead.injEq] at h
      rw [hs1] at h
      cases h.1
    · cases h
  | respSeals s' f' n' h1' h2' =>
    obtain ⟨_, _, -, -, -, hs1, -⟩ := write2_keys h2'
    rcases hmc with h | ⟨x, h⟩
    · simp only [T.aead.injEq] at h
      rw [hs1] at h
      simp only [T.hk2.injEq] at h
      obtain ⟨_, _, -, -, rfl⟩ := dh_some hse
      cases h.1.2
    · cases h


/-- **The responder authenticates the initiator.** A responder with
static `sR` that reads a message 1 the attacker can derive as from `sI`
accepts it only if it is exactly the message 1 the honest initiator
`sI` wrote to `sR`, with some ephemeral `e` and this payload; and the
responder holds the state the initiator wrote. Both statics must be
secret: message 1 rests on `ss` alone, so with `sR`'s secret the
attacker could write it (key-compromise impersonation, as Noise says of
KK's first message). Message 1 can be replayed; this is agreement on
its content, not on its freshness. -/
theorem kk_authentic_resp (hK : ∀ t, K t → Clean S t)
    (hK2 : ∀ t, K t → ∀ {k n ad p}, Part (.aead k n ad p) t → Clean S k)
    {sI sR : Nat} (hI : S sI) (hR : S sR) {pro m1 re p1 : T} {st : Sym T}
    (h1 : read1 sym pro (.atom sR) (.pub (.atom sI)) m1 = some (st, re, p1)) (hm1 : Derivable K m1) :
    ∃ e, re = .pub (.atom e) ∧ write1 sym pro (.atom sI) (.atom e) (.pub (.atom sR)) p1 = some (st, m1) := by
  obtain ⟨es, ss, c, hm, -, hss, hck, -, hc⟩ := read1_ck h1
  rw [dh_atom] at hss
  cases hss
  have hk : ¬ Clean S (.hk2 (.hk1 (.lit protocol) es) (.dh (min sR sI) (max sR sI))) :=
    fun h => (clean_dh.1 h.2).elim (· hR) (· hI)
  have hpart : Part (.aead (.hk2 (.hk1 (.lit protocol) es) (.dh (min sR sI) (max sR sI))) 0
      (hOne pro (.pub (.atom sI)) (.pub (.atom sR)) re) p1) m1 := by
    rw [hm, hc]; exact .snd .refl
  obtain ⟨q, m, -, hs, hmc⟩ := derivable_sealed hK hK2 hm1 hpart hk
  cases hs with
  | request s' e' hw =>
    obtain ⟨_, _, hM⟩ := write1_msg hw
    rcases hmc with h | ⟨x, h⟩
    · rw [hM] at h; cases h
    · have h' := h
      rw [hM] at h'
      simp only [T.pair.injEq, T.aead.injEq] at h'
      obtain ⟨hx, -, -, hh, rfl⟩ := h'
      simp only [hOne, T.hash.injEq, T.pair.injEq, T.pub.injEq, T.atom.injEq] at hh
      obtain ⟨⟨⟨⟨-, rfl⟩, rfl⟩, rfl⟩, hre⟩ := hh
      have hmm : m = m1 := by rw [h, hm, hc, ← hx, hre]
      rw [hmm] at hw
      obtain ⟨rfl, -, -⟩ := sent1_read1 good (sent1_write1 good hw) h1
      exact ⟨e', hre.symm, hw⟩
  | answer s' f' hr' hw' =>
    obtain ⟨_, _, hM, -⟩ := write2_keys hw'
    obtain ⟨_, _, _, -, -, -, hck', -, -⟩ := read1_ck hr'
    rcases hmc with h | ⟨x, h⟩
    · rw [hM] at h; cases h
    · rw [hM] at h
      simp only [T.pair.injEq, T.aead.injEq, T.hk2.injEq, T.hk1.injEq] at h
      have := h.2.1.1.1
      rw [hck'] at this
      cases this
  | initSeals s' e' n' h1' h2' =>
    obtain ⟨_, _, _, -, -, -, hs1, -⟩ := read2_keys h2'
    rcases hmc with h | ⟨x, h⟩
    · simp only [T.aead.injEq] at h
      rw [hs1] at h
      cases h.1
    · cases h
  | respSeals s' f' n' h1' h2' =>
    obtain ⟨_, _, -, -, -, hs1, -⟩ := write2_keys h2'
    rcases hmc with h | ⟨x, h⟩
    · simp only [T.aead.injEq] at h
      rw [hs1] at h
      simp only [T.hk2.injEq] at h
      cases h.1.2
    · cases h

/-- An attacker that starts from names and public keys holds no
ciphertext, so the authentication laws apply to it. -/
theorem exposed_parts {t : T} (h : Exposed S t) {k ad p : T} {n : Nat}
    (hp : Part (.aead k n ad p) t) : Clean S k := by
  rcases h with ⟨i, rfl, -⟩ | ⟨x, rfl⟩ <;> cases hp

end

end Symbolic
