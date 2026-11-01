/-
The symbolic (Dolev-Yao) model of the handshake's cryptography: the
terms `T`, the suite `sym` over them, what honest parties send and
reveal, what the attacker derives (`Derivable`), and the predicates the
laws are stated with. engine/wire/NoiseSymbolic.lean holds its laws and
explains its assumptions; the definitions are here, apart from them, so
that a Comparator challenge can import the model without the laws.
-/
import engine.wire.Noise

namespace Connection.Noise.Symbolic

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
  ValidKey _ := True
  ValidPayload _ := True
  ValidAD _ := True
  enc := .aead
  dec := dec
  hash := .hash
  hkdf ck ikm := (.hk1 ck ikm, .hk2 ck ikm)
  pair := .pair
  split := unpair
  lit := .lit

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
and by asking honest parties. `O` is the honest calls it may make: it
learns what an honest party sends, `m` handed `q`, only if `O q m`.
`Sends` says what an honest party would send; `O` says which of those
sends happen. The secrecy laws hold for every `O`, `AllCalls` among
them; the authentication laws say which call must be in `O`. What
honest parties read (`Reveals`) is open to the attacker whatever `O`
is. -/
inductive Derivable (O : T → T → Prop) (K : T → Prop) : T → Prop
  | know {t} : K t → Derivable O K t
  | lit (b : ByteArray) : Derivable O K (.lit b)
  | pair {a b} : Derivable O K a → Derivable O K b → Derivable O K (.pair a b)
  | fst {a b} : Derivable O K (.pair a b) → Derivable O K a
  | snd {a b} : Derivable O K (.pair a b) → Derivable O K b
  | pub {x} : Derivable O K x → Derivable O K (.pub x)
  | dh {x y z} : Derivable O K x → Derivable O K y → sym.dh x y = some z → Derivable O K z
  | hash {x} : Derivable O K x → Derivable O K (.hash x)
  | hk1 {a b} : Derivable O K a → Derivable O K b → Derivable O K (.hk1 a b)
  | hk2 {a b} : Derivable O K a → Derivable O K b → Derivable O K (.hk2 a b)
  | encrypt {k ad p} (n : Nat) : Derivable O K k → Derivable O K ad → Derivable O K p →
      Derivable O K (.aead k n ad p)
  | decrypt {k n ad p} : Derivable O K (.aead k n ad p) → Derivable O K k → Derivable O K p
  | sent {q m} : Derivable O K q → Sends q m → O q m → Derivable O K m
  | revealed {q m} : Derivable O K q → Reveals q m → Derivable O K m

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

/-- What the attacker starts with when the names in `S` are secret:
every other name, and every public key. -/
def Exposed (S : Nat → Prop) (t : T) : Prop := (∃ i, t = .atom i ∧ ¬ S i) ∨ ∃ x, t = .pub x

/-- A session's four secrets: both statics, both ephemerals. -/
def secrets (sI sR e f : Nat) (i : Nat) : Prop := i = sI ∨ i = sR ∨ i = e ∨ i = f

/-- `Part x t`: `x` comes out of `t` by unpairing and opening. -/
inductive Part (x : T) : T → Prop
  | refl : Part x x
  | fst {a b : T} : Part x a → Part x (.pair a b)
  | snd {a b : T} : Part x b → Part x (.pair a b)
  | body {k ad p : T} {n : Nat} : Part x p → Part x (.aead k n ad p)

/-- The honest call `q ↦ m` is responder `s` answering message 1 `m1`
(`Sends.answer` with static `s`), with any ephemeral and payload. -/
def Answers (s : Nat) (m1 q m : T) : Prop :=
  ∃ f pro rs re p1 p st ses, read1 sym pro (.atom s) rs m1 = some (st, re, p1) ∧
    write2 sym st (.atom f) rs re p = some (ses, m) ∧ q = .pair pro (.pair rs (.pair m1 p))

end Connection.Noise.Symbolic
