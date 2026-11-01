import engine.wire.NoiseSymbolic

/-! Non-vacuity for the *symbolic* handshake the README explicitly labels.
Four distinct fixed exponents: initiator static 11, responder static 22,
initiator ephemeral 33, responder ephemeral 44. Prologue and payloads are
nonempty synthetic literals. No Ed25519/X25519 implementation claim. -/
namespace Vacuity.Session
open Connection.Noise Connection.Noise.Symbolic

def prologue : ByteArray := "Quiet-vacuity/community/alice-bob".toUTF8
def payload1 : ByteArray := "Alice's hello".toUTF8
def payload2 : ByteArray := "Bob's reply".toUTF8

def Transcript (st : Sym T) (m1 : T) (sr : Connection.Noise.Session T)
    (m2 : T) (si : Connection.Noise.Session T) : Prop :=
  write1 sym (.lit prologue) (.atom 11) (.atom 33) (.pub (.atom 22)) (.lit payload1) = some (st, m1) ∧
  read1 sym (.lit prologue) (.atom 22) (.pub (.atom 11)) m1 = some (st, .pub (.atom 33), .lit payload1) ∧
  write2 sym st (.atom 44) (.pub (.atom 11)) (.pub (.atom 33)) (.lit payload2) = some (sr, m2) ∧
  read2 sym st (.atom 11) (.atom 33) m2 = some (si, .lit payload2)

theorem honestRun : ∃ st m1 sr m2 si, Transcript st m1 sr m2 si ∧
    si.h = sr.h ∧ si.send = sr.recv ∧ si.recv = sr.send := by
  obtain ⟨st, m1, hw1, hr1, sr, m2, hw2, si, hr2, hh, hs, hr⟩ :=
    kk_runs (.lit prologue) 11 22 33 44 (.lit payload1) (.lit payload2)
  exact ⟨st, m1, sr, m2, si, ⟨hw1, hr1, hw2, hr2⟩, hh, hs, hr⟩

def secretNames : Nat → Prop := secrets 11 22 33 44

/-- This fixture's attacker, which starts from names and public keys,
holds no ciphertext: the authentication laws' `hK2` premise. -/
theorem exposed_parts {S : Nat → Prop} {t : T} (h : Exposed S t) {k ad p : T} {n : Nat}
    (hp : Part (.aead k n ad p) t) : Clean S k := by
  rcases h with ⟨i, rfl, -⟩ | ⟨x, rfl⟩ <;> cases hp

theorem secretsHeld : ∃ st m1 sr m2 si, Transcript st m1 sr m2 si ∧
    ¬ Derivable AllCalls (Exposed secretNames) si.send.k ∧
    ¬ Derivable AllCalls (Exposed secretNames) si.recv.k ∧
    ¬ Derivable AllCalls (Exposed secretNames) sr.send.k ∧
    ¬ Derivable AllCalls (Exposed secretNames) sr.recv.k := by
  obtain ⟨st, m1, sr, m2, si, ht, _⟩ := honestRun
  exact ⟨st, m1, sr, m2, si, ht,
    kk_secret (sent1_write1 good trivial ht.1) ht.2.2.2 ht.2.1 ht.2.2.1⟩

-- The premise boundaries are not assumed: all four concrete names differ.
theorem distinctRoles : (11 : Nat) ≠ 33 ∧ 11 ≠ 44 ∧ 22 ≠ 33 ∧ 22 ≠ 44 := by decide

theorem afterStaticLeak : ∃ st m1 sr m2 si, Transcript st m1 sr m2 si ∧
    let K := Exposed (fun i => i = 33 ∨ i = 44)
    Derivable AllCalls K (.atom 11) ∧ Derivable AllCalls K (.atom 22) ∧
      Derivable AllCalls K m1 ∧ Derivable AllCalls K m2 ∧
      ¬ Derivable AllCalls K si.send.k ∧ ¬ Derivable AllCalls K si.recv.k ∧
      ¬ Derivable AllCalls K sr.send.k ∧ ¬ Derivable AllCalls K sr.recv.k := by
  obtain ⟨st, m1, sr, m2, si, ht, _⟩ := honestRun
  exact ⟨st, m1, sr, m2, si, ht,
    kk_forward_secret (by decide) (by decide) ht.1 ht.2.1 ht.2.2.1 ht.2.2.2⟩

/-- Negative control: leak the initiator's static AND ephemeral and the
same successful session's keys really are derivable. -/
theorem initiatorLeakBreaksSecrecy : ∃ st m1 sr m2 si, Transcript st m1 sr m2 si ∧
    Derivable AllCalls (Exposed (fun i => i = 22 ∨ i = 44)) si.send.k ∧
    Derivable AllCalls (Exposed (fun i => i = 22 ∨ i = 44)) si.recv.k := by
  obtain ⟨st, m1, sr, m2, si, ht, _⟩ := honestRun
  exact ⟨st, m1, sr, m2, si, ht,
    kk_secret_init_tight (by decide) (by decide) (sent1_write1 good trivial ht.1) ht.2.2.2⟩

/-- The transcript is actually available to the attacker, by asking the
honest parties to send it; this discharges authentication's derivability
premise without defining attacker knowledge to include the conclusion. -/
theorem transcriptPublic {st m1 sr m2 si} (ht : Transcript st m1 sr m2 si) :
    Derivable AllCalls (Exposed secretNames) m1 ∧ Derivable AllCalls (Exposed secretNames) m2 := by
  have pub (x : T) : Derivable AllCalls (Exposed secretNames) (.pub x) := .know (.inr ⟨x, rfl⟩)
  have hm1 : Derivable AllCalls (Exposed secretNames) m1 :=
    .sent (.pair (.lit _) (.pair (pub _) (.lit _))) (.request 11 33 ht.1) trivial
  have hm2 : Derivable AllCalls (Exposed secretNames) m2 :=
    .sent (.pair (.lit _) (.pair (pub _) (.pair hm1 (.lit _)))) (.answer 22 44 ht.2.1 ht.2.2.1) trivial
  exact ⟨hm1, hm2⟩

/-! ### Authentication, over explicit honest calls -/

/-- Every honest call but the responder 22 answering `m1`: the attacker
may have the initiator send its request, and 22 answer any other
session. -/
def OtherSessions (m1 q m : T) : Prop := ¬ Answers 22 m1 q m

/-- Every honest call but initiator 11 writing 22 a message 1 with
`payload1`: its requests with other payloads stay open. -/
def OtherRequests (q m : T) : Prop := ¬ Requests 11 (.pub (.atom 22)) (.lit payload1) q m

/-- The log of the honest run, and nothing else: 11's request, then 22's
answer to it. -/
def RunLog (m1 m2 q m : T) : Prop :=
  q = .pair (.lit prologue) (.pair (.pub (.atom 22)) (.lit payload1)) ∧ m = m1 ∨
    q = .pair (.lit prologue) (.pair (.pub (.atom 11)) (.pair m1 (.lit payload2))) ∧ m = m2

/-- No honest call is 22 answering, in any session. -/
def NoAnswerBy22 (q m : T) : Prop := ∀ m1, ¬ Answers 22 m1 q m

/-- No honest call is 11 writing a message 1. -/
def NoRequestBy11 (q m : T) : Prop := ∀ rs p, ¬ Requests 11 rs p q m

def payload3 : ByteArray := "Alice's other hello".toUTF8

theorem payload3_ne : payload3 ≠ payload1 := by decide

/-- Every name but 11, 33 and 44 is known: the responder's static 22
has leaked. -/
def leak22 (i : Nat) : Prop := i = 11 ∨ i = 33 ∨ i = 44

/-- **The initiator authenticates the responder, under a non-trivial
`O`.** Barred only from 22 answering this session's message 1, the
attacker still has the initiator send it, and has 22 answer another
session (initiator ephemeral 55, responder ephemeral 66), whose own
initiator accepts that answer. Yet this session's initiator accepts
nothing it derives. With every call open the honest reply is derivable
and accepted, so `O` is what makes the difference. -/
theorem initiatorAuthenticates : ∃ st m1 sr m2 si, Transcript st m1 sr m2 si ∧
    Derivable AllCalls (Exposed secretNames) m2 ∧
    Derivable (OtherSessions m1) (Exposed secretNames) m1 ∧
    (∃ st' m1' m2' si', m1' ≠ m1 ∧
      read2 sym st' (.atom 11) (.atom 55) m2' = some (si', .lit payload2) ∧
      Derivable (OtherSessions m1) (Exposed secretNames) m2') ∧
    ∀ m, Derivable (OtherSessions m1) (Exposed secretNames) m →
      read2 sym st (.atom 11) (.atom 33) m = none := by
  obtain ⟨st, m1, sr, m2, si, ht, _⟩ := honestRun
  have pub (x : T) : Derivable (OtherSessions m1) (Exposed secretNames) (.pub x) :=
    .know (.inr ⟨x, rfl⟩)
  have hm1 : Derivable (OtherSessions m1) (Exposed secretNames) m1 :=
    .sent (.pair (.lit _) (.pair (pub _) (.lit _))) (.request 11 33 ht.1)
      (fun ⟨_, _, _, _, _, _, _, _, _, _, hq⟩ => by cases hq)
  obtain ⟨st', m1', hw1', hr1', _, m2', hw2', si', hr2', -⟩ :=
    kk_runs (.lit prologue) 11 22 55 66 (.lit payload1) (.lit payload2)
  have hne : m1' ≠ m1 := by
    obtain ⟨_, _, h⟩ := write1_msg hw1'
    obtain ⟨_, _, h'⟩ := write1_msg ht.1
    rw [h, h']
    simp
  have hm1' : Derivable (OtherSessions m1) (Exposed secretNames) m1' :=
    .sent (.pair (.lit _) (.pair (pub _) (.lit _))) (.request 11 55 hw1')
      (fun ⟨_, _, _, _, _, _, _, _, _, _, hq⟩ => by cases hq)
  have hm2' : Derivable (OtherSessions m1) (Exposed secretNames) m2' :=
    .sent (.pair (.lit _) (.pair (pub _) (.pair hm1' (.lit _)))) (.answer 22 66 hr1' hw2')
      (fun ⟨_, _, _, _, _, _, _, _, _, _, hq⟩ => hne (by simp only [T.pair.injEq] at hq; exact hq.2.2.1))
  refine ⟨st, m1, sr, m2, si, ht, (transcriptPublic ht).2, hm1,
    ⟨st', m1', m2', si', hne, hr2', hm2'⟩, ?_⟩
  intro m hm
  exact kk_authentic (S := secretNames) (fun _ => exposed_clean) (fun _ h => exposed_parts h)
    (by simp [secretNames, secrets]) (Or.inl (by simp [secretNames, secrets]))
    (fun _ _ h => h) (sent1_write1 good trivial ht.1) hm

/-- **The initiator agrees with the responder, over the run's own log.**
With `O` exactly the two calls that happened, the attacker derives the
reply, and the reply the initiator accepts is the logged call by 22
answering this message 1; the sessions match. -/
theorem initiatorAgrees : ∃ st m1 sr m2 si, Transcript st m1 sr m2 si ∧
    Derivable (RunLog m1 m2) (Exposed secretNames) m2 ∧
    ∃ f p responder,
      RunLog m1 m2 (.pair (.lit prologue) (.pair (.pub (.atom 11)) (.pair m1 p))) m2 ∧
      read1 sym (.lit prologue) (.atom 22) (.pub (.atom 11)) m1 =
        some (st, .pub (.atom 33), .lit payload1) ∧
      write2 sym st (.atom f) (.pub (.atom 11)) (.pub (.atom 33)) p = some (responder, m2) ∧
      si.h = responder.h ∧ si.send = responder.recv ∧ si.recv = responder.send := by
  obtain ⟨st, m1, sr, m2, si, ht, _⟩ := honestRun
  have pub (x : T) : Derivable (RunLog m1 m2) (Exposed secretNames) (.pub x) := .know (.inr ⟨x, rfl⟩)
  have hm1 : Derivable (RunLog m1 m2) (Exposed secretNames) m1 :=
    .sent (.pair (.lit _) (.pair (pub _) (.lit _))) (.request 11 33 ht.1) (.inl ⟨rfl, rfl⟩)
  have hm2 : Derivable (RunLog m1 m2) (Exposed secretNames) m2 :=
    .sent (.pair (.lit _) (.pair (pub _) (.pair hm1 (.lit _)))) (.answer 22 44 ht.2.1 ht.2.2.1)
      (.inr ⟨rfl, rfl⟩)
  exact ⟨st, m1, sr, m2, si, ht, hm2,
    kk_agree (S := secretNames) (fun _ => exposed_clean) (fun _ h => exposed_parts h)
      (by simp [secretNames, secrets]) (Or.inl (by simp [secretNames, secrets]))
      (sent1_write1 good trivial ht.1) ht.2.2.2 hm2⟩

/-- **The responder authenticates the initiator, under a non-trivial
`O`.** Barred only from 11 writing 22 a message 1 with `payload1`, the
attacker still has 11 write one with `payload3`, which 22 accepts. Yet
22 accepts nothing it derives as from 11 with `payload1`, though with
every call open the honest message 1 is derivable and accepted. -/
theorem responderAuthenticates : ∃ st m1 sr m2 si, Transcript st m1 sr m2 si ∧
    Derivable AllCalls (Exposed secretNames) m1 ∧
    (∃ st' m1', read1 sym (.lit prologue) (.atom 22) (.pub (.atom 11)) m1' =
        some (st', .pub (.atom 55), .lit payload3) ∧
      Derivable OtherRequests (Exposed secretNames) m1') ∧
    ∀ m st' re, Derivable OtherRequests (Exposed secretNames) m →
      read1 sym (.lit prologue) (.atom 22) (.pub (.atom 11)) m ≠ some (st', re, .lit payload1) := by
  obtain ⟨st, m1, sr, m2, si, ht, _⟩ := honestRun
  obtain ⟨st', m1', hw, hr⟩ :=
    read1_write1 (prologue := T.lit prologue) (sI := .atom 11) (sR := .atom 22) (e := .atom 55)
      (p := .lit payload3) good trivial (dh_atom 55 22) (dh_atom 11 22)
  have hm1' : Derivable OtherRequests (Exposed secretNames) m1' :=
    .sent (.pair (.lit _) (.pair (.know (.inr ⟨_, rfl⟩)) (.lit _))) (.request 11 55 hw)
      (fun ⟨_, _, _, _, hq⟩ => payload3_ne (by simp only [T.pair.injEq, T.lit.injEq] at hq; exact hq.2.2))
  refine ⟨st, m1, sr, m2, si, ht, (transcriptPublic ht).1, ⟨st', m1', hr, hm1'⟩, ?_⟩
  intro m st' re hm
  exact kk_authentic_resp (S := secretNames) (fun _ => exposed_clean) (fun _ h => exposed_parts h)
    (by simp [secretNames, secrets]) (by simp [secretNames, secrets]) (fun _ _ h => h) hm st' re

/-- **The responder agrees with the initiator, over the run's own log.**
The message 1 the responder accepts is the logged call by 11, with
this payload, to 22. -/
theorem responderAgrees : ∃ st m1 sr m2 si, Transcript st m1 sr m2 si ∧
    Derivable (RunLog m1 m2) (Exposed secretNames) m1 ∧
    ∃ e, (.pub (.atom 33) : T) = .pub (.atom e) ∧
      RunLog m1 m2 (.pair (.lit prologue) (.pair (.pub (.atom 22)) (.lit payload1))) m1 ∧
      write1 sym (.lit prologue) (.atom 11) (.atom e) (.pub (.atom 22)) (.lit payload1) = some (st, m1) := by
  obtain ⟨st, m1, sr, m2, si, ht, _⟩ := honestRun
  have hm1 : Derivable (RunLog m1 m2) (Exposed secretNames) m1 :=
    .sent (.pair (.lit _) (.pair (.know (.inr ⟨_, rfl⟩)) (.lit _))) (.request 11 33 ht.1)
      (.inl ⟨rfl, rfl⟩)
  exact ⟨st, m1, sr, m2, si, ht, hm1,
    kk_agree_resp (S := secretNames) (fun _ => exposed_clean) (fun _ h => exposed_parts h)
      (by simp [secretNames, secrets]) (by simp [secretNames, secrets]) ht.2.1 hm1⟩

/-- Negative control: leak the responder's static 22. An attacker barred
from every answer by 22 has the initiator send this session's message 1,
then writes a message 2 that the initiator accepts: authentication fails
when `kk_authentic`'s `hR` does. -/
theorem forgedReply : ∃ st m1 sr m2 si, Transcript st m1 sr m2 si ∧
    ∃ m si', Derivable NoAnswerBy22 (Exposed leak22) m ∧
      read2 sym st (.atom 11) (.atom 33) m = some (si', .lit .empty) := by
  obtain ⟨st, m1, sr, m2, si, ht, _⟩ := honestRun
  have pub (x : T) : Derivable NoAnswerBy22 (Exposed leak22) (.pub x) := .know (.inr ⟨x, rfl⟩)
  have hm1 : Derivable NoAnswerBy22 (Exposed leak22) m1 :=
    .sent (.pair (.lit _) (.pair (pub _) (.lit _))) (.request 11 33 ht.1)
      (fun _ ⟨_, _, _, _, _, _, _, _, _, _, hq⟩ => by cases hq)
  exact ⟨st, m1, sr, m2, si, ht, kk_authentic_tight (f := 55) (sent1_write1 good trivial ht.1)
    (.inl (.know (.inl ⟨22, rfl, by simp [leak22]⟩))) (.know (.inl ⟨55, rfl, by simp [leak22]⟩))
    pub (.lit _) hm1⟩

/-- Negative control: leak the responder's static 22 (key-compromise
impersonation). An attacker barred from every request by 11 writes a
message 1 that 22 accepts as from 11 with `payload1`: authentication
fails when `kk_authentic_resp`'s `hR` does. -/
theorem forgedRequest : ∃ m st, Derivable NoRequestBy11 (Exposed leak22) m ∧
    read1 sym (.lit prologue) (.atom 22) (.pub (.atom 11)) m =
      some (st, .pub (.atom 55), .lit payload1) :=
  kk_authentic_resp_tight (.inr (.know (.inl ⟨22, rfl, by simp [leak22]⟩)))
    (.know (.inl ⟨55, rfl, by simp [leak22]⟩)) (fun x => .know (.inr ⟨x, rfl⟩)) (.lit _) (.lit _)

end Vacuity.Session
