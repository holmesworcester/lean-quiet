import ops.connection.NoiseSymbolic

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

theorem secretsHeld : ∃ st m1 sr m2 si, Transcript st m1 sr m2 si ∧
    ¬ Derivable (Exposed secretNames) si.send.k ∧
    ¬ Derivable (Exposed secretNames) si.recv.k ∧
    ¬ Derivable (Exposed secretNames) sr.send.k ∧
    ¬ Derivable (Exposed secretNames) sr.recv.k := by
  obtain ⟨st, m1, sr, m2, si, ht, _⟩ := honestRun
  exact ⟨st, m1, sr, m2, si, ht,
    kk_secret (sent1_write1 good ht.1) ht.2.2.2 ht.2.1 ht.2.2.1⟩

-- The premise boundaries are not assumed: all four concrete names differ.
theorem distinctRoles : (11 : Nat) ≠ 33 ∧ 11 ≠ 44 ∧ 22 ≠ 33 ∧ 22 ≠ 44 := by decide

theorem afterStaticLeak : ∃ st m1 sr m2 si, Transcript st m1 sr m2 si ∧
    let K := Exposed (fun i => i = 33 ∨ i = 44)
    Derivable K (.atom 11) ∧ Derivable K (.atom 22) ∧ Derivable K m1 ∧ Derivable K m2 ∧
      ¬ Derivable K si.send.k ∧ ¬ Derivable K si.recv.k ∧
      ¬ Derivable K sr.send.k ∧ ¬ Derivable K sr.recv.k := by
  obtain ⟨st, m1, sr, m2, si, ht, _⟩ := honestRun
  exact ⟨st, m1, sr, m2, si, ht,
    kk_forward_secret (by decide) (by decide) ht.1 ht.2.1 ht.2.2.1 ht.2.2.2⟩

/-- Negative control: leak the initiator's static AND ephemeral and the
same successful session's keys really are derivable. -/
theorem initiatorLeakBreaksSecrecy : ∃ st m1 sr m2 si, Transcript st m1 sr m2 si ∧
    Derivable (Exposed (fun i => i = 22 ∨ i = 44)) si.send.k ∧
    Derivable (Exposed (fun i => i = 22 ∨ i = 44)) si.recv.k := by
  obtain ⟨st, m1, sr, m2, si, ht, _⟩ := honestRun
  exact ⟨st, m1, sr, m2, si, ht,
    kk_secret_init_tight (by decide) (by decide) (sent1_write1 good ht.1) ht.2.2.2⟩

/-- The transcript is actually available to the attacker, by asking the
honest parties to send it; this discharges authentication's derivability
premise without defining attacker knowledge to include the conclusion. -/
theorem transcriptPublic {st m1 sr m2 si} (ht : Transcript st m1 sr m2 si) :
    Derivable (Exposed secretNames) m1 ∧ Derivable (Exposed secretNames) m2 := by
  have pub (x : T) : Derivable (Exposed secretNames) (.pub x) := .know (.inr ⟨x, rfl⟩)
  have hm1 : Derivable (Exposed secretNames) m1 :=
    .sent (.pair (.lit _) (.pair (pub _) (.lit _))) (.request 11 33 ht.1)
  have hm2 : Derivable (Exposed secretNames) m2 :=
    .sent (.pair (.lit _) (.pair (pub _) (.pair hm1 (.lit _)))) (.answer 22 44 ht.2.1 ht.2.2.1)
  exact ⟨hm1, hm2⟩

theorem initiatorAuthenticates : ∃ st m1 sr m2 si, Transcript st m1 sr m2 si ∧
    ∃ f p responder,
      read1 sym (.lit prologue) (.atom 22) (.pub (.atom 11)) m1 =
        some (st, .pub (.atom 33), .lit payload1) ∧
      write2 sym st (.atom f) (.pub (.atom 11)) (.pub (.atom 33)) p = some (responder, m2) ∧
      si.h = responder.h ∧ si.send = responder.recv ∧ si.recv = responder.send := by
  obtain ⟨st, m1, sr, m2, si, ht, _⟩ := honestRun
  refine ⟨st, m1, sr, m2, si, ht, ?_⟩
  exact kk_authentic (S := secretNames) (fun _ => exposed_clean) (fun _ h => exposed_parts h)
    (by simp [secretNames, secrets]) (Or.inl (by simp [secretNames, secrets])) (sent1_write1 good ht.1) ht.2.2.2 (transcriptPublic ht).2

theorem responderAuthenticates : ∃ st m1 sr m2 si, Transcript st m1 sr m2 si ∧
    ∃ e, (.pub (.atom 33) : T) = .pub (.atom e) ∧
      write1 sym (.lit prologue) (.atom 11) (.atom e) (.pub (.atom 22)) (.lit payload1) = some (st, m1) := by
  obtain ⟨st, m1, sr, m2, si, ht, _⟩ := honestRun
  refine ⟨st, m1, sr, m2, si, ht, ?_⟩
  exact kk_authentic_resp (S := secretNames) (fun _ => exposed_clean) (fun _ h => exposed_parts h)
    (by simp [secretNames, secrets]) (by simp [secretNames, secrets]) ht.2.1 (transcriptPublic ht).1

end Vacuity.Session
