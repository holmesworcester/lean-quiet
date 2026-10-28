/-
The connection family's laws.

Proven:
- `wire_kinds`: only the request and the connection cross the bare
  wire; every other connection op is local, so `intake_local` keeps it
  off every wire.
- `established_agrees`: when a responder's and an initiator's
  `established` validators both succeed over the same request and
  connection, they hold the same handshake hash and community, each
  names the other, and each one's send key is the other's receive key.
  It needs only that the suite is good and that device keys convert to
  the X25519 keys of their seeds.
- In Connection/Noise.lean: `handshake_agrees`, `sent1_write1`,
  `sent1_read1`, `read2_write2'`; in Connection/Frame.lean: `open_seal`,
  `cid_seal`.
- In Connection/NoiseSymbolic.lean, the same handshake functions over
  symbolic terms against an active Dolev-Yao attacker: `kk_secret`
  (session keys), `kk_forward_secret` (session keys once the statics
  leak), `kk_authentic` and `kk_authentic_resp` (each side accepts only
  the other's messages).

To prove, over the world as a pure step relation (holmes-a3's generic
Node; see the README):
- `established_own`: an initiator's `established` cites a request this
  device wrote, because `sent1` re-derives its message 1 from this
  device's seed and the ephemeral.
- `answer_trusted` / `untrusted_silent`: `react` writes a connection
  only for an opened request whose initiator `trusts` admits; for any
  other it writes no connection and no courier. This is lean-net's
  `no_connection_before_approval`, at the level of the ops that run.
- `close_forgets`: after the node purges `closing cid`, no eph, opened,
  or established op of cid is stored.
-/
import ops.connection.Intents

namespace Connection
open Engine Codec

/-- **Only the two handshake messages cross the bare wire.** -/
theorem wire_kinds (o : Op) (h : scopeOf o = .conn) : o.kind = 33 ∨ o.kind = 35 := by
  unfold scopeOf at h
  split at h
  · assumption
  · cases h

/-- Every other connection op is local. -/
theorem local_kinds (o : Op) (h : ¬ (o.kind = 33 ∨ o.kind = 35)) : scopeOf o = .local := by
  simp [scopeOf, h]

/-- **Both ends of a connection hold one session.** -/
theorem established_agrees (K : Keys) (G : K.suite.Good) (edPub : B → B)
    (hconv : ∀ seed, K.xPub (edPub seed) = K.suite.pub (K.xSec seed))
    {oR oI : Op} {r m2 to frm m1 ofR ofI pkR pkI f e seedR seedI skR eR xR skI eI xI : B}
    {cidR cR pR hR sR kR cidI cI pI hI sI kI : B}
    (hto : to = edPub seedR) (hfrm : frm = edPub seedI) (hne : to ≠ frm)
    (hRc : Established.check K oR [.inr (.connection r m2), .inr (.request to frm m1), .inr (.eph ofR pkR f),
      .inl (.secret to skR eR xR seedR)] = some (.established cidR cR pR hR sR kR false))
    (hIc : Established.check K oI [.inr (.connection r m2), .inr (.request to frm m1), .inr (.eph ofI pkI e),
      .inl (.secret frm skI eI xI seedI)] = some (.established cidI cI pI hI sI kI true)) :
    hR = hI ∧ cR = cI ∧ sR = kI ∧ kR = sI ∧ pR = frm ∧ pI = to := by
  have cR' : K.xPub to = K.suite.pub (K.xSec seedR) := by rw [hto]; exact hconv _
  have cI' : K.xPub frm = K.suite.pub (K.xSec seedI) := by rw [hfrm]; exact hconv _
  unfold Established.check at hRc hIc
  simp only [ite_true, hne.symm, ite_false, Ne] at hRc hIc
  split at hRc
  · cases hRc
  split at hIc
  · cases hIc
  rw [cI'] at hRc
  rw [cR'] at hIc
  cases h1 : Noise.read1 K.suite prologue (K.xSec seedR) (K.suite.pub (K.xSec seedI)) m1 with
  | none => simp [h1] at hRc
  | some x1 =>
    obtain ⟨st, re, p1⟩ := x1
    cases h2 : Noise.sent1 K.suite prologue (K.xSec seedI) e (K.suite.pub (K.xSec seedR)) m1 with
    | none => simp [h2] at hIc
    | some x2 =>
      obtain ⟨st', p1'⟩ := x2
      obtain ⟨rfl, rfl, rfl⟩ := Noise.sent1_read1 G h2 h1
      simp only [h1, h2, Option.bind_eq_bind, Option.bind_some] at hRc hIc
      cases h3 : (decode p1' : Option (B × B × List B)) with
      | none => simp [h3] at hRc
      | some d =>
        simp only [h3, Option.bind_some] at hRc hIc
        cases h4 : Noise.write2 K.suite st' f (K.suite.pub (K.xSec seedI)) (K.suite.pub e) ByteArray.empty with
        | none => simp [h4] at hRc
        | some w =>
          obtain ⟨sr, m2'⟩ := w
          simp only [h4, Option.bind_some] at hRc
          by_cases hm : m2' = m2
          · subst hm
            simp only [not_true_eq_false, ite_false] at hRc
            cases h5 : Noise.read2 K.suite st' (K.xSec seedI) e m2' with
            | none => simp [h5] at hIc
            | some q =>
              obtain ⟨si, pp⟩ := q
              simp only [h5, Option.bind_some, Option.some.injEq, Fact.established.injEq] at hRc hIc
              obtain ⟨hh, hs, hr⟩ := Noise.read2_write2' G h4 h5
              obtain ⟨_, rfl, rfl, rfl, rfl, rfl, -⟩ := hRc
              obtain ⟨_, rfl, rfl, rfl, rfl, rfl, -⟩ := hIc
              exact ⟨hh.symm, rfl, by rw [hr], by rw [hs], rfl, rfl⟩
          · simp [hm] at hRc

end Connection
