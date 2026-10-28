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
- `kept_heard`, `kept_unheard`: a session that has heard its peer is
  retired only for another that has; one that has not is never retired.
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
    {oR oI : Op} {r m2 to frm m1 ofR ofI pkR pkI f e seedR seedI : B}
    {cidR cR pR hR sR kR cidI cI pI hI sI kI : B}
    (hto : to = edPub seedR) (hfrm : frm = edPub seedI) (hne : to ≠ frm)
    (hRc : Established.check K oR [.inr (.connection r m2), .inr (.request to frm m1), .inr (.eph ofR pkR f),
      .inl (.secret to seedR)] = some (.established cidR cR pR hR sR kR false))
    (hIc : Established.check K oI [.inr (.connection r m2), .inr (.request to frm m1), .inr (.eph ofI pkI e),
      .inl (.secret frm seedI)] = some (.established cidI cI pI hI sI kI true)) :
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

/-! ## One session per peer -/

section
variable {U : List Cand}

theorem bestStep_sub {best : List Cand} {s b : Cand} (h : b ∈ bestStep best s) : b = s ∨ b ∈ best := by
  unfold bestStep at h
  split at h
  · split at h
    · rcases List.mem_cons.1 h with rfl | h
      · exact .inl rfl
      · exact .inr (List.mem_filter.1 h).1
    · exact .inr h
  · rcases List.mem_cons.1 h with rfl | h
    · exact .inl rfl
    · exact .inr h

theorem bestOf_sub : ∀ {l acc : List Cand} {b : Cand}, b ∈ l.foldl bestStep acc → b ∈ l ∨ b ∈ acc
  | [], _, _, h => .inr h
  | s :: l, acc, b, h => by
    rw [List.foldl_cons] at h
    rcases bestOf_sub h with h | h
    · exact .inl (List.mem_cons_of_mem _ h)
    · rcases bestStep_sub h with rfl | h
      · exact .inl (List.mem_cons_self ..)
      · exact .inr h

/-- Every peer of what a step has seen keeps a session among the best,
when ids name one peer. -/
theorem bestStep_cov (hid : ∀ a ∈ U, ∀ b ∈ U, a.cid = b.cid → a.peer = b.peer)
    {best X : List Cand} {s : Cand} (hb : ∀ b ∈ best, b ∈ U) (hs : s ∈ U)
    (hc : ∀ x ∈ X, ∃ b ∈ best, b.peer = x.peer) :
    ∀ x ∈ s :: X, ∃ b ∈ bestStep best s, b.peer = x.peer := by
  intro x hx
  unfold bestStep
  split
  · rename_i b hf
    have hbm := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    split
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨x, List.mem_cons_self .., rfl⟩
      · obtain ⟨b₀, hb₀, hpe⟩ := hc x hx
        by_cases he : b₀.cid = b.cid
        · exact ⟨s, List.mem_cons_self .., by rw [← hpe, hid _ (hb _ hb₀) _ (hb _ hbm) he, hp.1]⟩
        · exact ⟨b₀, List.mem_cons_of_mem _ (List.mem_filter.2 ⟨hb₀, by simp [he]⟩), hpe⟩
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨b, hbm, hp.1⟩
      · exact hc x hx
  · rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨x, List.mem_cons_self .., rfl⟩
    · obtain ⟨b₀, hb₀, hpe⟩ := hc x hx
      exact ⟨b₀, List.mem_cons_of_mem _ hb₀, hpe⟩

theorem bestOf_cov (hid : ∀ a ∈ U, ∀ b ∈ U, a.cid = b.cid → a.peer = b.peer) :
    ∀ {l acc X : List Cand}, (∀ s ∈ l, s ∈ U) → (∀ b ∈ acc, b ∈ U) →
      (∀ x ∈ X, ∃ b ∈ acc, b.peer = x.peer) →
      ∀ x ∈ l ++ X, ∃ b ∈ l.foldl bestStep acc, b.peer = x.peer
  | [], _, _, _, _, hc => by simpa using hc
  | s :: l, acc, X, hl, ha, hc => by
    intro x hx
    have hs : s ∈ U := hl s (List.mem_cons_self ..)
    have ha' : ∀ b ∈ bestStep acc s, b ∈ U := fun b hb => by
      rcases bestStep_sub hb with rfl | hb
      · exact hs
      · exact ha b hb
    have hx' : x ∈ l ++ (s :: X) := by
      rcases List.mem_append.1 (by simpa using hx : x ∈ (s :: l) ++ X) with hx | hx
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact List.mem_append_right _ (List.mem_cons_self ..)
        · exact List.mem_append_left _ hx
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hx)
    exact bestOf_cov hid (fun s hs => hl s (List.mem_cons_of_mem _ hs)) ha'
      (bestStep_cov hid ha hs hc) x hx'

end

theorem oneStep_cov {out : List (B × Id)} {X : List Cand} {s : Cand}
    (hc : ∀ x ∈ X, ∃ o ∈ out, o.1 = x.peer) :
    ∀ x ∈ s :: X, ∃ o ∈ oneStep out s, o.1 = x.peer := by
  intro x hx
  unfold oneStep
  split
  · rename_i p c hf
    have hom := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [decide_eq_true_eq] at hp
    split
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨_, List.mem_cons_self .., rfl⟩
      · obtain ⟨o, ho, hpe⟩ := hc x hx
        by_cases he : o.1 = s.peer
        · exact ⟨_, List.mem_cons_self .., by rw [← hpe, he]⟩
        · exact ⟨o, List.mem_cons_of_mem _ (List.mem_filter.2 ⟨ho, by simp [he]⟩), hpe⟩
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨_, hom, hp⟩
      · exact hc x hx
  · rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨_, List.mem_cons_self .., rfl⟩
    · obtain ⟨o, ho, hpe⟩ := hc x hx
      exact ⟨o, List.mem_cons_of_mem _ ho, hpe⟩

theorem oneStep_sound {out : List (B × Id)} {Y : List Cand} {s : Cand}
    (hs : ∀ o ∈ out, ∃ b ∈ Y, b.peer = o.1 ∧ b.cid = o.2) :
    ∀ o ∈ oneStep out s, ∃ b ∈ s :: Y, b.peer = o.1 ∧ b.cid = o.2 := by
  intro o ho
  unfold oneStep at ho
  split at ho
  · split at ho
    · rcases List.mem_cons.1 ho with rfl | ho
      · exact ⟨s, List.mem_cons_self .., rfl, rfl⟩
      · obtain ⟨b, hb, h1, h2⟩ := hs o (List.mem_filter.1 ho).1
        exact ⟨b, List.mem_cons_of_mem _ hb, h1, h2⟩
    · obtain ⟨b, hb, h1, h2⟩ := hs o ho
      exact ⟨b, List.mem_cons_of_mem _ hb, h1, h2⟩
  · rcases List.mem_cons.1 ho with rfl | ho
    · exact ⟨s, List.mem_cons_self .., rfl, rfl⟩
    · obtain ⟨b, hb, h1, h2⟩ := hs o ho
      exact ⟨b, List.mem_cons_of_mem _ hb, h1, h2⟩

theorem onePer_cov : ∀ {l : List Cand} {out : List (B × Id)} {X : List Cand},
    (∀ x ∈ X, ∃ o ∈ out, o.1 = x.peer) → ∀ x ∈ l ++ X, ∃ o ∈ l.foldl oneStep out, o.1 = x.peer
  | [], _, _, hc => by simpa using hc
  | s :: l, out, X, hc => by
    intro x hx
    have hx' : x ∈ l ++ (s :: X) := by
      rcases List.mem_append.1 (by simpa using hx : x ∈ (s :: l) ++ X) with hx | hx
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact List.mem_append_right _ (List.mem_cons_self ..)
        · exact List.mem_append_left _ hx
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hx)
    exact onePer_cov (oneStep_cov hc) x hx'

theorem onePer_sound : ∀ {l : List Cand} {out : List (B × Id)} {Y : List Cand},
    (∀ o ∈ out, ∃ b ∈ Y, b.peer = o.1 ∧ b.cid = o.2) →
      ∀ o ∈ l.foldl oneStep out, ∃ b ∈ l ++ Y, b.peer = o.1 ∧ b.cid = o.2
  | [], _, _, hs => by simpa using hs
  | s :: l, out, Y, hs => by
    intro o ho
    obtain ⟨b, hb, h1, h2⟩ := onePer_sound (oneStep_sound (s := s) hs) o ho
    refine ⟨b, ?_, h1, h2⟩
    rcases List.mem_append.1 hb with hb | hb
    · exact List.mem_append_left _ (List.mem_cons_of_mem _ hb)
    · rcases List.mem_cons.1 hb with rfl | hb
      · exact List.mem_append_left _ (List.mem_cons_self ..)
      · exact List.mem_append_right _ hb

/-- **A session that has heard its peer is retired only for another that
has**: for every such session, one of the same peer that has heard its
peer is kept (when each connection id names one peer, as it does). So a
newcomer nobody has answered for, a replayed request's included, never
displaces a live session. -/
theorem kept_heard {all : List Cand} (hid : ∀ a ∈ all, ∀ b ∈ all, a.cid = b.cid → a.peer = b.peer)
    {s : Cand} (hs : s ∈ all) (hh : s.heard = true) :
    ∃ s' ∈ all, s'.heard = true ∧ s'.peer = s.peer ∧ s'.cid ∈ kept all := by
  let H := all.filter (·.heard)
  have hsH : s ∈ H := List.mem_filter.2 ⟨hs, hh⟩
  have hidH : ∀ a ∈ H, ∀ b ∈ H, a.cid = b.cid → a.peer = b.peer := fun a ha b hb =>
    hid a (List.mem_filter.1 ha).1 b (List.mem_filter.1 hb).1
  have c1 := bestOf_cov hidH (l := H) (acc := []) (X := []) (fun _ h => h) (fun _ h => by simp at h)
    (fun _ h => by simp at h)
  obtain ⟨b, hb, hbp⟩ := c1 s (by simpa using hsH)
  have c2 := onePer_cov (l := bestOf H) (out := []) (X := []) (fun _ h => by simp at h)
  obtain ⟨o, ho, hop⟩ := c2 b (List.mem_append_left _ hb)
  have c3 := onePer_sound (l := bestOf H) (out := []) (Y := []) (fun _ h => by simp at h)
  obtain ⟨b', hb', h1, h2⟩ := c3 o ho
  have hb'H : b' ∈ H := by
    rcases bestOf_sub (l := H) (acc := []) (by simpa [bestOf] using hb') with h | h
    · exact h
    · simp at h
  obtain ⟨hb'a, hb'h⟩ := List.mem_filter.1 hb'H
  refine ⟨b', hb'a, by simpa using hb'h, by rw [h1, hop, hbp], ?_⟩
  unfold kept
  exact List.mem_append_left _ (List.mem_map.2 ⟨o, ho, h2.symm⟩)

/-- **A session that has not heard its peer is kept**: it is never
retired, and patience drops it if it never hears. -/
theorem kept_unheard {all : List Cand} {s : Cand} (hs : s ∈ all) (hh : s.heard = false) :
    s.cid ∈ kept all := by
  unfold kept
  exact List.mem_append_right _ (List.mem_map.2 ⟨s, List.mem_filter.2 ⟨hs, by simp [hh]⟩, rfl⟩)

end Connection
