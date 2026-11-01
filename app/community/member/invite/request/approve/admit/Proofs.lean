import app.community.Family

namespace Community
open Engine Codec

theorem check_admission {C : Crypto} {o : Op} {b : Body} {fs : List Fact} {c u : Id} {d e kid : Key}
    (h : check C o b fs = some (.admission c u d e kid)) :
    (∃ s, b = .root d e kid s ∧ fs = [] ∧ c = o.id ∧ u = o.id ∧ C.verify d (signed o b) s = true) ∨
    (∃ d0 e0 l a, b = .admit ∧
      fs = [.admission c c d0 e0 kid, .request c u d e l, .approval c (o.reqs.getD 1 .empty) a] ∧
      o.reqs.head? = some c) := by
  unfold check at h
  split at h <;> (try (simp at h; done))
  · rename_i b
    rcases b with ⟨d', e', k', s⟩
    simp only [Root.check] at h
    split at h
    · rename_i hs
      simp only [Option.map_some, Option.some.injEq, Fact.ofAdmission.injEq, Root.Fact.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
      exact Or.inl ⟨_, rfl, rfl, rfl, rfl, hs⟩
    · simp at h
  · rename_i b r q a
    rcases r with ⟨c0, u0, d0, e0, k0⟩; rcases q with ⟨c1, u', d', e', l⟩; rcases a with ⟨c2, r2, a2⟩
    simp only [Admit.check] at h
    split at h
    · rename_i hc
      simp only [Option.map_some, Option.some.injEq, Fact.ofAdmission.injEq, Root.Fact.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
      obtain ⟨h1, rfl, rfl, rfl, rfl⟩ := hc
      exact Or.inr ⟨_, _, _, _, rfl, rfl, h1⟩
    · simp at h

end Community
