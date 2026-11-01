import app.community.Family

namespace Community
open Engine Codec
variable {C : Crypto} {ops : Id → Option Op}

theorem check_secret {C : Crypto} {o : Op} {b : Body} {fs : List Fact} {pk seed : ByteArray}
    (h : check C o b fs = some (.secret pk seed)) : b = .secret pk seed ∧ fs = [] ∧ C.pub seed = pk := by
  unfold check at h
  split at h <;> (try (simp at h; done))
  rename_i b
  rcases b with ⟨pk', seed'⟩
  simp only [Secret.check] at h
  split at h
  · rename_i hc
    simp only [Option.map_some, Option.some.injEq, Fact.ofSecret.injEq, Secret.Fact.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl, hc⟩
  · simp at h

/-- **A secret's seed is its key's**: `secret.byKey [pk]` rows hold a
seed whose key pair has public key pk. -/
theorem secret_derives {x : Id} {pk seed : ByteArray} (h : V C ops x (.secret pk seed)) :
    C.pub seed = pk := by
  obtain ⟨o, b, fs, _, _, _, hv⟩ := valid_inv h
  exact (check_secret hv).2.2

end Community
