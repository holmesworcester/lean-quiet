import ops.community.Family

/-!
`community.profile`: laws about the op types in this folder and below.
-/
namespace Community
open Engine Codec

theorem check_profile {C : Crypto} {o : Op} {b : Body} {fs : List Fact} {c u : Id}
    {n : ByteArray} {tm : Nat}
    (h : check C o b fs = some (.profile c u n tm)) :
    ∃ s d0 e0 d e, b = .profile n tm s ∧ fs = [.admission c c d0 e0, .admission c u d e] ∧
      o.reqs.head? = some c ∧ n.size ≤ 64 ∧ C.verify d (signed o b) s = true := by
  unfold check at h
  split at h <;> (try (simp at h; done))
  rename_i b r a
  rcases b with ⟨n', tm', s⟩; rcases r with ⟨c0, u0, d0, e0⟩; rcases a with ⟨c1, u', d, e⟩
  simp only [Profile.check] at h
  split at h
  · rename_i hc
    simp only [Option.map_some, Option.some.injEq, Fact.ofProfile.injEq, Profile.Fact.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    obtain ⟨h1, rfl, rfl, h4, h5⟩ := hc
    exact ⟨_, _, _, _, _, rfl, rfl, h1, h4, h5⟩
  · simp at h
end Community
namespace Community
open Engine Codec
variable {C : Crypto} {ops : Id → Option Op}

/-- **A name is set only by its user.** A Valid profile of user u (the
name every row of u's shows) was signed, as this exact op, by a device
admitted into u, and the name is at most 64 bytes. -/
theorem profile_authorized {x c u : Id} {n : ByteArray} {tm : Nat}
    (h : V C ops x (.profile c u n tm)) :
    ∃ o s d e y, ops x = some o ∧ (decode o.body : Option Body) = some (.profile n tm s) ∧
      o.reqs = [c, y] ∧ V C ops y (.admission c u d e) ∧ n.size ≤ 64 ∧
      C.verify d (signed o (.profile n tm s)) s = true := by
  obtain ⟨o, b, fs, hx, hb, hr, hv⟩ := valid_inv h
  obtain ⟨s, d0, e0, d, e, rfl, rfl, hh, hn, hs⟩ := check_profile hv
  obtain ⟨a, y, hreq, _, hy⟩ := all2_two hr
  rw [hreq] at hh; simp at hh; subst hh
  exact ⟨o, s, d, e, y, hx, hb, hreq, hy, hn, hs⟩

end Community
