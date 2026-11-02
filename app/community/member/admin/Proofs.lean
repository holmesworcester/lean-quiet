import app.community.Family

namespace Community
open Engine Codec

theorem check_admin {C : Crypto} {o : Op} {b : Body} {fs : List Fact} {c t : Id}
    (h : check C o b fs = some (.admin c t)) :
    ∃ s d0 e0 k0 u d e k auth d' e' k', b = .grant s ∧
      fs = [.admission c c d0 e0 k0, .admission c u d e k, auth, .admission c t d' e' k'] ∧
      o.reqs.head? = some c ∧ isAdmin c u auth = true ∧ C.verify d (signed o b) s = true := by
  unfold check at h
  split at h <;> (try (simp at h; done))
  rename_i b r a auth tg
  rcases b with ⟨s⟩; rcases r with ⟨c0, u0, d0, e0, k0⟩; rcases a with ⟨c1, u, d, e, k⟩; rcases tg with ⟨c2, t', d', e', k'⟩
  simp only [Grant.check] at h
  split at h
  · rename_i hc
    simp only [Option.map_some, Option.some.injEq, Fact.ofAdmin.injEq, Grant.Fact.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨h1, rfl, rfl, rfl, h5, h6⟩ := hc
    exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl, rfl, h1, h5, h6⟩
  · simp at h
open Engine Codec
section
variable (C : Crypto) (ops : Id → Option Op)

/-- User u is an admin of c: the founder, or granted admin. -/
def IsAdmin (c u : Id) : Prop :=
  (u = c ∧ ∃ x d e k, V C ops x (.admission c c d e k)) ∨ ∃ x, V C ops x (.admin c u)
end
open Engine Codec
variable {C : Crypto} {ops : Id → Option Op}

theorem isAdmin_sound {c u y : Id} {g : Fact} (hg : V C ops y g) (h : isAdmin c u g = true) :
    IsAdmin C ops c u := by
  cases g with
  | ofAdmission a =>
    obtain ⟨c', u', d, e, k⟩ := a
    simp [isAdmin] at h; obtain ⟨rfl, rfl, rfl⟩ := h
    exact Or.inl ⟨rfl, y, d, e, k, hg⟩
  | ofAdmin a => obtain ⟨c', u'⟩ := a; simp [isAdmin] at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inr ⟨y, hg⟩
  | _ => simp [isAdmin] at h

/-- Admin is granted only by an admin. -/
theorem admin_granted {x c t : Id} (h : V C ops x (.admin c t)) : ∃ u, IsAdmin C ops c u := by
  obtain ⟨o, b, fs, _, _, hr, hv⟩ := valid_inv h
  obtain ⟨_, _, _, _, u, _, _, _, auth, _, _, _, rfl, rfl, _, ha, _⟩ := check_admin hv
  obtain ⟨_, _, z, _, _, _, _, hz, _⟩ := all2_four hr
  exact ⟨u, isAdmin_sound hz ha⟩

theorem isAdmin_shared {c u : Id} {g : Fact} (h : isAdmin c u g = true) : g.isLocal = false := by
  cases g <;> simp_all [isAdmin, Fact.isLocal]

end Community
