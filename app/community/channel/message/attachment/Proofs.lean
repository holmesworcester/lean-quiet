import app.community.Family
import app.community.channel.message.attachment.chunk.Proofs

/-!
`community.channel.message.attachment`: laws about the op types in this folder and below.
-/
namespace Community
open Engine Codec
variable {C : Crypto} {ops : Id → Option Op}

/-- **An attachment is its message's author's.** A Valid attachment
cites the root's admission, an admission of its signing device into user
u, and a message of c by the same user u; that device signed it. -/
theorem check_attach {C : Crypto} {o : Op} {b : Body} {fs : List Fact} {c m u root : Id} {len : Nat}
    {kid sealed : ByteArray} (h : check C o b fs = some (.attachment c m u root len kid sealed)) :
    ∃ s d0 e0 d e d2 k2 t2 n2 tm2 clump, b = .attach root len kid sealed s ∧
      fs = [.admission c c d0 e0, .admission c u d e, .message c u d2 k2 t2 n2 tm2 clump] ∧
      o.reqs.head? = some c ∧ m = o.reqs.getD 2 .empty ∧ root.size = 32 ∧
      C.verify d (signed o b) s = true := by
  unfold check at h
  split at h <;> (try (simp at h; done))
  rename_i b r a m
  rcases b with ⟨r', l, k, x, s⟩; rcases r with ⟨c0, u0, d0, e0⟩; rcases a with ⟨c1, u', d, e⟩; rcases m with ⟨c2, u2, d2, k2, t2, n2, tm2, clump⟩
  simp only [Attach.check] at h
  split at h
  · rename_i hc
    simp only [Option.map_some, Option.some.injEq, Fact.ofAttachment.injEq, Attach.Fact.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
    obtain ⟨h1, rfl, rfl, rfl, rfl, h6, _, _, _, h10⟩ := hc
    exact ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, rfl, h1, rfl, h6, h10⟩
  · simp at h

/-- **A chunk hangs off its message.** A Valid chunk of an attachment of
message m cites the attachment, which cites m. -/
theorem chunk_hangs_off {x c att root m u : Id} {len i : Nat} {k s : ByteArray}
    (h : V C ops x (.chunk c att root len i)) (ha : V C ops att (.attachment c m u root len k s)) :
    ∃ o oa, ops x = some o ∧ att ∈ o.reqs ∧ ops att = some oa ∧ m = oa.reqs.getD 2 .empty := by
  obtain ⟨o, _, _, _, _, hx, hreq, _⟩ := chunk_of_attachment h
  obtain ⟨oa, b, fs, hxa, _, _, hva⟩ := valid_inv ha
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _⟩ := check_attach hva
  exact ⟨o, oa, hx, by rw [hreq]; simp, hxa, hm⟩

end Community
