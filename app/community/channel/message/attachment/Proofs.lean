import app.community.Family
import app.community.channel.message.attachment.chunk.Proofs
import app.community.channel.message.Proofs

namespace Community
open Engine Codec
variable {C : Crypto} {ops : Id → Option Op}

/-- **An attachment is its message's author's.** A Valid attachment
cites the root's admission, an admission of its signing device into user
u, and a message of c by the same user u, at the message's time; that
device signed it. -/
theorem check_attach {C : Crypto} {o : Op} {b : Body} {fs : List Fact} {c m u root : Id} {len tm : Nat}
    {kid sealed : ByteArray} (h : check C o b fs = some (.attachment c m u root len tm kid sealed)) :
    ∃ s d0 e0 d e ka d2 k2 t2 n2 clump, b = .attach root len tm kid sealed s ∧
      fs = [.admission c c d0 e0 kid, .admission c u d e ka, .message c u d2 k2 t2 n2 tm clump] ∧
      o.reqs.head? = some c ∧ m = o.reqs.getD 2 .empty ∧ root.size = 32 ∧
      C.verify d (signed o b) s = true := by
  unfold check at h
  split at h <;> (try (simp at h; done))
  rename_i b r a m
  rcases b with ⟨r', l, tm', k, x, s⟩; rcases r with ⟨c0, u0, d0, e0, k0⟩; rcases a with ⟨c1, u', d, e, ka⟩; rcases m with ⟨c2, u2, d2, k2, t2, n2, tm2, clump⟩
  simp only [Attach.check] at h
  split at h
  · rename_i hc
    simp only [Option.map_some, Option.some.injEq, Fact.ofAttachment.injEq, Attach.Fact.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
    obtain ⟨h1, rfl, rfl, rfl, rfl, rfl, rfl, h6, _, _, _, h10⟩ := hc
    exact ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, rfl, h1, rfl, h6, h10⟩
  · simp at h

/-- **A chunk hangs off its message.** A Valid chunk of an attachment of
message m cites the attachment, which cites m. -/
theorem chunk_hangs_off {x c att root m u : Id} {len i tm : Nat} {k s : ByteArray}
    (h : V C ops x (.chunk c att root len i)) (ha : V C ops att (.attachment c m u root len tm k s)) :
    ∃ o oa, ops x = some o ∧ att ∈ o.reqs ∧ ops att = some oa ∧ m = oa.reqs.getD 2 .empty := by
  obtain ⟨o, _, _, _, _, _, hx, hreq, _⟩ := chunk_of_attachment h
  obtain ⟨oa, b, fs, hxa, _, _, hva⟩ := valid_inv ha
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _⟩ := check_attach hva
  exact ⟨o, oa, hx, by rw [hreq]; simp, hxa, hm⟩

/-- A Valid attachment's op claims its time, which is its message's. -/
theorem attach_order {x c m u root : Id} {len tm : Nat} {k s : ByteArray}
    (h : V C ops x (.attachment c m u root len tm k s)) :
    ∃ o, ops x = some o ∧ orderOf o = tm ∧ m = o.reqs.getD 2 .empty ∧
      ∃ d2 k2 t2 n2 clump, V C ops m (.message c u d2 k2 t2 n2 tm clump) := by
  obtain ⟨o, b, fs, hx, hb, hr, hv⟩ := valid_inv h
  obtain ⟨_, _, _, _, _, _, d2, k2, t2, n2, clump, rfl, rfl, _, hm, _⟩ := check_attach hv
  obtain ⟨_, _, z, hreq, _, _, hz⟩ := all2_three hr
  rw [hreq] at hm; simp at hm; subst hm
  exact ⟨o, hx, by simp [orderOf, hb], by rw [hreq]; rfl, d2, k2, t2, n2, clump, hz⟩

/-- **A message's attachments and their chunks sort at its time**
(`chunks_in_window`): a Valid chunk's op claims its attachment's time,
the attachment's op claims its message's, and the message's op claims
that time too. So every window that holds a message holds its photos,
and none holds an older message's photos with it. -/
theorem chunks_in_window {x c att root : Id} {len i : Nat}
    (h : V C ops x (.chunk c att root len i)) :
    ∃ o oa om m, ops x = some o ∧ att ∈ o.reqs ∧ ops att = some oa ∧ m = oa.reqs.getD 2 .empty ∧
      ops m = some om ∧ orderOf o = orderOf om ∧ orderOf oa = orderOf om := by
  obtain ⟨o, tm, _, _, _, _, hx, hreq, hord, ha⟩ := chunk_of_attachment h
  obtain ⟨oa, hxa, hoa, hm, d2, k2, t2, n2, clump, hmv⟩ := attach_order ha
  obtain ⟨om, hxm, hom⟩ := message_order hmv
  exact ⟨o, oa, om, _, hx, by rw [hreq]; simp, hxa, hm, hxm, by rw [hord, hom], by rw [hoa, hom]⟩

end Community
