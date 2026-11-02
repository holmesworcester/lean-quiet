import app.community.Family
import app.community.member.invite.request.approve.admit.Proofs
import app.community.member.invite.request.Commands

namespace Community
open Engine Codec

theorem check_request {C : Crypto} {o : Op} {b : Body} {fs : List Fact} {c u : Id} {d e : Key}
    {l : Bool} (h : check C o b fs = some (.request c u d e l)) :
    ∃ cs bs d0 e0 k0 issuer k, b = .request d e cs bs ∧
      fs = [.admission c c d0 e0 k0, .invitation c issuer k l] ∧ o.reqs.head? = some c ∧
      u = (if l then issuer else o.id) ∧
      C.verify d (signed o b) cs = true ∧ C.verify k (signed o b) bs = true := by
  unfold check at h
  split at h <;> (try (simp at h; done))
  rename_i b r i
  rcases b with ⟨d', e', cs, bs⟩; rcases r with ⟨c0, u0, d0, e0, k0⟩; rcases i with ⟨c', issuer, k, l'⟩
  simp only [Request.check] at h
  split at h
  · rename_i hc
    simp only [Option.map_some, Option.some.injEq, Fact.ofRequest.injEq, Request.Fact.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    obtain ⟨h1, rfl, rfl, h4, h5⟩ := hc
    exact ⟨_, _, _, _, _, _, _, rfl, rfl, h1, rfl, h4, h5⟩
  · simp at h
open Engine Codec
variable {C : Crypto} {ops : Id → Option Op}

/-- **Nobody requests uninvited.** A Valid request redeems a Valid
invitation of c, and the invitation's bearer key (from the link) and the
requesting device both signed it. Its user is the issuer's for a link
invitation, the new user the request names for a member invitation, and
it carries the invitation's link flag. -/
theorem request_invited (hk : Keyed ops) {r c u : Id} {d e : Key} {l : Bool}
    (h : V C ops r (.request c u d e l)) :
    ∃ o b i issuer k cs bs, ops r = some o ∧ (decode o.body : Option Body) = some b ∧
      o.reqs = [c, i] ∧ V C ops i (.invitation c issuer k l) ∧
      u = (if l then issuer else r) ∧
      C.verify d (signed o b) cs = true ∧ C.verify k (signed o b) bs = true := by
  obtain ⟨o, b, fs, hx, hb, hr, hv⟩ := valid_inv h
  have hid := hk r o hx
  obtain ⟨cs, bs, d0, e0, k0, issuer, k, rfl, rfl, hh, hu, hcs, hbs⟩ := check_request hv
  obtain ⟨a, i, hreq, _, hi⟩ := all2_two hr
  rw [hreq] at hh; simp at hh; subst hh
  rw [hid] at hu
  exact ⟨o, _, i, issuer, k, cs, bs, hx, hb, hreq, hi, hu, hcs, hbs⟩

/-- **A request with its invitation and both signatures is Valid.** -/
theorem request_valid (hk : Keyed ops) {r c i : Id} {o : Op} {d e cs bs : ByteArray}
    {d0 e0 k0 : Key} {issuer : Id} {k : Key} {l : Bool}
    (hy : ops r = some o) (hb : (decode o.body : Option Body) = some (.request d e cs bs)) (hkd : o.kind = Body.tag (.request d e cs bs))
    (hreq : o.reqs = [c, i]) (hc : V C ops c (.admission c c d0 e0 k0))
    (hi : V C ops i (.invitation c issuer k l))
    (hcs : C.verify d (signed o (.request d e cs bs)) cs = true)
    (hbs : C.verify k (signed o (.request d e cs bs)) bs = true) :
    V C ops r (.request c (if l then issuer else r) d e l) := by
  have hid := hk r o hy
  refine spec_valid_of hy (fs := [.admission c c d0 e0 k0, .invitation c issuer k l]) ?_ ?_
  · rw [hreq]; exact .cons hc (.cons hi .nil)
  · show validate C o _ = _
    unfold validate; rw [hb]; simp only [hkd, ↓reduceIte]
    simp [check, Root.check, Invitation.check, Request.check, Approve.check, Admit.check, Grant.check, Remove.check, Post.check, Profile.check, Attach.check, Chunk.check, React.check, Wrap.check, Rename.check, hreq, hcs, hbs, hid]
open Engine
variable {C : Crypto}

/-- **The binding (`endpoint_signed`).** Every admission's key was
signed by its device: the admission came from a root or a request whose
body carries the device key d and the key e, and d signed that body. -/
theorem endpoint_signed {ops : Id → Option Op} {y c u : Id} {d e kid : Key}
    (hv : V C ops y (.admission c u d e kid)) :
    ∃ x o b sg, (x = y ∨ ∃ oy, ops y = some oy ∧ oy.reqs.getD 1 .empty = x) ∧ ops x = some o ∧
      (Codec.decode o.body : Option Body) = some b ∧
      (b = .root d e kid sg ∨ ∃ bs, b = .request d e sg bs) ∧ C.verify d (signed o b) sg = true := by
  obtain ⟨o, b, fs, hx, hb, hr, hc⟩ := valid_inv hv
  rcases check_admission hc with ⟨sg, rfl, _, _, _, hs⟩ | ⟨d0, e0, l, a, rfl, rfl, _⟩
  · exact ⟨y, o, _, sg, Or.inl rfl, hx, hb, Or.inl rfl, hs⟩
  · obtain ⟨_, r, _, hreq, _, hrv, _⟩ := all2_cons2 hr
    obtain ⟨or, br, fsr, hor, hbr, _, hvr⟩ := valid_inv hrv
    obtain ⟨cs, bs, _, _, _, _, _, rfl, _, _, _, hcs, _⟩ := check_request hvr
    exact ⟨r, or, _, cs, Or.inr ⟨o, hx, by rw [hreq]; rfl⟩, hor, hbr, Or.inr ⟨bs, rfl⟩, hcs⟩

/-- **A device link's request is asked only of its issuer's user**
(`asks_link`): the requests page lists it for user me only when me is
the request's user, the link's issuer; any member's request is listed
for every member. -/
theorem asks_link {me c u : Id} {d e : Key} {l : Bool} :
    asks me (.request c u d e l) = true ↔ (l = true → u = me) := by
  cases l <;> simp [asks]

end Community
