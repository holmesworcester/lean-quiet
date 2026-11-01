import app.community.Family
import app.community.member.invite.request.approve.admit.Proofs

namespace Community
open Engine Codec

theorem check_approval {C : Crypto} {o : Op} {b : Body} {fs : List Fact} {c r a : Id}
    (h : check C o b fs = some (.approval c r a)) :
    ∃ s d0 e0 u d e l da ea, b = .approve s ∧
      fs = [.admission c c d0 e0, .request c u d e l, .admission c a da ea] ∧
      o.reqs.head? = some c ∧ r = o.reqs.getD 1 .empty ∧ (l = true → a = u) ∧ da ≠ d ∧
      C.verify da (signed o b) s = true := by
  unfold check at h
  split at h <;> (try (simp at h; done))
  rename_i b r q a
  rcases b with ⟨s⟩; rcases r with ⟨c0, u0, d0, e0⟩; rcases q with ⟨c1, u, d, e, l⟩; rcases a with ⟨c2, a', da, ea⟩
  simp only [Approve.check] at h
  split at h
  · rename_i hc
    simp only [Option.map_some, Option.some.injEq, Fact.ofApproval.injEq, Approve.Fact.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    obtain ⟨h1, rfl, rfl, rfl, h5, h6, h7⟩ := hc
    exact ⟨_, _, _, _, _, _, _, _, _, rfl, rfl, h1, rfl, h5, h6, h7⟩
  · simp at h

open Engine Codec
variable {C : Crypto} {ops : Id → Option Op}

/-- **Every approval is a member's signed yes.** A Valid approval of
request r by user a was signed by a device admitted into a, not the
requesting device, and a is the request's own user (the issuer's) when
the request is for a link. As with removals, its validity reads the
cited facts only: an approval by a user removed since still counts
(#1088 semantics). -/
theorem approval_signed {x c r a : Id} (h : V C ops x (.approval c r a)) :
    ∃ o s ra u d e l da ea, ops x = some o ∧
      (decode o.body : Option Body) = some (.approve s) ∧ o.reqs = [c, r, ra] ∧
      V C ops r (.request c u d e l) ∧ V C ops ra (.admission c a da ea) ∧
      (l = true → a = u) ∧ da ≠ d ∧ C.verify da (signed o (.approve s)) s = true := by
  obtain ⟨o, b, fs, hx, hb, hr, hv⟩ := valid_inv h
  obtain ⟨s, d0, e0, u, d, e, l, da, ea, rfl, rfl, hh, hrr, hl, hd, hs⟩ := check_approval hv
  obtain ⟨c', r', ra, hreq, _, hrv, hav⟩ := all2_three hr
  rw [hreq] at hh hrr; simp at hh hrr; subst hh; subst hrr
  exact ⟨o, s, ra, u, d, e, l, da, ea, hx, hb, hreq, hrv, hav, hl, hd, hs⟩

/-- **Nobody is admitted unapproved.** Every admission is the founder's
(by the root itself), or is produced by an admit op y that cites
exactly a Valid request r of c for that device and one Valid approval
x of r (one approval admits: the user's decision, 2026-10-31). -/
theorem admission_approved (hk : Keyed ops) {y c u : Id} {d e : Key}
    (h : V C ops y (.admission c u d e)) :
    (y = c ∧ u = c) ∨
    ∃ o r x a l, ops y = some o ∧ (decode o.body : Option Body) = some .admit ∧
      o.reqs = [c, r, x] ∧ V C ops r (.request c u d e l) ∧ V C ops x (.approval c r a) := by
  obtain ⟨o, b, fs, hx, hb, hr, hv⟩ := valid_inv h
  have hid := hk y o hx
  rcases check_admission hv with ⟨s, rfl, rfl, hc, hu, _⟩ | ⟨d0, e0, l, a, rfl, rfl, hh⟩
  · left; rw [hid] at hc hu; exact ⟨hc.symm, hu.trans hc.symm⟩
  · obtain ⟨c', r, x, hreq, _, hrv, hxv⟩ := all2_three hr
    rw [hreq] at hh hxv; simp at hh hxv; subst hh
    exact Or.inr ⟨o, r, x, a, l, hx, hb, hreq, hrv, hxv⟩

/-- **An eligible member's signed approval is Valid**, whoever else has
approved or been removed. -/
theorem approve_valid {x c r ra : Id} {o : Op} {s : ByteArray} {d0 e0 : Key} {u a : Id}
    {d e da ea : Key} {l : Bool}
    (hx : ops x = some o) (hb : (decode o.body : Option Body) = some (.approve s)) (hkd : o.kind = Body.tag (.approve s))
    (hreq : o.reqs = [c, r, ra]) (hc : V C ops c (.admission c c d0 e0))
    (hr : V C ops r (.request c u d e l)) (ha : V C ops ra (.admission c a da ea))
    (hl : l = true → a = u) (hd : da ≠ d) (hs : C.verify da (signed o (.approve s)) s = true) :
    V C ops x (.approval c r a) := by
  refine spec_valid_of hx (fs := [.admission c c d0 e0, .request c u d e l, .admission c a da ea])
    ?_ ?_
  · rw [hreq]; exact .cons hc (.cons hr (.cons ha .nil))
  · show validate C o _ = _
    unfold validate; rw [hb]; simp only [hkd, ↓reduceIte]
    simp [check, Root.check, Invitation.check, Request.check, Approve.check, Admit.check, Grant.check, Remove.check, Post.check, Profile.check, Attach.check, Chunk.check, React.check, Wrap.check, Rename.check, hreq, hd, hs]; exact hl

/-- **One approval admits.** An admit op citing a Valid request and one
Valid approval of it admits the requesting device: into the issuer's
user for a link, into the user the request names for a member
invitation. -/
theorem admit_admits {y c r x : Id} {o : Op} {d0 e0 : Key} {u a : Id}
    {d e : Key} {l : Bool}
    (hy : ops y = some o) (hb : (decode o.body : Option Body) = some .admit) (hkd : o.kind = Body.tag (.admit))
    (hreq : o.reqs = [c, r, x]) (hc : V C ops c (.admission c c d0 e0))
    (hr : V C ops r (.request c u d e l)) (hx : V C ops x (.approval c r a)) :
    V C ops y (.admission c u d e) := by
  refine spec_valid_of hy (fs := [.admission c c d0 e0, .request c u d e l, .approval c r a]) ?_ ?_
  · rw [hreq]; exact .cons hc (.cons hr (.cons hx .nil))
  · show validate C o _ = _
    unfold validate; rw [hb]; simp only [hkd, ↓reduceIte]
    simp [check, Root.check, Invitation.check, Request.check, Approve.check, Admit.check, Grant.check, Remove.check, Post.check, Profile.check, Attach.check, Chunk.check, React.check, Wrap.check, Rename.check, hreq]

end Community
