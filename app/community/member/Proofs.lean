import app.community.Family
import app.community.member.admin.Proofs
import app.community.member.invite.request.Proofs
import app.community.member.invite.request.approve.Proofs
import app.community.member.remove.Proofs

/-!
`community.member`: laws about the op types in this folder and below.
-/
namespace Community
open Engine Codec

theorem check_removal {C : Crypto} {o : Op} {b : Body} {fs : List Fact} {c t u : Id}
    (h : check C o b fs = some (.removal c t u)) :
    ∃ s d0 e0 d e auth d' e', b = .remove s ∧
      fs = [.admission c c d0 e0, .admission c u d e, auth, .admission c t d' e'] ∧
      o.reqs.head? = some c ∧ ((t = u ∧ auth.isLocal = false) ∨ isAdmin c u auth = true) ∧
      C.verify d (signed o b) s = true := by
  unfold check at h
  split at h <;> (try (simp at h; done))
  rename_i b r a auth tg
  rcases b with ⟨s⟩; rcases r with ⟨c0, u0, d0, e0⟩; rcases a with ⟨c1, u', d, e⟩; rcases tg with ⟨c2, t', d', e'⟩
  simp only [Remove.check] at h
  split at h
  · rename_i hc
    simp only [Option.map_some, Option.some.injEq, Fact.ofRemoval.injEq, Remove.Fact.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    obtain ⟨h1, rfl, rfl, rfl, h5, h6⟩ := hc
    refine ⟨_, _, _, _, _, _, _, _, rfl, rfl, h1, ?_, h6⟩
    simpa using h5
  · simp at h
end Community
namespace Community
open Engine Codec
variable {C : Crypto} {ops : Id → Option Op}

/-- **A removed member's approval still counts.** An approval made by a
user of c stays Valid after that user's removal, so it can still
complete an admission: the admit reads the approval's fact, and nothing
about its approver's removal appears in the premises (#1088 semantics:
validity reads cited facts only). In practice it reaches only nodes the
removed user can still sync with, or that learned it from them. -/
theorem removed_approver_admits {y x c r : Id} {o : Op} {d0 e0 : Key} {u a : Id} {d e : Key}
    {l : Bool} (hy : ops y = some o) (hb : (decode o.body : Option Body) = some .admit)
    (hkd : o.kind = Body.tag .admit) (hreq : o.reqs = [c, r, x]) (hc : V C ops c (.admission c c d0 e0))
    (hr : V C ops r (.request c u d e l 1)) (hx : V C ops x (.approval c r a))
    (_removed : Removed C ops c a) :
    V C ops y (.admission c u d e) :=
  admit_admits (us := [a]) hy hb hkd hreq hc hr (.cons hx .nil) (by simp) rfl

/-- **Only admins remove others.** A Valid removal of user t by user u
is a self-removal, or u is an admin. -/
theorem removal_authorized {x c t u : Id} (h : V C ops x (.removal c t u)) :
    t = u ∨ IsAdmin C ops c u := by
  obtain ⟨o, b, fs, _, _, hr, hv⟩ := valid_inv h
  obtain ⟨_, _, _, _, _, auth, _, _, rfl, rfl, _, ha, _⟩ := check_removal hv
  obtain ⟨_, _, z, _, _, _, _, hz, _⟩ := all2_four hr
  rcases ha with ha | ha
  · exact Or.inl ha.1
  · exact Or.inr (isAdmin_sound hz ha)

/-- **Every admin-issued removal stands.** A removal op signed by an
admitted device of user u, citing a fact that shows u is admin and an
admission of the target t, is Valid — whoever t is (another admin
included), and whether or not u has itself been removed: nothing about
u's own removal appears in its premises. -/
theorem admin_removal_stands {x c ra au ta : Id} {o : Op} {s : ByteArray}
    {d0 e0 d e d' e' : Key} {u t : Id} {auth : Fact}
    (hx : ops x = some o) (hb : (decode o.body : Option Body) = some (.remove s)) (hkd : o.kind = Body.tag (.remove s))
    (hreq : o.reqs = [c, ra, au, ta])
    (hc : V C ops c (.admission c c d0 e0)) (hra : V C ops ra (.admission c u d e))
    (hau : V C ops au auth) (hadm : isAdmin c u auth = true)
    (hta : V C ops ta (.admission c t d' e'))
    (hs : C.verify d (signed o (.remove s)) s = true) :
    V C ops x (.removal c t u) := by
  refine spec_valid_of hx (fs := [.admission c c d0 e0, .admission c u d e, auth, .admission c t d' e'])
    ?_ ?_
  · rw [hreq]; exact .cons hc (.cons hra (.cons hau (.cons hta .nil)))
  · show validate C o _ = _
    unfold validate; rw [hb]; simp only [hkd, ↓reduceIte]
    simp [check, Root.check, Invitation.check, Request.check, Approve.check, Admit.check, Grant.check, Remove.check, Post.check, Profile.check, Attach.check, Chunk.check, React.check, Wrap.check, Rename.check, hreq, hadm, hs]
end Community
namespace Community
open Engine
variable {C : Crypto}

/-- **Only a device's own consent cuts it (`cut_consented`).** A cut
device signed the root or request that admitted it into the removed
user: nobody else can tie it to a user, so nobody else can cut it. -/
theorem cut_consented {ops : Id → Option Op} {c : Id} {d : Key} (h : Cut C ops c d) :
    ∃ u e y x o b sg, V C ops y (.admission c u d e) ∧ Removed C ops c u ∧
      (x = y ∨ ∃ oy, ops y = some oy ∧ oy.reqs.getD 1 .empty = x) ∧ ops x = some o ∧
      (Codec.decode o.body : Option Body) = some b ∧
      (b = .root d e sg ∨ ∃ bs, b = .request d e sg bs) ∧ C.verify d (signed o b) sg = true := by
  obtain ⟨u, e, ⟨y, hy⟩, hr⟩ := h
  obtain ⟨x, o, b, sg, hx, ho, hb, hbody, hs⟩ := endpoint_signed hy
  exact ⟨u, e, y, x, o, b, sg, hy, hr, hx, ho, hb, hbody, hs⟩

end Community
