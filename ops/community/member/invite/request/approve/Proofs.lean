import ops.community.Family
import ops.community.member.invite.request.approve.admit.Proofs

/-!
`community.member.invite.request.approve`: laws about the op types in this folder and below.
-/
namespace Community
open Engine Codec

theorem check_approval {C : Crypto} {o : Op} {b : Body} {fs : List Fact} {c r a : Id}
    (h : check C o b fs = some (.approval c r a)) :
    ∃ s d0 e0 u d e l t da ea, b = .approve s ∧
      fs = [.admission c c d0 e0, .request c u d e l t, .admission c a da ea] ∧
      o.reqs.head? = some c ∧ r = o.reqs.getD 1 .empty ∧ (l = true → a = u) ∧ da ≠ d ∧
      C.verify da (signed o b) s = true := by
  unfold check at h
  split at h <;> (try (simp at h; done))
  rename_i b r q a
  rcases b with ⟨s⟩; rcases r with ⟨c0, u0, d0, e0⟩; rcases q with ⟨c1, u, d, e, l, t⟩; rcases a with ⟨c2, a', da, ea⟩
  simp only [Approve.check] at h
  split at h
  · rename_i hc
    simp only [Option.map_some, Option.some.injEq, Fact.ofApproval.injEq, Approve.Fact.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    obtain ⟨h1, rfl, rfl, rfl, h5, h6, h7⟩ := hc
    exact ⟨_, _, _, _, _, _, _, _, _, _, rfl, rfl, h1, rfl, h5, h6, h7⟩
  · simp at h

/-- `approvers` reads off exactly the approvals of r it is given. -/
theorem approvers_iff {c r : Id} {fs : List Fact} {us : List Id} :
    approvers c r fs = some us ↔ All2 (fun f v => f = .approval c r v) fs us := by
  induction fs generalizing us with
  | nil =>
    constructor
    · intro h; simp [approvers] at h; subst h; exact .nil
    · intro h; cases h; rfl
  | cons f rest ih =>
    constructor
    · intro h
      cases f with
      | ofApproval a =>
        obtain ⟨c', r', v⟩ := a
        simp only [approvers] at h
        split at h
        · rename_i hc; obtain ⟨h1, h2⟩ := hc; subst c'; subst r'
          cases hrest : approvers c r rest with
          | none => rw [hrest] at h; simp at h
          | some vs =>
            rw [hrest] at h; simp at h; subst h
            exact .cons rfl (ih.1 hrest)
        · simp at h
      | _ => simp [approvers] at h
    · intro h
      cases h with
      | cons h1 h2 => subst h1; simp [approvers, ih.2 h2]

/-- A tally holds exactly when the facts are t approvals of r by t
distinct users. -/
theorem tally_iff {c r : Id} {t : Nat} {fs : List Fact} :
    tally c r t fs = true ↔
      ∃ us, All2 (fun f v => f = .approval c r v) fs us ∧ us.Nodup ∧ us.length = t := by
  unfold tally
  constructor
  · intro h
    cases ha : approvers c r fs with
    | none => rw [ha] at h; simp at h
    | some us => rw [ha] at h; simp at h; exact ⟨us, approvers_iff.1 ha, h⟩
  · rintro ⟨us, hus, hn, hl⟩
    rw [approvers_iff.2 hus]; simp [hn, hl]
end Community
namespace Community
open Engine Codec
variable {C : Crypto} {ops : Id → Option Op}

/-- **Every approval is a member's signed yes.** A Valid approval of
request r by user a was signed by a device admitted into a, not the
requesting device, and a is the request's own user (the issuer's) when
the request is for a link. As with removals, its validity reads the
cited facts only: an approval by a user removed since still counts
(#1088 semantics). -/
theorem approval_signed {x c r a : Id} (h : V C ops x (.approval c r a)) :
    ∃ o s ra u d e l t da ea, ops x = some o ∧
      (decode o.body : Option Body) = some (.approve s) ∧ o.reqs = [c, r, ra] ∧
      V C ops r (.request c u d e l t) ∧ V C ops ra (.admission c a da ea) ∧
      (l = true → a = u) ∧ da ≠ d ∧ C.verify da (signed o (.approve s)) s = true := by
  obtain ⟨o, b, fs, hx, hb, hr, hv⟩ := valid_inv h
  obtain ⟨s, d0, e0, u, d, e, l, t, da, ea, rfl, rfl, hh, hrr, hl, hd, hs⟩ := check_approval hv
  obtain ⟨c', r', ra, hreq, _, hrv, hav⟩ := all2_three hr
  rw [hreq] at hh hrr; simp at hh hrr; subst hh; subst hrr
  exact ⟨o, s, ra, u, d, e, l, t, da, ea, hx, hb, hreq, hrv, hav, hl, hd, hs⟩

/-- **Nobody is admitted unapproved.** Every admission is the founder's
(by the root itself), or is produced by an admit op y that cites a
Valid request r of c for that device, and exactly t Valid approvals of
r by t distinct users, where t is the threshold of the invitation r
redeems (request_invited). -/
theorem admission_approved (hk : Keyed ops) {y c u : Id} {d e : Key}
    (h : V C ops y (.admission c u d e)) :
    (y = c ∧ u = c) ∨
    ∃ o r aps l t us, ops y = some o ∧ (decode o.body : Option Body) = some .admit ∧
      o.reqs = c :: r :: aps ∧ V C ops r (.request c u d e l t) ∧
      All2 (fun a v => V C ops a (.approval c r v)) aps us ∧ us.Nodup ∧ us.length = t := by
  obtain ⟨o, b, fs, hx, hb, hr, hv⟩ := valid_inv h
  have hid := hk y o hx
  rcases check_admission hv with ⟨s, rfl, rfl, hc, hu, _⟩ | ⟨d0, e0, l, t, apfs, rfl, rfl, hh, hta⟩
  · left; rw [hid] at hc hu; exact ⟨hc.symm, hu.trans hc.symm⟩
  · obtain ⟨c', r, aps, hreq, _, hrv, haps⟩ := all2_cons2 hr
    rw [hreq] at hh hta; simp at hh hta; subst hh
    obtain ⟨us, hus, hn, hl⟩ := tally_iff.1 hta
    refine Or.inr ⟨o, r, aps, l, t, us, hx, hb, hreq, hrv, ?_, hn, hl⟩
    exact (All2.comp haps hus).imp fun ⟨_, hv, he⟩ => he ▸ hv

/-- **An eligible member's signed approval is Valid**, whoever else has
approved or been removed since. -/
theorem approve_valid {x c r ra : Id} {o : Op} {s : ByteArray} {d0 e0 : Key} {u a : Id}
    {d e da ea : Key} {l : Bool} {t : Nat}
    (hx : ops x = some o) (hb : (decode o.body : Option Body) = some (.approve s)) (hkd : o.kind = Body.tag (.approve s))
    (hreq : o.reqs = [c, r, ra]) (hc : V C ops c (.admission c c d0 e0))
    (hr : V C ops r (.request c u d e l t)) (ha : V C ops ra (.admission c a da ea))
    (hl : l = true → a = u) (hd : da ≠ d) (hs : C.verify da (signed o (.approve s)) s = true) :
    V C ops x (.approval c r a) := by
  refine spec_valid_of hx (fs := [.admission c c d0 e0, .request c u d e l t, .admission c a da ea])
    ?_ ?_
  · rw [hreq]; exact .cons hc (.cons hr (.cons ha .nil))
  · show validate C o _ = _
    unfold validate; rw [hb]; simp only [hkd, ↓reduceIte]
    simp [check, Root.check, Invitation.check, Request.check, Approve.check, Admit.check, Grant.check, Remove.check, Post.check, Profile.check, Attach.check, Chunk.check, React.check, Wrap.check, Rename.check, hreq, hd, hs]; exact hl

/-- **Enough approvals admit.** An admit op citing a Valid request and
exactly its threshold of Valid approvals by distinct users admits the
requesting device: into the issuer's user for a link, into the user the
request names for a member invitation. -/
theorem admit_admits {y c r : Id} {o : Op} {aps us : List Id} {d0 e0 : Key} {u : Id}
    {d e : Key} {l : Bool} {t : Nat}
    (hy : ops y = some o) (hb : (decode o.body : Option Body) = some .admit) (hkd : o.kind = Body.tag (.admit))
    (hreq : o.reqs = c :: r :: aps) (hc : V C ops c (.admission c c d0 e0))
    (hr : V C ops r (.request c u d e l t))
    (hap : All2 (fun a v => V C ops a (.approval c r v)) aps us) (hn : us.Nodup)
    (ht : us.length = t) :
    V C ops y (.admission c u d e) := by
  have hf : All2 (fun f v => f = Fact.approval c r v) (us.map (Fact.approval c r)) us := by
    clear hap hn ht; induction us with
    | nil => exact .nil
    | cons v vs ih => exact .cons rfl ih
  have hv : All2 (fun a g => V C ops a g) aps (us.map (Fact.approval c r)) := by
    clear hn ht hf hreq hy hb; induction hap with
    | nil => exact .nil
    | cons h1 _ ih => exact .cons h1 ih
  refine spec_valid_of hy (fs := .admission c c d0 e0 :: .request c u d e l t ::
    us.map (Fact.approval c r)) ?_ ?_
  · rw [hreq]; exact .cons hc (.cons hr hv)
  · show validate C o _ = _
    unfold validate; rw [hb]; simp only [hkd, ↓reduceIte]
    have := tally_iff.2 ⟨us, hf, hn, ht⟩
    simp [check, Root.check, Invitation.check, Request.check, Approve.check, Admit.check, Grant.check, Remove.check, Post.check, Profile.check, Attach.check, Chunk.check, React.check, Wrap.check, Rename.check, hreq, this]

theorem approvers_shared {c r : Id} : ∀ {fs : List Fact} {us}, approvers c r fs = some us →
    ∀ g ∈ fs, g.isLocal = false
  | [], _, _, g, hg => by cases hg
  | .approval .. :: rest, us, h, g, hg => by
    simp only [approvers] at h
    split at h
    · obtain ⟨vs, hv, _⟩ := Option.map_eq_some_iff.1 h
      rcases List.mem_cons.1 hg with rfl | hg
      · rfl
      · exact approvers_shared hv g hg
    · cases h
  | .admission .. :: _, _, h, _, _ | .invitation .. :: _, _, h, _, _ | .admin .. :: _, _, h, _, _
  | .removal .. :: _, _, h, _, _ | .message .. :: _, _, h, _, _ | .wrap .. :: _, _, h, _, _
  | .profile .. :: _, _, h, _, _ | .react .. :: _, _, h, _, _ | .request .. :: _, _, h, _, _
  | .attachment .. :: _, _, h, _, _ | .chunk .. :: _, _, h, _, _ | .secret .. :: _, _, h, _, _ | .accepted .. :: _, _, h, _, _
  | .joining .. :: _, _, h, _, _ | .named .. :: _, _, h, _, _ | .abandoned .. :: _, _, h, _, _
  | .key .. :: _, _, h, _, _ => by simp [approvers] at h

theorem tally_shared {c r : Id} {t : Nat} {fs : List Fact} (h : tally c r t fs = true) :
    ∀ g ∈ fs, g.isLocal = false := by
  unfold tally at h
  split at h
  · rename_i us hu; exact approvers_shared hu
  · cases h

end Community
