import app.community.Family
import app.community.member.invite.request.approve.admit.Proofs

namespace Community
open Engine Codec

@[simp] theorem approvals_map (ps : List Approve.Fact) : approvals (ps.map .ofApproval) = some ps := by
  induction ps with
  | nil => rfl
  | cons p t ih => simp [approvals, ih]

theorem approvals_eq {ls : List Fact} {ps : List Approve.Fact} (h : approvals ls = some ps) :
    ls = ps.map .ofApproval := by
  induction ls generalizing ps with
  | nil => simp [approvals] at h; subst h; rfl
  | cons g t ih =>
    cases g <;> simp [approvals] at h
    obtain ⟨t', ht, rfl⟩ := h
    simp [ih ht]

theorem all2_cons3 {α β} {R : α → β → Prop} {l : List α} {a b c : β} {rest : List β}
    (h : All2 R l (a :: b :: c :: rest)) :
    ∃ x y z t, l = x :: y :: z :: t ∧ R x a ∧ R y b ∧ R z c ∧ All2 R t rest := by
  cases h with | cons h1 h2 => cases h2 with | cons h3 h4 => cases h4 with
  | cons h5 h6 => exact ⟨_, _, _, _, rfl, h1, h3, h5, h6⟩

theorem all2_one {α β} {R : α → β → Prop} {l : List α} {a : β} (h : All2 R l [a]) :
    ∃ x, l = [x] ∧ R x a := by
  cases h with | cons h1 h2 => cases h2; exact ⟨_, rfl, h1⟩

theorem all2_nil {α β} {R : α → β → Prop} {l : List α} (h : All2 R l ([] : List β)) : l = [] := by
  cases h; rfl

theorem check_approval {C : Crypto} {o : Op} {b : Body} {fs : List Fact} {f : Approve.Fact}
    (h : check C o b fs = some (.ofApproval f)) :
    ∃ s d0 e0 k0 l ea ka ps, b = .approve s ∧
      fs = .admission f.c f.c d0 e0 k0 :: .request f.c f.ru f.rd f.re l :: .admission f.c f.u f.dev ea ka ::
        ps.map .ofApproval ∧
      o.reqs.head? = some f.c ∧ f.req = o.reqs.getD 1 .empty ∧ (l = true → f.u = f.ru) ∧ f.dev ≠ f.rd ∧
      C.verify f.dev (signed o b) s = true ∧
      Approve.links o f.c f.u f.dev ea (decide (f.u = f.c ∧ f.dev = d0 ∧ ea = e0)) ps =
        some (f.up, f.depth, f.prev, f.n) := by
  unfold check at h
  split at h <;> (try (simp at h; done))
  rename_i b r q a ls
  rcases b with ⟨s⟩; rcases r with ⟨c0, u0, d0, e0, k0⟩; rcases q with ⟨c1, u, d, e, l⟩; rcases a with ⟨c2, a', da, ea, ka⟩
  simp only [Approve.check] at h
  split at h
  · rename_i hc
    obtain ⟨h1, rfl, rfl, rfl, h5, h6, h7⟩ := hc
    obtain ⟨t, ht, hf⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨tup, htup, rfl⟩ := Option.map_eq_some_iff.1 ht
    obtain ⟨ps, hps, hl⟩ := Option.bind_eq_some_iff.1 htup
    simp only [Fact.ofApproval.injEq] at hf
    subst hf
    obtain ⟨up, depth, prev, n⟩ := tup
    rw [approvals_eq hps]
    exact ⟨s, _, _, _, l, ea, _, ps, rfl, rfl, h1, rfl, h5, h6, h7, hl⟩
  · simp at h

open Engine Codec
variable {C : Crypto} {ops : Id → Option Op}

/-- The requirements of a Valid approval, with what each produced: the
root, the request, its approver's admission, then its links. -/
theorem approval_reqs {x : Id} {f : Approve.Fact} (h : V C ops x (.ofApproval f)) :
    ∃ o s d0 e0 k0 l ea ka ra ys ps, ops x = some o ∧ (decode o.body : Option Body) = some (.approve s) ∧
      o.reqs = f.c :: f.req :: ra :: ys ∧
      V C ops f.c (.admission f.c f.c d0 e0 k0) ∧ V C ops f.req (.request f.c f.ru f.rd f.re l) ∧
      V C ops ra (.admission f.c f.u f.dev ea ka) ∧ All2 (fun r g => V C ops r g) ys (ps.map .ofApproval) ∧
      (l = true → f.u = f.ru) ∧ f.dev ≠ f.rd ∧ C.verify f.dev (signed o (.approve s)) s = true ∧
      Approve.links o f.c f.u f.dev ea (decide (f.u = f.c ∧ f.dev = d0 ∧ ea = e0)) ps =
        some (f.up, f.depth, f.prev, f.n) := by
  obtain ⟨o, b, fs, hx, hb, hr, hv⟩ := valid_inv h
  obtain ⟨s, d0, e0, k0, l, ea, ka, ps, rfl, rfl, hh, hrr, hl, hd, hs, hlk⟩ := check_approval hv
  obtain ⟨c', r', ra, ys, hreq, h1, h3, h5, h6⟩ := all2_cons3 hr
  rw [hreq] at hh hrr; simp at hh hrr; subst hh; subst hrr
  exact ⟨o, s, d0, e0, k0, l, ea, ka, ra, ys, ps, hx, hb, hreq, h1, h3, h5, h6, hl, hd, hs, hlk⟩

/-- **Every approval is a member's signed yes.** A Valid approval by user
a was signed by a device admitted into a, not the requesting device, and
a is the request's own user (the issuer's) when the request is for a
link. It names the admission it gives (`ru`, `rd`, `re`): the request's.
As with removals, its validity reads the cited facts only: an approval
by a user removed since stays Valid (#1088 semantics); whether it still
admits is the trust rule's (`Counts`). -/
theorem approval_signed {x : Id} {f : Approve.Fact} (h : V C ops x (.ofApproval f)) :
    ∃ o s ra ys l ea ka, ops x = some o ∧
      (decode o.body : Option Body) = some (.approve s) ∧ o.reqs = f.c :: f.req :: ra :: ys ∧
      V C ops f.req (.request f.c f.ru f.rd f.re l) ∧ V C ops ra (.admission f.c f.u f.dev ea ka) ∧
      (l = true → f.u = f.ru) ∧ f.dev ≠ f.rd ∧ C.verify f.dev (signed o (.approve s)) s = true := by
  obtain ⟨o, s, _, _, _, l, ea, ka, ra, ys, _, hx, hb, hreq, _, hrv, hav, _, hl, hd, hs, _⟩ := approval_reqs h
  exact ⟨o, s, ra, ys, l, ea, ka, hx, hb, hreq, hrv, hav, hl, hd, hs⟩

/-- **An approval's links (`approval_links`).** At depth 0 it is the
founder's device's: its approver's admission is the root's own.
Otherwise its `up` is a Valid approval that admitted its approver, one
step shallower. At place 0 it is its device's first; otherwise its
`prev` is its device's approval one place earlier. Both are among its
requirements, so its hash fixes them. -/
theorem approval_links {x : Id} {f : Approve.Fact} (h : V C ops x (.ofApproval f)) :
    ∃ ea, (∃ ra ka, V C ops ra (.admission f.c f.u f.dev ea ka)) ∧
      (f.depth = 0 → ∃ k, V C ops f.c (.admission f.c f.u f.dev ea k)) ∧
      (0 < f.depth → ∃ g, V C ops f.up (.ofApproval g) ∧ g.depth + 1 = f.depth ∧ g.c = f.c ∧
        g.ru = f.u ∧ g.rd = f.dev ∧ g.re = ea) ∧
      (0 < f.n → ∃ p, V C ops f.prev (.ofApproval p) ∧ p.n + 1 = f.n ∧ p.c = f.c ∧ p.dev = f.dev) := by
  obtain ⟨o, _, d0, e0, k0, _, ea, ka, ra, ys, ps, _, _, hreq, hroot, _, hra, hys, _, _, _, hlk⟩ := approval_reqs h
  refine ⟨ea, ⟨ra, ka, hra⟩, ?_⟩
  have root_of : decide (f.u = f.c ∧ f.dev = d0 ∧ ea = e0) = true →
      ∃ k, V C ops f.c (.admission f.c f.u f.dev ea k) := by
    intro hf; simp only [decide_eq_true_eq] at hf; obtain ⟨h1, h2, h3⟩ := hf; rw [h1, h2, h3]; exact ⟨k0, hroot⟩
  match ps, hys, hlk with
  | [], hys, hlk =>
    simp only [Approve.links] at hlk
    split at hlk
    · rename_i hf
      simp only [Option.some.injEq, Prod.mk.injEq] at hlk
      obtain ⟨_, h2, _, h4⟩ := hlk
      exact ⟨fun _ => root_of hf, fun hd => by omega, fun hn => by omega⟩
    · cases hlk
  | [p], hys, hlk =>
    obtain ⟨y, rfl, hy⟩ := all2_one hys
    have h3 : o.reqs.getD 3 .empty = y := by rw [hreq]; rfl
    simp only [Approve.links, h3] at hlk
    split at hlk
    · rename_i hf
      split at hlk
      · rename_i hm
        simp only [Option.some.injEq, Prod.mk.injEq] at hlk
        obtain ⟨_, h2, h3', h4⟩ := hlk
        simp only [Approve.mine, decide_eq_true_eq] at hm
        refine ⟨fun _ => root_of hf, fun hd => by omega, fun _ => ⟨p, ?_, by omega, hm.1, hm.2⟩⟩
        rw [← h3']; exact hy
      · cases hlk
    · split at hlk
      · rename_i hf ha
        simp only [Option.some.injEq, Prod.mk.injEq] at hlk
        obtain ⟨h1, h2, _, h4⟩ := hlk
        simp only [Approve.admits, decide_eq_true_eq] at ha
        refine ⟨fun hd => by omega, fun _ => ⟨p, ?_, by omega, ha.1, ha.2.1, ha.2.2.1, ha.2.2.2⟩,
          fun hn => by omega⟩
        rw [← h1]; exact hy
      · cases hlk
  | [q, p], hys, hlk =>
    obtain ⟨y1, y2, rfl, hq, hp⟩ := all2_two hys
    have h3 : o.reqs.getD 3 .empty = y1 := by rw [hreq]; rfl
    have h4 : o.reqs.getD 4 .empty = y2 := by rw [hreq]; rfl
    simp only [Approve.links, h3, h4] at hlk
    split at hlk
    · rename_i hc
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, Approve.admits, Approve.mine,
        decide_eq_true_eq] at hc
      obtain ⟨⟨_, ha⟩, hm⟩ := hc
      simp only [Option.some.injEq, Prod.mk.injEq] at hlk
      obtain ⟨h1, h2, h3', h4'⟩ := hlk
      refine ⟨fun hd => by omega, fun _ => ⟨q, ?_, by omega, ha.1, ha.2.1, ha.2.2.1, ha.2.2.2⟩,
        fun _ => ⟨p, ?_, by omega, hm.1, hm.2⟩⟩
      · rw [← h1]; exact hq
      · rw [← h3']; exact hp
    · cases hlk
  | _ :: _ :: _ :: _, _, hlk => simp [Approve.links] at hlk

/-- **Nobody is admitted unapproved.** Every admission is the founder's
(by the root itself), or is produced by an admit op y that cites
exactly a Valid request r of c for that device and one Valid approval
x of r, which names that admission (one approval admits: the user's
decision, 2026-10-31). -/
theorem admission_approved (hk : Keyed ops) {y c u : Id} {d e kid : Key}
    (h : V C ops y (.admission c u d e kid)) :
    (y = c ∧ u = c) ∨
    ∃ o r x l, ∃ g : Approve.Fact, ops y = some o ∧ (decode o.body : Option Body) = some .admit ∧
      o.reqs = [c, r, x] ∧ V C ops r (.request c u d e l) ∧ V C ops x (.ofApproval g) ∧
      g.c = c ∧ g.req = r ∧ g.ru = u ∧ g.rd = d ∧ g.re = e := by
  obtain ⟨o, b, fs, hx, hb, hr, hv⟩ := valid_inv h
  have hid := hk y o hx
  rcases check_admission hv with ⟨s, rfl, rfl, hc, hu, _⟩ | ⟨d0, e0, l, g, rfl, rfl, hgc, hgr, hh⟩
  · left; rw [hid] at hc hu; exact ⟨hc.symm, hu.trans hc.symm⟩
  · obtain ⟨c', r, x, hreq, _, hrv, hxv⟩ := all2_three hr
    rw [hreq] at hh hgr; simp at hh hgr; subst hh
    obtain ⟨_, _, _, _, l', _, _, _, _, _, hrv', _⟩ := approval_signed hxv
    rw [hgc, hgr] at hrv'
    have := spec_det hrv hrv'
    simp only [Verdict.valid.injEq, Fact.ofRequest.injEq, Request.Fact.mk.injEq] at this
    obtain ⟨_, h2, h3, h4, _⟩ := this
    exact Or.inr ⟨o, r, x, l, g, hx, hb, hreq, hrv, hxv, hgc, hgr, h2.symm, h3.symm, h4.symm⟩

/-- **An eligible member's signed approval is Valid**, whoever else has
approved or been removed: it cites the root, the request, its approver's
admission, then its links (`Approve.links`: none, or its previous
approval, for the founder's device; the approval that admitted its
approver, then its previous approval if any, for any other). -/
theorem approve_valid {x c r ra : Id} {o : Op} {s : ByteArray} {d0 e0 k0 : Key} {u a : Id}
    {d e da ea ka : Key} {l : Bool} {ys : List Id} {ps : List Approve.Fact} {t : Id × Nat × Id × Nat}
    (hx : ops x = some o) (hb : (decode o.body : Option Body) = some (.approve s)) (hkd : o.kind = Body.tag (.approve s))
    (hreq : o.reqs = c :: r :: ra :: ys) (hc : V C ops c (.admission c c d0 e0 k0))
    (hr : V C ops r (.request c u d e l)) (ha : V C ops ra (.admission c a da ea ka))
    (hys : All2 (fun y g => V C ops y g) ys (ps.map .ofApproval))
    (hlk : Approve.links o c a da ea (decide (a = c ∧ da = d0 ∧ ea = e0)) ps = some t)
    (hl : l = true → a = u) (hd : da ≠ d) (hs : C.verify da (signed o (.approve s)) s = true) :
    V C ops x (.ofApproval ⟨c, r, a, da, u, d, e, t.1, t.2.1, t.2.2.1, t.2.2.2⟩) := by
  refine spec_valid_of hx (fs := .admission c c d0 e0 k0 :: .request c u d e l :: .admission c a da ea ka ::
    ps.map .ofApproval) ?_ ?_
  · rw [hreq]; exact .cons hc (.cons hr (.cons ha hys))
  · show validate C o _ = _
    unfold validate; rw [hb]; simp only [hkd, ↓reduceIte]
    have hr1 : o.reqs.getD 1 .empty = r := by rw [hreq]; rfl
    have hh : o.reqs.head? = some c := by rw [hreq]; rfl
    simp only [check, Approve.check, approvals_map, Option.bind_some, hlk, hh, hr1,
      signedBy_ofApprove, hs]
    simp
    exact ⟨hl, hd⟩

/-- **One approval admits.** An admit op citing a Valid request and one
Valid approval of it admits the requesting device: into the issuer's
user for a link, into the user the request names for a member
invitation. -/
theorem admit_admits {y c r x : Id} {o : Op} {d0 e0 k0 : Key} {u : Id}
    {d e : Key} {l : Bool} {g : Approve.Fact}
    (hy : ops y = some o) (hb : (decode o.body : Option Body) = some .admit) (hkd : o.kind = Body.tag (.admit))
    (hreq : o.reqs = [c, r, x]) (hc : V C ops c (.admission c c d0 e0 k0))
    (hr : V C ops r (.request c u d e l)) (hx : V C ops x (.ofApproval g)) (hgc : g.c = c) (hgr : g.req = r) :
    V C ops y (.admission c u d e k0) := by
  refine spec_valid_of hy (fs := [.admission c c d0 e0 k0, .request c u d e l, .ofApproval g]) ?_ ?_
  · rw [hreq]; exact .cons hc (.cons hr (.cons hx .nil))
  · show validate C o _ = _
    unfold validate; rw [hb]; simp only [hkd, ↓reduceIte]
    simp [check, Admit.check, hreq, hgc, hgr]

end Community
