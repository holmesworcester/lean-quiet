/-
Laws of community state, over the Valid facts of any set of ops (what
a node holds at rest: Engine.status_iff_spec). Signatures are read
through `Crypto.verify`; where a law needs unforgeability it takes it
as the hypothesis `Unforgeable`.
-/
import ops.community.Facts

namespace Community
open Engine Codec

/-! ## Inverting the validators -/

theorem check_admission {C : Crypto} {o : Op} {b : Body} {fs : List Fact} {c u : Id} {d e : Key}
    (h : check C o b fs = some (.admission c u d e)) :
    (∃ s, b = .root d e s ∧ fs = [] ∧ c = o.id ∧ u = o.id ∧ C.verify d (signed o b) s = true) ∨
    (∃ d0 e0 l a, b = .admit ∧
      fs = [.admission c c d0 e0, .request c u d e l, .approval c (o.reqs.getD 1 .empty) a] ∧
      o.reqs.head? = some c) := by
  unfold check at h
  split at h <;> (try split at h) <;> (try simp at h; done)
  · simp only [Option.some.injEq, Fact.admission.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact Or.inl ⟨_, rfl, rfl, rfl, rfl, by assumption⟩
  · simp only [Option.some.injEq, Fact.admission.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    rename_i hc
    obtain ⟨h1, rfl, rfl, rfl, rfl⟩ := hc
    exact Or.inr ⟨_, _, _, _, rfl, rfl, h1⟩

theorem check_invitation {C : Crypto} {o : Op} {b : Body} {fs : List Fact} {c issuer : Id}
    {k : Key} {l : Bool} (h : check C o b fs = some (.invitation c issuer k l)) :
    ∃ s d0 e0 d e, b = .invite k l s ∧ fs = [.admission c c d0 e0, .admission c issuer d e] ∧
      o.reqs.head? = some c ∧ C.verify d (signed o b) s = true := by
  unfold check at h
  split at h <;> (try split at h) <;> (try simp at h; done)
  simp only [Option.some.injEq, Fact.invitation.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  rename_i hc
  obtain ⟨h1, rfl, rfl, h5⟩ := hc
  exact ⟨_, _, _, _, _, rfl, rfl, h1, h5⟩

theorem check_request {C : Crypto} {o : Op} {b : Body} {fs : List Fact} {c u : Id} {d e : Key}
    {l : Bool} (h : check C o b fs = some (.request c u d e l)) :
    ∃ cs bs d0 e0 issuer k, b = .request d e cs bs ∧
      fs = [.admission c c d0 e0, .invitation c issuer k l] ∧ o.reqs.head? = some c ∧
      u = (if l then issuer else o.id) ∧
      C.verify d (signed o b) cs = true ∧ C.verify k (signed o b) bs = true := by
  unfold check at h
  split at h <;> (try split at h) <;> (try simp at h; done)
  simp only [Option.some.injEq, Fact.request.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
  rename_i hc
  obtain ⟨h1, rfl, rfl, h4, h5⟩ := hc
  exact ⟨_, _, _, _, _, _, rfl, rfl, h1, rfl, h4, h5⟩

theorem check_approval {C : Crypto} {o : Op} {b : Body} {fs : List Fact} {c r a : Id}
    (h : check C o b fs = some (.approval c r a)) :
    ∃ s d0 e0 u d e l da ea, b = .approve s ∧
      fs = [.admission c c d0 e0, .request c u d e l, .admission c a da ea] ∧
      o.reqs.head? = some c ∧ r = o.reqs.getD 1 .empty ∧ (l = true → a = u) ∧ da ≠ d ∧
      C.verify da (signed o b) s = true := by
  unfold check at h
  split at h <;> (try split at h) <;> (try simp at h; done)
  simp only [Option.some.injEq, Fact.approval.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rename_i hc
  obtain ⟨h1, rfl, rfl, rfl, h5, h6, h7⟩ := hc
  exact ⟨_, _, _, _, _, _, _, _, _, rfl, rfl, h1, rfl, h5, h6, h7⟩

theorem check_admin {C : Crypto} {o : Op} {b : Body} {fs : List Fact} {c t : Id}
    (h : check C o b fs = some (.admin c t)) :
    ∃ s d0 e0 u d e auth d' e', b = .grant s ∧
      fs = [.admission c c d0 e0, .admission c u d e, auth, .admission c t d' e'] ∧
      o.reqs.head? = some c ∧ isAdmin c u auth = true ∧ C.verify d (signed o b) s = true := by
  unfold check at h
  split at h <;> (try split at h) <;> (try simp at h; done)
  simp only [Option.some.injEq, Fact.admin.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rename_i hc
  obtain ⟨h1, rfl, rfl, rfl, h5, h6⟩ := hc
  exact ⟨_, _, _, _, _, _, _, _, _, rfl, rfl, h1, h5, h6⟩

theorem check_removal {C : Crypto} {o : Op} {b : Body} {fs : List Fact} {c t u : Id}
    (h : check C o b fs = some (.removal c t u)) :
    ∃ s d0 e0 d e auth d' e', b = .remove s ∧
      fs = [.admission c c d0 e0, .admission c u d e, auth, .admission c t d' e'] ∧
      o.reqs.head? = some c ∧ ((t = u ∧ auth.isLocal = false) ∨ isAdmin c u auth = true) ∧
      C.verify d (signed o b) s = true := by
  unfold check at h
  split at h <;> (try split at h) <;> (try simp at h; done)
  simp only [Option.some.injEq, Fact.removal.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rename_i hc
  obtain ⟨h1, rfl, rfl, rfl, h5, h6⟩ := hc
  exact ⟨_, _, _, _, _, _, _, _, rfl, rfl, h1, h5, h6⟩

theorem check_message {C : Crypto} {o : Op} {b : Body} {fs : List Fact} {c u : Id}
    {d k t : ByteArray} {n tm : Nat}
    (h : check C o b fs = some (.message c u d k t n tm)) :
    ∃ s d0 e0 e, b = .post k t n tm s ∧ fs = [.admission c c d0 e0, .admission c u d e] ∧
      o.reqs.head? = some c ∧ C.verify d (signed o b) s = true := by
  unfold check at h
  split at h <;> (try split at h) <;> (try simp at h; done)
  simp only [Option.some.injEq, Fact.message.injEq, and_true] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
  rename_i hc
  obtain ⟨h1, rfl, rfl, h4⟩ := hc
  exact ⟨_, _, _, _, rfl, rfl, h1, h4⟩

/-- A child is signed by an admitted device of its root's user. Only a
root can be cited: the final fact's clump is explicitly `none`. -/
theorem check_child {C : Crypto} {o : Op} {b : Body} {fs : List Fact} {c u root : Id}
    {d k t : ByteArray} {n tm : Nat}
    (h : check C o b fs = some (.message c u d k t n tm (some root))) :
    ∃ s d0 e0 e d2 k2 t2 n2 tm2, b = .post k t n tm s ∧
      fs = [.admission c c d0 e0, .admission c u d e, .message c u d2 k2 t2 n2 tm2 none] ∧
      o.reqs.head? = some c ∧ root = o.reqs.getD 2 .empty ∧ C.verify d (signed o b) s = true := by
  unfold check at h
  split at h <;> (try split at h) <;> (try simp at h; done)
  simp only [Option.some.injEq, Fact.message.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hr⟩ := h
  subst root
  rename_i hc
  obtain ⟨h1, rfl, rfl, rfl, rfl, hs⟩ := hc
  exact ⟨_, _, _, _, _, _, _, _, _, rfl, rfl, h1, rfl, hs⟩

theorem check_profile {C : Crypto} {o : Op} {b : Body} {fs : List Fact} {c u : Id}
    {n : ByteArray} {tm : Nat}
    (h : check C o b fs = some (.profile c u n tm)) :
    ∃ s d0 e0 d e, b = .profile n tm s ∧ fs = [.admission c c d0 e0, .admission c u d e] ∧
      o.reqs.head? = some c ∧ n.size ≤ 64 ∧ C.verify d (signed o b) s = true := by
  unfold check at h
  split at h <;> (try split at h) <;> (try simp at h; done)
  simp only [Option.some.injEq, Fact.profile.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  rename_i hc
  obtain ⟨h1, rfl, rfl, h4, h5⟩ := hc
  exact ⟨_, _, _, _, _, rfl, rfl, h1, h4, h5⟩

theorem all2_two {α β} {R : α → β → Prop} {l : List α} {a b : β} (h : All2 R l [a, b]) :
    ∃ x y, l = [x, y] ∧ R x a ∧ R y b := by
  cases h with | cons h1 h2 => cases h2 with | cons h3 h4 => cases h4; exact ⟨_, _, rfl, h1, h3⟩

theorem all2_cons2 {α β} {R : α → β → Prop} {l : List α} {a b : β} {rest : List β}
    (h : All2 R l (a :: b :: rest)) :
    ∃ x y t, l = x :: y :: t ∧ R x a ∧ R y b ∧ All2 R t rest := by
  cases h with | cons h1 h2 => cases h2 with | cons h3 h4 => exact ⟨_, _, _, rfl, h1, h3, h4⟩

theorem all2_four {α β} {R : α → β → Prop} {l : List α} {a b c d : β} (h : All2 R l [a, b, c, d]) :
    ∃ x y z w, l = [x, y, z, w] ∧ R x a ∧ R y b ∧ R z c ∧ R w d := by
  cases h with | cons h1 h2 => cases h2 with | cons h3 h4 => cases h4 with
  | cons h5 h6 => cases h6 with | cons h7 h8 => cases h8; exact ⟨_, _, _, _, rfl, h1, h3, h5, h7⟩

theorem all2_three {α β} {R : α → β → Prop} {l : List α} {a b c : β} (h : All2 R l [a, b, c]) :
    ∃ x y z, l = [x, y, z] ∧ R x a ∧ R y b ∧ R z c := by
  cases h with | cons h1 h2 => cases h2 with | cons h3 h4 => cases h4 with
  | cons h5 h6 => cases h6; exact ⟨_, _, _, rfl, h1, h3, h5⟩

theorem All2.comp {α β γ} {R : α → β → Prop} {S : β → γ → Prop} {l : List α} {m : List β}
    {n : List γ} (h1 : All2 R l m) (h2 : All2 S m n) : All2 (fun a c => ∃ b, R a b ∧ S b c) l n := by
  induction h1 generalizing n with
  | nil => cases h2; exact .nil
  | cons ha _ ih => cases h2 with | cons hb hr => exact .cons ⟨_, ha, hb⟩ (ih hr)

/-! ## Community state -/

section
variable (C : Crypto) (ops : Id → Option Op)

/-- x is Valid with fact f. -/
def V (x : Id) (f : Fact) : Prop := Spec (family C) ops x (.valid f)

/-- Device d is admitted into user u of community c, with key e. -/
def Admitted (c u : Id) (d e : Key) : Prop := ∃ x, V C ops x (.admission c u d e)

/-- User u of community c has been removed (by anyone allowed to). -/
def Removed (c u : Id) : Prop := ∃ x r, V C ops x (.removal c u r)

/-- User u is an admin of c: the founder, or granted admin. -/
def IsAdmin (c u : Id) : Prop :=
  (u = c ∧ ∃ x d e, V C ops x (.admission c c d e)) ∨ ∃ x, V C ops x (.admin c u)

/-- A member: an admitted user not removed. -/
def Member (c u : Id) : Prop := (∃ d e, Admitted C ops c u d e) ∧ ¬ Removed C ops c u

/-- Device d is live in c: admitted, and none of the users it is
admitted into (under any key) removed. A device may be admitted into
several users; removing any of them cuts it (docs/REMOVAL.md). -/
def Live (c : Id) (d : Key) : Prop :=
  (∃ u e, Admitted C ops c u d e) ∧ ∀ u e, Admitted C ops c u d e → ¬ Removed C ops c u

/-- Device d is cut in c: admitted into a user that is removed. -/
def Cut (c : Id) (d : Key) : Prop := ∃ u e, Admitted C ops c u d e ∧ Removed C ops c u

end

variable {C : Crypto} {ops : Id → Option Op}

theorem valid_inv {x : Id} {f : Fact} (h : V C ops x f) :
    ∃ o b fs, ops x = some o ∧ (decode o.body : Option Body) = some b ∧
      All2 (fun r g => V C ops r g) o.reqs fs ∧ check C o b fs = some f := by
  obtain ⟨o, fs, hx, hr, hv⟩ := spec_valid_inv h
  unfold family validate at hv; simp only at hv
  cases hb : (decode o.body : Option Body) with
  | none => rw [hb] at hv; simp at hv
  | some b =>
    rw [hb] at hv; simp only at hv
    split at hv
    · exact ⟨o, b, fs, hx, hb, hr, hv⟩
    · cases hv

/-- **A Valid op is the op its requirements and body make**: its type is
its body's type and its body bytes are its body's encoding. So nobody
makes a second op of a Valid fact by re-sending it under another type. -/
theorem op_of_valid {x : Id} {f : Fact} (h : V C ops x f) :
    ∃ o b, ops x = some o ∧ o = Op.make b.tag o.reqs (encode b) ∧
      (decode o.body : Option Body) = some b := by
  obtain ⟨o, fs, hx, _, hv⟩ := spec_valid_inv h
  unfold family validate at hv; simp only at hv
  cases hb : (decode o.body : Option Body) with
  | none => rw [hb] at hv; simp at hv
  | some b =>
    rw [hb] at hv; simp only at hv
    split at hv
    · rename_i hkd
      exact ⟨o, b, hx, Op.ext' hkd rfl (Codec.encode_decode hb).symm, hb⟩
    · cases hv

theorem isAdmin_sound {c u y : Id} {g : Fact} (hg : V C ops y g) (h : isAdmin c u g = true) :
    IsAdmin C ops c u := by
  cases g with
  | admission c' u' d e =>
    simp [isAdmin] at h; obtain ⟨rfl, rfl, rfl⟩ := h
    exact Or.inl ⟨rfl, y, d, e, hg⟩
  | admin c' u' => simp [isAdmin] at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inr ⟨y, hg⟩
  | _ => simp [isAdmin] at h

/-! ## Authorization: every message is by an admitted device -/

/-- A Valid message cites an admission of its author's device into its
author's user, and that device signed it. -/
theorem message_authorized {x c u : Id} {d k t : ByteArray} {n tm : Nat} {clump : Option Id}
    (h : V C ops x (.message c u d k t n tm clump)) :
    ∃ o s e y, ops x = some o ∧ (decode o.body : Option Body) = some (.post k t n tm s) ∧
      o.reqs.take 2 = [c, y] ∧ V C ops y (.admission c u d e) ∧
      C.verify d (signed o (.post k t n tm s)) s = true := by
  obtain ⟨o, b, fs, hx, hb, hr, hv⟩ := valid_inv h
  cases clump with
  | none =>
    obtain ⟨s, d0, e0, e, rfl, rfl, hh, hs⟩ := check_message hv
    obtain ⟨a, y, hreq, _, hy⟩ := all2_two hr
    rw [hreq] at hh; simp at hh; subst hh
    exact ⟨o, s, e, y, hx, hb, by rw [hreq]; rfl, hy, hs⟩
  | some root =>
    obtain ⟨s, d0, e0, e, d2, k2, t2, n2, tm2, rfl, rfl, hh, _, hs⟩ := check_child hv
    obtain ⟨a, y, rest, hreq, _, hy, _⟩ := all2_cons2 hr
    rw [hreq] at hh; simp at hh; subst hh
    exact ⟨o, s, e, y, hx, hb, by rw [hreq]; rfl, hy, hs⟩

/-- Every child has one Valid root by the same user in the same community.
This is about the running validator and signed requirement graph. -/
theorem child_has_root {x c u root : Id} {d k t : ByteArray} {n tm : Nat}
    (h : V C ops x (.message c u d k t n tm (some root))) :
    ∃ d2 k2 t2 n2 tm2, V C ops root (.message c u d2 k2 t2 n2 tm2 none) := by
  obtain ⟨o, b, fs, _, _, hr, hv⟩ := valid_inv h
  obtain ⟨_, _, _, _, d2, k2, t2, n2, tm2, _, rfl, _, he, _⟩ := check_child hv
  obtain ⟨a, y, rest, hreq, _, _, hrest⟩ := all2_cons2 hr
  cases hrest with
  | cons hroot hnil =>
    cases hnil
    rw [hreq] at he
    simp only [List.getD_cons_succ, List.getD_cons_zero] at he
    subst root
    exact ⟨d2, k2, t2, n2, tm2, hroot⟩

/-! ## No impersonation -/

/-- What a device key has signed. -/
def Unforgeable (C : Crypto) (Signed : Key → ByteArray → Prop) : Prop :=
  ∀ pk m s, C.verify pk m s = true → Signed pk m

/-- Every admission was consented to by its device: the device signed
the root that admits it (x = y), or the request its admit cites (x is
y's slot 1). -/
theorem admission_consented {y c u : Id} {d e : Key} (h : V C ops y (.admission c u d e)) :
    ∃ x o b s, (x = y ∨ ∃ oy, ops y = some oy ∧ oy.reqs.getD 1 .empty = x) ∧
      ops x = some o ∧ (decode o.body : Option Body) = some b ∧
      C.verify d (signed o b) s = true := by
  obtain ⟨o, b, fs, hx, hb, hr, hv⟩ := valid_inv h
  rcases check_admission hv with ⟨s, rfl, _, _, _, hs⟩ | ⟨d0, e0, l, a, rfl, rfl, _⟩
  · exact ⟨y, o, _, s, Or.inl rfl, hx, hb, hs⟩
  · obtain ⟨_, r, _, hreq, _, hrv, _⟩ := all2_cons2 hr
    obtain ⟨or, br, fsr, hor, hbr, _, hvr⟩ := valid_inv hrv
    obtain ⟨cs, _, _, _, _, _, rfl, _, _, _, hcs, _⟩ := check_request hvr
    exact ⟨r, or, _, cs, Or.inr ⟨o, hx, by rw [hreq]; rfl⟩, hor, hbr, hcs⟩

/-- **Impersonation is impossible.** If signatures are unforgeable, a
message attributed to user u and device d was signed, as this exact op,
by the holder of d's key, and that holder also signed the op that
admitted d into u: the root, or the request its admission cites.
Nobody can post as a user without a device the user's admission binds
and that device's key. -/
theorem no_impersonation {Signed : Key → ByteArray → Prop} (hU : Unforgeable C Signed)
    {x c u : Id} {d k t : ByteArray} {n tm : Nat} {clump : Option Id}
    (h : V C ops x (.message c u d k t n tm clump)) :
    ∃ o s, ops x = some o ∧ (decode o.body : Option Body) = some (.post k t n tm s) ∧
      Signed d (signed o (.post k t n tm s)) ∧
      ∃ y e z oz bz, V C ops y (.admission c u d e) ∧
        (z = y ∨ ∃ oy, ops y = some oy ∧ oy.reqs.getD 1 .empty = z) ∧ ops z = some oz ∧
        (decode oz.body : Option Body) = some bz ∧ Signed d (signed oz bz) := by
  obtain ⟨o, s, e, y, hx, hb, _, hy, hs⟩ := message_authorized h
  obtain ⟨z, oz, bz, s', hz, hoz, hbz, hs'⟩ := admission_consented hy
  exact ⟨o, s, hx, hb, hU _ _ _ hs, y, e, z, oz, bz, hy, hz, hoz, hbz, hU _ _ _ hs'⟩

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

/-- **Nobody can rename another user.** If signatures are unforgeable, a
Valid profile of user u was signed, as this exact op, by the holder of a
device key admitted into u, and that holder also signed the op that
admitted it: the root, or the request its admission cites. -/
theorem no_renaming {Signed : Key → ByteArray → Prop} (hU : Unforgeable C Signed)
    {x c u : Id} {n : ByteArray} {tm : Nat}
    (h : V C ops x (.profile c u n tm)) :
    ∃ o s d, ops x = some o ∧ (decode o.body : Option Body) = some (.profile n tm s) ∧
      Signed d (signed o (.profile n tm s)) ∧
      ∃ y e z oz bz, V C ops y (.admission c u d e) ∧
        (z = y ∨ ∃ oy, ops y = some oy ∧ oy.reqs.getD 1 .empty = z) ∧ ops z = some oz ∧
        (decode oz.body : Option Body) = some bz ∧ Signed d (signed oz bz) := by
  obtain ⟨o, s, d, e, y, hx, hb, _, hy, _, hs⟩ := profile_authorized h
  obtain ⟨z, oz, bz, s', hz, hoz, hbz, hs'⟩ := admission_consented hy
  exact ⟨o, s, d, hx, hb, hU _ _ _ hs, y, e, z, oz, bz, hy, hz, hoz, hbz, hU _ _ _ hs'⟩

/-- Every invitation was signed by a device admitted into its issuer. -/
theorem invitation_issued {i c issuer : Id} {k : Key} {l : Bool}
    (h : V C ops i (.invitation c issuer k l)) :
    ∃ o b s z d e, ops i = some o ∧ (decode o.body : Option Body) = some b ∧
      V C ops z (.admission c issuer d e) ∧ C.verify d (signed o b) s = true := by
  obtain ⟨o, b, fs, hx, hb, hr, hv⟩ := valid_inv h
  obtain ⟨s, d0, e0, d, e, rfl, rfl, _, hs⟩ := check_invitation hv
  obtain ⟨_, z, _, _, hz⟩ := all2_two hr
  exact ⟨o, _, s, z, d, e, hx, hb, hz, hs⟩

/-- Ops are stored under their own ids (Engine.Inv.key). -/
def Keyed (ops : Id → Option Op) : Prop := ∀ x o, ops x = some o → o.id = x

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
  obtain ⟨cs, bs, d0, e0, issuer, k, rfl, rfl, hh, hu, hcs, hbs⟩ := check_request hv
  obtain ⟨a, i, hreq, _, hi⟩ := all2_two hr
  rw [hreq] at hh; simp at hh; subst hh
  rw [hid] at hu
  exact ⟨o, _, i, issuer, k, cs, bs, hx, hb, hreq, hi, hu, hcs, hbs⟩

/-- **Every approval is a member's signed yes.** A Valid approval of
request r by user a was signed by a device admitted into a, not the
requesting device, and a is the request's own user (the issuer's) when
the request is for a link. As with removals, its validity reads the
cited facts only: an approval by a removed user counts, whenever it
was made (#1088 semantics). -/
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

/-- **A request with its invitation and both signatures is Valid.** -/
theorem request_valid (hk : Keyed ops) {r c i : Id} {o : Op} {d e cs bs : ByteArray}
    {d0 e0 : Key} {issuer : Id} {k : Key} {l : Bool}
    (hy : ops r = some o) (hb : (decode o.body : Option Body) = some (.request d e cs bs)) (hkd : o.kind = Body.tag (.request d e cs bs))
    (hreq : o.reqs = [c, i]) (hc : V C ops c (.admission c c d0 e0))
    (hi : V C ops i (.invitation c issuer k l))
    (hcs : C.verify d (signed o (.request d e cs bs)) cs = true)
    (hbs : C.verify k (signed o (.request d e cs bs)) bs = true) :
    V C ops r (.request c (if l then issuer else r) d e l) := by
  have hid := hk r o hy
  refine spec_valid_of hy (fs := [.admission c c d0 e0, .invitation c issuer k l]) ?_ ?_
  · rw [hreq]; exact .cons hc (.cons hi .nil)
  · show validate C o _ = _
    unfold validate; rw [hb]; simp only [hkd, ↓reduceIte]
    simp [check, hreq, hcs, hbs, hid]

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
    simp [check, hreq, hd, hs]; exact hl

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
    simp [check, hreq]

/-- **Nobody is admitted without a member's approval.** Every admission
is the founder's (the root itself), or its admit cites exactly a Valid
request for that very device and one Valid approval of it. The approval
was signed by a device admitted into the approving user, other than the
requesting device, and for a device link the approving user is the
request's own. The bearer key alone admits nobody. -/
theorem admission_needs_approval (hk : Keyed ops) {y c u : Id} {d e : Key}
    (h : V C ops y (.admission c u d e)) :
    (y = c ∧ u = c) ∨
    ∃ o r x a l da ea ra, ops y = some o ∧ o.reqs = [c, r, x] ∧ V C ops r (.request c u d e l) ∧
      V C ops x (.approval c r a) ∧ V C ops ra (.admission c a da ea) ∧ da ≠ d ∧
      (l = true → a = u) := by
  rcases admission_approved hk h with h | ⟨o, r, x, a, l, hy, _, hreq, hr, hx⟩
  · exact Or.inl h
  · obtain ⟨_, _, ra, u', d', e', l', da, ea, _, _, _, hr', hra, hl, hd, _⟩ := approval_signed hx
    have := spec_det hr hr'
    simp only [Verdict.valid.injEq, Fact.request.injEq] at this
    obtain ⟨_, rfl, rfl, rfl, rfl⟩ := this
    exact Or.inr ⟨o, r, x, a, l, da, ea, ra, hy, hreq, hr, hx, hra, hd, hl⟩

/-- **A removed member's approval counts.** An approval by a user of c
stays Valid whatever removals follow, and admits: the admit reads the
approval's fact, and nothing about its approver's removal appears in
the premises. Nothing orders an approval before or after a removal,
so an approval a removed user makes after its removal counts too
(#1088 semantics: validity reads cited facts only). In practice it
reaches only nodes the removed user can still sync with, or that
learned it from them. -/
theorem removed_approver_admits {y x c r : Id} {o : Op} {d0 e0 : Key} {u a : Id} {d e : Key}
    {l : Bool} (hy : ops y = some o) (hb : (decode o.body : Option Body) = some .admit)
    (hkd : o.kind = Body.tag .admit) (hreq : o.reqs = [c, r, x]) (hc : V C ops c (.admission c c d0 e0))
    (hr : V C ops r (.request c u d e l)) (hx : V C ops x (.approval c r a))
    (_removed : Removed C ops c a) :
    V C ops y (.admission c u d e) :=
  admit_admits hy hb hkd hreq hc hr hx

/-! ## Removal -/

/-- **An admission's community has a Valid root.** -/
theorem root_of_admission (hk : Keyed ops) {y c u : Id} {d e : Key} (h : V C ops y (.admission c u d e)) :
    ∃ d0 e0, V C ops c (.admission c c d0 e0) := by
  obtain ⟨o, b, fs, hx, _, hr, hv⟩ := valid_inv h
  rcases check_admission hv with ⟨s, rfl, rfl, hc, hu, _⟩ | ⟨d0, e0, l, a, rfl, rfl, hh⟩
  · have h1 : c = y := hc.trans (hk y o hx)
    have h2 : u = y := hu.trans (hk y o hx)
    subst h1; subst h2
    exact ⟨d, e, h⟩
  · obtain ⟨x, _, _, hreq, hxv, _, _⟩ := all2_cons2 hr
    rw [hreq] at hh; simp at hh; subst hh
    exact ⟨d0, e0, hxv⟩

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
    simp [check, hreq, hadm, hs]

/-- **Mutual removal.** Two admins who remove each other, concurrently
or not, are both removed: neither removal invalidates the other. -/
theorem mutual_removal {x y c : Id} {u v : Id}
    (hx : V C ops x (.removal c v u)) (hy : V C ops y (.removal c u v)) :
    Removed C ops c u ∧ Removed C ops c v :=
  ⟨⟨y, v, hy⟩, ⟨x, u, hx⟩⟩

/-- Admin is granted only by an admin. -/
theorem admin_granted {x c t : Id} (h : V C ops x (.admin c t)) : ∃ u, IsAdmin C ops c u := by
  obtain ⟨o, b, fs, _, _, hr, hv⟩ := valid_inv h
  obtain ⟨_, _, _, u, _, _, auth, _, _, rfl, rfl, _, ha, _⟩ := check_admin hv
  obtain ⟨_, _, z, _, _, _, _, hz, _⟩ := all2_four hr
  exact ⟨u, isAdmin_sound hz ha⟩

/-- **Removal is permanent.** More ops never restore a removed user:
redelivery, delay and reordering cannot undo a removal. -/
theorem removed_stays {ops' : Id → Option Op} (he : Extends ops ops') {c u : Id}
    (h : Removed C ops c u) : Removed C ops' c u := by
  obtain ⟨x, r, hx⟩ := h
  exact ⟨x, r, spec_extends he hx⟩

/-- **Removal does not rewrite history.** Every Valid fact stays Valid
as ops arrive, removals included: a removed user's messages, admissions
and attributions remain. -/
theorem valid_stays {ops' : Id → Option Op} (he : Extends ops ops') {x : Id} {f : Fact}
    (h : V C ops x f) : V C ops' x f := spec_extends he h

/-! ## A device's own state, and community names -/

theorem check_secret {C : Crypto} {o : Op} {b : Body} {fs : List Fact} {pk seed : ByteArray}
    (h : check C o b fs = some (.secret pk seed)) : b = .secret pk seed ∧ fs = [] ∧ C.pub seed = pk := by
  unfold check at h
  split at h <;> (try split at h) <;> (try simp at h; done)
  simp only [Option.some.injEq, Fact.secret.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rename_i hc
  exact ⟨rfl, rfl, hc⟩

/-- **A secret's seed is its key's**: `secret.byKey [pk]` rows hold a
seed whose key pair has public key pk. -/
theorem secret_derives {x : Id} {pk seed : ByteArray} (h : V C ops x (.secret pk seed)) :
    C.pub seed = pk := by
  obtain ⟨o, b, fs, _, _, _, hv⟩ := valid_inv h
  exact (check_secret hv).2.2

theorem check_named {C : Crypto} {o : Op} {b : Body} {fs : List Fact} {c u : Id} {nm : ByteArray}
    {n : Nat} (h : check C o b fs = some (.named c u nm n)) :
    ∃ s d0 e0 d e auth prev, b = .name n nm s ∧
      fs = .admission c c d0 e0 :: .admission c u d e :: auth :: prev ∧ o.reqs.head? = some c ∧
      isAdmin c u auth = true ∧ nm.size ≤ 64 ∧ counterOk c n prev = true ∧
      C.verify d (signed o b) s = true := by
  unfold check at h
  split at h <;> (try split at h) <;> (try simp at h; done)
  simp only [Option.some.injEq, Fact.named.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  rename_i hc
  obtain ⟨h1, rfl, rfl, h4, h5, h6, h7⟩ := hc
  exact ⟨_, _, _, _, _, _, _, rfl, rfl, h1, h4, h5, h6, h7⟩

/-- **Only admins name a community.** -/
theorem named_by_admin {x c u : Id} {nm : ByteArray} {n : Nat} (h : V C ops x (.named c u nm n)) :
    IsAdmin C ops c u := by
  obtain ⟨o, b, fs, _, _, hr, hv⟩ := valid_inv h
  obtain ⟨_, _, _, _, _, auth, _, rfl, rfl, _, ha, _⟩ := check_named hv
  obtain ⟨_, _, t, _, _, _, hrest⟩ := all2_cons2 hr
  cases hrest with
  | cons hz _ => exact isAdmin_sound hz ha

/-- The facts only a device's own local ops produce. -/

theorem check_local {C : Crypto} {o : Op} {b : Body} {fs : List Fact} {f : Fact}
    (h : check C o b fs = some f) (hl : f.isLocal = true) : b.isLocal = true := by
  unfold check at h
  split at h <;> (try split at h) <;> (try simp at h; done) <;>
    first
    | rfl
    | (simp only [Option.some.injEq] at h; subst h; simp [Fact.isLocal] at hl)

/-- **A device's own state is its own.** In a node fed by its own writes
and by peers' jobs through `intake`, every op behind a Valid secret,
acceptance or pending join is one of its own writes. -/
theorem local_fact_mine {M : List Op} {s : DB Fact} (hf : Fed (family C) M s) {x : Id} {f : Fact}
    (hv : V C s.ops x f) (hl : f.isLocal = true) : ∃ o ∈ M, s.ops x = some o := by
  obtain ⟨o, b, fs, hx, hb, _, hc⟩ := valid_inv hv
  refine ⟨o, stored_local hf hx ?_, hx⟩
  show (family C).room o = none
  simp [Family.room, family, scopeOf, hb, check_local hc hl]


/-! ## Attachments -/

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
  split at h <;> (try split at h) <;> (try simp at h; done)
  simp only [Option.some.injEq, Fact.attachment.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
  rename_i hc
  obtain ⟨h1, rfl, rfl, rfl, rfl, h6, _, _, _, h10⟩ := hc
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, rfl, rfl, h1, rfl, h6, h10⟩

/-- **A chunk is Valid only if its Merkle path verifies** against the
root and length it names (`Merkle.verify_sound` then makes it that
file's slice). -/
theorem check_chunk {C : Crypto} {o : Op} {b : Body} {fs : List Fact} {c att root : Id} {len i : Nat}
    (h : check C o b fs = some (.chunk c att root len i)) :
    ∃ slice sibs, b = .chunk root len i slice sibs ∧ o.reqs.head? = some c ∧ att = o.reqs.getD 1 .empty ∧
      Merkle.verify sha256 root len i slice sibs = true ∧
      ∃ d e m u k x, fs = [.admission c c d e, .attachment c m u root len k x] := by
  unfold check at h
  split at h <;> (try split at h) <;> (try simp at h; done)
  simp only [Option.some.injEq, Fact.chunk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
  rename_i hc
  obtain ⟨h1, rfl, rfl, rfl, rfl, h6⟩ := hc
  exact ⟨_, _, rfl, h1, rfl, h6, _, _, _, _, _, _, rfl⟩

/-- **A Valid chunk is its file's slice.** If its root is a file's root
(SHA-256 32 bytes wide, and nothing the root hashes having a second
preimage), its length is the file's, its slice is the file's slice at
its index, and its siblings are that slice's proof. -/
theorem chunk_is_slice {C : Crypto} {o : Op} {b : Body} {fs : List Fact} {c att : Id} {len i : Nat}
    {ct : ByteArray} (hsize : ∀ x, (sha256 x).size = 32)
    (hspr : Merkle.NoSecondPreimage sha256 (Merkle.treeInputs sha256 ct))
    (h : check C o b fs = some (.chunk c att (Merkle.fileRoot sha256 ct) len i)) :
    ∃ slice, b = .chunk (Merkle.fileRoot sha256 ct) len i slice (Merkle.proof sha256 ct i) ∧
      len = ct.size ∧ (Merkle.slices ct)[i]? = some slice := by
  obtain ⟨slice, sibs, rfl, _, _, hv, _⟩ := check_chunk h
  obtain ⟨hl, hs, rfl⟩ := Merkle.verify_sound hsize hspr hv
  exact ⟨slice, rfl, hl, hs⟩

/-- A receipt's validator: it cites one message, saturated, and names
it with its community and key. -/
theorem check_received {clump : Option Id} {C : Crypto} {o : Op} {b : Body} {fs : List Fact} {c kid m : Id} {k : Nat}
    (h : check C o b fs = some (.received c kid m k clump)) :
    b = .receive k ∧ m = o.reqs.headD .empty ∧
      ∃ u d sealed n tm, fs = [.message c u d kid sealed n tm clump] ∧ countCap ≤ n := by
  unfold check at h
  split at h <;> (try split at h) <;> (try simp at h; done)
  simp only [Option.some.injEq, Fact.received.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
  rename_i hc
  exact ⟨rfl, rfl, _, _, _, _, _, rfl, hc⟩

/-- **A receipt is of a saturated message.** A Valid receipt of m in c
under kid cites only m, a Valid message of c sealed under kid that
claims the counter cap or more. -/
theorem received_of_message {clump : Option Id} {x c kid m : Id} {k : Nat} (h : V C ops x (.received c kid m k clump)) :
    ∃ o u d sealed n tm, ops x = some o ∧ o.reqs = [m] ∧ countCap ≤ n ∧
      V C ops m (.message c u d kid sealed n tm clump) := by
  obtain ⟨o, b, fs, hx, _, hr, hv⟩ := valid_inv h
  obtain ⟨rfl, hm, u, d, sealed, n, tm, rfl, hn⟩ := check_received hv
  have h1 : ∃ y, o.reqs = [y] ∧ V C ops y (.message c u d kid sealed n tm clump) := by
    generalize o.reqs = l at hr
    cases hr with | cons hy hrest => cases hrest; exact ⟨_, rfl, hy⟩
  obtain ⟨y, hreq, hy⟩ := h1
  rw [hreq] at hm; simp at hm; subst hm
  exact ⟨o, u, d, sealed, n, tm, hx, hreq, hn, hy⟩

/-- **A chunk is its attachment's.** A Valid chunk cites an attachment
of its community whose root and length are the chunk's, and that
attachment cites its message: so a message's dependents reach every
chunk of its attachments. -/
theorem chunk_of_attachment {x c att root : Id} {len i : Nat}
    (h : V C ops x (.chunk c att root len i)) :
    ∃ o m u k s, ops x = some o ∧ o.reqs = [c, att] ∧ V C ops att (.attachment c m u root len k s) := by
  obtain ⟨o, b, fs, hx, _, hr, hv⟩ := valid_inv h
  obtain ⟨_, _, _, hhead, hatt, _, d, e, m, u, k, s, rfl⟩ := check_chunk hv
  obtain ⟨r0, r1, rest, hreq, _, hav, hrest⟩ := all2_cons2 hr
  cases hrest
  rw [hreq] at hhead hatt; simp at hhead hatt; subst hhead; subst hatt
  exact ⟨o, m, u, k, s, hx, hreq, hav⟩

/-- **A chunk hangs off its message.** A Valid chunk of an attachment of
message m cites the attachment, which cites m. -/
theorem chunk_hangs_off {x c att root m u : Id} {len i : Nat} {k s : ByteArray}
    (h : V C ops x (.chunk c att root len i)) (ha : V C ops att (.attachment c m u root len k s)) :
    ∃ o oa, ops x = some o ∧ att ∈ o.reqs ∧ ops att = some oa ∧ m = oa.reqs.getD 2 .empty := by
  obtain ⟨o, _, _, _, _, hx, hreq, _⟩ := chunk_of_attachment h
  obtain ⟨oa, b, fs, hxa, _, _, hva⟩ := valid_inv ha
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hm, _⟩ := check_attach hva
  exact ⟨o, oa, hx, by rw [hreq]; simp, hxa, hm⟩

/-- Chunk i of file ct, of attachment att in community c: the one op it
can be. -/
def fileChunk (c att : Id) (ct : ByteArray) (i : Nat) : Op :=
  let b := Body.chunk (Merkle.fileRoot sha256 ct) ct.size i ((Merkle.slices ct).getD i .empty)
    (Merkle.proof sha256 ct i)
  Op.make b.tag [c, att] (encode b)

/-- **A Valid chunk under a file's root is that file's chunk op** for
its attachment: the slice and siblings are the file's
(`chunk_is_slice`), the op cites c and the attachment, and its type is
its body's (`op_of_valid`). -/
theorem chunk_id (hk : Keyed ops) (hsize : ∀ x, (sha256 x).size = 32) {ct : ByteArray}
    (hspr : Merkle.NoSecondPreimage sha256 (Merkle.treeInputs sha256 ct)) {c att z : Id} {l i : Nat}
    (hz : V C ops z (.chunk c att (Merkle.fileRoot sha256 ct) l i)) : z = (fileChunk c att ct i).id := by
  obtain ⟨o, b, hzo, hmk, hb⟩ := op_of_valid hz
  obtain ⟨o', b', fs, hzo', hb', hr, hc⟩ := valid_inv hz
  rw [hzo] at hzo'; cases hzo'
  rw [hb] at hb'; cases hb'
  obtain ⟨slice, rfl, rfl, hs⟩ := chunk_is_slice hsize hspr hc
  obtain ⟨o2, _, _, _, _, hzo2, hreqs, _⟩ := chunk_of_attachment hz
  rw [hzo] at hzo2; cases hzo2
  have hsl : (Merkle.slices ct).getD i .empty = slice := by simp [List.getD, hs]
  rw [← hk z o hzo, hmk, hreqs]; unfold fileChunk; rw [hsl]

/-- **An attachment's chunk at an index is one op**, so no chunk is
counted twice; and two attachments never share a chunk op, since each
cites its own. -/
theorem chunk_unique (hk : Keyed ops) (hsize : ∀ x, (sha256 x).size = 32) {ct : ByteArray}
    (hspr : Merkle.NoSecondPreimage sha256 (Merkle.treeInputs sha256 ct)) {c att x y : Id} {l l' i : Nat}
    (hx : V C ops x (.chunk c att (Merkle.fileRoot sha256 ct) l i))
    (hy : V C ops y (.chunk c att (Merkle.fileRoot sha256 ct) l' i)) : x = y := by
  rw [chunk_id hk hsize hspr hx, chunk_id hk hsize hspr hy]

theorem chunk_own {x c att att' root root' : Id} {len len' i i' : Nat}
    (hx : V C ops x (.chunk c att root len i)) (hy : V C ops x (.chunk c att' root' len' i')) :
    att = att' := by
  have := spec_det hx hy
  simp only [Verdict.valid.injEq, Fact.chunk.injEq] at this
  exact this.2.1

/-! ## Shared ops never read local state

A shared op's validator reads only shared facts: never a secret, an
acceptance, a pending join or a content key. So a verdict never depends
on a key or on any plaintext, and every node holding the same shared ops
judges them alike, whatever keys it holds. -/

theorem prevMax_shared {c : Id} : ∀ {fs : List Fact} {m}, prevMax c fs = some m →
    ∀ g ∈ fs, g.isLocal = false
  | [], _, _, g, hg => by cases hg
  | .named .. :: rest, m, h, g, hg => by
    simp only [prevMax] at h
    split at h
    · obtain ⟨k, hk, _⟩ := Option.map_eq_some_iff.1 h
      rcases List.mem_cons.1 hg with rfl | hg
      · rfl
      · exact prevMax_shared hk g hg
    · cases h
  | .admission .. :: _, _, h, _, _ | .invitation .. :: _, _, h, _, _ | .admin .. :: _, _, h, _, _
  | .removal .. :: _, _, h, _, _ | .message .. :: _, _, h, _, _ | .wrap .. :: _, _, h, _, _
  | .profile .. :: _, _, h, _, _ | .react .. :: _, _, h, _, _ | .request .. :: _, _, h, _, _
  | .attachment .. :: _, _, h, _, _ | .chunk .. :: _, _, h, _, _ | .secret .. :: _, _, h, _, _ | .accepted .. :: _, _, h, _, _
  | .joining .. :: _, _, h, _, _ | .approval .. :: _, _, h, _, _ | .abandoned .. :: _, _, h, _, _
  | .key .. :: _, _, h, _, _ => by simp [prevMax] at h

theorem isAdmin_shared {c u : Id} {g : Fact} (h : isAdmin c u g = true) : g.isLocal = false := by
  cases g <;> simp_all [isAdmin, Fact.isLocal]

theorem counterOk_shared {c : Id} {n : Nat} {fs : List Fact} (h : counterOk c n fs = true) :
    ∀ g ∈ fs, g.isLocal = false := by
  unfold counterOk at h
  split at h
  · rename_i m hm; exact prevMax_shared hm
  · cases h

/-- **A shared op's validator reads only shared facts.** -/
theorem check_reads_shared {C : Crypto} {o : Op} {b : Body} {fs : List Fact} {f : Fact}
    (h : check C o b fs = some f) (hb : b.isLocal = false) : ∀ g ∈ fs, g.isLocal = false := by
  unfold check at h
  split at h <;> (try split at h) <;> (try simp at h; done) <;> (try (simp [Body.isLocal] at hb); done)
  all_goals
    rename_i hc
    try simp only [List.forall_mem_cons]
    repeat' constructor
  all_goals first
    | rfl
    | (intro x hx; exact absurd hx List.not_mem_nil)
    | exact isAdmin_shared hc.1
    | exact isAdmin_shared hc.2
    | exact isAdmin_shared hc.2.1
    | exact isAdmin_shared hc.2.2.1
    | exact isAdmin_shared hc.2.2.2.1
    | exact isAdmin_shared hc.2.2.2.2.1
    | exact isAdmin_shared hc.2.2.2.2.2.1
    | exact isAdmin_shared hc.2.2.2.2.2.2.1
    | exact isAdmin_shared hc.2.2.2.2.2.2.2.1
    | exact isAdmin_shared hc.2.2
    | exact isAdmin_shared hc.2.2.2
    | exact isAdmin_shared hc.2.2.2.2
    | exact isAdmin_shared hc.2.2.2.2.2
    | exact isAdmin_shared hc.2.2.2.2.2.2
    | exact isAdmin_shared hc.2.2.2.2.2.2.2
    | exact isAdmin_shared hc.2.2.2.2.2.2.2.2
    | exact counterOk_shared hc.1
    | exact counterOk_shared hc.2
    | exact counterOk_shared hc.2.1
    | exact counterOk_shared hc.2.2.1
    | exact counterOk_shared hc.2.2.2.1
    | exact counterOk_shared hc.2.2.2.2.1
    | exact counterOk_shared hc.2.2.2.2.2.1
    | exact counterOk_shared hc.2.2.2.2.2.2.1
    | exact counterOk_shared hc.2.2.2.2.2.2.2.1
    | exact counterOk_shared hc.2.2
    | exact counterOk_shared hc.2.2.2
    | exact counterOk_shared hc.2.2.2.2
    | exact counterOk_shared hc.2.2.2.2.2
    | exact counterOk_shared hc.2.2.2.2.2.2
    | exact counterOk_shared hc.2.2.2.2.2.2.2
    | exact counterOk_shared hc.2.2.2.2.2.2.2.2
    | (rcases hc.1 with ⟨_, hh⟩ | hh <;> first | exact hh | exact isAdmin_shared hh)
    | (rcases hc.2 with ⟨_, hh⟩ | hh <;> first | exact hh | exact isAdmin_shared hh)
    | (rcases hc.2.1 with ⟨_, hh⟩ | hh <;> first | exact hh | exact isAdmin_shared hh)
    | (rcases hc.2.2.1 with ⟨_, hh⟩ | hh <;> first | exact hh | exact isAdmin_shared hh)
    | (rcases hc.2.2.2.1 with ⟨_, hh⟩ | hh <;> first | exact hh | exact isAdmin_shared hh)
    | (rcases hc.2.2.2.2.1 with ⟨_, hh⟩ | hh <;> first | exact hh | exact isAdmin_shared hh)
    | (rcases hc.2.2.2.2.2.1 with ⟨_, hh⟩ | hh <;> first | exact hh | exact isAdmin_shared hh)
    | (rcases hc.2.2.2.2.2.2.1 with ⟨_, hh⟩ | hh <;> first | exact hh | exact isAdmin_shared hh)
    | (rcases hc.2.2.2.2.2.2.2.1 with ⟨_, hh⟩ | hh <;> first | exact hh | exact isAdmin_shared hh)
    | (rcases hc.2.2 with ⟨_, hh⟩ | hh <;> first | exact hh | exact isAdmin_shared hh)
    | (rcases hc.2.2.2 with ⟨_, hh⟩ | hh <;> first | exact hh | exact isAdmin_shared hh)
    | (rcases hc.2.2.2.2 with ⟨_, hh⟩ | hh <;> first | exact hh | exact isAdmin_shared hh)
    | (rcases hc.2.2.2.2.2 with ⟨_, hh⟩ | hh <;> first | exact hh | exact isAdmin_shared hh)
    | (rcases hc.2.2.2.2.2.2 with ⟨_, hh⟩ | hh <;> first | exact hh | exact isAdmin_shared hh)
    | (rcases hc.2.2.2.2.2.2.2 with ⟨_, hh⟩ | hh <;> first | exact hh | exact isAdmin_shared hh)
    | (rcases hc.2.2.2.2.2.2.2.2 with ⟨_, hh⟩ | hh <;> first | exact hh | exact isAdmin_shared hh)

/-! ## Sealed bodies -/

/-- **A sealed body opens with its key.** -/
theorem openSealed_seal {S : Seal} (G : S.Good) {c kid k n text : ByteArray}
    (hk : k.size = 32) (hn : n.size = 24) (ht : text.size < Seal.maxPlaintextSize)
    (ha : (bodyAd c kid).size < Seal.maxAssociatedDataSize) :
    openSealed S c kid (n ++ sealBody S k n c kid text) k = some text := by
  have hs : ¬ (n ++ sealBody S k n c kid text).size < 24 := by rw [ByteArray.size_append, hn]; omega
  unfold openSealed
  simp only [hs, ↓reduceIte]
  rw [ByteArray.extract_append_eq_left hn.symm,
    ByteArray.extract_append_eq_right hn.symm (by rw [ByteArray.size_append, hn])]
  exact openBody_sealBody G _ _ _ _ _ hk hn ht ha

/-- **An admitted device opens every body sealed under a key wrapped to
it.** A key wrapped to the device's X25519 key unwraps with its secret,
and that key opens what was sealed under it. -/
theorem member_opens {S : Seal} (G : S.Good) (rsk esk k n c text : ByteArray)
    (hr : rsk.size = 32) (he : esk.size = 32) (hk : k.size = 32) (hn : n.size = 24)
    (ht : text.size < Seal.maxPlaintextSize)
    (ha : (bodyAd c (kidOf S k)).size < Seal.maxAssociatedDataSize) :
    let kid := kidOf S k
    ((unbox S rsk kid (box S esk (S.pub rsk) kid k)).bind fun k' =>
      openSealed S c kid (n ++ sealBody S k n c kid text) k') = some text := by
  have hkb : k.size < Seal.maxPlaintextSize := by simp [hk, Seal.maxPlaintextSize]
  have hki : (kidOf S k).size < Seal.maxAssociatedDataSize := by
    simp only [kidOf, G.hash_size, Seal.maxAssociatedDataSize]; decide
  simp only [unbox_box G _ _ _ _ hr he hkb hki, Option.bind_some, openSealed_seal G hk hn ht ha]
end Community
