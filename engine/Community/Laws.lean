/-
Laws of community state, over the Valid facts of any set of ops (what
a node holds at rest: Engine.status_iff_spec). Signatures are read
through `Crypto.verify`; where a law needs unforgeability it takes it
as the hypothesis `Unforgeable`.
-/
import Community.Facts

namespace Community
open Engine Codec

/-! ## Inverting the validators -/

theorem check_admission {C : Crypto} {o : Op} {b : Body} {fs : List Fact} {c u : Id} {d e : Key}
    (h : check C o b fs = some (.admission c u d e)) :
    (∃ s, b = .root d e s ∧ fs = [] ∧ c = o.id ∧ u = o.id ∧ C.verify d (signed o b) s = true) ∨
    (∃ cs bs d0 e0 issuer k l, b = .join d e cs bs ∧
      fs = [.admission c c d0 e0, .invitation c issuer k l] ∧ o.reqs.head? = some c ∧
      u = (if l then issuer else o.id) ∧
      C.verify d (signed o b) cs = true ∧ C.verify k (signed o b) bs = true) := by
  unfold check at h
  split at h <;> (try split at h) <;> (try simp at h; done)
  · simp only [Option.some.injEq, Fact.admission.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    exact Or.inl ⟨_, rfl, rfl, rfl, rfl, by assumption⟩
  · simp only [Option.some.injEq, Fact.admission.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    rename_i hc
    obtain ⟨h1, rfl, rfl, h4, h5⟩ := hc
    exact Or.inr ⟨_, _, _, _, _, _, _, rfl, rfl, h1, rfl, h4, h5⟩

theorem check_invitation {C : Crypto} {o : Op} {b : Body} {fs : List Fact} {c issuer : Id}
    {k : Key} {l : Bool} (h : check C o b fs = some (.invitation c issuer k l)) :
    ∃ s d0 e0 d e, b = .invite k l s ∧ fs = [.admission c c d0 e0, .admission c issuer d e] ∧
      o.reqs.head? = some c ∧ C.verify d (signed o b) s = true := by
  unfold check at h
  split at h <;> (try split at h) <;> (try simp at h; done)
  simp only [Option.some.injEq, Fact.invitation.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  rename_i hc
  obtain ⟨h1, rfl, rfl, h4⟩ := hc
  exact ⟨_, _, _, _, _, rfl, rfl, h1, h4⟩

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
      o.reqs.head? = some c ∧ (t = u ∨ isAdmin c u auth = true) ∧
      C.verify d (signed o b) s = true := by
  unfold check at h
  split at h <;> (try split at h) <;> (try simp at h; done)
  simp only [Option.some.injEq, Fact.removal.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rename_i hc
  obtain ⟨h1, rfl, rfl, rfl, h5, h6⟩ := hc
  exact ⟨_, _, _, _, _, _, _, _, rfl, rfl, h1, h5, h6⟩

theorem check_message {C : Crypto} {o : Op} {b : Body} {fs : List Fact} {c u : Id}
    {d k t : ByteArray} {tm : Nat} {atts : List Id}
    (h : check C o b fs = some (.message c u d k t tm atts)) :
    ∃ s d0 e0 e rest, b = .post k t tm s ∧ fs = .admission c c d0 e0 :: .admission c u d e :: rest ∧
      o.reqs.head? = some c ∧ atts = o.reqs.drop 2 ∧ blobsOf c rest = true ∧
      C.verify d (signed o b) s = true := by
  unfold check at h
  split at h <;> (try split at h) <;> (try simp at h; done)
  simp only [Option.some.injEq, Fact.message.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
  rename_i hc
  obtain ⟨h1, rfl, rfl, h4, h5⟩ := hc
  exact ⟨_, _, _, _, _, rfl, rfl, h1, rfl, h4, h5⟩

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

end

variable {C : Crypto} {ops : Id → Option Op}

theorem valid_inv {x : Id} {f : Fact} (h : V C ops x f) :
    ∃ o b fs, ops x = some o ∧ (decode o.body : Option Body) = some b ∧
      All2 (fun r g => V C ops r g) o.reqs fs ∧ check C o b fs = some f := by
  obtain ⟨o, fs, hx, hr, hv⟩ := spec_valid_inv h
  unfold family validate at hv; simp only at hv
  cases hb : (decode o.body : Option Body) with
  | none => rw [hb] at hv; simp at hv
  | some b => rw [hb] at hv; exact ⟨o, b, fs, hx, hb, hr, hv⟩

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
author's user, and that device signed it; what it attaches are the
requirements after those two. -/
theorem message_authorized {x c u : Id} {d k t : ByteArray} {tm : Nat} {atts : List Id}
    (h : V C ops x (.message c u d k t tm atts)) :
    ∃ o s e y, ops x = some o ∧ (decode o.body : Option Body) = some (.post k t tm s) ∧
      o.reqs = c :: y :: atts ∧ V C ops y (.admission c u d e) ∧
      C.verify d (signed o (.post k t tm s)) s = true := by
  obtain ⟨o, b, fs, hx, hb, hr, hv⟩ := valid_inv h
  obtain ⟨s, d0, e0, e, rest, rfl, rfl, hh, ha, _, hs⟩ := check_message hv
  obtain ⟨a, y, t', hreq, _, hy, _⟩ := all2_cons2 hr
  rw [hreq] at hh ha; simp at hh; subst hh
  simp at ha; subst ha
  exact ⟨o, s, e, y, hx, hb, hreq, hy, hs⟩

/-! ## No impersonation -/

/-- What a device key has signed. -/
def Unforgeable (C : Crypto) (Signed : Key → ByteArray → Prop) : Prop :=
  ∀ pk m s, C.verify pk m s = true → Signed pk m

/-- Every admission was consented to by its device: the device signed
the op that admits it (the root, or its join). -/
theorem admission_consented {y c u : Id} {d e : Key} (h : V C ops y (.admission c u d e)) :
    ∃ o b s, ops y = some o ∧ (decode o.body : Option Body) = some b ∧
      C.verify d (signed o b) s = true := by
  obtain ⟨o, b, fs, hx, hb, _, hv⟩ := valid_inv h
  rcases check_admission hv with ⟨s, rfl, _, _, _, hs⟩ | ⟨cs, bs, _, _, _, _, _, rfl, _, _, _, hs, _⟩
  · exact ⟨o, _, s, hx, hb, hs⟩
  · exact ⟨o, _, cs, hx, hb, hs⟩

/-- **Impersonation is impossible.** If signatures are unforgeable, a
message attributed to user u and device d was signed, as this exact op,
by the holder of d's key, and that holder also signed an op admitting d
into u. Nobody can post as a user without a device the user's admission
binds and that device's key. -/
theorem no_impersonation {Signed : Key → ByteArray → Prop} (hU : Unforgeable C Signed)
    {x c u : Id} {d k t : ByteArray} {tm : Nat} {atts : List Id}
    (h : V C ops x (.message c u d k t tm atts)) :
    ∃ o s, ops x = some o ∧ (decode o.body : Option Body) = some (.post k t tm s) ∧
      Signed d (signed o (.post k t tm s)) ∧
      ∃ y e oy by_, V C ops y (.admission c u d e) ∧ ops y = some oy ∧
        (decode oy.body : Option Body) = some by_ ∧ Signed d (signed oy by_) := by
  obtain ⟨o, s, e, y, hx, hb, _, hy, hs⟩ := message_authorized h
  obtain ⟨oy, by_, s', hoy, hby, hs'⟩ := admission_consented hy
  exact ⟨o, s, hx, hb, hU _ _ _ hs, y, e, oy, by_, hy, hoy, hby, hU _ _ _ hs'⟩

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

/-- **Nobody joins uninvited.** Every admission is the founder's (by the
root itself), or redeems an invitation of c, issued by an admitted
device, and signed by the invitation's bearer key; a link invitation
adds the device to its issuer, a member invitation starts the user the
join names. -/
theorem admission_invited (hk : Keyed ops) {y c u : Id} {d e : Key}
    (h : V C ops y (.admission c u d e)) :
    (y = c ∧ u = c) ∨
    ∃ o b i issuer k l s, ops y = some o ∧ (decode o.body : Option Body) = some b ∧
      o.reqs = [c, i] ∧ V C ops i (.invitation c issuer k l) ∧
      u = (if l then issuer else y) ∧ C.verify k (signed o b) s = true := by
  obtain ⟨o, b, fs, hx, hb, hr, hv⟩ := valid_inv h
  have hid := hk y o hx
  rcases check_admission hv with ⟨s, rfl, rfl, hc, hu, _⟩ | ⟨cs, bs, d0, e0, issuer, k, l, rfl, rfl, hh, hu, _, hbs⟩
  · left; rw [hid] at hc hu; exact ⟨hc.symm, hu.trans hc.symm⟩
  · obtain ⟨a, i, hreq, _, hi⟩ := all2_two hr
    rw [hreq] at hh; simp at hh; subst hh
    rw [hid] at hu
    exact Or.inr ⟨o, _, i, issuer, k, l, bs, hx, hb, hreq, hi, hu, hbs⟩

/-- **Invited and linked devices are admitted.** A join redeeming a Valid
invitation of c, signed by the joining device and by the invitation's
bearer key, admits the device: into the issuer's user for a link
invitation, into the new user the join names for a member invitation. -/
theorem join_admits (hk : Keyed ops) {y c i : Id} {o : Op} {d e cs bs : ByteArray}
    {d0 e0 : Key} {issuer : Id} {k : Key} {l : Bool}
    (hy : ops y = some o) (hb : (decode o.body : Option Body) = some (.join d e cs bs))
    (hreq : o.reqs = [c, i]) (hc : V C ops c (.admission c c d0 e0))
    (hi : V C ops i (.invitation c issuer k l))
    (hcs : C.verify d (signed o (.join d e cs bs)) cs = true)
    (hbs : C.verify k (signed o (.join d e cs bs)) bs = true) :
    V C ops y (.admission c (if l then issuer else y) d e) := by
  have hid := hk y o hy
  refine spec_valid_of hy (fs := [.admission c c d0 e0, .invitation c issuer k l]) ?_ ?_
  · rw [hreq]; exact .cons hc (.cons hi .nil)
  · show validate C o _ = _
    unfold validate; rw [hb]
    simp [check, hreq, hcs, hbs, hid]

/-! ## Removal -/

/-- **Only admins remove others.** A Valid removal of user t by user u
is a self-removal, or u is an admin. -/
theorem removal_authorized {x c t u : Id} (h : V C ops x (.removal c t u)) :
    t = u ∨ IsAdmin C ops c u := by
  obtain ⟨o, b, fs, _, _, hr, hv⟩ := valid_inv h
  obtain ⟨_, _, _, _, _, auth, _, _, rfl, rfl, _, ha, _⟩ := check_removal hv
  obtain ⟨_, _, z, _, _, _, _, hz, _⟩ := all2_four hr
  rcases ha with ha | ha
  · exact Or.inl ha
  · exact Or.inr (isAdmin_sound hz ha)

/-- **Every admin-issued removal stands.** A removal op signed by an
admitted device of user u, citing a fact that shows u is admin and an
admission of the target t, is Valid — whoever t is (another admin
included), and whether or not u has itself been removed: nothing about
u's own removal appears in its premises. -/
theorem admin_removal_stands {x c ra au ta : Id} {o : Op} {s : ByteArray}
    {d0 e0 d e d' e' : Key} {u t : Id} {auth : Fact}
    (hx : ops x = some o) (hb : (decode o.body : Option Body) = some (.remove s))
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
    unfold validate; rw [hb]
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

end Community
