import app.community.Family
import app.community.member.invite.Commands
import app.community.member.invite.request.Proofs
import app.community.member.invite.request.approve.Proofs

/-!
`community.member.invite`: laws about the op types in this folder and below.
-/
namespace Community
open Engine Codec

theorem check_invitation {C : Crypto} {o : Op} {b : Body} {fs : List Fact} {c issuer : Id}
    {k : Key} {l : Bool} {t : Nat} (h : check C o b fs = some (.invitation c issuer k l t)) :
    ∃ s d0 e0 d e, b = .invite k l t s ∧ fs = [.admission c c d0 e0, .admission c issuer d e] ∧
      o.reqs.head? = some c ∧ 1 ≤ t ∧ (l = true → t = 1) ∧ C.verify d (signed o b) s = true := by
  unfold check at h
  split at h <;> (try (simp at h; done))
  rename_i b r a
  rcases b with ⟨k', l', t', s⟩; rcases r with ⟨c0, u0, d0, e0⟩; rcases a with ⟨c', u, d, e⟩
  simp only [Invitation.check] at h
  split at h
  · rename_i hc
    simp only [Option.map_some, Option.some.injEq, Fact.ofInvitation.injEq, Invitation.Fact.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    obtain ⟨h1, rfl, rfl, h3, h4, h5⟩ := hc
    exact ⟨_, _, _, _, _, rfl, rfl, h1, h3, h4, h5⟩
  · simp at h
end Community
namespace Community
open Engine Codec
variable {C : Crypto} {ops : Id → Option Op}

/-- Every invitation was signed by a device admitted into its issuer,
needs at least one approval, and exactly one for a link. -/
theorem invitation_issued {i c issuer : Id} {k : Key} {l : Bool} {t : Nat}
    (h : V C ops i (.invitation c issuer k l t)) :
    ∃ o b s z d e, ops i = some o ∧ (decode o.body : Option Body) = some b ∧
      V C ops z (.admission c issuer d e) ∧ C.verify d (signed o b) s = true ∧
      1 ≤ t ∧ (l = true → t = 1) := by
  obtain ⟨o, b, fs, hx, hb, hr, hv⟩ := valid_inv h
  obtain ⟨s, d0, e0, d, e, rfl, rfl, _, ht, hl, hs⟩ := check_invitation hv
  obtain ⟨_, z, _, _, hz⟩ := all2_two hr
  exact ⟨o, _, s, z, d, e, hx, hb, hz, hs, ht, hl⟩

/-- **Nobody is admitted without a member's approval.** Every admission
is the founder's (the root itself), or its admit cites a Valid approval,
signed by a device admitted into the approving user, of a Valid request
for that very device: the bearer key alone admits nobody. -/
theorem admission_needs_approval (hk : Keyed ops) {y c u : Id} {d e : Key}
    (h : V C ops y (.admission c u d e)) :
    (y = c ∧ u = c) ∨
    ∃ o r x a l t da ea ra, ops y = some o ∧ x ∈ o.reqs ∧ V C ops r (.request c u d e l t) ∧
      V C ops x (.approval c r a) ∧ V C ops ra (.admission c a da ea) := by
  rcases admission_approved hk h with h | ⟨o, r, aps, l, t, us, hy, _, hreq, hr, hap, _, hlen⟩
  · exact Or.inl h
  · obtain ⟨_, _, i, issuer, k, _, _, _, _, _, hi, _, _, _⟩ := request_invited hk hr
    obtain ⟨_, _, _, _, _, _, _, _, _, _, ht, _⟩ := invitation_issued hi
    cases hap with
    | nil => simp at hlen; omega
    | @cons x a _ _ hx _ =>
      obtain ⟨_, _, ra, _, _, _, _, _, da, ea, _, _, _, _, hra, _⟩ := approval_signed hx
      exact Or.inr ⟨o, r, x, a, l, t, da, ea, ra, hy, by rw [hreq]; simp, hr, hx, hra⟩
end Community
namespace Community
open Engine Codec
namespace Base62

theorem digitOf_charOf : ∀ d, d < 62 → digitOf (charOf d) = some d := by decide

theorem charOf_not_ws : ∀ d, d < 62 → (charOf d).isWhitespace = false := by decide

theorem ofDigits_go (n : Nat) (acc : List Nat) : ofDigits 0 (go n acc) = ofDigits n acc := by
  induction n using Nat.strongRecOn generalizing acc with
  | _ n ih =>
    rw [go]
    split
    · simp [ofDigits]
    · rename_i h
      rw [ih (n / 62) (by omega)]
      simp only [ofDigits, List.foldl_cons]
      rw [Nat.div_add_mod' n 62]

theorem go_lt (n : Nat) (acc : List Nat) (h : ∀ d ∈ acc, d < 62) : ∀ d ∈ go n acc, d < 62 := by
  induction n using Nat.strongRecOn generalizing acc with
  | _ n ih =>
    rw [go]
    split
    · rename_i hn; intro d hd
      rcases List.mem_cons.1 hd with rfl | hd
      · exact hn
      · exact h d hd
    · exact ih (n / 62) (by omega) _ fun d hd => by
        rcases List.mem_cons.1 hd with rfl | hd
        · exact Nat.mod_lt _ (by decide)
        · exact h d hd

/-- Peeling a number with bytes appended gives those bytes back. -/
theorem peel_foldl (l : List UInt8) (m : Nat) (hm : 1 ≤ m) :
    peel (l.foldl (fun n b => n * 256 + b.toNat) m) = ((peel m).1, (peel m).2 ++ l) := by
  induction l generalizing m with
  | nil => simp
  | cons b t ih =>
    rw [List.foldl_cons, ih _ (by omega)]
    have hb := b.toNat_lt
    have e : peel (m * 256 + b.toNat) = ((peel m).1, (peel m).2 ++ [b]) := by
      rw [peel, if_neg (by omega)]
      have h1 : (m * 256 + b.toNat) / 256 = m := by omega
      have h2 : (m * 256 + b.toNat) % 256 = b.toNat := by omega
      have hb' : b.toNat.toUInt8 = b := UInt8.ofNat_toNat
      simp only [h1, h2, hb']
    rw [e]; simp

theorem peel_natOf (l : List UInt8) : peel (natOf l) = (1, l) := by
  unfold natOf
  rw [peel_foldl l 1 (by decide)]
  simp [peel]

theorem bytesOf_natOf (l : List UInt8) : bytesOf (natOf l) = some l := by
  unfold bytesOf; rw [peel_natOf]; rfl

theorem mapM_digitOf (ds : List Nat) (h : ∀ d ∈ ds, d < 62) : (ds.map charOf).mapM digitOf = some ds := by
  induction ds with
  | nil => rfl
  | cons d t ih =>
    simp only [List.map_cons, List.mapM_cons, digitOf_charOf d (h d (List.mem_cons_self ..)),
      ih fun x hx => h x (List.mem_cons_of_mem _ hx)]
    rfl

theorem decode_encode (l : List UInt8) : decode (encode l) = some l := by
  have hlt : ∀ d ∈ digits (natOf l), d < 62 := go_lt _ _ (by simp)
  have hd : ofDigits 0 (digits (natOf l)) = natOf l := ofDigits_go _ _
  unfold decode encode
  rw [mapM_digitOf _ hlt]
  show bytesOf (ofDigits 0 (digits (natOf l))) = some l
  rw [hd, bytesOf_natOf]

theorem encode_not_ws (l : List UInt8) : ∀ c ∈ encode l, c.isWhitespace = false := by
  intro c hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
  exact charOf_not_ws d (go_lt _ _ (by simp) d hd)
end Base62
end Community
namespace Community
open Engine Codec

theorem web_not_ws : ∀ c ∈ web, c.isWhitespace = false := by decide

theorem scheme_not_ws : ∀ c ∈ scheme, c.isWhitespace = false := by decide

theorem isPrefixOf_self_append (l x : List Char) : l.isPrefixOf (l ++ x) = true := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [List.isPrefixOf, ih]

/-- The page and the scheme differ in their first character, so a
scheme URI is never read as the page. -/
theorem web_not_prefix_scheme (x : List Char) : web.isPrefixOf (scheme ++ x) = false := by
  rw [show web = 'h' :: web.tail by decide, show scheme = 'l' :: scheme.tail by decide]
  rfl

theorem unprefix_web (x : List Char) : unprefix (web ++ x) = x := by
  simp [unprefix, isPrefixOf_self_append]

theorem unprefix_scheme (x : List Char) : unprefix (scheme ++ x) = x := by
  simp [unprefix, web_not_prefix_scheme, isPrefixOf_self_append]

/-- A prefix with no whitespace that `unprefix` drops: the fields behind
it parse back to the invite. -/
theorem parse_code {i : Invite} (hv : i.Valid) (p : List Char)
    (hp : ∀ c ∈ p, c.isWhitespace = false) (hu : unprefix (p ++ i.code) = i.code) :
    Invite.parse (String.ofList (p ++ i.code)) = some i := by
  unfold Invite.parse
  rw [String.toList_ofList]
  have hf : (p ++ i.code).filter (fun c => !c.isWhitespace) = p ++ i.code := by
    refine List.filter_eq_self.2 fun c hc => ?_
    rcases List.mem_append.1 hc with hc | hc
    · simp [hp c hc]
    · simp [Base62.encode_not_ws _ c hc]
  simp only [hf, hu]
  unfold Invite.code
  simp only [Base62.decode_encode]
  rw [show (⟨i.bytes.data.toList.toArray⟩ : ByteArray) = i.bytes from rfl, Invite.bytes,
    Codec.decode_encode]
  simp only
  rw [if_pos (by first | exact ⟨rfl, hv⟩ | exact ⟨trivial, hv⟩ | exact hv)]

/-- **A valid invite's text (the join page link) parses back to it.** -/
theorem parse_text {i : Invite} (hv : i.Valid) : Invite.parse i.text = some i :=
  parse_code hv web web_not_ws (unprefix_web _)

/-- **The URI the join page opens parses back to the same invite.** -/
theorem parse_uri {i : Invite} (hv : i.Valid) : Invite.parse i.uri = some i :=
  parse_code hv scheme scheme_not_ws (unprefix_scheme _)

/-- **Whatever parses is valid.** -/
theorem parse_valid {s : String} {i : Invite} (h : Invite.parse s = some i) : i.Valid := by
  unfold Invite.parse at h
  simp only at h
  split at h
  · cases h
  · split at h
    · split at h
      · rename_i hv; cases h; exact hv.2
      · cases h
    · cases h

end Community
