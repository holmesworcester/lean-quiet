import app.community.Family
import app.community.member.invite.Commands
import app.community.member.invite.request.Proofs
import app.community.member.invite.request.approve.Proofs

namespace Community
open Engine Codec

theorem check_invitation {C : Crypto} {o : Op} {b : Body} {fs : List Fact} {c issuer : Id}
    {k : Key} {l : Bool} (h : check C o b fs = some (.invitation c issuer k l)) :
    ∃ s d0 e0 k0 d e ka, b = .invite k l s ∧ fs = [.admission c c d0 e0 k0, .admission c issuer d e ka] ∧
      o.reqs.head? = some c ∧ C.verify d (signed o b) s = true := by
  unfold check at h
  split at h <;> (try (simp at h; done))
  rename_i b r a
  rcases b with ⟨k', l', s⟩; rcases r with ⟨c0, u0, d0, e0, k0⟩; rcases a with ⟨c', u, d, e, ka⟩
  simp only [Invitation.check] at h
  split at h
  · rename_i hc
    simp only [Option.map_some, Option.some.injEq, Fact.ofInvitation.injEq, Invitation.Fact.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    obtain ⟨h1, rfl, rfl, h5⟩ := hc
    exact ⟨_, _, _, _, _, _, _, rfl, rfl, h1, h5⟩
  · simp at h
open Engine Codec
variable {C : Crypto} {ops : Id → Option Op}

/-- Every invitation was signed by a device admitted into its issuer. -/
theorem invitation_issued {i c issuer : Id} {k : Key} {l : Bool}
    (h : V C ops i (.invitation c issuer k l)) :
    ∃ o b s z d e k, ops i = some o ∧ (decode o.body : Option Body) = some b ∧
      V C ops z (.admission c issuer d e k) ∧ C.verify d (signed o b) s = true := by
  obtain ⟨o, b, fs, hx, hb, hr, hv⟩ := valid_inv h
  obtain ⟨s, d0, e0, k0, d, e, k, rfl, rfl, _, hs⟩ := check_invitation hv
  obtain ⟨_, z, _, _, hz⟩ := all2_two hr
  exact ⟨o, _, s, z, d, e, k, hx, hb, hz, hs⟩

/-- **Nobody is admitted without a member's approval.** Every admission
is the founder's (the root itself), or its admit cites exactly a Valid
request for that very device and one Valid approval of it. The approval
was signed by a device admitted into the approving user, other than the
requesting device, and for a device link the approving user is the
request's own. The bearer key alone admits nobody. -/
theorem admission_needs_approval (hk : Keyed ops) {y c u : Id} {d e kid : Key}
    (h : V C ops y (.admission c u d e kid)) :
    (y = c ∧ u = c) ∨
    ∃ o r x l ea ka ra, ∃ g : Approve.Fact, ops y = some o ∧ o.reqs = [c, r, x] ∧
      V C ops r (.request c u d e l) ∧ V C ops x (.ofApproval g) ∧ g.c = c ∧ g.req = r ∧
      V C ops ra (.admission c g.u g.dev ea ka) ∧ g.dev ≠ d ∧ (l = true → g.u = u) := by
  rcases admission_approved hk h with h | ⟨o, r, x, l, g, hy, _, hreq, hr, hx, hgc, hgr, hgu, hgd, hge⟩
  · exact Or.inl h
  · obtain ⟨_, _, ra, _, l', ea, ka, _, _, _, hr', hra, hl, hd, _⟩ := approval_signed hx
    rw [hgc, hgr, hgu, hgd, hge] at hr'
    have := spec_det hr hr'
    simp only [Verdict.valid.injEq, Fact.ofRequest.injEq, Request.Fact.mk.injEq] at this
    obtain ⟨_, _, _, _, rfl⟩ := this
    rw [hgc] at hra
    exact Or.inr ⟨o, r, x, l, ea, ka, ra, g, hy, hreq, hr, hx, hgc, hgr, hra, hgd ▸ hd, hgu ▸ hl⟩
/-- **Only the issuer's user approves a device link's request**
(`link_approved_by_issuer`). A Valid approval by user a of a Valid
request that redeems a device link is by the request's own user, which
is the issuer of the device link it redeems: a Valid invitation of c,
with `link`, issued by a. The approval was signed by a device admitted
into a, not the requesting one. -/
theorem link_approved_by_issuer (hk : Keyed ops) {x r c a u : Id} {d e : Key}
    (hx : V C ops x (.approval c r a)) (hr : V C ops r (.request c u d e true)) :
    a = u ∧ (∃ o i k, ops r = some o ∧ o.reqs = [c, i] ∧ V C ops i (.invitation c a k true)) ∧
      ∃ ra da ea, V C ops ra (.admission c a da ea) ∧ da ≠ d := by
  obtain ⟨_, _, ra, u', d', e', l', da, ea, _, _, _, hr', hra, hl, hd, _⟩ := approval_signed hx
  have := spec_det hr hr'
  simp only [Verdict.valid.injEq, Fact.request.injEq] at this
  obtain ⟨_, rfl, rfl, rfl, rfl⟩ := this
  have hau := hl rfl
  subst hau
  obtain ⟨o, _, i, issuer, k, _, _, ho, _, hreq, hi, hu, _, _⟩ := request_invited hk hr
  rw [if_pos rfl] at hu
  subst hu
  exact ⟨rfl, ⟨o, i, k, ho, hreq, hi⟩, ra, da, ea, hra, hd⟩

/-- **A linked device joins its issuer's user** (`link_admits_issuer`).
Every admission is the founder's, or cites a Valid request and one Valid
approval of it (`admission_needs_approval`); when that request redeems a
device link, the admission is into the link's issuer, and the approval
is that same user's, signed by another of its devices. -/
theorem link_admits_issuer (hk : Keyed ops) {y c u : Id} {d e : Key}
    (h : V C ops y (.admission c u d e)) :
    (y = c ∧ u = c) ∨
    ∃ o r x l, ops y = some o ∧ o.reqs = [c, r, x] ∧ V C ops r (.request c u d e l) ∧
      (l = true → (∃ or i k, ops r = some or ∧ or.reqs = [c, i] ∧ V C ops i (.invitation c u k true)) ∧
        V C ops x (.approval c r u) ∧ ∃ ra da ea, V C ops ra (.admission c u da ea) ∧ da ≠ d) := by
  rcases admission_needs_approval hk h with h | ⟨o, r, x, a, l, _, _, _, hy, hreq, hr, hx, _, _, _⟩
  · exact Or.inl h
  · refine Or.inr ⟨o, r, x, l, hy, hreq, hr, fun hl => ?_⟩
    subst hl
    obtain ⟨rfl, hi, ra', da', ea', hra', hd'⟩ := link_approved_by_issuer hk hx hr
    exact ⟨hi, hx, ra', da', ea', hra', hd'⟩

/-- **A device link is a link of its own kind, and carries no secret but
its invitation's bearer seed** (`issue_link`). What `issue` writes for a
device link is an invitation with `link`, whose bearer key is the seed's;
the link names that invitation, says it is a device link, and holds the
seed as its only secret. The seed signs a request; it approves nothing
(`link_approved_by_issuer`: only a device admitted into the issuer's user
does). -/
theorem issue_link (c issuerAdm : Id) (by_ : Device) (key secret : ByteArray)
    (hints : List ByteArray) (link : Bool) :
    let w := issue c issuerAdm by_ key secret hints link
    (∃ s, w.1 = mkOp [c, issuerAdm] (.invite (Device.ofSeed secret).pk link s)) ∧
      w.2 = ⟨c, w.1.id, key, hints, secret, link⟩ ∧ w.2.bearer.pk = (Device.ofSeed secret).pk :=
  ⟨⟨_, rfl⟩, rfl, rfl⟩

/-! ### Negative controls: the two clauses the link laws rest on, dropped -/

/-- `Approve.check` without its link clause (`l = true → a = u`): any
member may approve a device link's request. A negative control: never
run. -/
def Approve.checkAnyUser (C : Crypto) (o : Op) :
    Approve.Body → Root.Fact → Request.Fact → Root.Fact → Option Approve.Fact
  | ⟨s⟩, ⟨c, u0, _, _⟩, ⟨c1, _, d, _, _⟩, ⟨c2, a, da, _⟩ =>
    if o.reqs.head? = some c ∧ u0 = c ∧ c1 = c ∧ c2 = c ∧ da ≠ d ∧
      C.verify da (signedBy o (Approve.Body.unsigned ⟨s⟩)) s
    then some ⟨c, o.reqs.getD 1 .empty, a⟩ else none

/-- **Without the link clause, another user approves a device link**
(`anyUser_approves_link`): where the mutant takes user a's signed yes to
user u's device link request, the running check refuses it. So
`link_approved_by_issuer` rests on that clause. -/
theorem anyUser_approves_link (C : Crypto) (o : Op) (s : ByteArray) {c a u : Id} {d e d0 e0 da ea : Key}
    (hc : o.reqs.head? = some c) (hau : a ≠ u) (hd : da ≠ d)
    (hv : C.verify da (signed o (.approve s)) s = true) :
    Approve.checkAnyUser C o ⟨s⟩ ⟨c, c, d0, e0⟩ ⟨c, u, d, e, true⟩ ⟨c, a, da, ea⟩ =
      some ⟨c, o.reqs.getD 1 .empty, a⟩ ∧
    Approve.check C o ⟨s⟩ ⟨c, c, d0, e0⟩ ⟨c, u, d, e, true⟩ ⟨c, a, da, ea⟩ = none := by
  simp [Approve.checkAnyUser, Approve.check, hc, hau, hd, hv]

/-- `Request.check` naming a new user for every request, a device link's
too. A negative control: never run. -/
def Request.checkNewUser (C : Crypto) (o : Op) :
    Request.Body → Root.Fact → Invitation.Fact → Option Request.Fact
  | ⟨d, e, cs, bs⟩, ⟨c, u0, _, _⟩, ⟨c', _, k, l⟩ =>
    if o.reqs.head? = some c ∧ u0 = c ∧ c' = c ∧ C.verify d (signedBy o (Request.Body.unsigned ⟨d, e, cs, bs⟩)) cs ∧
      C.verify k (signedBy o (Request.Body.unsigned ⟨d, e, cs, bs⟩)) bs
    then some ⟨c, o.id, d, e, l⟩ else none

/-- **Without it, a linked device would be a new user** (`newUser_links`):
on the same device link, the running check names the issuer's user and
the mutant the request's own new one. So `link_admits_issuer` rests on
`Request.check`'s `if l then issuer`. -/
theorem newUser_links (C : Crypto) (o : Op) {d e cs bs : ByteArray} {c issuer : Id} {d0 e0 k : Key}
    (hc : o.reqs.head? = some c) (hi : issuer ≠ o.id)
    (hd : C.verify d (signed o (.request d e cs bs)) cs = true)
    (hk : C.verify k (signed o (.request d e cs bs)) bs = true) :
    Request.check C o ⟨d, e, cs, bs⟩ ⟨c, c, d0, e0⟩ ⟨c, issuer, k, true⟩ = some ⟨c, issuer, d, e, true⟩ ∧
    Request.checkNewUser C o ⟨d, e, cs, bs⟩ ⟨c, c, d0, e0⟩ ⟨c, issuer, k, true⟩ = some ⟨c, o.id, d, e, true⟩ ∧
    issuer ≠ o.id := by
  simp [Request.check, Request.checkNewUser, hc, hd, hk, hi]

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
open Engine Codec

theorem web_not_ws : ∀ c ∈ web, c.isWhitespace = false := by decide

theorem scheme_not_ws : ∀ c ∈ scheme, c.isWhitespace = false := by decide

theorem webLink_not_ws : ∀ c ∈ webLink, c.isWhitespace = false := by decide

theorem schemeLink_not_ws : ∀ c ∈ schemeLink, c.isWhitespace = false := by decide

theorem isPrefixOf_self_append (l x : List Char) : l.isPrefixOf (l ++ x) = true := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [List.isPrefixOf, ih]

/-- Whether l begins m ++ x is whether it begins m, when m is no shorter. -/
theorem isPrefixOf_append_long : ∀ (l m x : List Char), l.length ≤ m.length →
    l.isPrefixOf (m ++ x) = l.isPrefixOf m
  | [], _, _, _ => rfl
  | _ :: _, [], _, h => absurd h (by simp)
  | a :: l, b :: m, x, h => by
    simp only [List.cons_append, List.isPrefixOf]
    rw [isPrefixOf_append_long l m x (by simpa using h)]

/-! The four prefixes differ (the pages from the schemes in their first
character, a member's from a device link's in the word after the
site), so no one is read as another. -/

theorem web_not_prefix_scheme (x : List Char) : web.isPrefixOf (scheme ++ x) = false := by
  rw [show web = 'h' :: web.tail by decide, show scheme = 'l' :: scheme.tail by decide]
  rfl

theorem web_not_prefix_webLink (x : List Char) : web.isPrefixOf (webLink ++ x) = false := by
  rw [isPrefixOf_append_long _ _ _ (by decide)]; decide

theorem web_not_prefix_schemeLink (x : List Char) : web.isPrefixOf (schemeLink ++ x) = false := by
  rw [show web = 'h' :: web.tail by decide, show schemeLink = 'l' :: schemeLink.tail by decide]
  rfl

theorem scheme_not_prefix_webLink (x : List Char) : scheme.isPrefixOf (webLink ++ x) = false := by
  rw [show scheme = 'l' :: scheme.tail by decide, show webLink = 'h' :: webLink.tail by decide]
  rfl

theorem scheme_not_prefix_schemeLink (x : List Char) : scheme.isPrefixOf (schemeLink ++ x) = false := by
  rw [isPrefixOf_append_long _ _ _ (by decide)]; decide

theorem webLink_not_prefix_schemeLink (x : List Char) : webLink.isPrefixOf (schemeLink ++ x) = false := by
  rw [show webLink = 'h' :: webLink.tail by decide, show schemeLink = 'l' :: schemeLink.tail by decide]
  rfl

theorem unprefix_web (x : List Char) : unprefix (web ++ x) = (some false, x) := by
  simp [unprefix, isPrefixOf_self_append]

theorem unprefix_scheme (x : List Char) : unprefix (scheme ++ x) = (some false, x) := by
  simp [unprefix, web_not_prefix_scheme, isPrefixOf_self_append]

theorem unprefix_webLink (x : List Char) : unprefix (webLink ++ x) = (some true, x) := by
  simp [unprefix, web_not_prefix_webLink, scheme_not_prefix_webLink, isPrefixOf_self_append]

theorem unprefix_schemeLink (x : List Char) : unprefix (schemeLink ++ x) = (some true, x) := by
  simp [unprefix, web_not_prefix_schemeLink, scheme_not_prefix_schemeLink,
    webLink_not_prefix_schemeLink, isPrefixOf_self_append]

theorem kindOf_two (l : Bool) : (kindOf l == 2) = l := by cases l <;> rfl

/-- The fields behind a prefix with no whitespace that `unprefix` drops,
naming kind `pre`: what parse makes of them. -/
theorem parse_code_eq {i : Invite} (p : List Char) {pre : Option Bool}
    (hp : ∀ c ∈ p, c.isWhitespace = false) (hu : unprefix (p ++ i.code) = (pre, i.code)) :
    Invite.parse (String.ofList (p ++ i.code)) =
      if (pre = none ∨ pre = some i.link) ∧ i.Valid then some i else none := by
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
  simp only [kindOf_two, true_and]

/-- A prefix with no whitespace that `unprefix` drops, of the link's own
kind or none: the fields behind it parse back to the invite. -/
theorem parse_code {i : Invite} (hv : i.Valid) (p : List Char) {pre : Option Bool}
    (hp : ∀ c ∈ p, c.isWhitespace = false) (hu : unprefix (p ++ i.code) = (pre, i.code))
    (hpre : pre = none ∨ pre = some i.link) :
    Invite.parse (String.ofList (p ++ i.code)) = some i := by
  rw [parse_code_eq p hp hu, if_pos ⟨hpre, hv⟩]

/-- **A valid invite's text (its page's link) parses back to it.** -/
theorem parse_text {i : Invite} (hv : i.Valid) : Invite.parse i.text = some i := by
  unfold Invite.text
  cases h : i.link
  · exact parse_code hv web web_not_ws (unprefix_web _) (Or.inr (by rw [h]))
  · exact parse_code hv webLink webLink_not_ws (unprefix_webLink _) (Or.inr (by rw [h]))

/-- **The URI its page opens parses back to the same invite.** -/
theorem parse_uri {i : Invite} (hv : i.Valid) : Invite.parse i.uri = some i := by
  unfold Invite.uri
  cases h : i.link
  · exact parse_code hv scheme scheme_not_ws (unprefix_scheme _) (Or.inr (by rw [h]))
  · exact parse_code hv schemeLink schemeLink_not_ws (unprefix_schemeLink _) (Or.inr (by rw [h]))

/-- **A link behind the other kind's page or scheme is refused** (the
scheme must match the offer, as libquiet's): a device link's code under
`join` reads as no invite, and a member's under `link`. -/
theorem parse_other_kind (i : Invite) :
    Invite.parse (String.ofList ((if i.link then web else webLink) ++ i.code)) = none ∧
    Invite.parse (String.ofList ((if i.link then scheme else schemeLink) ++ i.code)) = none := by
  cases h : i.link
  · constructor
    · rw [if_neg (by simp), parse_code_eq webLink webLink_not_ws (unprefix_webLink _), h]; simp
    · rw [if_neg (by simp), parse_code_eq schemeLink schemeLink_not_ws (unprefix_schemeLink _), h]; simp
  · constructor
    · rw [if_pos rfl, parse_code_eq web web_not_ws (unprefix_web _), h]; simp
    · rw [if_pos rfl, parse_code_eq scheme scheme_not_ws (unprefix_scheme _), h]; simp

/-- **Whatever parses is valid.** -/
theorem parse_valid {s : String} {i : Invite} (h : Invite.parse s = some i) : i.Valid := by
  unfold Invite.parse at h
  simp only at h
  split at h
  · cases h
  · split at h
    · split at h
      · rename_i hv; cases h; exact hv.2.2
      · cases h
    · cases h

end Community
