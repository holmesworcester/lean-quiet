import engine.core.Order
import app.community.Commands
import app.community.Family
import app.community.channel.message.Commands
import app.community.channel.message.Proofs
import app.community.channel.message.attachment.chunk.Commands
import app.community.channel.message.attachment.chunk.Proofs
import app.community.channel.message.reaction.Commands
import app.community.channel.message.receipt.Commands
import app.community.channel.message.receipt.Proofs
import app.community.device.endpoint.Commands
import app.community.device.endpoint.Proofs
import app.community.device.secret.Commands
import app.community.key.Commands
import app.community.key.wrap.Commands
import app.community.key.wrap.Proofs
import app.community.member.Proofs
import app.community.member.admin.Proofs
import app.community.member.invite.request.Commands
import app.community.member.invite.request.Proofs
import app.community.member.invite.request.approve.Commands
import app.community.member.invite.request.approve.Proofs
import app.community.member.invite.request.approve.admit.Commands
import app.community.member.invite.request.approve.admit.Proofs
import app.community.member.join.accept.Commands
import app.community.member.join.joining.Commands
import app.community.member.join.joining.Proofs
import app.community.member.join.joining.abandon.Commands
import app.community.member.remove.Commands
import app.community.member.remove.Proofs
import app.community.name.Commands
import app.community.name.Proofs
import app.community.profile.Commands
import app.community.profile.Proofs
import app.community.Op
import app.community.Validate
import app.community.channel.message.Op
import app.community.channel.message.Validate
import app.community.channel.message.attachment.Op
import app.community.channel.message.attachment.Proofs
import app.community.channel.message.attachment.Validate
import app.community.channel.message.attachment.chunk.Op
import app.community.channel.message.attachment.chunk.Validate
import app.community.channel.message.reaction.Op
import app.community.channel.message.reaction.Validate
import app.community.channel.message.receipt.Op
import app.community.channel.message.receipt.Validate
import app.community.device.endpoint.Op
import app.community.device.endpoint.Validate
import app.community.device.secret.Op
import app.community.device.secret.Proofs
import app.community.device.secret.Validate
import app.community.key.Op
import app.community.key.Validate
import app.community.key.wrap.Op
import app.community.key.wrap.Validate
import app.community.member.admin.Commands
import app.community.member.admin.Op
import app.community.member.admin.Validate
import app.community.member.invite.Commands
import app.community.member.invite.Op
import app.community.member.invite.Proofs
import app.community.member.invite.Validate
import app.community.member.invite.request.Op
import app.community.member.invite.request.Validate
import app.community.member.invite.request.approve.Op
import app.community.member.invite.request.approve.Validate
import app.community.member.invite.request.approve.admit.Op
import app.community.member.invite.request.approve.admit.Validate
import app.community.member.join.accept.Op
import app.community.member.join.accept.Validate
import app.community.member.join.joining.Op
import app.community.member.join.joining.Validate
import app.community.member.join.joining.abandon.Op
import app.community.member.join.joining.abandon.Proofs
import app.community.member.join.joining.abandon.Validate
import app.community.member.remove.Op
import app.community.member.remove.Validate
import app.community.name.Op
import app.community.name.Validate
import app.community.profile.Op
import app.community.profile.Validate
import engine.core.MerkleCost
import engine.core.FIFO

namespace Community
open Engine Codec
variable {C : Crypto} {ops : Id → Option Op}

/-- The unscoped form forces `Signed` everywhere: if every message has a
signature verifying under pk (Ed25519, for every key), every message
counts as signed by pk's holder. Why `Unforgeable` ranges over a store. -/
theorem unscoped_signs_all {Signed : Key → ByteArray → Prop} {pk : Key}
    (hU : ∀ pk m s, C.verify pk m s = true → Signed pk m)
    (hall : ∀ m, ∃ s, C.verify pk m s = true) (m : ByteArray) : Signed pk m :=
  let ⟨s, hs⟩ := hall m
  hU pk m s hs

/-- Every admission was consented to by its device: the device signed
the root that admits it (x = y), or the request its admit cites (x is
y's slot 1). -/
theorem admission_consented {y c u : Id} {d e kid : Key} (h : V C ops y (.admission c u d e kid)) :
    ∃ x o b s, (x = y ∨ ∃ oy, ops y = some oy ∧ oy.reqs.getD 1 .empty = x) ∧
      ops x = some o ∧ (decode o.body : Option Body) = some b ∧ s ∈ b.sigs ∧
      C.verify d (signed o b) s = true := by
  obtain ⟨o, b, fs, hx, hb, hr, hv⟩ := valid_inv h
  rcases check_admission hv with ⟨s, rfl, _, _, _, hs⟩ | ⟨d0, e0, l, a, rfl, rfl, _⟩
  · exact ⟨y, o, _, s, Or.inl rfl, hx, hb, by simp [Body.sigs], hs⟩
  · obtain ⟨_, r, _, hreq, _, hrv, _⟩ := all2_cons2 hr
    obtain ⟨or, br, fsr, hor, hbr, _, hvr⟩ := valid_inv hrv
    obtain ⟨cs, _, _, _, _, _, _, rfl, _, _, _, hcs, _⟩ := check_request hvr
    exact ⟨r, or, _, cs, Or.inr ⟨o, hx, by rw [hreq]; rfl⟩, hor, hbr, by simp [Body.sigs], hcs⟩

/-- **Impersonation is impossible.** If no signature in the store is
forged, a message attributed to user u and device d was signed, as this
exact op, by the holder of d's key, and that holder also signed the op
that admitted d into u: the root, or the request its admission cites.
Nobody can post as a user without a device the user's admission binds
and that device's key. -/
theorem no_impersonation {Signed : Key → ByteArray → Prop} (hU : Unforgeable C ops Signed)
    {x c u : Id} {d k t : ByteArray} {n tm : Nat} {clump : Option Id}
    (h : V C ops x (.message c u d k t n tm clump)) :
    ∃ o s, ops x = some o ∧ (decode o.body : Option Body) = some (.post k t n tm s) ∧
      Signed d (signed o (.post k t n tm s)) ∧
      ∃ y e ka z oz bz, V C ops y (.admission c u d e ka) ∧
        (z = y ∨ ∃ oy, ops y = some oy ∧ oy.reqs.getD 1 .empty = z) ∧ ops z = some oz ∧
        (decode oz.body : Option Body) = some bz ∧ Signed d (signed oz bz) := by
  obtain ⟨o, s, e, ka, y, hx, hb, _, hy, hs⟩ := message_authorized h
  obtain ⟨z, oz, bz, s', hz, hoz, hbz, hm', hs'⟩ := admission_consented hy
  exact ⟨o, s, hx, hb, hU _ _ _ _ _ hx hb (by simp [Body.sigs]) hs, y, e, ka, z, oz, bz, hy, hz,
    hoz, hbz, hU _ _ _ _ _ hoz hbz hm' hs'⟩

/-- **Nobody can rename another user.** If no signature in the store is
forged, a Valid profile of user u was signed, as this exact op, by the
holder of a device key admitted into u, and that holder also signed the
op that admitted it: the root, or the request its admission cites. -/
theorem no_renaming {Signed : Key → ByteArray → Prop} (hU : Unforgeable C ops Signed)
    {x c u : Id} {n : ByteArray} {tm : Nat}
    (h : V C ops x (.profile c u n tm)) :
    ∃ o s d, ops x = some o ∧ (decode o.body : Option Body) = some (.profile n tm s) ∧
      Signed d (signed o (.profile n tm s)) ∧
      ∃ y e ka z oz bz, V C ops y (.admission c u d e ka) ∧
        (z = y ∨ ∃ oy, ops y = some oy ∧ oy.reqs.getD 1 .empty = z) ∧ ops z = some oz ∧
        (decode oz.body : Option Body) = some bz ∧ Signed d (signed oz bz) := by
  obtain ⟨o, s, d, e, ka, y, hx, hb, _, hy, _, hs⟩ := profile_authorized h
  obtain ⟨z, oz, bz, s', hz, hoz, hbz, hm', hs'⟩ := admission_consented hy
  exact ⟨o, s, d, hx, hb, hU _ _ _ _ _ hx hb (by simp [Body.sigs]) hs, y, e, ka, z, oz, bz, hy, hz,
    hoz, hbz, hU _ _ _ _ _ hoz hbz hm' hs'⟩

/-- **An admission's community has a Valid root**, which names the key
id the admission names: an admission copies its root's. -/
theorem root_of_admission (hk : Keyed ops) {y c u : Id} {d e kid : Key} (h : V C ops y (.admission c u d e kid)) :
    ∃ d0 e0, V C ops c (.admission c c d0 e0 kid) := by
  obtain ⟨o, b, fs, hx, _, hr, hv⟩ := valid_inv h
  rcases check_admission hv with ⟨s, rfl, rfl, hc, hu, _⟩ | ⟨d0, e0, l, a, rfl, rfl, hh⟩
  · have h1 : c = y := hc.trans (hk y o hx)
    have h2 : u = y := hu.trans (hk y o hx)
    subst h1; subst h2
    exact ⟨d, e, h⟩
  · obtain ⟨x, _, _, hreq, hxv, _, _⟩ := all2_cons2 hr
    rw [hreq] at hh; simp at hh; subst hh
    exact ⟨d0, e0, hxv⟩

theorem check_named {C : Crypto} {o : Op} {b : Body} {fs : List Fact} {c u : Id} {nm : ByteArray}
    {n : Nat} (h : check C o b fs = some (.named c u nm n)) :
    ∃ s d0 e0 k0 d e k auth prev, b = .name n nm s ∧
      fs = .admission c c d0 e0 k0 :: .admission c u d e k :: auth :: prev ∧ o.reqs.head? = some c ∧
      isAdmin c u auth = true ∧ nm.size ≤ 64 ∧ counterOk c n prev = true ∧
      C.verify d (signed o b) s = true := by
  unfold check at h
  split at h <;> (try (simp at h; done))
  rename_i b r a auth prev
  rcases b with ⟨n', nm', s⟩; rcases r with ⟨c0, u0, d0, e0, k0⟩; rcases a with ⟨c1, u', d, e, k⟩
  simp only [Rename.check] at h
  split at h
  · rename_i hc
    simp only [Option.map_some, Option.some.injEq, Fact.ofNamed.injEq, Rename.Fact.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    obtain ⟨h1, rfl, rfl, h4, h5, h6, h7⟩ := hc
    exact ⟨_, _, _, _, _, _, _, _, _, rfl, rfl, h1, h4, h5, h6, h7⟩
  · simp at h

/-- **Only admins name a community.** -/
theorem named_by_admin {x c u : Id} {nm : ByteArray} {n : Nat} (h : V C ops x (.named c u nm n)) :
    IsAdmin C ops c u := by
  obtain ⟨o, b, fs, _, _, hr, hv⟩ := valid_inv h
  obtain ⟨_, _, _, _, _, _, _, auth, _, rfl, rfl, _, ha, _⟩ := check_named hv
  obtain ⟨_, _, t, _, _, _, hrest⟩ := all2_cons2 hr
  cases hrest with
  | cons hz _ => exact isAdmin_sound hz ha

/-- **A shared op's validator reads only shared facts.** -/
theorem check_reads_shared {C : Crypto} {o : Op} {b : Body} {fs : List Fact} {f : Fact}
    (h : check C o b fs = some f) (hb : b.isLocal = false) : ∀ g ∈ fs, g.isLocal = false := by
  unfold check at h
  split at h <;> (try (simp at h; done)) <;> (try (simp [Body.isLocal] at hb; done))
  all_goals (obtain ⟨f', hf', -⟩ := Option.map_eq_some_iff.1 h)
  all_goals (intro g hg; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg)
  all_goals first
    | (rcases hg with rfl | rfl | rfl <;> rfl)
    | (rcases hg with rfl | rfl <;> rfl)
    | (subst hg; rfl)
    | skip
  -- grant, remove and name: their authority; name: the names before it
  · rename_i b r a auth tg
    rcases b; rcases r; rcases a; rcases tg
    simp only [Grant.check] at hf'
    split at hf'
    · rename_i hc
      rcases hg with rfl | rfl | rfl | rfl
      · rfl
      · rfl
      · exact isAdmin_shared hc.2.2.2.2.1
      · rfl
    · cases hf'
  · rename_i b r a auth tg
    rcases b; rcases r; rcases a; rcases tg
    simp only [Remove.check] at hf'
    split at hf'
    · rename_i hc
      rcases hg with rfl | rfl | rfl | rfl
      · rfl
      · rfl
      · rcases hc.2.2.2.2.1 with ⟨_, hh⟩ | hh
        · simpa using hh
        · exact isAdmin_shared hh
      · rfl
    · cases hf'
  · rename_i b r a auth prev
    rcases b; rcases r; rcases a
    simp only [Rename.check] at hf'
    split at hf'
    · rename_i hc
      rcases hg with rfl | rfl | rfl | hg
      · rfl
      · rfl
      · exact isAdmin_shared hc.2.2.2.1
      · exact counterOk_shared hc.2.2.2.2.2.1 g hg
    · cases hf'

/-- **A sealed body opens with its key.** -/
theorem openSealed_seal {S : Seal} (G : S.Good) {c kid text : ByteArray} (k : Key32) (n : Nonce24)
    (ht : text.size < Crypto.maxPlaintext) (ha : (bodyAd c kid).size < Crypto.maxAD) :
    openSealed S c kid (n.1 ++ sealBody S k n c kid text) k = some text := by
  have hn := n.2
  have hs : ¬ (n.1 ++ sealBody S k n c kid text).size < 24 := by rw [ByteArray.size_append, hn]; omega
  unfold openSealed
  rw [dif_neg hs]
  have hf : Bytes.front (n := 24) (n.1 ++ sealBody S k n c kid text) (by omega) = n :=
    Subtype.ext (ByteArray.extract_append_eq_left hn.symm)
  rw [hf, ByteArray.extract_append_eq_right hn.symm (by rw [ByteArray.size_append, hn])]
  exact openBody_sealBody G _ _ _ _ _ ht ha

/-- **An admitted device opens every body sealed under a key wrapped to
it.** A key wrapped to the device's X25519 key unwraps with its secret,
and that key opens what was sealed under it. -/
theorem member_opens {S : Seal} (G : S.Good) (rsk esk k : Key32) (n : Nonce24) (c text : ByteArray)
    (ht : text.size < Crypto.maxPlaintext)
    (ha : (bodyAd c (kidOf S k)).size < Crypto.maxAD) :
    let kid := kidOf S k
    ((unbox S rsk kid (box S esk (S.pub rsk) kid k)).bind fun k' =>
      openSealed S c kid (n.1 ++ sealBody S k n c kid text) k') = some text := by
  have hki : (kidOf S k).size < Crypto.maxAD := by
    simp only [kidOf, G.hash_size, Crypto.maxAD]; decide
  simp only [unbox_box G _ _ _ _ hki, Option.bind_some, openSealed_seal G k n ht ha]

/-- What a sealed body is bound to fits the AEAD when the community and
key ids are 32 bytes (an op id and a hash are). -/
theorem bodyAd_size {c kid : ByteArray} (hc : c.size = 32) (hk : kid.size = 32) :
    (bodyAd c kid).size = 66 := by
  show (Codec.enc c ++ Codec.enc kid).toArray.size = 66
  rw [List.size_toArray, List.length_append, Codec.length_enc_bytes, Codec.length_enc_bytes, hc, hk,
    Codec.encNat_small (show 32 < 128 by decide)]
  rfl

/-- **A running post opens with its key** (`openSealed_seal` at the
running suite, through the post command and the read path): the body
`sealedPost` writes, the screen's `openStored` opens with the stored
key to the text sealed. Every premise but the crates' correctness is
discharged: key and nonce sizes by their types, the key id's by
SHA-256's digest size; the community id is an op id (32 bytes) and the
text is under the AEAD's limit (274877906817 bytes; an op that fits a
frame is under 1 MiB). -/
theorem sealedPost_opens (t : Trust.NativeCrypto) (c adm : Id) (d : Device) (k : Key32) (nonce : Nonce24)
    (text : ByteArray) (n time : Nat) (clump : Option Id)
    (hc : c.size = 32) (ht : text.size < Crypto.maxPlaintext) :
    ∃ kid sealed sg, (Codec.decode (sealedPost c adm d k nonce text n time clump).body : Option Body) =
      some (.post kid sealed n time sg) ∧ kid = kidOf cryptoSeal k ∧
      openStored cryptoSeal c kid sealed k.1 = some text := by
  refine ⟨_, _, _, body_mkOp _ _, rfl, ?_⟩
  have G := cryptoSeal_good t
  unfold openStored
  rw [Bytes.of?_val, Option.bind_some]
  exact openSealed_seal G k nonce ht
    (by rw [bodyAd_size hc (show (kidOf cryptoSeal k).size = 32 from G.hash_size _)]; decide)

/-- **A running wrap opens at its recipient** (`unbox_box` at the
running suite, through the approver's `wrapKey` and the member's
`unwrap`): the wrap `wrapKey` writes to the node key of secret rsk,
`unbox` opens with rsk, under the key's own id, to the content key,
given the crates' correctness. -/
theorem wrapKey_opens (t : Trust.NativeCrypto) (c myAdm toAdm : Id) (d : Device) (k esk rsk : Key32) :
    ∃ bx sg, (Codec.decode (wrapKey c myAdm toAdm d k esk (cryptoSeal.pub rsk)).body : Option Body) =
      some (.wrap bx sg) ∧ unbox cryptoSeal rsk (kidOf cryptoSeal k) bx = some k := by
  have G := cryptoSeal_good t
  refine ⟨_, _, body_mkOp _ _, unbox_box G rsk esk k _ ?_⟩
  rw [show (kidOf cryptoSeal k).size = 32 from G.hash_size _]; decide

/-- **An admitted device reads every post sealed under a key wrapped to
it**, through the functions the app runs: the approver's `wrapKey` to
the device's node key, the member's `unbox`, the poster's `sealedPost`
and the screen's `openStored`. The one premise left about the code is
the crates' correctness (`member_opens` at the running suite). -/
theorem member_reads (t : Trust.NativeCrypto) (c adm toAdm : Id) (d w : Device) (k esk rsk : Key32) (nonce : Nonce24)
    (text : ByteArray) (n time : Nat) (clump : Option Id)
    (hc : c.size = 32) (ht : text.size < Crypto.maxPlaintext) :
    ∃ kid bx wsg sealed sg,
      (Codec.decode (wrapKey c adm toAdm w k esk (cryptoSeal.pub rsk)).body : Option Body) =
        some (.wrap bx wsg) ∧
      (Codec.decode (sealedPost c adm d k nonce text n time clump).body : Option Body) =
        some (.post kid sealed n time sg) ∧
      ((unbox cryptoSeal rsk kid bx).bind fun k' => openStored cryptoSeal c kid sealed k'.1) = some text := by
  obtain ⟨bx, wsg, hw, hu⟩ := wrapKey_opens t c adm toAdm w k esk rsk
  obtain ⟨kid', sealed, sg, hp, hk', ho⟩ := sealedPost_opens t c adm d k nonce text n time clump hc ht
  subst hk'
  exact ⟨_, bx, wsg, sealed, sg, hw, hp, by rw [hu, Option.bind_some, ho]⟩
open Engine

/-! ## One community key

A community has one content key, made at founding: keys do not rotate
yet. Its root names its id, and every admission copies it
(`root_of_admission`), so every member agrees which key it is
(`rootKid_unique`). The laws below hold of the code that runs: every
Valid post and attachment is sealed under it (`post_community_key`,
`attach_community_key`); the key a sender seals with is it
(`currentKey_community`, `send_community_key`); a key filed under its id
is it, up to a SHA-256 collision (`key_kid`); `unwrap` takes no other key
(`unwrap_community`); a Valid wrap is an admitted device's, to an
admitted node (`wrap_signed`, `no_wrap_forgery`); and an approval wraps
it, beside the admission it gives (`approveReq_wrap_admits`). -/

section
variable (C : Crypto) (ops : Id → Option Op)

/-- c's root names content key id kid. -/
def RootKid (c : Id) (kid : ByteArray) : Prop := ∃ d e, V C ops c (.admission c c d e kid)
end

section
variable {s : DB Fact} {C : Crypto} {ops : Id → Option Op}

/-- **Every member agrees on the community key**: c's root names one key
id, whatever store holds it. -/
theorem rootKid_unique {c : Id} {k k' : ByteArray} (h : RootKid C ops c k) (h' : RootKid C ops c k') :
    k = k' := by
  obtain ⟨d, e, hv⟩ := h; obtain ⟨d', e', hv'⟩ := h'
  have := spec_det hv hv'
  simp only [Verdict.valid.injEq, Fact.admission.injEq] at this
  exact this.2.2.2.2

/-- **Every Valid post is sealed under the community key**: its key id is
the one c's root names. A post sealed under any other key is Invalid. -/
theorem post_community_key {x c u : Id} {d k t : ByteArray} {n tm : Nat} {clump : Option Id}
    (h : V C ops x (.message c u d k t n tm clump)) : RootKid C ops c k := by
  obtain ⟨o, b, fs, _, _, hr, hv⟩ := valid_inv h
  cases clump with
  | none =>
    obtain ⟨_, d0, e0, _, _, _, rfl, hh, _⟩ := check_message hv
    obtain ⟨y, _, hreq, hy, _⟩ := all2_two hr
    rw [hreq] at hh; simp at hh; subst hh
    exact ⟨d0, e0, hy⟩
  | some root =>
    obtain ⟨_, d0, e0, _, _, _, _, _, _, _, _, rfl, hh, _, _⟩ := check_child hv
    obtain ⟨y, _, _, hreq, hy, _, _⟩ := all2_cons2 hr
    rw [hreq] at hh; simp at hh; subst hh
    exact ⟨d0, e0, hy⟩

/-- **Every Valid attachment is sealed under the community key.** -/
theorem attach_community_key {x c m u root : Id} {len : Nat} {kid sealed : ByteArray}
    (h : V C ops x (.attachment c m u root len kid sealed)) : RootKid C ops c kid := by
  obtain ⟨o, b, fs, _, _, hr, hv⟩ := valid_inv h
  obtain ⟨_, d0, e0, _, _, _, _, _, _, _, _, _, _, rfl, hh, _⟩ := check_attach hv
  obtain ⟨y, _, _, hreq, hy, _, _⟩ := all2_cons2 hr
  rw [hreq] at hh; simp at hh; subst hh
  exact ⟨d0, e0, hy⟩

/-- **A key is filed under its own hash.** A Valid local key fact holds a
32-byte key whose id is its `kidOf` (SHA-256). So a key under the
community's id is the community's key, unless SHA-256 has a collision
(not proven). -/
theorem key_kid {x : Id} {c kid k : ByteArray} (h : V C ops x (.key c kid k)) :
    ∃ k' : Key32, k'.1 = k ∧ kid = kidOf cryptoSeal k' := by
  obtain ⟨o, b, fs, -, -, -, hv⟩ := valid_inv h
  unfold check at hv
  split at hv <;> (try (simp at hv; done))
  rename_i b
  rcases b with ⟨c', k'⟩
  simp only [ContentKey.check] at hv
  split at hv
  · rename_i hs
    simp only [Option.map_some, Option.some.injEq, Fact.ofKey.injEq, ContentKey.Fact.mk.injEq] at hv
    obtain ⟨rfl, rfl, rfl⟩ := hv
    exact ⟨⟨_, hs⟩, rfl, rfl⟩
  · simp at hv

theorem opKey_inj {x y : Id} (h : opKey x = opKey y) : x = y := by
  have h1 := congrArg (fun b : ByteArray => b.data.toList) h
  simp only [opKey, Array.toList_append, List.cons_append, List.nil_append, List.cons.injEq,
    true_and] at h1
  cases x; cases y
  simp only [ByteArray.mk.injEq]
  exact Array.toList_inj.1 h1

/-- A row read under an op's own key, at rest, is that op's Valid fact. -/
theorem own_row (h : Inv (family C) s) (hq : s.queue = []) {x : Id} {lim : Option Nat}
    {pf : Pos × Fact} (hp : pf ∈ (Engine.eval s { key := opKey x, limit := lim }).rows) :
    V C s.ops x pf.2 := by
  obtain ⟨y, f, rfl, hy, hf⟩ := (mem_matching _ _).1 (mem_eval_matching hp)
  obtain ⟨g, hg, hk⟩ := (h.idx _ y).1 hy
  rw [hf] at hg; cases hg
  have hyx : y = x := by
    rcases List.mem_cons.1 hk with he | hk
    · exact (opKey_inj he).symm
    · exfalso
      obtain ⟨r, hr, hra⟩ := List.mem_filterMap.1 (show opKey x ∈ keysOf rels f from hk)
      cases ha : r.args f with
      | none => simp [ha] at hra
      | some as => simp only [ha, Option.map_some, Option.some.injEq] at hra; exact r.key_ne_opKey (rels_short r hr) as x hra
  subst hyx
  exact (status_iff_spec h hq y _).1 hf

/-- **Every member reads the root's key id.** At rest, the key id
`communityKid c` answers is the one c's root names. -/
theorem communityKid_root (h : Inv (family C) s) (hq : s.queue = []) {c kid : ByteArray}
    (hk : (communityKid c).eval s = some kid) : RootKid C s.ops c kid := by
  simp only [communityKid, View.eval_bind, View.eval_read, View.eval_pure] at hk
  split at hk
  · rename_i p c' u d e k hr
    split at hk
    · rename_i hc
      cases hk; subst hc
      have hv := own_row h hq (List.mem_of_mem_head? hr)
      obtain ⟨d0, e0, hroot⟩ := root_of_admission h.key hv
      exact ⟨d0, e0, hroot⟩
    · cases hk
  · cases hk

/-- **The key a device seals with is the community's.** At rest, the key
`currentKey c` answers hashes to the id c's root names: every member's
`currentKey` answers a key of that one id (`rootKid_unique`). -/
theorem currentKey_community (h : Inv (family C) s) (hq : s.queue = []) {c : Id} {k : Key32}
    (hk : (currentKey c).eval s = some k) :
    (communityKid c).eval s = some (kidOf cryptoSeal k) ∧ RootKid C s.ops c (kidOf cryptoSeal k) := by
  simp only [currentKey, View.eval_bind] at hk
  cases hc : (communityKid c).eval s with
  | none => simp [hc] at hk
  | some kid =>
    simp only [hc, Rel.read, View.eval_read, View.eval_pure] at hk
    obtain ⟨⟨p, f⟩, hrow, hf⟩ := Option.bind_eq_some_iff.1 hk
    cases f <;> (try (rename_i x; cases x)) <;> simp only at hf <;> (try (cases hf; done))
    rename_i c' kid' k'
    obtain ⟨hv, hargs⟩ := row_filed (r := key.byId) (by simp [rels]) h hq (List.mem_of_mem_head? hrow)
    simp [key.byId] at hargs
    subst hargs
    obtain ⟨k'', rfl, rfl⟩ := key_kid hv
    have : k'' = k := by rw [Bytes.of?_val] at hf; exact Option.some.inj hf
    subst this
    exact ⟨rfl, communityKid_root h hq hc⟩

/-- **No wrap plants a key.** Whatever the store holds, `unwrap c` writes
nothing, or one op: a key whose id is the one `communityKid c` reads
(c's root's, at rest: `communityKid_root`). A wrap holding any other key,
from any member, is passed over. -/
theorem unwrap_community (s : DB Fact) (c : Id) :
    ((unwrap c).eval s).ops = [] ∨
      ∃ k : Key32, (communityKid c).eval s = some (kidOf cryptoSeal k) ∧
        ((unwrap c).eval s).ops = [contentKey c k.1] := by
  simp only [unwrap, View.eval_bind]
  split
  · rename_i pk sk _
    simp only [View.eval_bind]
    split
    · rename_i kid hkid
      simp only [Rel.read, View.eval_bind, View.eval_read]
      by_cases hz : (Engine.eval s (key.byId.query [kid] (some 0))).total = 0
      · simp only [hz, ne_eq, not_true_eq_false, ↓reduceIte, View.eval_bind, View.eval_read,
          View.eval_pure]
        generalize hks : List.filterMap _ _ = ks
        cases hh : ks.head? with
        | none => exact Or.inl rfl
        | some k =>
          right
          refine ⟨k, ?_, rfl⟩
          have hm := List.mem_of_mem_head? hh
          rw [← hks, List.mem_filterMap] at hm
          obtain ⟨⟨_, f⟩, _, hf⟩ := hm
          cases f <;> (try (rename_i x; cases x)) <;> simp only at hf <;> (try (cases hf; done))
          obtain ⟨_, hp⟩ := Option.filter_eq_some_iff.1 hf
          rw [hkid, of_decide_eq_true hp]
      · simp only [hz, ne_eq, not_false_eq_true, ↓reduceIte, View.eval_pure]
        exact Or.inl trivial
    · exact Or.inl rfl
  · exact Or.inl rfl

/-- **A sender seals with the community key.** At rest, the first op the
app's send writes, with the key `currentKey c` answers, is a post whose
key id is the one c's root names: what the post validator requires
(`post_community_key`), so a member never writes a post its peers
refuse, nor one sealed under any other key. -/
theorem send_community_key (h : Inv (family C) s) (hq : s.queue = []) {c myAdm : Id} {d : Device}
    {k : Key32} (hk : (currentKey c).eval s = some k) (nonce : Nonce24) (text : ByteArray) (now : Nat)
    (files : List NewFile) :
    ∃ p rest kid sealed n sg, ((send c myAdm d k nonce text now files).eval s).ops = p :: rest ∧
      (decode p.body : Option Body) = some (.post kid sealed n now sg) ∧ RootKid C s.ops c kid := by
  simp only [send, View.eval_bind, View.eval_pure]
  exact ⟨_, _, _, _, _, _, rfl, body_mkOp _ _, (currentKey_community h hq hk).2⟩

/-- **Every post a member holds is sealed under the key it holds.** At
rest, every Valid post of c in a store is sealed under the id of the key
that store's `currentKey c` answers: the one key a member seals with is
the one every post it holds needs. -/
theorem post_sealed_current (h : Inv (family C) s) (hq : s.queue = []) {c : Id} {k : Key32}
    (hk : (currentKey c).eval s = some k) {x u : Id} {d kid t : ByteArray} {n tm : Nat}
    {clump : Option Id} (hp : V C s.ops x (.message c u d kid t n tm clump)) :
    kid = kidOf cryptoSeal k :=
  rootKid_unique (post_community_key hp) (currentKey_community h hq hk).2

/-- **A Valid wrap is an admitted device's, of the community's key id, to
an admitted node.** It carries the id c's root names; a device admitted
into c signed it, as this exact op; and its recipient is the node key an
admission into c names. -/
theorem wrap_signed {x c : Id} {kid e bx : ByteArray} (h : V C ops x (.wrap c kid e bx)) :
    RootKid C ops c kid ∧
    (∃ o s y ua da ea ka, ops x = some o ∧ (decode o.body : Option Body) = some (.wrap bx s) ∧
      o.reqs.take 2 = [c, y] ∧ V C ops y (.admission c ua da ea ka) ∧
      C.verify da (signed o (.wrap bx s)) s = true) ∧
    ∃ ut dt, Admitted C ops c ut dt e := by
  obtain ⟨o, b, fs, hx, hb, hr, hv⟩ := valid_inv h
  obtain ⟨s, d0, e0, ua, da, ea, ka, ut, dt, kt, rfl, rfl, hh, hs⟩ := check_wrap hv
  obtain ⟨r0, y, z, hreq, h0, hy, hz⟩ := all2_three hr
  rw [hreq] at hh; simp at hh; subst hh
  exact ⟨⟨d0, e0, h0⟩, ⟨o, s, y, ua, da, ea, ka, hx, hb, by rw [hreq]; rfl, hy, hs⟩, ut, dt, z, kt, hz⟩

/-- **Only a member wraps.** If no signature in the store is forged, a
Valid wrap was signed, as this exact op, by the holder of a device key
admitted into c: no outsider, and no forged author, delivers a key. -/
theorem no_wrap_forgery {Signed : Key → ByteArray → Prop} (hU : Unforgeable C ops Signed)
    {x c : Id} {kid e bx : ByteArray} (h : V C ops x (.wrap c kid e bx)) :
    ∃ o s y ua da ea ka, ops x = some o ∧ (decode o.body : Option Body) = some (.wrap bx s) ∧
      V C ops y (.admission c ua da ea ka) ∧ Signed da (signed o (.wrap bx s)) := by
  obtain ⟨_, ⟨o, s, y, ua, da, ea, ka, hx, hb, _, hy, hs⟩, _⟩ := wrap_signed h
  exact ⟨o, s, y, ua, da, ea, ka, hx, hb, hy, hU _ _ _ _ _ hx hb (by simp [Body.sigs]) hs⟩
end

/-- **Joining is just ops, and only the request leaves the device.** The
join intent writes the device's secret, the request, the acceptance and
the pending join; of these, sync may offer only the request. -/
theorem joinOps_travels (C : Crypto) (i : Invite) (seed name : ByteArray) (key : Key) :
    (joinOps i seed name key).ops.filter (family C).shared = [i.request (Device.ofSeed seed) key] := by
  simp [joinOps, Invite.request, Community.request, secret, accept, joining, shared_mkOp, Body.isLocal]

/-- **Founding is just ops**; the node's key, the secret, the acceptance
and the content key stay. Only the root, the name, the profile and the
key's wrap travel. -/
theorem found_travels (C : Crypto) (s : DB Fact) (seed name myName : ByteArray) (time : Nat)
    (k esk fresh : Key32) :
    ((found seed name myName time k esk fresh).eval s).ops.filter (family C).shared =
      let key := ((nodeKeyOr fresh).eval s).1; let d := Device.ofSeed seed
      let r := root d key (kidOf cryptoSeal k)
      [r, setName r.id r.id r.id [] 1 d name, profile r.id r.id d myName time,
        wrapKey r.id r.id r.id d k esk key] := by
  unfold found
  rw [View.eval_bind]
  simp only [View.eval_pure, List.filter_append, nodeKeyOr_local, List.nil_append]
  simp [root, secret, accept, setName, profile, contentKey, wrapKey, wrap, shared_mkOp,
    Body.isLocal]
open Engine
section
variable {s : DB Fact} {C : Crypto}

/-- The keys `heldKids` names are held: a Valid local key fact holds each. -/
theorem heldKids_held (h : Inv (family C) s) (hq : s.queue = []) {c kid : ByteArray}
    (hkid : kid ∈ (heldKids c).eval s) : ∃ x k, V C s.ops x (.key c kid k) := by
  unfold heldKids at hkid
  rw [View.eval_bind] at hkid
  simp only [View.eval_pure, List.mem_filterMap] at hkid
  obtain ⟨⟨p, g⟩, hg, hk⟩ := hkid
  cases g <;> (try (rename_i x; cases x)) <;> simp at hk
  subst hk
  obtain ⟨_, hv, hargs⟩ := row_at (C := C) (r := key.byCommunity) (by simp [rels]) h hq hg
  simp [key.byCommunity] at hargs
  subst hargs
  exact ⟨_, _, hv⟩

/-- Every key a Valid local key fact holds is one `heldKids` names. -/
theorem held_heldKids (h : Inv (family C) s) (hq : s.queue = []) {c kid k : ByteArray} {x : Id}
    (hk : V C s.ops x (.key c kid k)) : kid ∈ (heldKids c).eval s := by
  unfold heldKids
  rw [View.eval_bind]
  simp only [View.eval_pure, List.mem_filterMap]
  exact ⟨_, at_row (C := C) (r := key.byCommunity) (by simp [rels]) h hq hk (by simp [key.byCommunity]), rfl⟩

theorem eval_readable (c : Id) (lim : Option Nat) (desc : Bool) (after before : Option Pos) :
    (readable c lim desc after before).eval s =
      let kids := (heldKids c).eval s
      unionAnswers desc lim
        (kids.map (fun kid => Engine.eval s (message.byKey.query [c, kid] lim desc after before)) ++
         kids.map fun kid =>
          let a := Engine.eval s (received.byKey.query [c, kid] lim desc (after.map afterRec)
            (before.map beforeRec))
          { a with rows := a.rows.map asMsg }) := by
  simp [readable, View.eval_bind, eval_readAll, List.map_map]
  rfl

/-- **A channel's list holds only messages this device can read, each
where it belongs.** Every row of `readable c` is a Valid message of c
sealed under a key a Valid local key fact holds, named by its id: below
the counter cap at its own position (its counter, time and id), at or
past it at a receipt of it this device holds. -/
theorem readable_held (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (lim : Option Nat)
    (desc : Bool) (after before : Option Pos) {pf : Pos × Fact}
    (hp : pf ∈ ((readable c lim desc after before).eval s).rows) :
    ∃ u d kid sealed n tm clump, V C s.ops pf.1.2 (.message c u d kid sealed n tm clump) ∧
      (∃ x k, V C s.ops x (.key c kid k)) ∧
      ((n < countCap ∧ pf = ((msgKey n tm, pf.1.2), .message c u d kid sealed n tm clump)) ∨
       (countCap ≤ n ∧ ∃ y k, V C s.ops y (.received c kid pf.1.2 k clump) ∧
          pf = ((recKey k pf.1.2, pf.1.2), .received c kid pf.1.2 k clump))) := by
  rw [eval_readable] at hp
  obtain ⟨a, ha, hpa⟩ := mem_union hp
  rcases List.mem_append.1 ha with ha | ha
  · obtain ⟨kid, hkid, rfl⟩ := List.mem_map.1 ha
    obtain ⟨he, hv, hargs⟩ := row_at (C := C) (r := message.byKey) (by simp [rels]) h hq hpa
    obtain ⟨⟨sk, y⟩, f⟩ := pf
    simp only at he hv hargs ⊢
    cases f <;> (try (rename_i x; cases x)) <;> simp [message.byKey] at hargs
    rename_i c' u d kid' sealed n tm clump
    obtain ⟨hn, hc, hk⟩ := hargs
    subst c'; subst kid'
    refine ⟨u, d, kid, sealed, n, tm, clump, hv, heldKids_held h hq hkid, .inl ⟨hn, ?_⟩⟩
    rw [he]; rfl
  · obtain ⟨kid, hkid, rfl⟩ := List.mem_map.1 ha
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hpa
    obtain ⟨he, hv, hargs⟩ := row_at (C := C) (r := received.byKey) (by simp [rels]) h hq hr
    obtain ⟨⟨sk, z⟩, f⟩ := r
    simp only at he hv hargs
    cases f <;> (try (rename_i x; cases x)) <;> simp [received.byKey] at hargs
    rename_i c' kid' m k clump
    obtain ⟨hc, hk⟩ := hargs
    subst c'; subst kid'
    obtain ⟨_, u, d, sealed, n, tm, _, _, hn, hm⟩ := received_of_message hv
    refine ⟨u, d, kid, sealed, n, tm, clump, hm, heldKids_held h hq hkid, .inr ⟨hn, z, k, hv, ?_⟩⟩
    simp only [Prod.mk.injEq] at he
    rw [he.1.1]; rfl

/-- **A channel's list misses no message this device can read.** Read
whole (no limit, no range), `readable c` lists every Valid message of c
sealed under a key a Valid local key fact holds: below the counter cap
at its own position, and at each receipt of it this device holds. -/
theorem readable_complete (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (desc : Bool)
    {clump : Option Id} {y x : Id} {u d kid sealed k : ByteArray} {n tm : Nat}
    (hm : V C s.ops y (.message c u d kid sealed n tm clump)) (hk : V C s.ops x (.key c kid k)) :
    (n < countCap → ((msgKey n tm, y), Fact.message c u d kid sealed n tm clump) ∈
        ((readable c none desc).eval s).rows) ∧
      ∀ z j, V C s.ops z (.received c kid y j clump) →
        ((recKey j y, y), Fact.received c kid y j clump) ∈ ((readable c none desc).eval s).rows := by
  have hkid := held_heldKids h hq hk
  rw [eval_readable]
  simp only
  refine ⟨fun hn => ?_, fun z j hz => ?_⟩
  · rw [mem_union_all]
    refine ⟨_, List.mem_append_left _ (List.mem_map.2 ⟨kid, hkid, rfl⟩), ?_⟩
    exact at_row (C := C) (r := message.byKey) (by simp [rels]) h hq hm (by simp [message.byKey, hn])
  · rw [mem_union_all]
    refine ⟨_, List.mem_append_right _ (List.mem_map.2 ⟨kid, hkid, rfl⟩), List.mem_map.2 ⟨_,
      at_row (C := C) (r := received.byKey) (by simp [rels]) h hq hz (by simp [received.byKey]), rfl⟩⟩

/-- **A removal the remover flow writes stands.** Every op
`removeMember c t d` writes is, once stored, a Valid removal of t by
an admin u other than t (d's signatures verifying under the suite). -/
theorem removeMember_valid (h : Inv (family C) s) (hq : s.queue = []) {c t : Id} {d : Device}
    (hsig : ∀ m, C.verify d.pk m (edSign d.sk m) = true)
    {o : Op} (ho : o ∈ ((removeMember c t d).eval s).ops)
    {ops' : Id → Option Op} (he : Extends s.ops ops') (hs : ops' o.id = some o) :
    ∃ u, u ≠ t ∧ IsAdmin C s.ops c u ∧ V C ops' o.id (.removal c t u) := by
  unfold removeMember at ho
  simp only [Rel.read, View.eval_bind, View.eval_read] at ho
  split at ho
  · rename_i p myAdm c' u dv ev kv hme
    simp only [View.eval_bind, View.eval_read] at ho
    split at ho
    · rename_i a pt ta g hauth htg
      simp only [View.eval_pure] at ho
      by_cases hcond : u = t ∨ (Engine.eval s (removal.byUser.query [c, t] (some 0))).total ≠ 0
      · simp [hcond] at ho
      · simp only [not_or, ne_eq, Decidable.not_not] at hcond
        obtain ⟨hut, hgone⟩ := hcond
        simp only [hut, hgone, ne_eq, not_true_eq_false, or_self, ↓reduceIte,
          List.mem_singleton] at ho
        subst ho
        have hmeV := row_filed (r := admission.byDevice) (by simp [rels]) h hq
          (List.mem_of_mem_head? (by rw [hme]; rfl))
        obtain ⟨hmv, hma⟩ := hmeV
        obtain ⟨u', e', k', hfe⟩ := byDevice_args.1 hma
        simp only [Fact.admission.injEq] at hfe
        obtain ⟨hc', _, hdv, _, _⟩ := hfe
        subst c'
        have htgV := row_filed (r := admission.byUser) (by simp [rels]) h hq
          (List.mem_of_mem_head? (by rw [htg]; rfl))
        obtain ⟨htv, hta⟩ := htgV
        obtain ⟨dt, et, kt, hg⟩ := admission_byUser_args.1 hta
        rw [hg] at htv
        obtain ⟨d0, e0, hroot⟩ := root_of_admission h.key hmv
        -- what makes u an admin
        have hadm : ∃ g, V C s.ops a g ∧ isAdmin c u g = true := by
          by_cases hu : u = c
          · rw [if_pos hu] at hauth
            cases hauth
            exact ⟨_, hmv, by simp [isAdmin, hu]⟩
          · rw [if_neg hu] at hauth
            obtain ⟨⟨⟨p2, a'⟩, g2⟩, hg2, ha'⟩ := Option.map_eq_some_iff.1 hauth
            simp only at ha'
            subst ha'
            obtain ⟨hgv, hga⟩ := row_filed (r := admin.byUser) (by simp [rels]) h hq
              (List.mem_of_mem_head? hg2)
            refine ⟨g2, hgv, ?_⟩
            cases g2 <;> simp [admin.byUser] at hga
            simp [isAdmin, hga]
        obtain ⟨g, hgv, hga⟩ := hadm
        refine ⟨u, hut, isAdmin_sound hgv hga, ?_⟩
        rw [hdv] at hmv
        exact admin_removal_stands hs (Codec.decode_encode _) rfl rfl
          (valid_stays he hroot) (valid_stays he hmv) (valid_stays he hgv) hga (valid_stays he htv)
          (hsig _)
    · simp at ho
  · simp at ho
end
open Engine
section
variable {s : DB Fact} {C : Crypto}
section
variable (hsize : ∀ x, (sha256 x).size = 32) {ct : ByteArray}
  (hspr : ChunksSound s.ops ct)
include hsize hspr

/-- **Download progress is exact.** The count `progress` reads is the
number of distinct indices i at which this device holds a Valid chunk
of the attachment, each below the chunk count; the total is the chunk
count. -/
theorem progress_exact (h : Inv (family C) s) (hq : s.queue = []) {c att m u : Id} {len : Nat}
    {k x : ByteArray} (ha : V C s.ops att (.attachment c m u (Merkle.fileRoot sha256 ct) len k x)) :
    ∃ is : List Nat, is.Nodup ∧
      (∀ i, i ∈ is ↔ ∃ y, V C s.ops y (.chunk c att (Merkle.fileRoot sha256 ct) len i)) ∧
      (∀ i ∈ is, i < Merkle.nChunks len) ∧
      (progress c att len).eval s = (is.length, Merkle.nChunks len) := by
  let root := Merkle.fileRoot sha256 ct
  let M := matching s { key := chunkKey c att }
  let ix : Pos × Fact → Nat := fun p => match p.2 with | .chunk _ _ _ _ i => i | _ => 0
  have hrow : ∀ p ∈ M, ∃ y i, p = ((SortKey.sortOf (Fact.chunk c att root len i), y), .chunk c att root len i) ∧
      V C s.ops y (.chunk c att root len i) := by
    intro p hp
    obtain ⟨y, f, rfl, hy, hf⟩ := (mem_matching _ _).1 hp
    obtain ⟨hv, hargs⟩ := (filed (C := C) (r := chunk.byAttachment) (by simp [rels]) h hq _ y f).1 ⟨hy, hf⟩
    cases f <;> (try (rename_i x; cases x)) <;> simp [chunk.byAttachment] at hargs
    obtain ⟨rfl, rfl⟩ := hargs
    obtain ⟨_, _, _, _, _, _, _, hav⟩ := chunk_of_attachment hv
    have := spec_det hav ha
    simp only [Verdict.valid.injEq, Fact.attachment.injEq] at this
    obtain ⟨_, _, _, rfl, rfl, _, _⟩ := this
    exact ⟨y, _, rfl, hv⟩
  have hheld : ∀ i, (∃ p ∈ M, ix p = i) ↔ ∃ y, V C s.ops y (.chunk c att root len i) := by
    intro i; constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨y, j, rfl, hv⟩ := hrow p hp
      exact ⟨y, hv⟩
    · rintro ⟨y, hv⟩
      have hf := (filed (C := C) (r := chunk.byAttachment) (by simp [rels]) h hq [c, att] y _).2
        ⟨hv, by simp [chunk.byAttachment]⟩
      exact ⟨_, (mem_matching _ _).2 ⟨y, _, rfl, hf.1, hf.2⟩, rfl⟩
  refine ⟨M.map ix, ?_, ?_, ?_, ?_⟩
  · show List.Pairwise _ _
    rw [List.pairwise_map]
    have hn' : List.Pairwise (fun a b : Pos × Fact => a.1.2 ≠ b.1.2) M := by
      have := matching_nodup h { key := chunkKey c att }
      unfold List.Nodup at this; rwa [List.pairwise_map] at this
    refine hn'.imp_of_mem fun ha hb hne heq => hne ?_
    obtain ⟨y1, i1, rfl, hv1⟩ := hrow _ ha
    obtain ⟨y2, i2, rfl, hv2⟩ := hrow _ hb
    simp only [ix] at heq; subst heq
    exact chunk_unique h.key hsize hspr hv1 hv2
  · intro i; rw [List.mem_map]; exact hheld i
  · intro i hi
    obtain ⟨y, hv⟩ := (hheld i).1 (List.mem_map.1 hi)
    obtain ⟨o, b, fs, _, _, _, hc⟩ := valid_inv hv
    obtain ⟨_, _, _, _, _, hver, _⟩ := check_chunk hc
    exact (Merkle.index_bound hver).1
  · unfold progress
    simp only [View.eval_bind, View.eval_pure, List.length_map]
    show ((Engine.eval s _).total, _) = _
    unfold Engine.eval
    rw [matching_also_nil _ rfl]
    rfl

/-- **Progress never passes the total.** -/
theorem progress_le (h : Inv (family C) s) (hq : s.queue = []) {c att m u : Id} {len : Nat}
    {k x : ByteArray} (ha : V C s.ops att (.attachment c m u (Merkle.fileRoot sha256 ct) len k x)) :
    ((progress c att len).eval s).1 ≤ ((progress c att len).eval s).2 := by
  obtain ⟨is, hnd, _, hb, he⟩ := progress_exact hsize hspr h hq ha
  rw [he]
  have := nodup_sub_length_le hnd fun y hy => List.mem_range.2 (hb y hy)
  simpa using this

/-- **Progress is full exactly when every chunk is here.** -/
theorem progress_full (h : Inv (family C) s) (hq : s.queue = []) {c att m u : Id} {len : Nat}
    {k x : ByteArray} (ha : V C s.ops att (.attachment c m u (Merkle.fileRoot sha256 ct) len k x)) :
    ((progress c att len).eval s).1 = ((progress c att len).eval s).2 ↔
      ∀ i < Merkle.nChunks len, ∃ y, V C s.ops y (.chunk c att (Merkle.fileRoot sha256 ct) len i) := by
  obtain ⟨is, hnd, hmem, hb, he⟩ := progress_exact hsize hspr h hq ha
  rw [he]
  simp only
  rw [nodup_full hnd hb]
  exact forall_congr' fun i => imp_congr_right fun _ => hmem i

/-- **Full progress is the whole file.** When the count reaches the
total, the attachment's length is the file's and the store holds each
of the attachment's chunk ops (`fileChunk`), whose slices are the file
(`Merkle.assemble_slices`). -/
theorem progress_done (h : Inv (family C) s) (hq : s.queue = []) {c att m u : Id} {len : Nat}
    {k x : ByteArray} (ha : V C s.ops att (.attachment c m u (Merkle.fileRoot sha256 ct) len k x))
    (hd : ((progress c att len).eval s).1 = ((progress c att len).eval s).2) :
    len = ct.size ∧ ∀ i < Merkle.nChunks ct.size,
      V C s.ops (fileChunk c att ct i).id (.chunk c att (Merkle.fileRoot sha256 ct) ct.size i) := by
  have hall := (progress_full hsize hspr h hq ha).1 hd
  obtain ⟨y0, h0⟩ := hall 0 (Merkle.one_le_nChunks len)
  obtain ⟨o, b, fs, ho, hb, _, hc⟩ := valid_inv h0
  obtain ⟨_, _, rfl, _⟩ := chunk_is_slice hsize (hspr y0 o b ho hb) hc
  refine ⟨rfl, fun i hi => ?_⟩
  obtain ⟨y, hy⟩ := hall i hi
  rw [← chunk_id h.key hsize hspr hy]
  exact hy
end
end
open Engine Codec

theorem signed_eq (o : Op) (b : Body) : signed o b = toSign o.reqs b := rfl
open Engine
variable {s : DB Fact} {C : Crypto}

theorem all_args {c : Id} {f : Fact} :
    admission.all.args f = some [c] ↔ ∃ u d e kid, f = .admission c u d e kid := by
  cases f <;> (try (rename_i x; cases x)) <;> simp [admission.all, Root.all, Rel.comap, Fact.admission?, eq_comm]

theorem removals_iff (h : Inv (family C) s) (hq : s.queue = []) (c u : Id) :
    (eval s (removals c u)).total ≠ 0 ↔ Removed C s.ops c u := by
  rw [← Nat.pos_iff_ne_zero, removals]
  show 0 < (eval s { key := removal.byUser.key [c, u], limit := some 0 }).total ↔ _
  rw [total_pos]
  constructor
  · rintro ⟨y, f, hy, hf⟩
    obtain ⟨hv, hk⟩ := (filed (by simp [rels]) h hq [c, u] y f).1 ⟨hy, hf⟩
    obtain ⟨r, rfl⟩ := byUser_args.1 hk
    exact ⟨y, r, hv⟩
  · rintro ⟨y, r, hv⟩
    obtain ⟨hy, hf⟩ := (filed (by simp [rels]) h hq [c, u] y _).2 ⟨hv, byUser_args.2 ⟨r, rfl⟩⟩
    exact ⟨y, _, hy, hf⟩

/-- At rest, a fact is a row of a community relation's list exactly when
it is Valid and filed in it. -/
theorem exists_row (h : Inv (family C) s) (hq : s.queue = []) {r : Rel Fact} (hr : r ∈ rels)
    (as : List ByteArray) (f : Fact) :
    (∃ p, (p, f) ∈ (eval s (r.query as)).rows) ↔ ∃ y, V C s.ops y f ∧ r.args f = some as := by
  show (∃ p, (p, f) ∈ (eval s { key := r.key as, limit := none }).rows) ↔ _
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨y, f', he, hy, hf⟩ := (mem_rows_all _).1 hp
    simp only [Prod.mk.injEq] at he
    obtain ⟨_, rfl⟩ := he
    exact ⟨y, (filed hr h hq as y _).1 ⟨hy, hf⟩⟩
  · rintro ⟨y, hv, hk⟩
    obtain ⟨hy, hf⟩ := (filed hr h hq as y _).2 ⟨hv, hk⟩
    exact ⟨_, (mem_rows_all _).2 ⟨y, _, rfl, hy, hf⟩⟩

theorem mem_cons_row {p : Pos} {f g : Fact} {t : List (Pos × Fact)} :
    (∃ q, (q, g) ∈ (p, f) :: t) ↔ f = g ∨ ∃ q, (q, g) ∈ t := by
  constructor
  · rintro ⟨q, hq⟩
    rcases List.mem_cons.1 hq with hq | hq
    · simp only [Prod.mk.injEq] at hq; exact Or.inl hq.2.symm
    · exact Or.inr ⟨q, hq⟩
  · rintro (rfl | ⟨q, hq⟩)
    · exact ⟨p, List.mem_cons_self ..⟩
    · exact ⟨q, List.mem_cons_of_mem _ hq⟩

/-- A row of fact `P k`, for some k, among a cons: the head's, or the tail's. -/
theorem mem_cons_rowK {p : Pos} {f : Fact} {t : List (Pos × Fact)} {P : ByteArray → Fact} :
    (∃ q k, (q, P k) ∈ (p, f) :: t) ↔ (∃ k, f = P k) ∨ ∃ q k, (q, P k) ∈ t := by
  constructor
  · rintro ⟨q, k, hq⟩
    rcases List.mem_cons.1 hq with hq | hq
    · simp only [Prod.mk.injEq] at hq; exact Or.inl ⟨k, hq.2.symm⟩
    · exact Or.inr ⟨q, k, hq⟩
  · rintro (⟨k, rfl⟩ | ⟨q, k, hq⟩)
    · exact ⟨p, k, List.mem_cons_self ..⟩
    · exact ⟨q, k, List.mem_cons_of_mem _ hq⟩

/-- `unremoved` holds of rows exactly when every admission into c among
them is into a user whose removals count none. -/
theorem unremoved_iff (c : Id) (rows : List (Pos × Fact)) :
    (unremoved c rows).eval s = true ↔
      ∀ u d e, (∃ p k, (p, .admission c u d e k) ∈ rows) → (eval s (removals c u)).total = 0 := by
  induction rows with
  | nil => simp [unremoved, View.eval]
  | cons pf t ih =>
    obtain ⟨p, f⟩ := pf
    simp only [mem_cons_rowK]
    cases f with
    | ofAdmission a =>
      obtain ⟨c', u', d', e', k'⟩ := a
      by_cases hc : c' = c
      · subst hc
        show View.eval s (if c' = c' then _ else _) = true ↔ _
        rw [if_pos rfl]
        show View.eval s (if (eval s (removals c' u')).total = 0 then _ else _) = true ↔ _
        by_cases hz : (eval s (removals c' u')).total = 0
        · rw [if_pos hz, ih]
          constructor
          · rintro hall u d e (⟨k, he⟩ | hm)
            · simp only [Fact.admission.injEq] at he; obtain ⟨_, rfl, _, _, _⟩ := he; exact hz
            · exact hall u d e hm
          · intro hall u d e hm; exact hall u d e (Or.inr hm)
        · rw [if_neg hz]
          show (false = true) ↔ _
          constructor
          · intro hf; cases hf
          · intro hall; exact absurd (hall u' d' e' (Or.inl ⟨k', rfl⟩)) hz
      · show View.eval s (if c' = c then _ else _) = true ↔ _
        rw [if_neg hc, ih]
        constructor
        · rintro hall u d e (⟨k, he⟩ | hm)
          · simp only [Fact.admission.injEq] at he; exact absurd he.1 hc
          · exact hall u d e hm
        · intro hall u d e hm; exact hall u d e (Or.inr hm)
    | _ =>
      show (unremoved c t).eval s = true ↔ _
      rw [ih]
      simp

/-- **A device is live exactly when the view says so.** At rest,
`deviceLive c d` holds exactly when d is admitted into c and none of its
users is removed. -/
theorem deviceLive_iff (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (d : Key) :
    (deviceLive c d).eval s = true ↔ Live C s.ops c d := by
  have hrow : ∀ u e, (∃ p k, (p, .admission c u d e k) ∈ (eval s (admission.byDevice.query [c, d])).rows) ↔
      Admitted C s.ops c u d e := by
    intro u e
    constructor
    · rintro ⟨p, k, hp⟩
      obtain ⟨y, hv, _⟩ := (exists_row h hq (by simp [rels]) _ _).1 ⟨p, hp⟩
      exact ⟨y, k, hv⟩
    · rintro ⟨y, k, hv⟩
      obtain ⟨p, hp⟩ := (exists_row h hq (by simp [rels]) _ _).2 ⟨y, hv, byDevice_args.2 ⟨u, e, k, rfl⟩⟩
      exact ⟨p, k, hp⟩
  have hd : ∀ u d' e, (∃ p k, (p, .admission c u d' e k) ∈ (eval s (admission.byDevice.query [c, d])).rows) →
      d' = d := by
    rintro u d' e ⟨p, k, hp⟩
    obtain ⟨_, hv, hk⟩ := (exists_row h hq (by simp [rels]) [c, d] _).1 ⟨p, hp⟩
    obtain ⟨_, _, _, he⟩ := byDevice_args.1 hk
    simp only [Fact.admission.injEq] at he; exact he.2.2.1
  have hev : (deviceLive c d).eval s =
      if (eval s (admission.byDevice.query [c, d])).rows.isEmpty then false
      else (unremoved c (eval s (admission.byDevice.query [c, d])).rows).eval s := by
    unfold deviceLive
    rw [View.eval_bind]
    by_cases he : (eval s (admission.byDevice.query [c, d])).rows.isEmpty = true
    · simp only [Rel.read, View.eval_read, he, ite_true]; rfl
    · simp only [Rel.read, View.eval_read, he, ite_false, Bool.false_eq_true]
  rw [hev]
  split
  · rename_i he
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨⟨u, e, ha⟩, _⟩
    obtain ⟨p, k, hp⟩ := (hrow u e).2 ha
    rw [List.isEmpty_iff] at he; rw [he] at hp; cases hp
  · rename_i he
    rw [unremoved_iff]
    constructor
    · intro hall
      obtain ⟨⟨p, f⟩, hm⟩ := List.exists_mem_of_ne_nil _ (by simpa using he)
      obtain ⟨_, hv, hk⟩ := (exists_row h hq (by simp [rels]) [c, d] f).1 ⟨p, hm⟩
      obtain ⟨u, e, k, rfl⟩ := byDevice_args.1 hk
      refine ⟨⟨u, e, _, _, hv⟩, fun u' e' ha => ?_⟩
      rw [← removals_iff h hq]
      exact fun hne => hne (hall u' d e' ((hrow u' e').2 ha))
    · rintro ⟨_, hall⟩ u d' e hm
      have := hd u d' e hm; subst this
      exact Decidable.of_not_not fun hne => hall u e ((hrow u e).1 hm) ((removals_iff h hq c u).1 hne)

theorem eval_live_adm {c c' : Id} {p : Pos} {u : Id} {d e k : Key} {t : List (Pos × Fact)}
    (hc : c' = c) :
    (live c ((p, .admission c' u d e k) :: t)).eval s =
      if (deviceLive c d).eval s then (u, d, e) :: (live c t).eval s
      else (live c t).eval s := by
  subst hc
  show View.eval s (if c' = c' then _ else _) = _
  rw [if_pos rfl, View.eval_bind', View.eval_bind']
  split <;> rfl

theorem mem_live (c : Id) (rows : List (Pos × Fact)) (u : Id) (d e : Key) :
    (u, d, e) ∈ (live c rows).eval s ↔
      (∃ p k, (p, .admission c u d e k) ∈ rows) ∧ (deviceLive c d).eval s = true := by
  induction rows with
  | nil => simp [live, View.eval]
  | cons pf t ih =>
    obtain ⟨p, f⟩ := pf
    rw [mem_cons_rowK]
    cases f with
    | ofAdmission a =>
      obtain ⟨c', u', d', e', k'⟩ := a
      by_cases hc : c' = c
      · rw [eval_live_adm hc]
        subst hc
        by_cases hz : (deviceLive c' d').eval s = true
        · rw [if_pos hz, List.mem_cons, ih]
          constructor
          · rintro (he | ⟨hq, hr⟩)
            · simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl, rfl⟩ := he
              exact ⟨Or.inl ⟨k', rfl⟩, hz⟩
            · exact ⟨Or.inr hq, hr⟩
          · rintro ⟨⟨k, he⟩ | hq, hr⟩
            · simp only [Fact.admission.injEq] at he
              obtain ⟨_, rfl, rfl, rfl, _⟩ := he; exact Or.inl rfl
            · exact Or.inr ⟨hq, hr⟩
        · rw [if_neg hz, ih]
          constructor
          · rintro ⟨hq, hr⟩; exact ⟨Or.inr hq, hr⟩
          · rintro ⟨⟨k, he⟩ | hq, hr⟩
            · simp only [Fact.admission.injEq] at he
              obtain ⟨_, _, rfl, _, _⟩ := he; exact absurd hr hz
            · exact ⟨hq, hr⟩
      · have : (live c ((p, .admission c' u' d' e' k') :: t)).eval s = (live c t).eval s := by
          show View.eval s (if c' = c then _ else _) = _
          rw [if_neg hc]
        rw [this, ih]
        constructor
        · rintro ⟨hq, hr⟩; exact ⟨Or.inr hq, hr⟩
        · rintro ⟨⟨k, he⟩ | hq, hr⟩
          · simp only [Fact.admission.injEq] at he; exact absurd he.1 hc
          · exact ⟨hq, hr⟩
    | _ =>
      show (u, d, e) ∈ (live c t).eval s ↔ _
      rw [ih]
      simp

/-- At rest, the live admissions of a whole list of a community relation:
its Valid admissions whose device is live. -/
theorem live_iff (h : Inv (family C) s) (hq : s.queue = []) {r : Rel Fact} (hr : r ∈ rels)
    (as : List ByteArray) (c u : Id) (d e : Key) :
    (u, d, e) ∈ (live c (eval s (r.query as)).rows).eval s ↔
      (∃ y k, V C s.ops y (.admission c u d e k) ∧ r.args (.admission c u d e k) = some as) ∧
        Live C s.ops c d := by
  rw [mem_live, deviceLive_iff h hq]
  constructor
  · rintro ⟨⟨p, k, hp⟩, hl⟩
    obtain ⟨y, hv, ha⟩ := (exists_row h hq hr _ _).1 ⟨p, hp⟩
    exact ⟨⟨y, k, hv, ha⟩, hl⟩
  · rintro ⟨⟨y, k, hv, ha⟩, hl⟩
    obtain ⟨p, hp⟩ := (exists_row h hq hr _ _).2 ⟨y, hv, ha⟩
    exact ⟨⟨p, k, hp⟩, hl⟩

/-- **Who we connect to.** At rest, the `allowPeer` view, read over the
node's persisted tables, accepts node key e for community c exactly when
a live device is admitted under e. -/
theorem connect_iff (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (e : Key) :
    (allowPeer c e).eval s = true ↔ ∃ u d, Admitted C s.ops c u d e ∧ Live C s.ops c d := by
  simp only [allowPeer, View.eval_bind, View.eval_read, View.eval_pure, List.any_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨⟨u, d, e'⟩, hm, rfl⟩
    obtain ⟨⟨y, k, hv, _⟩, hl⟩ := (live_iff h hq (by simp [rels]) [c, e'] c u d e').1 hm
    exact ⟨u, d, ⟨y, k, hv⟩, hl⟩
  · rintro ⟨u, d, ⟨y, k, hv⟩, hl⟩
    exact ⟨(u, d, e), (live_iff h hq (by simp [rels]) [c, e] c u d e).2
      ⟨⟨y, k, hv, byKey_args.2 ⟨u, d, k, rfl⟩⟩, hl⟩, rfl⟩

/-- **No connection to a node with no live device.** -/
theorem refuse_nonmember (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (e : Key)
    (hd : ∀ u d, Admitted C s.ops c u d e → Cut C s.ops c d) :
    (allowPeer c e).eval s = false := by
  cases hb : (allowPeer c e).eval s
  · rfl
  · obtain ⟨u, d, ha, hl⟩ := (connect_iff h hq c e).1 hb
    exact absurd hl (cut_not_live (hd u d ha))

/-- **Approved devices' nodes are let in.** A request admitted by an
admit op citing one approval of it lets in the key it names, unless one
of its device's users is removed. -/
theorem connect_admitted (h : Inv (family C) s) (hq : s.queue = []) {y c r x : Id} {o : Op}
    {d0 e0 k0 : Key} {u a : Id} {d e : Key} {l : Bool}
    (hy : s.ops y = some o) (hb : (Codec.decode o.body : Option Body) = some .admit)
    (hkd : o.kind = Body.tag .admit) (hreq : o.reqs = [c, r, x]) (hc : V C s.ops c (.admission c c d0 e0 k0))
    (hr : V C s.ops r (.request c u d e l)) (hx : V C s.ops x (.approval c r a))
    (hnr : ∀ u' e', Admitted C s.ops c u' d e' → ¬ Removed C s.ops c u') :
    (allowPeer c e).eval s = true :=
  have ha : Admitted C s.ops c u d e := ⟨y, k0, admit_admits hy hb hkd hreq hc hr hx⟩
  (connect_iff h hq c e).2 ⟨u, d, ha, ⟨u, e, ha⟩, hnr⟩

/-- **Only the founder's and approved devices' nodes are let in.** At
rest, a key `allowPeer` accepts has a live device admitted under it, by
the root (the founder) or by an admit op citing exactly a Valid request
naming that device and key and one Valid approval of it. A request
alone never connects: requests sit under keys of their own. -/
theorem connect_approved (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (e : Key)
    (ha : (allowPeer c e).eval s = true) :
    ∃ u d y k, V C s.ops y (.admission c u d e k) ∧ Live C s.ops c d ∧
      ((y = c ∧ u = c) ∨
        ∃ o r x a l, s.ops y = some o ∧ (Codec.decode o.body : Option Body) = some .admit ∧
          o.reqs = [c, r, x] ∧ V C s.ops r (.request c u d e l) ∧
          V C s.ops x (.approval c r a)) := by
  obtain ⟨u, d, ⟨y, k, hy⟩, hl⟩ := (connect_iff h hq c e).1 ha
  exact ⟨u, d, y, k, hy, hl, admission_approved h.key hy⟩

theorem mem_live_all (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (u : Id) (d e : Key) :
    (u, d, e) ∈ (live c (eval s (admission.all.query [c])).rows).eval s ↔
      Admitted C s.ops c u d e ∧ Live C s.ops c d := by
  rw [live_iff h hq (by simp [rels])]
  constructor
  · rintro ⟨⟨y, k, hv, _⟩, hl⟩; exact ⟨⟨y, k, hv⟩, hl⟩
  · rintro ⟨⟨y, k, hv⟩, hl⟩; exact ⟨⟨y, k, hv, all_args.2 ⟨u, d, e, k, rfl⟩⟩, hl⟩

/-- **Whom we dial.** At rest, `members` names exactly the live devices. -/
theorem members_iff (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (d : Key) :
    d ∈ (members c).eval s ↔ Live C s.ops c d := by
  simp only [members, View.eval_bind, View.eval_read, View.eval_pure, List.mem_map]
  constructor
  · rintro ⟨⟨u, d', e⟩, hm, rfl⟩; exact ((mem_live_all h hq c u d' e).1 hm).2
  · rintro hl
    obtain ⟨u, e, ha⟩ := hl.1
    exact ⟨(u, d, e), (mem_live_all h hq c u d e).2 ⟨ha, hl⟩, rfl⟩

/-- **Content keys go exactly where connections go.** At rest,
`recipients` names exactly the keys a live device is admitted under: the
keys `allowPeer` lets in. No outsider, no node with only cut devices,
and no live device's node left out. -/
theorem recipients_iff (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (e : Key) :
    e ∈ (recipients c).eval s ↔ ∃ u d, Admitted C s.ops c u d e ∧ Live C s.ops c d := by
  simp only [recipients, View.eval_bind, View.eval_read, View.eval_pure, List.mem_map]
  constructor
  · rintro ⟨⟨u, d, e'⟩, hm, rfl⟩; exact ⟨u, d, (mem_live_all h hq c u d e').1 hm⟩
  · rintro ⟨u, d, hm⟩; exact ⟨(u, d, e), (mem_live_all h hq c u d e).2 hm, rfl⟩

/-- **Nodes that hold the same ops agree on whom to connect to.** -/
theorem connect_agree {s t : DB Fact} (hs : Inv (family C) s) (ht : Inv (family C) t)
    (qs : s.queue = []) (qt : t.queue = []) (hops : s.ops = t.ops) (c : Id) (e : Key) :
    (allowPeer c e).eval s = (allowPeer c e).eval t := by
  have hs' := connect_iff hs qs c e
  have ht' := connect_iff ht qt c e
  rw [hops] at hs'
  cases h1 : (allowPeer c e).eval s <;> cases h2 : (allowPeer c e).eval t
  · rfl
  · rw [h1] at hs'; rw [h2] at ht'
    exact absurd (hs'.2 (ht'.1 rfl)) (by simp)
  · rw [h1] at hs'; rw [h2] at ht'
    exact absurd (ht'.2 (hs'.1 rfl)) (by simp)
  · rfl

/-- **A removal, once held, cuts off the removed user's node.** Every
device of u is cut, wherever else it is admitted; so a node key that
names only u's devices is refused. A node is let in again only through
a live device under its key (`new_device_trusted`). -/
theorem removal_cuts_off (h : Inv (family C) s) (hq : s.queue = []) {c u : Id} {e : Key}
    (hr : Removed C s.ops c u)
    (only : ∀ u' d, Admitted C s.ops c u' d e → ∃ e', Admitted C s.ops c u d e') :
    (allowPeer c e).eval s = false :=
  refuse_nonmember h hq c e fun u' d ha =>
    let ⟨e', ha'⟩ := only u' d ha
    ⟨u, e', ha', hr⟩
open Engine
variable {C : Crypto}
section
variable {s : DB Fact}

/-- **A new device on a removed user's node is let in
(`new_device_trusted`).** A node whose key names a removed user's device
is let in once a live device is admitted under the same key: the cut
device does not block the node. -/
theorem new_device_trusted (h : Inv (family C) s) (hq : s.queue = []) {c u u2 : Id} {d d2 e : Key}
    (_ha : Admitted C s.ops c u d e) (_hr : Removed C s.ops c u)
    (ha2 : Admitted C s.ops c u2 d2 e) (hl : Live C s.ops c d2) : (allowPeer c e).eval s = true :=
  (connect_iff h hq c e).2 ⟨u2, d2, ha2, hl⟩

/-- At rest, the ids of a user's removals list are its Valid removals. -/
theorem byUser_ids (h : Inv (family C) s) (hq : s.queue = []) (c u x : Id) :
    x ∈ (Engine.eval s (removal.byUser.query [c, u])).rows.map (·.1.2) ↔
      ∃ by_, V C s.ops x (.removal c u by_) := by
  simp only [List.mem_map]
  constructor
  · rintro ⟨pf, hm, rfl⟩
    obtain ⟨y, f, rfl, hv, hk⟩ := (mem_rows h hq (by simp [rels]) _).1 hm
    obtain ⟨r, rfl⟩ := byUser_args.1 hk
    exact ⟨r, hv⟩
  · rintro ⟨r, hv⟩
    exact ⟨_, (mem_rows h hq (by simp [rels]) _).2 ⟨x, _, rfl, hv, byUser_args.2 ⟨r, rfl⟩⟩, rfl⟩

theorem mem_removalsOf (h : Inv (family C) s) (hq : s.queue = []) (c x : Id) (rows : List (Pos × Fact)) :
    x ∈ (removalsOf c rows).eval s ↔
      ∃ p c' u d e k by_, (p, .admission c' u d e k) ∈ rows ∧ V C s.ops x (.removal c u by_) := by
  induction rows with
  | nil => simp [removalsOf, View.eval]
  | cons pf t ih =>
    obtain ⟨p, f⟩ := pf
    cases f with
    | ofAdmission x =>
      obtain ⟨c', u, d, e, k⟩ := x
      show x ∈ View.eval s ((removalsOf c t).bind _) ↔ _
      rw [View.eval_bind']
      simp only [View.eval, List.mem_append, ih, byUser_ids h hq, List.mem_cons, Prod.mk.injEq]
      constructor
      · rintro (⟨r, hv⟩ | ⟨p', c'', u', d', e', k', r, hm, hv⟩)
        · exact ⟨p, c', u, d, e, k, r, Or.inl ⟨rfl, rfl⟩, hv⟩
        · exact ⟨p', c'', u', d', e', k', r, Or.inr hm, hv⟩
      · rintro ⟨p', c'', u', d', e', k', r, ⟨_, he⟩ | hm, hv⟩
        · simp only [Fact.admission.injEq] at he
          obtain ⟨_, rfl, _, _, _⟩ := he
          exact Or.inl ⟨r, hv⟩
        · exact Or.inr ⟨p', c'', u', d', e', k', r, hm, hv⟩
    | _ =>
      show x ∈ (removalsOf c t).eval s ↔ _
      rw [ih]
      constructor
      · rintro ⟨p', c'', u', d', e', k', r, hm, hv⟩; exact ⟨p', c'', u', d', e', k', r, List.mem_cons_of_mem _ hm, hv⟩
      · rintro ⟨p', c'', u', d', e', k', r, hm, hv⟩
        rcases List.mem_cons.1 hm with he | hm
        · simp at he
        · exact ⟨p', c'', u', d', e', k', r, hm, hv⟩

theorem mem_deviceRemovals (h : Inv (family C) s) (hq : s.queue = []) (c x : Id) (rows : List (Pos × Fact)) :
    x ∈ (deviceRemovals c rows).eval s ↔
      ∃ p c' u0 d e k, (p, .admission c' u0 d e k) ∈ rows ∧
        ∃ u e' by_, Admitted C s.ops c u d e' ∧ V C s.ops x (.removal c u by_) := by
  have hdev : ∀ d, x ∈ (removalsOf c (Engine.eval s (admission.byDevice.query [c, d])).rows).eval s ↔
      ∃ u e' by_, Admitted C s.ops c u d e' ∧ V C s.ops x (.removal c u by_) := by
    intro d
    rw [mem_removalsOf h hq]
    constructor
    · rintro ⟨p, c', u, d', e', k', r, hm, hv⟩
      obtain ⟨y, f, he, hy, hk⟩ := (mem_rows h hq (by simp [rels]) _).1 hm
      simp only [Prod.mk.injEq] at he; obtain ⟨_, rfl⟩ := he
      obtain ⟨u'', e'', k'', hf⟩ := byDevice_args.1 hk
      simp only [Fact.admission.injEq] at hf; obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hf
      exact ⟨u, e', r, ⟨y, k', hy⟩, hv⟩
    · rintro ⟨u, e', r, ⟨y, k', hy⟩, hv⟩
      exact ⟨_, c, u, d, e', k', r, (mem_rows h hq (by simp [rels]) _).2
        ⟨y, _, rfl, hy, byDevice_args.2 ⟨u, e', k', rfl⟩⟩, hv⟩
  induction rows with
  | nil => simp [deviceRemovals, View.eval]
  | cons pf t ih =>
    obtain ⟨p, f⟩ := pf
    cases f with
    | ofAdmission x =>
      obtain ⟨c', u0, d, e, k⟩ := x
      show x ∈ View.eval s ((removalsOf c _).bind _) ↔ _
      rw [View.eval_bind', View.eval_bind']
      simp only [View.eval, List.mem_append, ih, hdev, List.mem_cons, Prod.mk.injEq]
      constructor
      · rintro (hm | ⟨p', c'', u0', d', e', k', hm, rest⟩)
        · exact ⟨p, c', u0, d, e, k, Or.inl ⟨rfl, rfl⟩, hm⟩
        · exact ⟨p', c'', u0', d', e', k', Or.inr hm, rest⟩
      · rintro ⟨p', c'', u0', d', e', k', ⟨_, he⟩ | hm, rest⟩
        · simp only [Fact.admission.injEq] at he
          obtain ⟨_, _, rfl, _, _⟩ := he
          exact Or.inl rest
        · exact Or.inr ⟨p', c'', u0', d', e', k', hm, rest⟩
    | _ =>
      show x ∈ (deviceRemovals c t).eval s ↔ _
      refine ih.trans ⟨?_, ?_⟩
      · rintro ⟨p', c'', u0', d', e', k', hm, rest⟩
        exact ⟨p', c'', u0', d', e', k', List.mem_cons_of_mem _ hm, rest⟩
      · rintro ⟨p', c'', u0', d', e', k', hm, rest⟩
        rcases List.mem_cons.1 hm with he | hm
        · simp at he
        · exact ⟨p', c'', u0', d', e', k', hm, rest⟩

/-- **The notices owed to a node (`removals_at`).** At rest,
`removalsAt c e` lists exactly the Valid removals that cut a device
admitted under e: removals of any user such a device is admitted into,
under any key. -/
theorem removals_at (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (e : Key) (x : Id) :
    x ∈ (removalsAt c e).eval s ↔
      ∃ u0 d u e' by_, Admitted C s.ops c u0 d e ∧ Admitted C s.ops c u d e' ∧
        V C s.ops x (.removal c u by_) := by
  unfold removalsAt
  rw [View.eval_bind]
  simp only [Rel.read, View.eval_read]
  rw [mem_deviceRemovals h hq]
  constructor
  · rintro ⟨p, c', u0, d, e'', k'', hm, u, e', r, ha, hv⟩
    obtain ⟨y, f, he, hy, hk⟩ := (mem_rows h hq (by simp [rels]) _).1 hm
    simp only [Prod.mk.injEq] at he; obtain ⟨_, rfl⟩ := he
    obtain ⟨u'', d'', k3, hf⟩ := byKey_args.1 hk
    simp only [Fact.admission.injEq] at hf; obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hf
    exact ⟨u0, d, u, e', r, ⟨y, k'', hy⟩, ha, hv⟩
  · rintro ⟨u0, d, u, e', r, ⟨y, k, hy⟩, ha, hv⟩
    exact ⟨_, c, u0, d, e, k, (mem_rows h hq (by simp [rels]) _).2
      ⟨y, _, rfl, hy, byKey_args.2 ⟨u0, d, k, rfl⟩⟩, u, e', r, ha, hv⟩

theorem deviceLive_eval (c : Id) (d : Key) : (deviceLive c d).eval s =
    if (Engine.eval s (admission.byDevice.query [c, d])).rows.isEmpty then false
    else (unremoved c (Engine.eval s (admission.byDevice.query [c, d])).rows).eval s := by
  unfold deviceLive
  rw [View.eval_bind]
  by_cases he : (Engine.eval s (admission.byDevice.query [c, d])).rows.isEmpty = true
  · simp only [Rel.read, View.eval_read, he, ite_true]; rfl
  · simp only [Rel.read, View.eval_read, he, ite_false, Bool.false_eq_true]

/-- With no rows of d's admissions, d is admitted nowhere in c. -/
theorem not_admitted_of_empty (h : Inv (family C) s) (hq : s.queue = []) {c : Id} {d : Key}
    (he : (Engine.eval s (admission.byDevice.query [c, d])).rows.isEmpty = true) :
    ∀ u e, ¬ Admitted C s.ops c u d e := by
  rintro u e ⟨y, k, hy⟩
  obtain ⟨p, hp⟩ := (exists_row h hq (by simp [rels]) [c, d] _).2 ⟨y, hy, byDevice_args.2 ⟨u, e, k, rfl⟩⟩
  rw [List.isEmpty_iff] at he; rw [he] at hp; cases hp

/-- At rest, d's admissions counted are nonzero exactly when d is admitted. -/
theorem admitted_total (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (d : Key) :
    (Engine.eval s (admission.byDevice.query [c, d] (limit := some 0))).total ≠ 0 ↔
      ∃ u e, Admitted C s.ops c u d e := by
  rw [← Nat.pos_iff_ne_zero,
    total_rel (fam := family C) rfl rels_distinct (by simp [rels]) (rels_short _ (by simp [rels])) h hq]
  constructor
  · rintro ⟨y, f, hv, hk⟩
    obtain ⟨u, e, k, rfl⟩ := byDevice_args.1 hk
    exact ⟨u, e, y, k, hv⟩
  · rintro ⟨u, e, y, k, hv⟩
    exact ⟨y, _, hv, byDevice_args.2 ⟨u, e, k, rfl⟩⟩

theorem standing_eval (c : Id) (d : Key) (joins : List (Pos × Fact)) :
    (standing c d joins).eval s =
      if (Engine.eval s (secret.byKey.query [d] (limit := some 0))).total = 0 then none
      else if (Engine.eval s (admission.byDevice.query [c, d])).rows.isEmpty then
        (if (waiting c d joins).eval s then some false else none)
      else if (deviceLive c d).eval s then some true else none := by
  rw [deviceLive_eval]
  unfold standing
  rw [eval_list]
  by_cases h0 : (Engine.eval s (secret.byKey.query [d] (limit := some 0))).total = 0
  · simp only [h0, ite_true]; rfl
  · simp only [h0, ite_false]
    rw [eval_list]
    by_cases he : (Engine.eval s (admission.byDevice.query [c, d])).rows.isEmpty = true
    · simp only [he, ite_true]; rw [View.eval_bind']; rfl
    · simp only [he, ite_false, Bool.false_eq_true]; rw [View.eval_bind']; rfl

/-- What a held acceptance's standing says of its device: admitted and
live, or not admitted at all. -/
theorem standing_some (h : Inv (family C) s) (hq : s.queue = []) {c : Id} {d : Key}
    {joins : List (Pos × Fact)} {adm : Bool} (hs : (standing c d joins).eval s = some adm) :
    Live C s.ops c d ∨ ∀ u e, ¬ Admitted C s.ops c u d e := by
  rw [standing_eval] at hs
  split at hs
  · cases hs
  · split at hs
    · rename_i he; exact Or.inr (not_admitted_of_empty h hq he)
    · split at hs
      · rename_i hl; exact Or.inl ((deviceLive_iff h hq c d).1 hl)
      · cases hs

/-- A cut device's acceptance is not held. -/
theorem standing_cut (h : Inv (family C) s) (hq : s.queue = []) {c : Id} {d : Key}
    (joins : List (Pos × Fact)) (hc : Cut C s.ops c d) : (standing c d joins).eval s = none := by
  rw [standing_eval]
  split
  · rfl
  · have ⟨u, e, ha, _⟩ := hc
    have hne : (Engine.eval s (admission.byDevice.query [c, d])).rows.isEmpty = false := by
      cases he : (Engine.eval s (admission.byDevice.query [c, d])).rows.isEmpty
      · rfl
      · exact absurd ha (not_admitted_of_empty h hq he u e)
    rw [if_neg (by simp [hne])]
    have hl : (deviceLive c d).eval s = false := by
      cases hd : (deviceLive c d).eval s
      · rfl
      · exact absurd ((deviceLive_iff h hq c d).1 hd) (cut_not_live hc)
    rw [hl]; rfl

theorem pick_some {c : Id} {joins : List (Pos × Fact)} :
    ∀ {rows : List (Pos × Fact)} {d : Key} {a : Id} {adm : Bool},
      (pick c joins rows).eval s = some (d, a, adm) →
      ∃ k, ((k, a), Fact.accepted c d) ∈ rows ∧ (standing c d joins).eval s = some adm
  | [], _, _, _, hp => by cases hp
  | ((k, aid), f) :: t, d, a, adm, hp => by
    cases f with
    | ofAccepted x =>
      obtain ⟨c', d'⟩ := x
      by_cases hc : c' = c
      · subst hc
        have hp' : (match (standing c' d' joins).eval s, (pick c' joins t).eval s with
            | some adm', some b => some (better (d', aid, adm') b)
            | some adm', none => some (d', aid, adm')
            | none, r => r) = some (d, a, adm) := by
          have := hp
          simp only [pick, ite_true] at this
          rw [View.eval_bind', View.eval_bind'] at this
          exact this
        have tail : ∀ {d a adm}, (pick c' joins t).eval s = some (d, a, adm) →
            ∃ k', ((k', a), Fact.accepted c' d) ∈ ((k, aid), Fact.accepted c' d') :: t ∧
              (standing c' d joins).eval s = some adm := by
          intro d a adm ht
          obtain ⟨k', hm, hs⟩ := pick_some ht
          exact ⟨k', List.mem_cons_of_mem _ hm, hs⟩
        cases hst : (standing c' d' joins).eval s with
        | none => rw [hst] at hp'; exact tail hp'
        | some adm' =>
          cases hr : (pick c' joins t).eval s with
          | none =>
            rw [hst, hr] at hp'
            simp only [Option.some.injEq, Prod.mk.injEq] at hp'
            obtain ⟨rfl, rfl, rfl⟩ := hp'
            exact ⟨k, List.mem_cons_self .., hst⟩
          | some b =>
            rw [hst, hr] at hp'
            simp only [Option.some.injEq] at hp'
            rcases better_cases (d', aid, adm') b with hb | hb
            · rw [hb] at hp'
              simp only [Prod.mk.injEq] at hp'
              obtain ⟨rfl, rfl, rfl⟩ := hp'
              exact ⟨k, List.mem_cons_self .., hst⟩
            · rw [hb] at hp'; subst hp'; exact tail hr
      · have : (pick c joins (((k, aid), Fact.accepted c' d') :: t)).eval s = (pick c joins t).eval s := by
          simp only [pick, if_neg hc]
        rw [this] at hp
        obtain ⟨k', hm, hs⟩ := pick_some hp
        exact ⟨k', List.mem_cons_of_mem _ hm, hs⟩
    | _ =>
      obtain ⟨k', hm, hs⟩ := pick_some (rows := t) hp
      exact ⟨k', List.mem_cons_of_mem _ hm, hs⟩

theorem pick_none {c : Id} {joins : List (Pos × Fact)} :
    ∀ {rows : List (Pos × Fact)},
      (∀ k a d, ((k, a), Fact.accepted c d) ∈ rows → (standing c d joins).eval s = none) →
      (pick c joins rows).eval s = none
  | [], _ => rfl
  | ((k, aid), f) :: t, hall => by
    have ht := pick_none (rows := t) fun k a d hm => hall k a d (List.mem_cons_of_mem _ hm)
    cases f with
    | ofAccepted x =>
      obtain ⟨c', d'⟩ := x
      by_cases hc : c' = c
      · subst hc
        simp only [pick, ite_true]
        rw [View.eval_bind', View.eval_bind', hall k aid d' (List.mem_cons_self ..), ht]
        rfl
      · simp only [pick, if_neg hc]; exact ht
    | _ => exact ht

/-- **A removed entry is not held (`mine_not_removed`).** At rest, the
device `mine c` names is live, or not admitted at all (a join still
waiting): never a cut device. -/
theorem mine_not_removed (h : Inv (family C) s) (hq : s.queue = []) {c : Id} {d : Key} {a : Id}
    (hm : (mine c).eval s = some (d, a)) : Live C s.ops c d ∨ ∀ u e, ¬ Admitted C s.ops c u d e := by
  have hm' : ((pick c (Engine.eval s (joining.all.query [])).rows
      (Engine.eval s (accepted.all.query [])).rows).eval s).map (fun (d, a, _) => (d, a)) =
      some (d, a) := by
    have := hm
    unfold mine at this
    rw [show ∀ q (k : Answer Fact → View Fact _), View.eval s (.list q k) = View.eval s (k (Engine.eval s q))
      from fun _ _ => rfl, show ∀ q (k : Answer Fact → View Fact _), View.eval s (.list q k) =
      View.eval s (k (Engine.eval s q)) from fun _ _ => rfl, View.eval_bind'] at this
    exact this
  obtain ⟨⟨d', a', adm⟩, hp, he⟩ := Option.map_eq_some_iff.1 hm'
  simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
  obtain ⟨_, _, hs⟩ := pick_some hp
  exact standing_some h hq hs

/-- **Rejoining is a fresh join (`rejoin_fresh`).** At rest, on a node
holding its key, if every acceptance of the link's community held here
is of a cut device, every join of it here is of an admitted device (so
none is waiting), and the new seed's device is not admitted, `join`
writes a fresh join: the new seed's secret, its request from this
node's key, acceptance and pending join. The request is for the new
seed's device, never the cut one (`joinOps_travels`). -/
theorem rejoin_fresh (h : Inv (family C) s) (hq : s.queue = []) {i : Invite}
    {seed name key : ByteArray} {fresh sk : Key32} (hk : nodeKey.eval s = some (key, sk))
    (hacc : ∀ x d, V C s.ops x (.accepted i.community d) → Cut C s.ops i.community d)
    (hjoin : ∀ x k hs r nm d n, V C s.ops x (.joining i.community k hs r nm d n) →
      ∃ u e, Admitted C s.ops i.community u d e)
    (hnew : ∀ u e, ¬ Admitted C s.ops i.community u (Device.ofSeed seed).pk e) :
    ((join i seed name fresh).eval s).ops = (joinOps i seed name key).ops := by
  have hmine : (mine i.community).eval s = none := by
    show ((pick i.community _ _).bind _).eval s = none
    rw [View.eval_bind', pick_none]
    · rfl
    · intro k a d hm
      obtain ⟨y, f, he, hv, _⟩ := (mem_rows h hq (by simp [rels]) _).1 hm
      simp only [Prod.mk.injEq] at he; obtain ⟨⟨_, _⟩, rfl⟩ := he
      exact standing_cut h hq _ (hacc _ d hv)
  have hdorm : (dormant i.community (Engine.eval s (joining.all.query [])).rows).eval s = none :=
    dormant_none fun p k hs r nm d n hm => by
      obtain ⟨y, f, he, hv, _⟩ := (mem_rows h hq (by simp [rels]) _).1 hm
      simp only [Prod.mk.injEq] at he; obtain ⟨_, rfl⟩ := he
      exact (admitted_total h hq _ d).2 (hjoin y k hs r nm d n hv)
  have hz : (Engine.eval s (admission.byDevice.query [i.community, (Device.ofSeed seed).pk]
      (limit := some 0))).total = 0 :=
    Decidable.of_not_not fun hne => by
      obtain ⟨u, e, ha⟩ := (admitted_total h hq _ _).1 hne
      exact hnew u e ha
  unfold join
  rw [View.eval_bind', hmine]
  simp only [Option.isSome_none, Bool.false_eq_true, ite_false]
  rw [eval_list, View.eval_bind', hdorm, eval_list]
  simp only [hz, ne_eq, not_true_eq_false, ite_false]
  rw [View.eval_bind', nodeKeyOr_held hk]
  rfl

/-- **A join never asks for an admitted device (`join_new_device`).** At
rest, every request `join` writes is for a device with no admission in
the link's community: never a cut device, whatever seed is passed. -/
theorem join_new_device (h : Inv (family C) s) (hq : s.queue = []) {i : Invite}
    {seed name : ByteArray} {fresh : Key32} {o : Op} {d e cs bs : ByteArray}
    (ho : o ∈ ((join i seed name fresh).eval s).ops)
    (hb : (Codec.decode o.body : Option Body) = some (.request d e cs bs)) :
    ∀ u e', ¬ Admitted C s.ops i.community u d e' := by
  unfold join at ho
  rw [View.eval_bind'] at ho
  split at ho
  · cases ho
  · rw [eval_list, View.eval_bind'] at ho
    split at ho
    · simp only [View.eval, List.mem_singleton] at ho
      subst ho; rw [body_mkOp] at hb; cases hb
    · rw [eval_list] at ho
      split at ho
      · cases ho
      · rename_i hz
        rw [View.eval_bind'] at ho
        simp only [View.eval, List.mem_append] at ho
        rcases ho with ho | ho
        · -- the node's key, if it had none: not a request
          unfold nodeKeyOr at ho
          rw [View.eval_bind'] at ho
          split at ho
          · cases ho
          · simp only [View.eval, List.mem_singleton] at ho
            subst ho; rw [body_endpoint] at hb; cases hb
        · simp only [joinOps, Invite.request, Community.request, secret, accept, joining,
            List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ho
          rcases ho with rfl | rfl | rfl | rfl
          · rw [body_mkOp] at hb; cases hb
          · rw [body_mkOp] at hb
            simp only [Option.some.injEq, Body.request.injEq] at hb
            obtain ⟨rfl, _, _, _⟩ := hb
            intro u e' ha
            exact hz ((admitted_total h hq _ _).2 ⟨u, e', ha⟩)
          · rw [body_mkOp] at hb; cases hb
          · rw [body_mkOp] at hb; cases hb
end
open Engine
variable {C : Crypto}

/-- **Removed stays removed (`removed_stays_removed`).** Whatever is
written after, the rejoining node's new device and its admission
included: u stays removed, every device ever admitted into u is cut, and
every key `allowPeer` lets in is let in for a live device that was never
u's. -/
theorem removed_stays_removed {s s' : DB Fact} (h' : Inv (family C) s') (hq' : s'.queue = [])
    {c u : Id} (he : Extends s.ops s'.ops) (hr : Removed C s.ops c u) :
    Removed C s'.ops c u ∧
      (∀ d e, Admitted C s'.ops c u d e → Cut C s'.ops c d ∧ ¬ Live C s'.ops c d) ∧
      ∀ e, (allowPeer c e).eval s' = true →
        ∃ u' d, Admitted C s'.ops c u' d e ∧ Live C s'.ops c d ∧ ∀ e', ¬ Admitted C s'.ops c u d e' := by
  have hr' := removed_stays he hr
  refine ⟨hr', fun d e ha => ⟨⟨u, e, ha, hr'⟩, cut_not_live ⟨u, e, ha, hr'⟩⟩, fun e hp => ?_⟩
  obtain ⟨u', d, ha, hl⟩ := (connect_iff h' hq' c e).1 hp
  exact ⟨u', d, ha, hl, fun e' hu => hl.2 u e' hu hr'⟩
open Engine Engine.View

/-- **An approval writes at most three ops**: the approval, the
admission it gives, and one wrap of the key to the new member's node
key, whatever the community holds. -/
theorem approveReq_ops (c req myAdm : Id) (d : Device) (esk : ByteArray) :
    Always (fun w : Write => w.ops.length ≤ 3) (approveReq c req myAdm d esk) := by
  unfold approveReq
  refine always_bind fun _ => always_bind fun _ => always_bind (always_true fun _ => ?_)
  dsimp only
  repeat' split
  all_goals (try simp only [Always, pure_eq])
  all_goals (repeat' split)
  all_goals simp

/-- **An approval wraps the community's key, and only beside its
admission.** Whatever the store holds, an approval's write is the
approval alone; or the approval, then the admission citing exactly it
(`admit_admits`: Valid when the approval is); or those two, then one
wrap by the approving device of the key `currentKey` reads (the key
under the id c's root names: `currentKey_community`), to the node key
of the request it approves, citing that admission as its recipient's.
So no approval wraps a key to a requester the same write does not
admit, and none wraps any key but the community's. -/
theorem approveReq_wrap_admits (s : DB Fact) (c req myAdm : Id) (d : Device) (esk : ByteArray) :
    let ok := approve c req myAdm d
    let adm := admit c req ok.id
    ((approveReq c req myAdm d esk).eval s).ops = [ok] ∨
      ((approveReq c req myAdm d esk).eval s).ops = [ok, adm] ∨
      ∃ k esk' e, (currentKey c).eval s = some k ∧
        ((approveReq c req myAdm d esk).eval s).ops = [ok, adm, wrapKey c myAdm adm.id d k esk' e] := by
  intro ok adm
  simp only [approveReq, View.eval_bind, View.eval_read]
  split
  · simp only [View.eval_pure]
    split
    · rename_i k esk' hk _
      exact Or.inr (Or.inr ⟨k, esk', _, hk, rfl⟩)
    · exact Or.inr (Or.inl (by simp [ok, adm]))
  · exact Or.inl rfl

/-- The mutant: an approval that wraps the key to every member. -/
def approveWrapAll (c req myAdm : Id) (d : Device) (esk : Key32) : View Fact Write := do
  let ok := approve c req myAdm d
  let ks ← key.byCommunity.read [c] (limit := some 1)
  let rs ← recipients c
  return ⟨ok :: (match ks.rows.head? with
    | some (_, .key _ _ k) => match Bytes.of? k with
      | some k => rs.map (wrapKey c myAdm c d k esk)
      | none => []
    | _ => [])⟩

/-- **Wrapping to every member is over the budget**: a community of
three members makes four ops. -/
theorem wrapAll_over (c req myAdm : Id) (d : Device) (esk : Key32) (p : Pos) (kid : ByteArray) (k : Key32)
    (u₁ u₂ u₃ : Id) (d₁ d₂ d₃ e₁ e₂ e₃ : Key) :
    ¬ Always (fun w : Write => w.ops.length ≤ 3) (approveWrapAll c req myAdm d esk) := by
  intro h
  let none0 : Answer Fact := ⟨[], 0, 0⟩
  -- the key; c's admissions; then, per member, its device's admissions
  -- (it is live: one, into a user) and that user's removals (none)
  let dev (u : Id) (d e : Key) : Answer Fact := ⟨[(p, .admission c u d e kid)], 1, 1⟩
  have := always_runWith [⟨[(p, .key c kid k.1)], 1, 1⟩,
    ⟨[(p, .admission c u₁ d₁ e₁ kid), (p, .admission c u₂ d₂ e₂ kid), (p, .admission c u₃ d₃ e₃ kid)], 3, 3⟩,
    dev u₁ d₁ e₁, none0, dev u₂ d₂ e₂, none0, dev u₃ d₃ e₃, none0] h (by
      simp only [approveWrapAll, recipients, live, deviceLive, unremoved, removals, Rel.read, View.read,
        bind_eq, pure_eq, View.bind, ite_true, runWith, none0, dev, List.isEmpty_cons,
        Bool.false_eq_true, ite_false]
      rfl)
  simp [Bytes.of?_val] at this
open Engine Codec
section
variable {s : DB Fact} {C : Crypto}

/-- Renaming a receipt list's rows by their messages (`asMsg`) keeps
them in order: a receipt's sort key names its message (`recKey_inj`),
so two rows level on it name one message. -/
theorem asMsg_sorted (h : Inv (family C) s) (hq : s.queue = []) {c kid : ByteArray} {lim : Option Nat}
    {desc : Bool} {after before : Option Pos} :
    let a := Engine.eval s (received.byKey.query [c, kid] lim desc after before)
    (orient desc (a.rows.map asMsg)).Pairwise (fun p q => posLE p q = true) := by
  intro a
  have ho : (orient desc a.rows).Pairwise (fun p q => posLE p q = true) :=
    eval_oriented s (received.byKey.query [c, kid] lim desc after before)
  rw [orient_map, List.pairwise_map]
  refine ho.imp_of_mem fun {x y} hx hy hxy => ?_
  have row : ∀ {r}, r ∈ orient desc a.rows →
      ∃ k m z clump, r = ((recKey k m, z), .received c kid m k clump) := fun {r} hr => by
    obtain ⟨he, _, hargs⟩ := row_at (C := C) (r := received.byKey) (by simp [rels]) h hq (mem_orient.1 hr)
    obtain ⟨⟨sk, z⟩, f⟩ := r
    cases f with
    | ofReceived x =>
      obtain ⟨c', kid', m, k, clump⟩ := x
      simp only [received.byKey, Option.some.injEq, List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      exact ⟨k, m, z, clump, by simpa [SortKey.sortOf, sortOf] using he⟩
    | _ => simp [received.byKey] at hargs
  obtain ⟨k, m, z, clump, rfl⟩ := row hx
  obtain ⟨k', m', z', clump', rfl⟩ := row hy
  rw [posLE_iff] at hxy ⊢
  simp only [asMsg, Pos.cmp] at hxy ⊢
  cases e : bcmp (recKey k m) (recKey k' m')
  · simp
  · rw [recKey_inj (bcmp_eq e), (bcmp_eq_iff m' m').2 rfl]; simp
  · simp [e] at hxy

/-- **A channel's list is a strict total order on its messages.**
`readable`'s rows are in its order, newest first or oldest first as
asked, and two rows naming different messages are never level: one is
strictly before the other (with equal counter and time, by id:
`msg_cmp`). Sorting before is a strict total order on positions
(`Pos.cmp_eq_iff`, `Pos.cmp_swap`, `Pos.cmp_lt_trans`). Nothing sorts it:
each of its lists comes in order (`eval_oriented`, `asMsg_sorted`) and
the union merges them (`union_sorted`). -/
theorem order_total (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (lim : Option Nat) (desc : Bool)
    (after before : Option Pos) :
    ((readable c lim desc after before).eval s).rows.Pairwise (InOrder desc) := by
  rw [eval_readable]
  simp only
  have hu := union_sorted (desc := desc) (limit := lim) (F := Fact) (as :=
    ((heldKids c).eval s).map (fun kid => Engine.eval s (message.byKey.query [c, kid] lim desc after before)) ++
      ((heldKids c).eval s).map fun kid =>
        let a := Engine.eval s (received.byKey.query [c, kid] lim desc (after.map afterRec)
          (before.map beforeRec))
        { a with rows := a.rows.map asMsg }) (fun a ha => by
    rcases List.mem_append.1 ha with ha | ha
    · obtain ⟨kid, _, rfl⟩ := List.mem_map.1 ha
      exact eval_oriented s (message.byKey.query [c, kid] lim desc after before)
    · obtain ⟨kid, _, rfl⟩ := List.mem_map.1 ha
      exact asMsg_sorted h hq)
  have one : ∀ a b : Pos × Fact, Pos.cmp a.1 b.1 ≠ .gt → InOrder false a b := fun a b h =>
    ⟨h, fun hne => strict_of h fun e => hne (congrArg Prod.snd e)⟩
  rw [← orient_orient desc (unionAnswers ..).rows]
  generalize orient desc (unionAnswers ..).rows = l at hu ⊢
  cases desc
  · exact hu.imp fun {a b} h => one a b (posLE_iff.1 h)
  · simp only [orient, ite_true]
    rw [List.pairwise_reverse]
    refine hu.imp fun {a b} h => ?_
    have h := posLE_iff.1 h
    exact ⟨h, fun hne => strict_of h fun e => hne (congrArg Prod.snd e).symm⟩

/-- Every row of a channel's list is a listed message, at its place. -/
theorem readable_listed (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (lim : Option Nat) (desc : Bool)
    (after before : Option Pos) {pf : Pos × Fact} (hp : pf ∈ ((readable c lim desc after before).eval s).rows) :
    Listed C s.ops c pf.1.2 pf.1.1 := by
  obtain ⟨u, d, kid, sealed, n, tm, clump, hv, _, hw⟩ := readable_held h hq c lim desc after before hp
  rcases hw with ⟨hn, he⟩ | ⟨_, z, k, hz, he⟩
  · exact .inl ⟨u, d, kid, sealed, n, tm, clump, hv, hn, by rw [he]⟩
  · exact .inr ⟨z, kid, k, clump, hz, by rw [he]⟩

/-- **`send`'s counter is past every message's.** The counter it starts
from is at least every Valid message's of c, capped. -/
theorem topCount_ge (h : Inv (family C) s) (hq : s.queue = []) {c y : Id} {u d kid sealed : ByteArray}
    {clump : Option Id} {n tm : Nat} (hv : V C s.ops y (.message c u d kid sealed n tm clump)) :
    min n countCap ≤ (topCount c).eval s := by
  obtain ⟨y', f', ht, _, ha', hle⟩ :=
    first_after (r := message.all) (as := [c]) (by simp [rels]) h hq hv (by simp [message.all])
  cases f' with
  | ofMessage x => ?_
  | _ => simp [message.all] at ha'
  obtain ⟨c', u', d', kid', sealed', n', tm', clump'⟩ := x
  have hc : (topCount c).eval s = min n' countCap := by
    simp only [topCount, Rel.read, View.eval_bind, View.eval_read, View.eval_pure, ht]
  rw [hc]
  rw [msg_cmp] at hle
  refine Nat.not_lt.1 fun hlt => hle ?_
  rw [Nat.compare_eq_gt.2 hlt]; rfl

/-- **A receipt's counter is past every held receipt's.** -/
theorem topReceived_ge (h : Inv (family C) s) (hq : s.queue = []) {c z : Id} {kid m : ByteArray} {j : Nat} {clump : Option Id}
    (hall : ∀ z kid m j clump, V C s.ops z (.received c kid m j clump) → j < 2 ^ 64)
    (hv : V C s.ops z (.received c kid m j clump)) :
    j ≤ (topReceived c).eval s ∧ ∃ z' kid' m' clump', V C s.ops z' (.received c kid' m' ((topReceived c).eval s) clump') := by
  obtain ⟨y', f', ht, hv', ha', hle⟩ :=
    first_after (r := received.all) (as := [c]) (by simp [rels]) h hq hv (by simp [received.all])
  cases f' with
  | ofReceived x => ?_
  | _ => simp [received.all] at ha'
  obtain ⟨c', kid', m', j', clump'⟩ := x
  simp [received.all] at ha'
  subst ha'
  have hc : (topReceived c').eval s = j' := by
    simp only [topReceived, Rel.read, View.eval_bind, View.eval_read, View.eval_pure, ht]
  rw [hc]
  refine ⟨?_, y', kid', m', clump', hv'⟩
  have e : Pos.cmp (sortOf (Fact.received c' kid m j clump), z) (sortOf (Fact.received c' kid' m' j' clump'), y') =
      ((compare j j').then (bcmp m m')).then (bcmp z y') := by
    show (bcmp (recKey j m) (recKey j' m')).then (bcmp z y') = _
    rw [bcmp_recKey (hall _ _ _ _ _ hv) (hall _ _ _ _ _ hv')]
  rw [e] at hle
  refine Nat.not_lt.1 fun hlt => hle ?_
  rw [Nat.compare_eq_gt.2 hlt]; rfl

/-- The counter `receiptFor` writes is past every held receipt's in c,
and below 2^64 while every held one's successor is. -/
theorem receipt_past (h : Inv (family C) s) (hq : s.queue = []) {c : Id}
    (hk : ∀ z kid m j clump, V C s.ops z (.received c kid m j clump) → j + 1 < 2 ^ 64) :
    (topReceived c).eval s + 1 < 2 ^ 64 ∧
      ∀ z kid m j clump, V C s.ops z (.received c kid m j clump) → Pos.cmp (recKey j m, m) (recKey ((topReceived c).eval s + 1) m', m') = .lt := by
  have hall : ∀ z kid m j clump, V C s.ops z (.received c kid m j clump) → j < 2 ^ 64 :=
    fun z kid m j clump hv => Nat.lt_of_succ_lt (hk z kid m j clump hv)
  have hb : (topReceived c).eval s + 1 < 2 ^ 64 := by
    simp only [topReceived, Rel.read, View.eval_bind, View.eval_read, View.eval_pure]
    cases ht : (Engine.eval s (received.all.query [c] (some 1))).rows.head? with
    | none => decide
    | some t =>
      obtain ⟨⟨sk, z⟩, f⟩ := t
      obtain ⟨_, hv, ha⟩ := row_at (C := C) (r := received.all) (by simp [rels]) h hq (List.mem_of_mem_head? ht)
      cases f with
      | ofReceived x =>
        obtain ⟨c', kid, m, j, clump⟩ := x
        simp [received.all] at ha; subst ha
        exact hk _ _ _ _ _ hv
      | _ => simp [received.all] at ha
  refine ⟨hb, fun z kid m j clump hv => ?_⟩
  have hj := (topReceived_ge h hq hall hv).1
  rw [Pos.cmp, bcmp_recKey (hall _ _ _ _ _ hv) hb, Nat.compare_eq_lt.2 (by omega)]
  rfl

/-- **One receipt per message.** A device holding a receipt of o writes
no other. -/
theorem receipt_once (h : Inv (family C) s) (hq : s.queue = []) {o : Op} {z : Id} {c kid : ByteArray} {j : Nat} {clump : Option Id}
    (hz : V C s.ops z (.received c kid o.id j clump)) : (receiptFor o).eval s = [] := by
  have hpos : (Engine.eval s (received.byMsg.query [o.id] (some 0))).total ≠ 0 := by
    have hf := (filed (C := C) (r := received.byMsg) (by simp [rels]) h hq [o.id] z _).2
      ⟨hz, by simp [received.byMsg]⟩
    show (matching s _).length ≠ 0
    rw [matching_also_nil _ rfl]
    exact Nat.pos_iff_ne_zero.1 (List.length_pos_iff_exists_mem.2 ⟨_, (mem_matching _ _).2 ⟨z, _, rfl, hf.1, hf.2⟩⟩)
  unfold receiptFor
  by_cases hk : o.kind ≠ 23
  · simp [hk]
  simp only [hk, ite_false]
  split
  · rename_i n _ _ _
    by_cases hn : n < countCap
    · simp [hn]
    · simp [hn, Rel.read, View.eval_bind, hpos]
  · rfl

/-- What `receiptFor` writes for a saturated post it holds no receipt of:
one receipt, one past the newest in the post's community. -/
theorem receipt_post (h : Inv (family C) s) (hq : s.queue = []) {o : Op} {kid sealed sig : ByteArray}
    {n tm : Nat} (hkind : o.kind = 23) (hb : (decode o.body : Option Body) = some (.post kid sealed n tm sig))
    (hn : countCap ≤ n) (hnew : s.ops o.id = none) :
    (receiptFor o).eval s = [receipt o.id ((topReceived (o.reqs.headD .empty)).eval s + 1)] := by
  have hzero : (Engine.eval s (received.byMsg.query [o.id] (some 0))).total = 0 := by
    show (matching s _).length = 0
    rw [List.length_eq_zero_iff, List.eq_nil_iff_forall_not_mem]
    intro pf hp
    rw [matching_also_nil _ rfl, mem_matching] at hp
    obtain ⟨z, f, rfl, hz, hf⟩ := hp
    obtain ⟨hv, ha⟩ := (filed (C := C) (r := received.byMsg) (by simp [rels]) h hq [o.id] z f).1 ⟨hz, hf⟩
    cases f <;> (try (rename_i x; cases x)) <;> simp [received.byMsg] at ha
    subst ha
    obtain ⟨_, _, _, _, _, _, _, _, _, hm⟩ := received_of_message hv
    obtain ⟨o', _, _, hx, _⟩ := valid_inv hm
    rw [hnew] at hx; cases hx
  unfold receiptFor
  rw [hb]
  simp [hkind, Nat.not_lt.2 hn, Rel.read, View.eval_bind, hzero]

/-- **Past the cap, a channel is in this device's arrival order.** A
receipt `receiptFor` writes for op o sorts after every receipt this device
held in o's community when it wrote it, so saturated messages are listed
in the order this device received them (`readable_held`), at the grain
of its writes: receipts written in one write read the same receipts, so
they share a counter and fall back on their messages' ids. The counter
must stay below 2^64: the device has received fewer saturated messages
there. -/
theorem arrival_order (h : Inv (family C) s) (hq : s.queue = []) (o : Op)
    (hk : ∀ z kid m j clump, V C s.ops z (.received (o.reqs.headD .empty) kid m j clump) → j + 1 < 2 ^ 64)
    {r : Op} (hr : r ∈ (receiptFor o).eval s) :
    ∃ j, r = receipt o.id j ∧ ∀ z kid m j' clump, V C s.ops z (.received (o.reqs.headD .empty) kid m j' clump) →
      Pos.cmp (recKey j' m, m) (recKey j o.id, o.id) = .lt := by
  refine ⟨(topReceived (o.reqs.headD .empty)).eval s + 1, ?_, (receipt_past h hq hk).2⟩
  unfold receiptFor at hr
  by_cases hkind : o.kind ≠ 23
  · simp [hkind] at hr
  simp only [hkind, ite_false] at hr
  split at hr
  · rename_i n _ _ _
    by_cases hn : n < countCap
    · simp [hn] at hr
    · simp only [hn, Rel.read, View.eval_bind, View.eval_read, ite_false] at hr
      by_cases ht : (Engine.eval s (received.byMsg.query [o.id] (some 0))).total ≠ 0
      · simp [ht] at hr
      · simp only [ht, ite_false, View.eval_bind, View.eval_pure, List.mem_singleton] at hr
        exact hr
  · simp at hr

/-- **What `send` writes sorts after everything the device lists in
that channel.** The post `send` writes (the first op of its write)
claims a counter n. If the post is new to this store, then below the
cap it sorts at its own key, and past it at the receipt the same write
holds; either way after every message this device lists in c when it
writes (`Listed`, which every row of `readable c` is). The receipt
counter must stay below 2^64, as in `arrival_order`. -/
theorem send_after (h : Inv (family C) s) (hq : s.queue = []) (c myAdm : Id) (d : Device) (k : Key32) (nonce : Nonce24)
    (text : ByteArray)
    (now : Nat) (files : List NewFile)
    (hk : ∀ z kid m j clump, V C s.ops z (.received c kid m j clump) → j + 1 < 2 ^ 64) :
    let group := (Clump.choose c myAdm now).eval s
    ∃ n, ((send c myAdm d k nonce text now files).eval s).ops.head? =
        some (sealedPost c myAdm d k nonce text n now group) ∧
      (s.ops (sealedPost c myAdm d k nonce text n now group).id = none →
        ∃ sk, (n < countCap ∧ sk = msgKey n now ∨
            ∃ j, receipt (sealedPost c myAdm d k nonce text n now group).id j ∈
              ((send c myAdm d k nonce text now files).eval s).ops ∧
              sk = recKey j (sealedPost c myAdm d k nonce text n now group).id) ∧
          ∀ x sk', Listed C s.ops c x sk' →
            Pos.cmp (sk', x) (sk, (sealedPost c myAdm d k nonce text n now group).id) = .lt) := by
  dsimp only
  let group := (Clump.choose c myAdm now).eval s
  let T := (topCount c).eval s
  let n := min (T + 1) countCap
  let p := sealedPost c myAdm d k nonce text n now group
  have hw : (send c myAdm d k nonce text now files).eval s =
      ⟨p :: (receiptFor p).eval s ++ files.flatMap (fun f =>
        let (a, cs) := attach c myAdm p.id d k f; a :: cs)⟩ := by
    simp only [send, View.eval_bind, View.eval_pure]; rfl
  refine ⟨n, by rw [hw]; rfl, fun hnew => ?_⟩
  -- every message of c the device lists is at most T
  have hmsg : ∀ y u d kid sealed n' tm' clump, V C s.ops y (.message c u d kid sealed n' tm' clump) → min n' countCap ≤ T :=
    fun _ _ _ _ _ _ _ _ hv => topCount_ge h hq hv
  by_cases hn : T + 1 < countCap
  · have hn' : n = T + 1 := Nat.min_eq_left (Nat.le_of_lt hn)
    refine ⟨msgKey n now, .inl ⟨by omega, rfl⟩, fun x sk' hl => ?_⟩
    rcases hl with ⟨u, d, kid, sealed, n', tm', clump, hv, hlt, rfl⟩ | ⟨z, kid, j, clump, hz, _⟩
    · have hle := hmsg _ _ _ _ _ _ _ _ hv
      have e := time_is_display (clump := clump) (clump' := none) (c := c) (u := u) (d := d) (kid := kid) (sealed := sealed) (c' := c) (u' := .empty)
        (d' := .empty) (kid' := .empty) (sealed' := .empty) (n := n') (n' := n) (by omega) tm' now x p.id
      show Pos.cmp (sortOf (Fact.message c u d kid sealed n' tm' clump), x) (sortOf (Fact.message c .empty .empty .empty .empty n now), p.id) = .lt
      rw [e, Nat.compare_eq_lt.2 (by omega)]
    · obtain ⟨_, _, _, _, n'', _, _, _, hcap, hm⟩ := received_of_message hz
      have := hmsg _ _ _ _ _ _ _ _ hm
      omega
  · have hsat : countCap ≤ n := by simp only [n]; omega
    have hp : (decode p.body : Option Body) = some (.post (kidOf cryptoSeal k)
        (nonce.1 ++ sealBody cryptoSeal k nonce c (kidOf cryptoSeal k) text) n now
        (sig d.sk ([c, myAdm] ++ group.toList) (.post (kidOf cryptoSeal k)
          (nonce.1 ++ sealBody cryptoSeal k nonce c (kidOf cryptoSeal k) text) n now .empty))) :=
      body_mkOp _ _
    have hc : p.reqs.headD .empty = c := rfl
    have hr := receipt_post h hq rfl hp hsat hnew
    rw [hc] at hr
    refine ⟨recKey ((topReceived c).eval s + 1) p.id, .inr ⟨_, by rw [hw, hr]; simp; exact .inr (.inl rfl), rfl⟩,
      fun x sk' hl => ?_⟩
    rcases hl with ⟨u, d, kid, sealed, n', tm', clump, hv, hlt, rfl⟩ | ⟨z, kid, j, clump, hz, rfl⟩
    · show (bcmp (msgKey n' tm') _).then _ = .lt
      rw [bcmp_msg_rec hlt]; rfl
    · exact (receipt_past h hq hk).2 z kid x j clump hz

/-- A receipt list's bounds for p's two sides are a position and its
successor. -/
theorem rec_succ (p : Pos) : beforeRec (p.1, p.2.push 0) = ((afterRec p).1, (afterRec p).2.push 0) := by
  unfold afterRec beforeRec
  simp only
  congr 1
  cases e : bcmp (recMsg p.1) p.2
  · have : bcmp (recMsg p.1) (p.2.push 0) = .lt := (bcmp_push_zero _ _).2 (by rw [e]; decide)
    simp [this]
  · have : bcmp (recMsg p.1) (p.2.push 0) = .lt := (bcmp_push_zero _ _).2 (by rw [e]; decide)
    simp [this]
  · have : bcmp (recMsg p.1) (p.2.push 0) ≠ .lt := fun h => absurd ((bcmp_push_zero _ _).1 h) (by rw [e]; decide)
    simp [this]

/-- **A window's two sides partition what this device can read.** For
any anchor p, the rows past it and the rows at or before it (before its
successor) are together all of `readable`'s rows, each counted once:
in every list, a message's or a receipt's. -/
theorem count_partition (s : DB Fact) (c : Id) (lim : Option Nat) (desc : Bool) (p : Pos) :
    ((readable c lim desc (some p)).eval s).inRange +
      ((readable c lim desc none (some (p.1, p.2.push 0))).eval s).inRange =
    ((readable c lim desc).eval s).total := by
  rw [eval_readable, eval_readable, eval_readable]
  simp only [unionAnswers, List.map_append, List.sum_append, List.map_map, Function.comp_def]
  have hm := sum_map_add ((heldKids c).eval s)
    (fun kid => (Engine.eval s (message.byKey.query [c, kid] lim desc (some p) none)).inRange)
    (fun kid => (Engine.eval s (message.byKey.query [c, kid] lim desc none (some (p.1, p.2.push 0)))).inRange)
    (fun kid => (Engine.eval s (message.byKey.query [c, kid] lim desc none none)).total)
    (fun kid _ => eval_partition s p rfl rfl rfl rfl rfl rfl rfl rfl)
  have hr := sum_map_add ((heldKids c).eval s)
    (fun kid => (Engine.eval s (received.byKey.query [c, kid] lim desc (some (afterRec p)) none)).inRange)
    (fun kid => (Engine.eval s (received.byKey.query [c, kid] lim desc none
      (some (beforeRec (p.1, p.2.push 0))))).inRange)
    (fun kid => (Engine.eval s (received.byKey.query [c, kid] lim desc none none)).total)
    (fun kid _ => by
      rw [rec_succ]
      exact eval_partition s (afterRec p) rfl rfl rfl rfl rfl rfl rfl rfl)
  simp only [Option.map_some, Option.map_none] at hm hr ⊢
  omega

/-- **A window holds its own anchor**: a row this device can read is in
the read of the rows at or before it, below the counter cap (its
message's row) and past it (its receipt's, named by its message). -/
theorem anchor_read (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (desc : Bool) {pf : Pos × Fact}
    (hp : pf ∈ ((readable c none desc).eval s).rows) :
    pf ∈ ((readable c none desc none (some (pf.1.1, pf.1.2.push 0))).eval s).rows := by
  rw [eval_readable] at hp ⊢
  simp only at hp ⊢
  rw [mem_union_all] at hp ⊢
  obtain ⟨a, ha, hpa⟩ := hp
  rcases List.mem_append.1 ha with ha | ha
  · obtain ⟨kid, hkid, rfl⟩ := List.mem_map.1 ha
    refine ⟨_, List.mem_append_left _ (List.mem_map.2 ⟨kid, hkid, rfl⟩), ?_⟩
    rw [mem_eval_unlimited rfl] at hpa ⊢
    refine ⟨hpa.1, ?_⟩
    simp only [ListQ.inside, Rel.query, Bool.true_and, beq_iff_eq]
    exact (Pos.cmp_succ pf.1 pf.1).2 (by rw [(Pos.cmp_eq_iff _ _).2 rfl]; decide)
  · obtain ⟨kid, hkid, rfl⟩ := List.mem_map.1 ha
    refine ⟨_, List.mem_append_right _ (List.mem_map.2 ⟨kid, hkid, rfl⟩), ?_⟩
    simp only [Option.map_none] at hpa
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hpa
    obtain ⟨he, _, hargs⟩ := row_at (C := C) (r := received.byKey) (by simp [rels]) h hq hr
    obtain ⟨⟨sk, z⟩, f⟩ := r
    cases f with
    | ofReceived x =>
      obtain ⟨c', kid', m, k, clump⟩ := x
      simp only [received.byKey, Option.some.injEq, List.cons.injEq, and_true] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      have hsk : sk = recKey k m := by simpa [SortKey.sortOf, sortOf] using congrArg (·.1.1) he
      subst hsk
      refine List.mem_map.2 ⟨_, ?_, rfl⟩
      rw [mem_eval_unlimited rfl] at hr ⊢
      refine ⟨hr.1, ?_⟩
      simp only [ListQ.inside, Rel.query, Bool.true_and, beq_iff_eq, Option.map_some, asMsg, beforeRec,
        recMsg_recKey]
      have hm : bcmp m (m.push 0) = .lt := (bcmp_push_zero _ _).2 (by rw [(bcmp_eq_iff m m).2 rfl]; decide)
      have hk : bcmp (recKey k m) ((recKey k m).push 0) = .lt :=
        (bcmp_push_zero _ _).2 (by rw [(bcmp_eq_iff _ _).2 rfl]; decide)
      simp [hm, Pos.cmp, hk, Ordering.then]
    | _ => simp [received.byKey] at hargs

end
end Community
