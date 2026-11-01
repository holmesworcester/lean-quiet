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
theorem admission_consented {y c u : Id} {d e : Key} (h : V C ops y (.admission c u d e)) :
    ∃ x o b s, (x = y ∨ ∃ oy, ops y = some oy ∧ oy.reqs.getD 1 .empty = x) ∧
      ops x = some o ∧ (decode o.body : Option Body) = some b ∧ s ∈ b.sigs ∧
      C.verify d (signed o b) s = true := by
  obtain ⟨o, b, fs, hx, hb, hr, hv⟩ := valid_inv h
  rcases check_admission hv with ⟨s, rfl, _, _, _, hs⟩ | ⟨d0, e0, l, a, rfl, rfl, _⟩
  · exact ⟨y, o, _, s, Or.inl rfl, hx, hb, by simp [Body.sigs], hs⟩
  · obtain ⟨_, r, _, hreq, _, hrv, _⟩ := all2_cons2 hr
    obtain ⟨or, br, fsr, hor, hbr, _, hvr⟩ := valid_inv hrv
    obtain ⟨cs, _, _, _, _, _, rfl, _, _, _, hcs, _⟩ := check_request hvr
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
      ∃ y e z oz bz, V C ops y (.admission c u d e) ∧
        (z = y ∨ ∃ oy, ops y = some oy ∧ oy.reqs.getD 1 .empty = z) ∧ ops z = some oz ∧
        (decode oz.body : Option Body) = some bz ∧ Signed d (signed oz bz) := by
  obtain ⟨o, s, e, y, hx, hb, _, hy, hs⟩ := message_authorized h
  obtain ⟨z, oz, bz, s', hz, hoz, hbz, hm', hs'⟩ := admission_consented hy
  exact ⟨o, s, hx, hb, hU _ _ _ _ _ hx hb (by simp [Body.sigs]) hs, y, e, z, oz, bz, hy, hz,
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
      ∃ y e z oz bz, V C ops y (.admission c u d e) ∧
        (z = y ∨ ∃ oy, ops y = some oy ∧ oy.reqs.getD 1 .empty = z) ∧ ops z = some oz ∧
        (decode oz.body : Option Body) = some bz ∧ Signed d (signed oz bz) := by
  obtain ⟨o, s, d, e, y, hx, hb, _, hy, _, hs⟩ := profile_authorized h
  obtain ⟨z, oz, bz, s', hz, hoz, hbz, hm', hs'⟩ := admission_consented hy
  exact ⟨o, s, d, hx, hb, hU _ _ _ _ _ hx hb (by simp [Body.sigs]) hs, y, e, z, oz, bz, hy, hz,
    hoz, hbz, hU _ _ _ _ _ hoz hbz hm' hs'⟩

/-- **An admission's community has a Valid root.** -/
theorem root_of_admission (hk : Keyed ops) {y c u : Id} {d e : Key} (h : V C ops y (.admission c u d e)) :
    ∃ d0 e0, V C ops c (.admission c c d0 e0) := by
  obtain ⟨o, b, fs, hx, _, hr, hv⟩ := valid_inv h
  rcases check_admission hv with ⟨s, rfl, rfl, hc, hu, _⟩ | ⟨d0, e0, l, a, rfl, rfl, _, _, hh⟩
  · have h1 : c = y := hc.trans (hk y o hx)
    have h2 : u = y := hu.trans (hk y o hx)
    subst h1; subst h2
    exact ⟨d, e, h⟩
  · obtain ⟨x, _, _, hreq, hxv, _, _⟩ := all2_cons2 hr
    rw [hreq] at hh; simp at hh; subst hh
    exact ⟨d0, e0, hxv⟩

theorem check_named {C : Crypto} {o : Op} {b : Body} {fs : List Fact} {c u : Id} {nm : ByteArray}
    {n : Nat} (h : check C o b fs = some (.named c u nm n)) :
    ∃ s d0 e0 d e auth prev, b = .name n nm s ∧
      fs = .admission c c d0 e0 :: .admission c u d e :: auth :: prev ∧ o.reqs.head? = some c ∧
      isAdmin c u auth = true ∧ nm.size ≤ 64 ∧ counterOk c n prev = true ∧
      C.verify d (signed o b) s = true := by
  unfold check at h
  split at h <;> (try (simp at h; done))
  rename_i b r a auth prev
  rcases b with ⟨n', nm', s⟩; rcases r with ⟨c0, u0, d0, e0⟩; rcases a with ⟨c1, u', d, e⟩
  simp only [Rename.check] at h
  split at h
  · rename_i hc
    simp only [Option.map_some, Option.some.injEq, Fact.ofNamed.injEq, Rename.Fact.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    obtain ⟨h1, rfl, rfl, h4, h5, h6, h7⟩ := hc
    exact ⟨_, _, _, _, _, _, _, rfl, rfl, h1, h4, h5, h6, h7⟩
  · simp at h

/-- **Only admins name a community.** -/
theorem named_by_admin {x c u : Id} {nm : ByteArray} {n : Nat} (h : V C ops x (.named c u nm n)) :
    IsAdmin C ops c u := by
  obtain ⟨o, b, fs, _, _, hr, hv⟩ := valid_inv h
  obtain ⟨_, _, _, _, _, auth, _, rfl, rfl, _, ha, _⟩ := check_named hv
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
  -- approve: its links; grant, remove and name: their authority; remove:
  -- its heads; name: the names before it
  · rename_i b r q a ls
    rcases b; rcases r; rcases q; rcases a
    simp only [Approve.check] at hf'
    split at hf'
    · obtain ⟨_, hb', -⟩ := Option.map_eq_some_iff.1 hf'
      obtain ⟨ps, hps, -⟩ := Option.bind_eq_some_iff.1 hb'
      rw [approvals_eq hps] at hg
      rcases hg with rfl | rfl | rfl | hg
      · rfl
      · rfl
      · rfl
      · obtain ⟨p, -, rfl⟩ := List.mem_map.1 hg; rfl
    · cases hf'
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
  · rename_i b r a auth tg hs
    rcases b; rcases r; rcases a; rcases tg
    simp only [Remove.check] at hf'
    split at hf'
    · rename_i hc
      obtain ⟨_, hb', -⟩ := Option.map_eq_some_iff.1 hf'
      obtain ⟨ps, hps, -⟩ := Option.bind_eq_some_iff.1 hb'
      rw [approvals_eq hps] at hg
      rcases hg with rfl | rfl | rfl | rfl | hg
      · rfl
      · rfl
      · rcases hc.2.2.2.2.1 with ⟨_, hh⟩ | hh
        · simpa using hh
        · exact isAdmin_shared hh
      · rfl
      · obtain ⟨p, -, rfl⟩ := List.mem_map.1 hg; rfl
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
`unbox` opens with rsk to the content key, given the crates'
correctness. -/
theorem wrapKey_opens (t : Trust.NativeCrypto) (c : Id) (k esk rsk : Key32) :
    ∃ kid bx, (Codec.decode (wrapKey c k esk (cryptoSeal.pub rsk)).body : Option Body) =
      some (.wrap kid (cryptoSeal.pub rsk) bx) ∧ kid = kidOf cryptoSeal k ∧
      unbox cryptoSeal rsk kid bx = some k := by
  have G := cryptoSeal_good t
  refine ⟨_, _, body_mkOp _ _, rfl, unbox_box G rsk esk k _ ?_⟩
  rw [show (kidOf cryptoSeal k).size = 32 from G.hash_size _]; decide

/-- **An admitted device reads every post sealed under a key wrapped to
it**, through the functions the app runs: the approver's `wrapKey` to
the device's node key, the member's `unbox`, the poster's `sealedPost`
and the screen's `openStored`. The one premise left about the code is
the crates' correctness (`member_opens` at the running suite). -/
theorem member_reads (t : Trust.NativeCrypto) (c adm : Id) (d : Device) (k esk rsk : Key32) (nonce : Nonce24)
    (text : ByteArray) (n time : Nat) (clump : Option Id)
    (hc : c.size = 32) (ht : text.size < Crypto.maxPlaintext) :
    ∃ kid bx sealed sg,
      (Codec.decode (wrapKey c k esk (cryptoSeal.pub rsk)).body : Option Body) =
        some (.wrap kid (cryptoSeal.pub rsk) bx) ∧
      (Codec.decode (sealedPost c adm d k nonce text n time clump).body : Option Body) =
        some (.post kid sealed n time sg) ∧
      ((unbox cryptoSeal rsk kid bx).bind fun k' => openStored cryptoSeal c kid sealed k'.1) = some text := by
  obtain ⟨kid, bx, hw, hk, hu⟩ := wrapKey_opens t c k esk rsk
  obtain ⟨kid', sealed, sg, hp, hk', ho⟩ := sealedPost_opens t c adm d k nonce text n time clump hc ht
  subst hk hk'
  exact ⟨_, bx, sealed, sg, hw, hp, by rw [hu, Option.bind_some, ho]⟩
open Engine

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
      let key := ((nodeKeyOr fresh).eval s).1; let d := Device.ofSeed seed; let r := root d key
      [r, setName r.id r.id r.id [] 1 d name, profile r.id r.id d myName time,
        wrapKey r.id k esk key] := by
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

/-- Every head `headsOf` reads is a Valid approval of c. -/
theorem headsOf_valid (h : Inv (family C) s) (hq : s.queue = []) (c : Id) :
    ∀ (seen : List Key) (rows : List (Pos × Fact)) (x : Id), x ∈ (headsOf c seen rows).eval s →
      ∃ g : Approve.Fact, V C s.ops x (.ofApproval g) ∧ g.c = c
  | _, [], x, hx => by simp [headsOf, View.eval] at hx
  | seen, (p, f) :: t, x, hx => by
    cases f with
    | ofAdmission a =>
      obtain ⟨c', u, d, e⟩ := a
      simp only [headsOf] at hx
      split at hx
      · exact headsOf_valid h hq c seen t x hx
      · simp only [View.eval, View.eval_bind'] at hx
        split at hx
        · rename_i hh
          rcases List.mem_cons.1 hx with rfl | hx
          · obtain ⟨hv, hk⟩ := row_filed (r := approval.byDev) (by simp [rels]) h hq
              (List.mem_of_mem_head? hh)
            rename_i g
            cases g <;> simp [approval.byDev, Approve.byDev, Rel.comap] at hk
            exact ⟨_, hv, hk.1⟩
          · exact headsOf_valid h hq c (d :: seen) t x hx
        · exact headsOf_valid h hq c (d :: seen) t x hx
    | _ => exact headsOf_valid h hq c seen t x (by simpa [headsOf] using hx)

/-- Heads that are Valid approvals of c make a cut. -/
theorem cut_of_heads {ops : Id → Option Op} {c : Id} :
    ∀ {hs : List Id}, (∀ x ∈ hs, ∃ g : Approve.Fact, V C ops x (.ofApproval g) ∧ g.c = c) →
      ∃ ps k, All2 (fun r g => V C ops r g) hs (ps.map .ofApproval) ∧ Remove.cutOf c hs ps = some k
  | [], _ => ⟨[], [], .nil, rfl⟩
  | x :: hs, hall => by
    obtain ⟨g, hg, hgc⟩ := hall x (List.mem_cons_self ..)
    obtain ⟨ps, k, hps, hk⟩ := cut_of_heads fun y hy => hall y (List.mem_cons_of_mem _ hy)
    exact ⟨g :: ps, (g.dev, x, g.n) :: k, .cons hg hps, by simp [Remove.cutOf, hgc, hk]⟩

/-- **A removal the remover flow writes stands.** Every op
`removeMember c t d` writes is, once stored, a Valid removal of t by
an admin u other than t (d's signatures verifying under the suite). -/
theorem removeMember_valid (h : Inv (family C) s) (hq : s.queue = []) {c t : Id} {d : Device}
    (hsig : ∀ m, C.verify d.pk m (edSign d.sk m) = true)
    {o : Op} (ho : o ∈ ((removeMember c t d).eval s).ops)
    {ops' : Id → Option Op} (he : Extends s.ops ops') (hs : ops' o.id = some o) :
    ∃ u k, u ≠ t ∧ IsAdmin C s.ops c u ∧ V C ops' o.id (.removal c t u k) := by
  unfold removeMember at ho
  simp only [Rel.read, View.eval_bind, View.eval_read] at ho
  split at ho
  · rename_i p myAdm c' u dv ev hme
    simp only [View.eval_bind, View.eval_read] at ho
    split at ho
    · rename_i a pt ta g hauth htg
      simp only [View.eval_bind, View.eval_pure] at ho
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
        obtain ⟨u', e', hfe⟩ := byDevice_args.1 hma
        simp only [Fact.admission.injEq] at hfe
        obtain ⟨hc', _, hdv, _⟩ := hfe
        subst c'
        have htgV := row_filed (r := admission.byUser) (by simp [rels]) h hq
          (List.mem_of_mem_head? (by rw [htg]; rfl))
        obtain ⟨htv, hta⟩ := htgV
        obtain ⟨dt, et, hg⟩ := admission_byUser_args.1 hta
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
        obtain ⟨ps, k, hall, hcut⟩ := cut_of_heads (C := C) (ops := ops') (c := c)
          (hs := ((headsOf c [] (Engine.eval s (admission.byUser.query [c, t])).rows).eval s).take maxHeads)
          (fun x hx => let ⟨g, hg, hgc⟩ := headsOf_valid h hq c [] _ x (List.mem_of_mem_take hx)
            ⟨g, valid_stays he hg, hgc⟩)
        refine ⟨u, k, hut, isAdmin_sound hgv hga, ?_⟩
        rw [hdv] at hmv
        exact admin_removal_stands hs (Codec.decode_encode _) rfl rfl
          (valid_stays he hroot) (valid_stays he hmv) (valid_stays he hgv) hga (valid_stays he htv)
          hall hcut (hsig _)
    · simp at ho
  · simp at ho

/-- What `removeMember` cites after its first four requirements: the
heads `headsOf` reads of the target's devices, at most `maxHeads`. -/
theorem removeMember_reqs {c t : Id} {d : Device} {o : Op} (ho : o ∈ ((removeMember c t d).eval s).ops) :
    o.reqs.drop 4 = ((headsOf c [] (Engine.eval s (admission.byUser.query [c, t])).rows).eval s).take maxHeads := by
  unfold removeMember at ho
  simp only [Rel.read, View.eval_bind, View.eval_read] at ho
  split at ho
  · rename_i p myAdm c' u dv ev hme
    simp only [View.eval_bind, View.eval_read] at ho
    split at ho
    · rename_i a pt ta g hauth htg
      simp only [View.eval_bind, View.eval_pure] at ho
      by_cases hcond : u = t ∨ (Engine.eval s (removal.byUser.query [c, t] (some 0))).total ≠ 0
      · simp [hcond] at ho
      · simp only [not_or, ne_eq, Decidable.not_not] at hcond
        obtain ⟨hut, hgone⟩ := hcond
        simp only [hut, hgone, ne_eq, not_true_eq_false, or_self, ↓reduceIte, List.mem_singleton] at ho
        subst ho; rfl
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
    admission.all.args f = some [c] ↔ ∃ u d e, f = .admission c u d e := by
  cases f <;> (try (rename_i x; cases x)) <;> simp [admission.all, Root.all, Rel.comap, Fact.admission?, eq_comm]

theorem removals_iff (h : Inv (family C) s) (hq : s.queue = []) (c u : Id) :
    (eval s (removals c u)).total ≠ 0 ↔ Removed C s.ops c u := by
  rw [← Nat.pos_iff_ne_zero, removals]
  show 0 < (eval s { key := removal.byUser.key [c, u], limit := some 0 }).total ↔ _
  rw [total_pos]
  constructor
  · rintro ⟨y, f, hy, hf⟩
    obtain ⟨hv, hk⟩ := (filed (by simp [rels]) h hq [c, u] y f).1 ⟨hy, hf⟩
    obtain ⟨r, k, rfl⟩ := byUser_args.1 hk
    exact ⟨y, r, k, hv⟩
  · rintro ⟨y, r, k, hv⟩
    obtain ⟨hy, hf⟩ := (filed (by simp [rels]) h hq [c, u] y _).2 ⟨hv, byUser_args.2 ⟨r, k, rfl⟩⟩
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

/-- `unremoved` holds of rows exactly when every admission into c among
them is into a user whose removals count none. -/
theorem unremoved_iff (c : Id) (rows : List (Pos × Fact)) :
    (unremoved c rows).eval s = true ↔
      ∀ u d e, (∃ p, (p, .admission c u d e) ∈ rows) → (eval s (removals c u)).total = 0 := by
  induction rows with
  | nil => simp [unremoved, View.eval]
  | cons pf t ih =>
    obtain ⟨p, f⟩ := pf
    simp only [mem_cons_row]
    cases f with
    | ofAdmission a =>
      obtain ⟨c', u', d', e'⟩ := a
      by_cases hc : c' = c
      · subst hc
        show View.eval s (if c' = c' then _ else _) = true ↔ _
        rw [if_pos rfl]
        show View.eval s (if (eval s (removals c' u')).total = 0 then _ else _) = true ↔ _
        by_cases hz : (eval s (removals c' u')).total = 0
        · rw [if_pos hz, ih]
          constructor
          · rintro hall u d e (he | hm)
            · simp only [Fact.admission.injEq] at he; obtain ⟨_, rfl, _, _⟩ := he; exact hz
            · exact hall u d e hm
          · intro hall u d e hm; exact hall u d e (Or.inr hm)
        · rw [if_neg hz]
          show (false = true) ↔ _
          constructor
          · intro hf; cases hf
          · intro hall; exact absurd (hall u' d' e' (Or.inl rfl)) hz
      · show View.eval s (if c' = c then _ else _) = true ↔ _
        rw [if_neg hc, ih]
        constructor
        · rintro hall u d e (he | hm)
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
  have hrow : ∀ u e, (∃ p, (p, .admission c u d e) ∈ (eval s (admission.byDevice.query [c, d])).rows) ↔
      Admitted C s.ops c u d e := by
    intro u e
    rw [exists_row h hq (by simp [rels])]
    exact ⟨fun ⟨y, hv, _⟩ => ⟨y, hv⟩, fun ⟨y, hv⟩ => ⟨y, hv, byDevice_args.2 ⟨u, e, rfl⟩⟩⟩
  have hd : ∀ u d' e, (∃ p, (p, .admission c u d' e) ∈ (eval s (admission.byDevice.query [c, d])).rows) →
      d' = d := by
    rintro u d' e ⟨p, hp⟩
    obtain ⟨_, hv, hk⟩ := (exists_row h hq (by simp [rels]) [c, d] _).1 ⟨p, hp⟩
    obtain ⟨_, _, he⟩ := byDevice_args.1 hk
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
    obtain ⟨p, hp⟩ := (hrow u e).2 ha
    rw [List.isEmpty_iff] at he; rw [he] at hp; cases hp
  · rename_i he
    rw [unremoved_iff]
    constructor
    · intro hall
      obtain ⟨⟨p, f⟩, hm⟩ := List.exists_mem_of_ne_nil _ (by simpa using he)
      obtain ⟨_, hv, hk⟩ := (exists_row h hq (by simp [rels]) [c, d] f).1 ⟨p, hm⟩
      obtain ⟨u, e, rfl⟩ := byDevice_args.1 hk
      refine ⟨⟨u, e, _, hv⟩, fun u' e' ha => ?_⟩
      rw [← removals_iff h hq]
      exact fun hne => hne (hall u' d e' ((hrow u' e').2 ha))
    · rintro ⟨_, hall⟩ u d' e hm
      have := hd u d' e hm; subst this
      exact Decidable.of_not_not fun hne => hall u e ((hrow u e).1 hm) ((removals_iff h hq c u).1 hne)

/-! ## The causal cut, read: each view is its predicate -/

theorem byDev_args {c d : Id} {f : Fact} :
    approval.byDev.args f = some [c, d] ↔ ∃ g : Approve.Fact, f = .ofApproval g ∧ g.c = c ∧ g.dev = d := by
  cases f <;> simp [approval.byDev, Approve.byDev, Rel.comap, Fact.approval?, eq_comm]

theorem byRequester_args {c d : Id} {f : Fact} :
    approval.byRequester.args f = some [c, d] ↔
      ∃ g : Approve.Fact, f = .ofApproval g ∧ g.c = c ∧ g.rd = d := by
  cases f <;> simp [approval.byRequester, Approve.byRequester, Rel.comap, Fact.approval?, eq_comm]

theorem factIn_some {x : Id} {f : Approve.Fact} :
    ∀ {rows : List (Pos × Fact)}, factIn x rows = some f → ∃ p, ((p, x), .ofApproval f) ∈ rows
  | [], h => by simp [factIn] at h
  | ((p, y), g) :: t, h => by
    cases g with
    | ofApproval f' =>
      simp only [factIn] at h
      split at h
      · rename_i hy; cases h; subst hy; exact ⟨p, List.mem_cons_self ..⟩
      · obtain ⟨q, hq⟩ := factIn_some h; exact ⟨q, List.mem_cons_of_mem _ hq⟩
    | _ => obtain ⟨q, hq⟩ := factIn_some (rows := t) h; exact ⟨q, List.mem_cons_of_mem _ hq⟩

theorem factIn_of_mem {x : Id} {f : Approve.Fact} {p : ByteArray} :
    ∀ {rows : List (Pos × Fact)}, ((p, x), .ofApproval f) ∈ rows → ∃ f', factIn x rows = some f'
  | [], h => by cases h
  | ((q, y), g) :: t, h => by
    rcases List.mem_cons.1 h with he | ht
    · simp only [Prod.mk.injEq] at he; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := he
      exact ⟨f, by simp [factIn]⟩
    · cases g with
      | ofApproval f' =>
        simp only [factIn]
        split
        · exact ⟨_, rfl⟩
        · exact factIn_of_mem ht
      | _ => exact factIn_of_mem (rows := t) ht

/-- At rest, the fact `factIn` finds among a relation's rows is the
Valid fact of that id, filed there. -/
theorem factIn_rows (h : Inv (family C) s) (hq : s.queue = []) {r : Rel Fact} (hr : r ∈ rels)
    (as : List ByteArray) (x : Id) (f : Approve.Fact) :
    factIn x (Engine.eval s (r.query as)).rows = some f ↔
      V C s.ops x (.ofApproval f) ∧ r.args (.ofApproval f) = some as := by
  constructor
  · intro hf
    obtain ⟨p, hp⟩ := factIn_some hf
    obtain ⟨y, g, he, hv, hk⟩ := (mem_rows h hq hr as).1 hp
    simp only [Prod.mk.injEq] at he
    obtain ⟨⟨_, rfl⟩, rfl⟩ := he
    exact ⟨hv, hk⟩
  · rintro ⟨hv, hk⟩
    have hm := (mem_rows h hq hr as).2 ⟨x, _, rfl, hv, hk⟩
    obtain ⟨f', hf'⟩ := factIn_of_mem hm
    obtain ⟨p, hp⟩ := factIn_some hf'
    obtain ⟨y, g, he, hv', _⟩ := (mem_rows h hq hr as).1 hp
    simp only [Prod.mk.injEq] at he
    obtain ⟨⟨_, rfl⟩, rfl⟩ := he
    have := spec_det hv hv'
    simp only [Verdict.valid.injEq, Fact.ofApproval.injEq] at this
    rw [hf', this]

theorem factIn_dev (h : Inv (family C) s) (hq : s.queue = []) (c dv x : Id) (f : Approve.Fact) :
    factIn x (Engine.eval s (approval.byDev.query [c, dv])).rows = some f ↔
      V C s.ops x (.ofApproval f) ∧ f.c = c ∧ f.dev = dv := by
  rw [factIn_rows h hq (by simp [rels]), byDev_args]
  simp

theorem factIn_req (h : Inv (family C) s) (hq : s.queue = []) (c d x : Id) (f : Approve.Fact) :
    factIn x (Engine.eval s (approval.byRequester.query [c, d])).rows = some f ↔
      V C s.ops x (.ofApproval f) ∧ f.c = c ∧ f.rd = d := by
  rw [factIn_rows h hq (by simp [rels]), byRequester_args]
  simp

/-- A chain's approvals step back one place at a time, on one device. -/
theorem behind_le {x h : Id} {fx fh : Approve.Fact} (hb : Behind C ops x h)
    (hx : V C ops x (.ofApproval fx)) (hh : V C ops h (.ofApproval fh)) : fx.n ≤ fh.n ∧ fx.dev = fh.dev := by
  induction hb generalizing fh with
  | here =>
    have := spec_det hx hh
    simp only [Verdict.valid.injEq, Fact.ofApproval.injEq] at this
    subst this; exact ⟨Nat.le_refl _, rfl⟩
  | @back h' f hv hn _ ih =>
    have := spec_det hv hh
    simp only [Verdict.valid.injEq, Fact.ofApproval.injEq] at this
    subst this
    obtain ⟨_, _, _, _, hp⟩ := approval_links hv
    obtain ⟨p, hpv, hpn, _, hpd⟩ := hp hn
    obtain ⟨h1, h2⟩ := ih hpv
    exact ⟨by omega, h2.trans hpd⟩

/-- **The chain walk is `Behind`.** Through device dv's chain rows, walking
back from approval h (place m) to x's place finds x exactly when x is at
or behind h. -/
theorem behindIn_iff (h : Inv (family C) s) (hq : s.queue = []) {c dv x : Id} {fx : Approve.Fact}
    (hx : V C s.ops x (.ofApproval fx)) :
    ∀ (k : Nat) (hd : Id) (fh : Approve.Fact), V C s.ops hd (.ofApproval fh) → fh.c = c → fh.dev = dv →
      fh.n = fx.n + k →
      (behindIn (Engine.eval s (approval.byDev.query [c, dv])).rows x k hd = true ↔ Behind C s.ops x hd)
  | 0, hd, fh, hv, _, _, hn => by
    simp only [behindIn, decide_eq_true_eq]
    constructor
    · rintro rfl; exact .here
    · intro hb
      cases hb with
      | here => rfl
      | back hv' hn' hb' =>
        rename_i f'
        have := spec_det hv hv'
        simp only [Verdict.valid.injEq, Fact.ofApproval.injEq] at this
        subst this
        obtain ⟨_, _, _, _, hp⟩ := approval_links hv
        obtain ⟨p, hpv, hpn, _, _⟩ := hp hn'
        have := (behind_le hb' hx hpv).1
        omega
  | k + 1, hd, fh, hv, hc, hdv, hn => by
    have hf : factIn hd (Engine.eval s (approval.byDev.query [c, dv])).rows = some fh :=
      (factIn_dev h hq c dv hd fh).2 ⟨hv, hc, hdv⟩
    simp only [behindIn, hf, Bool.and_eq_true, bne_iff_ne, ne_eq]
    have hpos : 0 < fh.n := by omega
    obtain ⟨_, _, _, _, hp⟩ := approval_links hv
    obtain ⟨p, hpv, hpn, hpc, hpd⟩ := hp hpos
    rw [behindIn_iff h hq hx k fh.prev p hpv (hpc.trans hc) (hpd.trans hdv) (by omega)]
    constructor
    · rintro ⟨_, hb⟩; exact .back hv hpos hb
    · intro hb
      cases hb with
      | here =>
        have := spec_det hx hv
        simp only [Verdict.valid.injEq, Fact.ofApproval.injEq] at this
        subst this; omega
      | back hv' _ hb' =>
        have := spec_det hv hv'
        simp only [Verdict.valid.injEq, Fact.ofApproval.injEq] at this
        subst this
        exact ⟨by omega, hb'⟩

/-- What a Valid removal's cut names: Valid approvals of its community,
by the device and at the place each entry says. -/
theorem removal_cut {z c u r : Id} {k : List (Key × Id × Nat)} (hz : V C ops z (.removal c u r k))
    {dv h : Id} {m : Nat} (hm : (dv, h, m) ∈ k) :
    ∃ g : Approve.Fact, V C ops h (.ofApproval g) ∧ g.c = c ∧ g.dev = dv ∧ g.n = m := by
  obtain ⟨o, b, fs, _, _, hr, hv⟩ := valid_inv hz
  obtain ⟨_, _, _, _, _, _, _, _, ps, rfl, rfl, hh, _, _, hcut⟩ := check_removal hv
  obtain ⟨c', _, _, t, hreq, _, _, _, hrest⟩ := all2_cons3 hr
  obtain ⟨y, ys, rfl, _, hys⟩ : ∃ y ys, t = y :: ys ∧ V C ops y _ ∧ All2 (fun r g => V C ops r g) ys _ := by
    cases hrest with | cons h1 h2 => exact ⟨_, _, rfl, h1, h2⟩
  have hd : o.reqs.drop 4 = ys := by rw [hreq]; rfl
  rw [hd] at hcut
  exact cutOf_mem hys hcut hm

theorem inCut_true (rows : List (Pos × Fact)) (x : Id) (f : Approve.Fact) :
    ∀ k : List (Key × Id × Nat), inCut rows x f k = true ↔
      ∃ h m, (f.dev, h, m) ∈ k ∧ f.n ≤ m ∧ behindIn rows x (m - f.n) h = true
  | [] => by simp [inCut]
  | (d, h, m) :: t => by
    simp only [inCut, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, inCut_true rows x f t,
      List.mem_cons, Prod.mk.injEq]
    constructor
    · rintro (⟨⟨rfl, hm⟩, hb⟩ | ⟨h', m', hm', hle, hb⟩)
      · exact ⟨h, m, Or.inl ⟨rfl, rfl, rfl⟩, hm, hb⟩
      · exact ⟨h', m', Or.inr hm', hle, hb⟩
    · rintro ⟨h', m', ⟨rfl, rfl, rfl⟩ | hm', hle, hb⟩
      · exact Or.inl ⟨⟨rfl, hle⟩, hb⟩
      · exact Or.inr ⟨h', m', hm', hle, hb⟩

/-- **The cut, read.** Over x's device's chain rows, `inCut` holds of a
Valid removal's cut exactly when x is inside it (`InCut`). -/
theorem inCut_iff (h : Inv (family C) s) (hq : s.queue = []) {x c z u r : Id} {f : Approve.Fact}
    {k : List (Key × Id × Nat)} (hx : V C s.ops x (.ofApproval f)) (hz : V C s.ops z (.removal c u r k)) :
    inCut (Engine.eval s (approval.byDev.query [c, f.dev])).rows x f k = true ↔ InCut C s.ops x f k := by
  rw [inCut_true]
  constructor
  · rintro ⟨hd, m, hm, hle, hb⟩
    obtain ⟨g, hg, hgc, hgd, hgn⟩ := removal_cut hz hm
    exact ⟨hd, m, hm, (behindIn_iff h hq hx (m - f.n) hd g hg hgc hgd (by omega)).1 hb⟩
  · rintro ⟨hd, m, hm, hb⟩
    obtain ⟨g, hg, hgc, hgd, hgn⟩ := removal_cut hz hm
    have hle := (behind_le hb hx hg).1
    exact ⟨hd, m, hm, by omega, (behindIn_iff h hq hx (m - f.n) hd g hg hgc hgd (by omega)).2 hb⟩

theorem cutsKeep_true (chain : List (Pos × Fact)) (x : Id) (f : Approve.Fact) :
    ∀ rows : List (Pos × Fact), cutsKeep chain x f rows = true ↔
      ∀ p g, (p, Fact.ofRemoval g) ∈ rows → inCut chain x f g.cut = true
  | [] => by simp [cutsKeep]
  | (p, g) :: t => by
    cases g with
    | ofRemoval g =>
      simp only [cutsKeep, Bool.and_eq_true, cutsKeep_true chain x f t, List.mem_cons, Prod.mk.injEq,
        Fact.ofRemoval.injEq]
      constructor
      · rintro ⟨h1, h2⟩ p' g' (⟨rfl, rfl⟩ | hm)
        · exact h1
        · exact h2 p' g' hm
      · intro hall; exact ⟨hall p g (Or.inl ⟨rfl, rfl⟩), fun p' g' hm => hall p' g' (Or.inr hm)⟩
    | _ =>
      simp only [cutsKeep, cutsKeep_true chain x f t, List.mem_cons, Prod.mk.injEq]
      constructor
      · rintro hall p' g' (⟨_, he⟩ | hm)
        · cases he
        · exact hall p' g' hm
      · intro hall p' g' hm; exact hall p' g' (Or.inr hm)

/-- At rest, every removal of user u keeps approval x exactly when the
removal rows of u all keep it. -/
theorem cutsKeep_iff (h : Inv (family C) s) (hq : s.queue = []) {x c u : Id} {f : Approve.Fact}
    (hx : V C s.ops x (.ofApproval f)) :
    cutsKeep (Engine.eval s (approval.byDev.query [c, f.dev])).rows x f
        (Engine.eval s (removal.byUser.query [c, u])).rows = true ↔
      ∀ z r k, V C s.ops z (.removal c u r k) → InCut C s.ops x f k := by
  rw [cutsKeep_true]
  constructor
  · intro hall z r k hz
    have hm := (mem_rows h hq (r := removal.byUser) (by simp [rels]) [c, u]).2
      ⟨z, _, rfl, hz, byUser_args.2 ⟨r, k, rfl⟩⟩
    exact (inCut_iff h hq hx hz).1 (hall _ ⟨c, u, r, k⟩ hm)
  · intro hall p g hm
    obtain ⟨y, g', he, hv, hk⟩ := (mem_rows h hq (r := removal.byUser) (by simp [rels]) [c, u]).1 hm
    simp only [Prod.mk.injEq] at he
    obtain ⟨_, rfl⟩ := he
    obtain ⟨r, k, he⟩ := byUser_args.1 hk
    cases he
    exact (inCut_iff h hq hx hv).2 (hall y r k hv)

theorem usersKeep_iff (h : Inv (family C) s) (hq : s.queue = []) {x c : Id} {f : Approve.Fact}
    (hx : V C s.ops x (.ofApproval f)) :
    ∀ rows : List (Pos × Fact), (usersKeep c x f rows).eval s = true ↔
      ∀ u d e, (∃ p, (p, .admission c u d e) ∈ rows) →
        ∀ z r k, V C s.ops z (.removal c u r k) → InCut C s.ops x f k
  | [] => by simp [usersKeep, View.eval]
  | (p, g) :: t => by
    have ih := usersKeep_iff (c := c) h hq hx t
    cases g with
    | ofAdmission a =>
      obtain ⟨c', u', d', e'⟩ := a
      by_cases hc : c' = c
      · subst hc
        show View.eval s (if c' = c' then _ else _) = true ↔ _
        rw [if_pos rfl]
        show View.eval s (if (Engine.eval s (removal.byUser.query [c', u'])).rows.isEmpty then _ else _) = true ↔ _
        have hnone : (Engine.eval s (removal.byUser.query [c', u'])).rows.isEmpty = true →
            ∀ z r k, ¬ V C s.ops z (.removal c' u' r k) := by
          intro he z r k hz
          have hm := (mem_rows h hq (r := removal.byUser) (by simp [rels]) [c', u']).2
            ⟨z, _, rfl, hz, byUser_args.2 ⟨r, k, rfl⟩⟩
          rw [List.isEmpty_iff] at he; rw [he] at hm; cases hm
        split
        · rename_i he
          rw [ih]
          constructor
          · rintro hall u d e ⟨q, hq'⟩ z r k hz
            rcases List.mem_cons.1 hq' with he' | hm
            · simp only [Prod.mk.injEq, Fact.admission.injEq] at he'
              obtain ⟨_, _, rfl, _, _⟩ := he'
              exact absurd hz (hnone he z r k)
            · exact hall u d e ⟨q, hm⟩ z r k hz
          · intro hall u d e ⟨q, hm⟩; exact hall u d e ⟨q, List.mem_cons_of_mem _ hm⟩
        · show View.eval s (if cutsKeep _ x f _ then _ else _) = true ↔ _
          split
          · rename_i _ hk
            rw [ih]
            have hk' := (cutsKeep_iff h hq hx).1 hk
            constructor
            · rintro hall u d e ⟨q, hq'⟩ z r k hz
              rcases List.mem_cons.1 hq' with he' | hm
              · simp only [Prod.mk.injEq, Fact.admission.injEq] at he'
                obtain ⟨_, _, rfl, _, _⟩ := he'
                exact hk' z r k hz
              · exact hall u d e ⟨q, hm⟩ z r k hz
            · intro hall u d e ⟨q, hm⟩; exact hall u d e ⟨q, List.mem_cons_of_mem _ hm⟩
          · rename_i _ hk
            simp only [View.eval, Bool.false_eq_true, false_iff]
            intro hall
            exact hk ((cutsKeep_iff h hq hx).2 (hall u' d' e' ⟨p, List.mem_cons_self ..⟩))
      · show View.eval s (if c' = c then _ else _) = true ↔ _
        rw [if_neg hc, ih]
        constructor
        · rintro hall u d e ⟨q, hq'⟩
          rcases List.mem_cons.1 hq' with he' | hm
          · simp only [Prod.mk.injEq, Fact.admission.injEq] at he'; exact absurd he'.2.1.symm hc
          · exact hall u d e ⟨q, hm⟩
        · intro hall u d e ⟨q, hm⟩; exact hall u d e ⟨q, List.mem_cons_of_mem _ hm⟩
    | _ =>
      show (usersKeep c x f t).eval s = true ↔ _
      rw [ih]
      constructor
      · rintro hall u d e ⟨q, hq'⟩
        rcases List.mem_cons.1 hq' with he' | hm
        · simp at he'
        · exact hall u d e ⟨q, hm⟩
      · intro hall u d e ⟨q, hm⟩; exact hall u d e ⟨q, List.mem_cons_of_mem _ hm⟩

/-- **Kept, read (`kept_iff`).** At rest, `kept c x f` holds exactly when
every removal of every user x's device is admitted into keeps x. -/
theorem kept_iff (h : Inv (family C) s) (hq : s.queue = []) {x c : Id} {f : Approve.Fact}
    (hx : V C s.ops x (.ofApproval f)) : (kept c x f).eval s = true ↔ Kept C s.ops c x f := by
  show (usersKeep c x f (Engine.eval s (admission.byDevice.query [c, f.dev])).rows).eval s = true ↔ _
  rw [usersKeep_iff h hq hx]
  constructor
  · intro hall u e z r k ⟨y, hy⟩ hz
    exact hall u f.dev e ((exists_row h hq (by simp [rels]) [c, f.dev] _).2
      ⟨y, hy, byDevice_args.2 ⟨u, e, rfl⟩⟩) z r k hz
  · intro hall u d e hm z r k hz
    obtain ⟨y, hy, hk⟩ := (exists_row h hq (by simp [rels]) [c, f.dev] _).1 hm
    obtain ⟨_, _, he⟩ := byDevice_args.1 hk
    simp only [Fact.admission.injEq] at he
    obtain ⟨_, _, rfl, _⟩ := he
    exact hall u e z r k ⟨y, hy⟩ hz

theorem counts_inv {c x : Id} {f : Approve.Fact} (hc : Counts C ops c x) (hx : V C ops x (.ofApproval f)) :
    f.c = c ∧ Kept C ops c x f ∧ (0 < f.depth → Counts C ops c f.up) := by
  cases hc with
  | founder hv hfc hd hk =>
    have := spec_det hx hv
    simp only [Verdict.valid.injEq, Fact.ofApproval.injEq] at this
    subst this; exact ⟨hfc, hk, fun h => by omega⟩
  | up hv hfc _ hu hk =>
    have := spec_det hx hv
    simp only [Verdict.valid.injEq, Fact.ofApproval.injEq] at this
    subst this; exact ⟨hfc, hk, fun _ => hu⟩

/-- **Counts, read (`counts_iff`).** At rest, `counts` read with an
approval's depth + 1 holds exactly when it counts: kept, and so is every
approval above it to the founder's device's. -/
theorem counts_iff (h : Inv (family C) s) (hq : s.queue = []) {c : Id} :
    ∀ (n : Nat) (x : Id) (f : Approve.Fact), f.depth = n → V C s.ops x (.ofApproval f) → f.c = c →
      ((counts c (f.depth + 1) x f).eval s = true ↔ Counts C s.ops c x)
  | n, x, f, hn, hx, hc => by
    show View.eval s ((kept c x f).bind _) = true ↔ _
    rw [View.eval_bind']
    cases hkb : (kept c x f).eval s with
    | false =>
      simp only [Bool.not_false, ↓reduceIte, View.eval, Bool.false_eq_true, false_iff]
      intro hcx
      have := (kept_iff h hq hx).2 (counts_inv hcx hx).2.1
      rw [hkb] at this; cases this
    | true =>
      have hk := (kept_iff h hq hx).1 hkb
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      by_cases hd : f.depth = 0
      · simp only [hd, ↓reduceIte, View.eval, true_iff]
        exact .founder hx hc hd hk
      · simp only [hd, ↓reduceIte]
        obtain ⟨_, _, _, hu, _⟩ := approval_links hx
        obtain ⟨g, hg, hgd, hgc, _, hgr, _⟩ := hu (Nat.pos_of_ne_zero hd)
        have hf := (factIn_req h hq c f.dev f.up g).2 ⟨hg, hgc.trans hc, hgr⟩
        show View.eval s (match factIn f.up _ with | some g => _ | none => _) = true ↔ _
        rw [hf]
        have hk1 : f.depth = g.depth + 1 := hgd.symm
        rw [hk1]
        rw [counts_iff h hq g.depth f.up g rfl hg (hgc.trans hc)]
        constructor
        · intro hu'; exact .up hx hc (Nat.pos_of_ne_zero hd) hu' hk
        · intro hcx; exact (counts_inv hcx hx).2.2 (Nat.pos_of_ne_zero hd)
  termination_by n => n
  decreasing_by omega

theorem approvedBy_true (h : Inv (family C) s) (hq : s.queue = []) {c d u : Id} {e : Key} :
    ∀ rows : List (Pos × Fact), (∀ p y g, ((p, y), g) ∈ rows →
        ∃ f : Approve.Fact, g = .ofApproval f ∧ V C s.ops y g ∧ f.c = c ∧ f.rd = d) →
      ((approvedBy c u e rows).eval s = true ↔
        ∃ p x f, ((p, x), Fact.ofApproval f) ∈ rows ∧ f.ru = u ∧ f.re = e ∧ Counts C s.ops c x)
  | [], _ => by simp [approvedBy, View.eval]
  | ((p, x), g) :: t, hrows => by
    have ih := approvedBy_true (u := u) (e := e) h hq t fun p y g hm => hrows p y g (List.mem_cons_of_mem _ hm)
    obtain ⟨f, rfl, hv, hc, hd⟩ := hrows p x g (List.mem_cons_self ..)
    show View.eval s (if f.ru = u ∧ f.re = e then _ else _) = true ↔ _
    split
    · rename_i hue
      rw [View.eval_bind']
      by_cases hct : Counts C s.ops c x
      · have := (counts_iff h hq f.depth x f rfl hv hc).2 hct
        rw [this]
        exact ⟨fun _ => ⟨p, x, f, List.mem_cons_self .., hue.1, hue.2, hct⟩, fun _ => rfl⟩
      · have : (counts c (f.depth + 1) x f).eval s = false := by
          cases hb : (counts c (f.depth + 1) x f).eval s
          · rfl
          · exact absurd ((counts_iff h hq f.depth x f rfl hv hc).1 hb) hct
        rw [this]
        show (approvedBy c u e t).eval s = true ↔ _
        rw [ih]
        constructor
        · rintro ⟨p', x', f', hm, h1, h2, h3⟩; exact ⟨p', x', f', List.mem_cons_of_mem _ hm, h1, h2, h3⟩
        · rintro ⟨p', x', f', hm, h1, h2, h3⟩
          rcases List.mem_cons.1 hm with he | hm
          · simp only [Prod.mk.injEq, Fact.ofApproval.injEq] at he
            obtain ⟨⟨_, rfl⟩, rfl⟩ := he
            exact absurd h3 hct
          · exact ⟨p', x', f', hm, h1, h2, h3⟩
    · rename_i hue
      show (approvedBy c u e t).eval s = true ↔ _
      rw [ih]
      constructor
      · rintro ⟨p', x', f', hm, h1, h2, h3⟩; exact ⟨p', x', f', List.mem_cons_of_mem _ hm, h1, h2, h3⟩
      · rintro ⟨p', x', f', hm, h1, h2, h3⟩
        rcases List.mem_cons.1 hm with he | hm
        · simp only [Prod.mk.injEq, Fact.ofApproval.injEq] at he
          obtain ⟨⟨_, rfl⟩, rfl⟩ := he
          exact absurd ⟨h1, h2⟩ hue
        · exact ⟨p', x', f', hm, h1, h2, h3⟩

/-- **Trusted, read (`trusted_iff`).** At rest, `trusted c u d e` holds
exactly when the admission is the root's, or an approval of a request
for it counts. -/
theorem trusted_iff (h : Inv (family C) s) (hq : s.queue = []) (c u : Id) (d e : Key) :
    (trusted c u d e).eval s = true ↔
      V C s.ops c (.admission c u d e) ∨
        ∃ x f, V C s.ops x (.ofApproval f) ∧ f.c = c ∧ f.ru = u ∧ f.rd = d ∧ f.re = e ∧ Counts C s.ops c x := by
  show View.eval s (if _ then _ else _) = true ↔ _
  have hroot : ((Engine.eval s (admission.byDevice.query [c, d])).rows.any
      (fun ((_, y), g) => decide (y = c ∧ g = .admission c u d e))) = true ↔ V C s.ops c (.admission c u d e) := by
    rw [List.any_eq_true]
    constructor
    · rintro ⟨⟨⟨p, y⟩, g⟩, hm, hd⟩
      simp only [decide_eq_true_eq] at hd
      obtain ⟨rfl, rfl⟩ := hd
      obtain ⟨y', g', he, hv, _⟩ := (mem_rows h hq (by simp [rels]) _).1 hm
      simp only [Prod.mk.injEq] at he; obtain ⟨⟨_, rfl⟩, rfl⟩ := he
      exact hv
    · intro hv
      exact ⟨_, (mem_rows h hq (r := admission.byDevice) (by simp [rels]) [c, d]).2
        ⟨c, _, rfl, hv, byDevice_args.2 ⟨u, e, rfl⟩⟩, by simp⟩
  split
  · rename_i hr
    simp only [View.eval, true_iff]
    exact Or.inl (hroot.1 hr)
  · rename_i hr
    show (approvedBy c u e (Engine.eval s (approval.byRequester.query [c, d])).rows).eval s = true ↔ _
    rw [approvedBy_true h hq _ fun p y g hm => by
      obtain ⟨y', g', he, hv, hk⟩ := (mem_rows h hq (by simp [rels]) _).1 hm
      simp only [Prod.mk.injEq] at he; obtain ⟨⟨_, rfl⟩, rfl⟩ := he
      obtain ⟨f, rfl, hfc, hfd⟩ := byRequester_args.1 hk
      exact ⟨f, rfl, hv, hfc, hfd⟩]
    constructor
    · rintro ⟨p, x, f, hm, h1, h2, h3⟩
      obtain ⟨y, g, he, hv, hk⟩ := (mem_rows h hq (by simp [rels]) _).1 hm
      simp only [Prod.mk.injEq] at he
      obtain ⟨⟨_, hxy⟩, hg⟩ := he
      subst hxy; subst hg
      obtain ⟨f', he', hfc, hfd⟩ := byRequester_args.1 hk
      simp only [Fact.ofApproval.injEq] at he'
      subst he'
      exact Or.inr ⟨_, _, hv, hfc, h1, hfd, h2, h3⟩
    · rintro (hv | ⟨x, f, hv, hc, h1, hd, h2, h3⟩)
      · exact absurd (hroot.2 hv) hr
      · obtain ⟨p, hp⟩ := factIn_some ((factIn_req h hq c d x f).2 ⟨hv, hc, hd⟩)
        exact ⟨p, x, f, hp, h1, h2, h3⟩

theorem trusted_iff' (h : Inv (family C) s) (hq : s.queue = []) {c u : Id} {d e : Key}
    (ha : Admitted C s.ops c u d e) : (trusted c u d e).eval s = true ↔ Trusted C s.ops c u d e := by
  rw [trusted_iff h hq]
  unfold Trusted
  constructor
  · rintro (hr | hx)
    · exact Or.inl hr
    · exact Or.inr ⟨ha, hx⟩
  · rintro (hr | ⟨_, hx⟩)
    · exact Or.inl hr
    · exact Or.inr hx

/-- A trusted admission is Valid. -/
theorem Trusted.admitted {c u : Id} {d e : Key} (h : Trusted C ops c u d e) : Admitted C ops c u d e := by
  rcases h with h | ⟨h, _⟩
  · exact ⟨c, h⟩
  · exact h

theorem eval_live_adm {c c' : Id} {p : Pos} {u : Id} {d e : Key} {t : List (Pos × Fact)}
    (hc : c' = c) :
    (live c ((p, .admission c' u d e) :: t)).eval s =
      if (deviceLive c d).eval s then (u, d, e) :: (live c t).eval s
      else (live c t).eval s := by
  subst hc
  show View.eval s (if c' = c' then _ else _) = _
  rw [if_pos rfl, View.eval_bind', View.eval_bind']
  split <;> rfl

theorem mem_live (c : Id) (rows : List (Pos × Fact)) (u : Id) (d e : Key) :
    (u, d, e) ∈ (live c rows).eval s ↔
      (∃ p, (p, .admission c u d e) ∈ rows) ∧ (deviceLive c d).eval s = true := by
  induction rows with
  | nil => simp [live, View.eval]
  | cons pf t ih =>
    obtain ⟨p, f⟩ := pf
    rw [mem_cons_row]
    cases f with
    | ofAdmission a =>
      obtain ⟨c', u', d', e'⟩ := a
      by_cases hc : c' = c
      · rw [eval_live_adm hc]
        subst hc
        by_cases hz : (deviceLive c' d').eval s = true
        · rw [if_pos hz, List.mem_cons, ih]
          constructor
          · rintro (he | ⟨hq, hr⟩)
            · simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl, rfl⟩ := he
              exact ⟨Or.inl rfl, hz⟩
            · exact ⟨Or.inr hq, hr⟩
          · rintro ⟨he | hq, hr⟩
            · simp only [Fact.admission.injEq] at he
              obtain ⟨_, rfl, rfl, rfl⟩ := he; exact Or.inl rfl
            · exact Or.inr ⟨hq, hr⟩
        · rw [if_neg hz, ih]
          constructor
          · rintro ⟨hq, hr⟩; exact ⟨Or.inr hq, hr⟩
          · rintro ⟨he | hq, hr⟩
            · simp only [Fact.admission.injEq] at he
              obtain ⟨_, _, rfl, _⟩ := he; exact absurd hr hz
            · exact ⟨hq, hr⟩
      · have : (live c ((p, .admission c' u' d' e') :: t)).eval s = (live c t).eval s := by
          show View.eval s (if c' = c then _ else _) = _
          rw [if_neg hc]
        rw [this, ih]
        constructor
        · rintro ⟨hq, hr⟩; exact ⟨Or.inr hq, hr⟩
        · rintro ⟨he | hq, hr⟩
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
      (∃ y, V C s.ops y (.admission c u d e) ∧ r.args (.admission c u d e) = some as) ∧
        Live C s.ops c d := by
  rw [mem_live, exists_row h hq hr, deviceLive_iff h hq]

theorem eval_letIn_adm {c c' : Id} {p : Pos} {u : Id} {d e : Key} {t : List (Pos × Fact)}
    (hc : c' = c) :
    (letIn c ((p, .admission c' u d e) :: t)).eval s =
      if (trusted c u d e).eval s && (deviceLive c d).eval s then (u, d, e) :: (letIn c t).eval s
      else (letIn c t).eval s := by
  subst hc
  show View.eval s (if c' = c' then _ else _) = _
  rw [if_pos rfl, View.eval_bind', View.eval_bind', View.eval_bind']
  split <;> rfl

theorem mem_letIn (c : Id) (rows : List (Pos × Fact)) (u : Id) (d e : Key) :
    (u, d, e) ∈ (letIn c rows).eval s ↔
      (∃ p, (p, .admission c u d e) ∈ rows) ∧ (trusted c u d e).eval s = true ∧
        (deviceLive c d).eval s = true := by
  induction rows with
  | nil => simp [letIn, View.eval]
  | cons pf t ih =>
    obtain ⟨p, f⟩ := pf
    rw [mem_cons_row]
    cases f with
    | ofAdmission a =>
      obtain ⟨c', u', d', e'⟩ := a
      by_cases hc : c' = c
      · rw [eval_letIn_adm hc]
        subst hc
        by_cases hz : ((trusted c' u' d' e').eval s && (deviceLive c' d').eval s) = true
        · rw [if_pos hz, List.mem_cons, ih]
          rw [Bool.and_eq_true] at hz
          constructor
          · rintro (he | ⟨hq, hr⟩)
            · simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl, rfl⟩ := he
              exact ⟨Or.inl rfl, hz⟩
            · exact ⟨Or.inr hq, hr⟩
          · rintro ⟨he | hq, hr⟩
            · simp only [Fact.admission.injEq] at he
              obtain ⟨_, rfl, rfl, rfl⟩ := he; exact Or.inl rfl
            · exact Or.inr ⟨hq, hr⟩
        · rw [if_neg hz, ih]
          constructor
          · rintro ⟨hq, hr⟩; exact ⟨Or.inr hq, hr⟩
          · rintro ⟨he | hq, hr⟩
            · simp only [Fact.admission.injEq] at he
              obtain ⟨_, rfl, rfl, rfl⟩ := he; exact absurd (Bool.and_eq_true _ _ ▸ hr) hz
            · exact ⟨hq, hr⟩
      · have : (letIn c ((p, .admission c' u' d' e') :: t)).eval s = (letIn c t).eval s := by
          show View.eval s (if c' = c then _ else _) = _
          rw [if_neg hc]
        rw [this, ih]
        constructor
        · rintro ⟨hq, hr⟩; exact ⟨Or.inr hq, hr⟩
        · rintro ⟨he | hq, hr⟩
          · simp only [Fact.admission.injEq] at he; exact absurd he.1 hc
          · exact ⟨hq, hr⟩
    | _ =>
      show (u, d, e) ∈ (letIn c t).eval s ↔ _
      rw [ih]
      simp

/-- At rest, the admissions of a whole list of a community relation the
trust rule lets in: its trusted admissions whose device is live. -/
theorem letIn_iff (h : Inv (family C) s) (hq : s.queue = []) {r : Rel Fact} (hr : r ∈ rels)
    (as : List ByteArray) (c u : Id) (d e : Key) :
    (u, d, e) ∈ (letIn c (eval s (r.query as)).rows).eval s ↔
      (∃ y, V C s.ops y (.admission c u d e) ∧ r.args (.admission c u d e) = some as) ∧
        Trusted C s.ops c u d e ∧ Live C s.ops c d := by
  rw [mem_letIn, exists_row h hq hr, deviceLive_iff h hq]
  constructor
  · rintro ⟨⟨y, hy, hk⟩, ht, hl⟩
    exact ⟨⟨y, hy, hk⟩, (trusted_iff' h hq ⟨y, hy⟩).1 ht, hl⟩
  · rintro ⟨⟨y, hy, hk⟩, ht, hl⟩
    exact ⟨⟨y, hy, hk⟩, (trusted_iff' h hq ⟨y, hy⟩).2 ht, hl⟩

/-- **Who we connect to.** At rest, the `allowPeer` view, read over the
node's persisted tables, accepts node key e for community c exactly when
a live device has a trusted admission under e: the root's, or one an
approval that counts admitted (`Trusted`). -/
theorem connect_iff (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (e : Key) :
    (allowPeer c e).eval s = true ↔ ∃ u d, Trusted C s.ops c u d e ∧ Live C s.ops c d := by
  simp only [allowPeer, View.eval_bind, View.eval_read, View.eval_pure, List.any_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨⟨u, d, e'⟩, hm, rfl⟩
    obtain ⟨_, ht, hl⟩ := (letIn_iff h hq (by simp [rels]) [c, e'] c u d e').1 hm
    exact ⟨u, d, ht, hl⟩
  · rintro ⟨u, d, ht, hl⟩
    obtain ⟨y, hv⟩ := ht.admitted
    exact ⟨(u, d, e), (letIn_iff h hq (by simp [rels]) [c, e] c u d e).2
      ⟨⟨y, hv, byKey_args.2 ⟨u, d, rfl⟩⟩, ht, hl⟩, rfl⟩

/-- **No connection to a node with no live device.** -/
theorem refuse_nonmember (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (e : Key)
    (hd : ∀ u d, Admitted C s.ops c u d e → Cut C s.ops c d) :
    (allowPeer c e).eval s = false := by
  cases hb : (allowPeer c e).eval s
  · rfl
  · obtain ⟨u, d, ht, hl⟩ := (connect_iff h hq c e).1 hb
    exact absurd hl (cut_not_live (hd u d ht.admitted))

/-- An approval's request is for the admission it names. -/
theorem approval_request {x r c u : Id} {d e : Key} {l : Bool} {g : Approve.Fact}
    (hx : V C ops x (.ofApproval g)) (hgc : g.c = c) (hgr : g.req = r) (hr : V C ops r (.request c u d e l)) :
    g.ru = u ∧ g.rd = d ∧ g.re = e := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hr', _⟩ := approval_signed hx
  rw [hgc, hgr] at hr'
  have := spec_det hr hr'
  simp only [Verdict.valid.injEq, Fact.ofRequest.injEq, Request.Fact.mk.injEq] at this
  exact ⟨this.2.1.symm, this.2.2.1.symm, this.2.2.2.1.symm⟩

/-- **Approved devices' nodes are let in.** A request admitted by an
admit op citing one approval of it that counts lets in the key it names,
unless one of its device's users is removed. -/
theorem connect_admitted (h : Inv (family C) s) (hq : s.queue = []) {y c r x : Id} {o : Op}
    {d0 e0 : Key} {u : Id} {d e : Key} {l : Bool} {g : Approve.Fact}
    (hy : s.ops y = some o) (hb : (Codec.decode o.body : Option Body) = some .admit)
    (hkd : o.kind = Body.tag .admit) (hreq : o.reqs = [c, r, x]) (hc : V C s.ops c (.admission c c d0 e0))
    (hr : V C s.ops r (.request c u d e l)) (hx : V C s.ops x (.ofApproval g)) (hgc : g.c = c)
    (hgr : g.req = r) (hct : Counts C s.ops c x)
    (hnr : ∀ u' e', Admitted C s.ops c u' d e' → ¬ Removed C s.ops c u') :
    (allowPeer c e).eval s = true :=
  have ha : Admitted C s.ops c u d e := ⟨y, admit_admits hy hb hkd hreq hc hr hx hgc hgr⟩
  have ⟨h1, h2, h3⟩ := approval_request hx hgc hgr hr
  have ht : Trusted C s.ops c u d e := Or.inr ⟨ha, x, g, hx, hgc, h1, h2, h3, hct⟩
  (connect_iff h hq c e).2 ⟨u, d, ht, ⟨u, e, ha⟩, hnr⟩

/-- **Only the founder's and approved devices' nodes are let in.** At
rest, a key `allowPeer` accepts has a live device with a trusted
admission under it: by the root (the founder), or by an admit op citing
exactly a Valid request naming that device and key and one Valid
approval of it; and trusted, so some approval of that request counts. A
request alone never connects: requests sit under keys of their own. -/
theorem connect_approved (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (e : Key)
    (ha : (allowPeer c e).eval s = true) :
    ∃ u d y, V C s.ops y (.admission c u d e) ∧ Live C s.ops c d ∧ Trusted C s.ops c u d e ∧
      ((y = c ∧ u = c) ∨
        ∃ o r x l, ∃ g : Approve.Fact, s.ops y = some o ∧ (Codec.decode o.body : Option Body) = some .admit ∧
          o.reqs = [c, r, x] ∧ V C s.ops r (.request c u d e l) ∧
          V C s.ops x (.ofApproval g) ∧ g.c = c ∧ g.req = r ∧ g.ru = u ∧ g.rd = d ∧ g.re = e) := by
  obtain ⟨u, d, ht, hl⟩ := (connect_iff h hq c e).1 ha
  obtain ⟨y, hy⟩ := ht.admitted
  exact ⟨u, d, y, hy, hl, ht, admission_approved h.key hy⟩

theorem mem_live_all (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (u : Id) (d e : Key) :
    (u, d, e) ∈ (live c (eval s (admission.all.query [c])).rows).eval s ↔
      Admitted C s.ops c u d e ∧ Live C s.ops c d := by
  rw [live_iff h hq (by simp [rels])]
  constructor
  · rintro ⟨⟨y, hv, _⟩, hl⟩; exact ⟨⟨y, hv⟩, hl⟩
  · rintro ⟨⟨y, hv⟩, hl⟩; exact ⟨⟨y, hv, all_args.2 ⟨u, d, e, rfl⟩⟩, hl⟩

theorem mem_letIn_all (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (u : Id) (d e : Key) :
    (u, d, e) ∈ (letIn c (eval s (admission.all.query [c])).rows).eval s ↔
      Trusted C s.ops c u d e ∧ Live C s.ops c d := by
  rw [letIn_iff h hq (by simp [rels])]
  constructor
  · rintro ⟨_, ht, hl⟩; exact ⟨ht, hl⟩
  · rintro ⟨ht, hl⟩
    obtain ⟨y, hv⟩ := ht.admitted
    exact ⟨⟨y, hv, all_args.2 ⟨u, d, e, rfl⟩⟩, ht, hl⟩

/-- **Whom we dial.** At rest, `members` names exactly the live devices
with a trusted admission. -/
theorem members_iff (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (d : Key) :
    d ∈ (members c).eval s ↔ (∃ u e, Trusted C s.ops c u d e) ∧ Live C s.ops c d := by
  simp only [members, View.eval_bind, View.eval_read, View.eval_pure, List.mem_map]
  constructor
  · rintro ⟨⟨u, d', e⟩, hm, rfl⟩
    obtain ⟨ht, hl⟩ := (mem_letIn_all h hq c u d' e).1 hm
    exact ⟨⟨u, e, ht⟩, hl⟩
  · rintro ⟨⟨u, e, ht⟩, hl⟩
    exact ⟨(u, d, e), (mem_letIn_all h hq c u d e).2 ⟨ht, hl⟩, rfl⟩

/-- **Content keys go exactly where connections go.** At rest,
`recipients` names exactly the keys a live device has a trusted
admission under: the keys `allowPeer` lets in. No outsider, no node
with only cut devices or untrusted admissions, and no live device's
node left out. -/
theorem recipients_iff (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (e : Key) :
    e ∈ (recipients c).eval s ↔ ∃ u d, Trusted C s.ops c u d e ∧ Live C s.ops c d := by
  simp only [recipients, View.eval_bind, View.eval_read, View.eval_pure, List.mem_map]
  constructor
  · rintro ⟨⟨u, d, e'⟩, hm, rfl⟩; exact ⟨u, d, (mem_letIn_all h hq c u d e').1 hm⟩
  · rintro ⟨u, d, hm⟩; exact ⟨(u, d, e), (mem_letIn_all h hq c u d e).2 hm, rfl⟩

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
is let in once a live device has a trusted admission under the same key:
the cut device does not block the node. Trusted means an approval that
counts admitted it: one by a current member, or by the removed user
inside a removal's cut (`no_self_readmission`). -/
theorem new_device_trusted (h : Inv (family C) s) (hq : s.queue = []) {c u u2 : Id} {d d2 e : Key}
    (_ha : Admitted C s.ops c u d e) (_hr : Removed C s.ops c u)
    (ht2 : Trusted C s.ops c u2 d2 e) (hl : Live C s.ops c d2) : (allowPeer c e).eval s = true :=
  (connect_iff h hq c e).2 ⟨u2, d2, ht2, hl⟩

/-! ## The causal cut's laws

A removal records which of the removed user's approvals its author had
seen: the heads of its devices' approval chains (`Behind`, `InCut`).
Those keep admitting; any other approval from its devices admits no one,
and neither does anything above it (`Counts`, `Above`). Trust is read
from the op set alone, so every node holding the same ops agrees. -/

/-- What counts, its up-path counts too. -/
theorem counts_above {c x y : Id} (hy : Counts C ops c y) (ha : Above C ops x y) : Counts C ops c x := by
  induction ha with
  | here => exact hy
  | @up y' f hv hd _ ih => exact ih ((counts_inv hy hv).2.2 hd)

/-- **Outside the cut, an approval admits no one
(`outside_cut_admits_none`).** Let z be a Valid removal of user u with
cut k, and x an approval by a device admitted into u that is not inside
k: one its device signed after its author's view, or a fork of its chain
signed with an old place. Then x does not count, and neither does any
approval x is above: whatever x admitted, and whatever they approved in
turn, is trusted only through some other approval. -/
theorem outside_cut_admits_none {z c u r x : Id} {k : List (Key × Id × Nat)} {f : Approve.Fact} {e : Key}
    (hz : V C ops z (.removal c u r k)) (hx : V C ops x (.ofApproval f)) (ha : Admitted C ops c u f.dev e)
    (hout : ¬ InCut C ops x f k) : ∀ y, Above C ops x y → ¬ Counts C ops c y := by
  intro y hab hy
  have hcx := counts_above hy hab
  exact hout ((counts_inv hcx hx).2.1 u e z r k ha hz)

/-- **No self-readmission (`no_self_readmission`).** Let z be a Valid
removal of user u with cut k, and e a node key not the root's. Suppose
every approval of a request naming e is for a device of u (cut by the
removal), or has at or above it an approval by a device of u outside k.
Then the trust rule refuses e: a removed member cannot readmit its node
with approvals signed after its author's view, by itself, by a fork of
its chain, or by anyone it then admits. Only an approval that counts, by
a current member or inside the cut, lets e in. -/
theorem no_self_readmission (h : Inv (family C) s) (hq : s.queue = []) {z c u r : Id}
    {k : List (Key × Id × Nat)} {e : Key} (hz : V C s.ops z (.removal c u r k))
    (hroot : ∀ u' d, ¬ V C s.ops c (.admission c u' d e))
    (hout : ∀ x f, V C s.ops x (.ofApproval f) → f.c = c → f.re = e →
      (∃ e', Admitted C s.ops c u f.rd e') ∨
      ∃ y g e', Above C s.ops y x ∧ V C s.ops y (.ofApproval g) ∧ Admitted C s.ops c u g.dev e' ∧
        ¬ InCut C s.ops y g k) :
    (allowPeer c e).eval s = false := by
  cases hb : (allowPeer c e).eval s
  · rfl
  · obtain ⟨u', d, ht, hl⟩ := (connect_iff h hq c e).1 hb
    rcases ht with hr | ⟨_, x, f, hx, hfc, _, hfd, hfe, hct⟩
    · exact absurd hr (hroot u' d)
    · rcases hout x f hx hfc hfe with ⟨e', hd⟩ | ⟨y, g, e', hab, hy, hay, hnot⟩
      · rw [hfd] at hd
        exact absurd hl (cut_not_live ⟨u, e', hd, z, r, k, hz⟩)
      · exact absurd hct (outside_cut_admits_none hz hy hay hnot x hab)

/-- **Inside the cut, admissions stay trusted: no cascade
(`inside_cut_stays`).** An approval that counts keeps counting as more
ops arrive, removals included, as long as each removal's cut keeps every
approval at or above it by the removed user's devices. So a removal
reaches only the approvals its author had not seen; everything its
author had seen, and everyone it admitted, stays. -/
theorem inside_cut_stays {ops ops' : Id → Option Op} (he : Extends ops ops') {c x : Id}
    (hc : Counts C ops c x)
    (hkeep : ∀ y g, Above C ops y x → V C ops y (.ofApproval g) → Kept C ops' c y g) :
    Counts C ops' c x := by
  induction hc with
  | founder hv hfc hd _ => exact .founder (valid_stays he hv) hfc hd (hkeep _ _ .here hv)
  | @up y f hv hfc hd _ _ ih =>
    exact .up (valid_stays he hv) hfc hd (ih fun w g hab hw => hkeep w g (.up hv hd hab) hw)
      (hkeep _ _ .here hv)

/-- **The same ops, the same trust (`trust_agree`).** Nodes holding the
same ops at rest give every admission the same trust verdict, and let in
the same node keys, whatever order the ops arrived in and however they
were judged (`order_free`): trust is a function of the op set. -/
theorem trust_agree {s t : DB Fact} (hs : Inv (family C) s) (ht : Inv (family C) t)
    (qs : s.queue = []) (qt : t.queue = []) (hops : s.ops = t.ops) (c u : Id) (d e : Key) :
    (trusted c u d e).eval s = (trusted c u d e).eval t ∧ (allowPeer c e).eval s = (allowPeer c e).eval t := by
  refine ⟨?_, connect_agree hs ht qs qt hops c e⟩
  have hs' := trusted_iff hs qs c u d e
  have ht' := trusted_iff ht qt c u d e
  rw [hops] at hs'
  cases h1 : (trusted c u d e).eval s <;> cases h2 : (trusted c u d e).eval t
  · rfl
  · rw [h1] at hs'; rw [h2] at ht'
    exact absurd (hs'.2 (ht'.1 rfl)) (by simp)
  · rw [h1] at hs'; rw [h2] at ht'
    exact absurd (ht'.2 (hs'.1 rfl)) (by simp)
  · rfl

/-- **In any arrival order (`trust_order_free`).** Two nodes that
received the same ops, in any orders, batches and interleavings of
judging, give the same trust verdicts once both are at rest. -/
theorem trust_order_free {L M : List Op} {s t : DB Fact} (hs : Reach (family C) L s) (ht : Reach (family C) M t)
    (hd : Distinct (L ++ M)) (hsame : ∀ o, o ∈ L ↔ o ∈ M) (qs : s.queue = []) (qt : t.queue = [])
    (c u : Id) (d e : Key) :
    (trusted c u d e).eval s = (trusted c u d e).eval t ∧ (allowPeer c e).eval s = (allowPeer c e).eval t := by
  have dL : Distinct L := fun a ha b hb => hd a (List.mem_append_left _ ha) b (List.mem_append_left _ hb)
  have dM : Distinct M := fun a ha b hb => hd a (List.mem_append_right _ ha) b (List.mem_append_right _ hb)
  refine trust_agree (reach_inv hs) (reach_inv ht) qs qt ?_ c u d e
  funext i
  cases h1 : s.ops i with
  | none =>
    cases h2 : t.ops i with
    | none => rfl
    | some o =>
      have := (reach_ops ht dM i o).1 h2
      have := (reach_ops hs dL i o).2 ⟨(hsame o).2 this.1, this.2⟩
      rw [h1] at this; cases this
  | some o =>
    have := (reach_ops hs dL i o).1 h1
    exact ((reach_ops ht dM i o).2 ⟨(hsame o).1 this.1, this.2⟩).symm

/-! ### The honest remover's cut

`removeMember` cites the newest approval of each of the target's devices
it holds. A device that signed one chain (one approval at each place) has
every earlier approval behind its newest: so the honest remover's cut
holds every approval of the target it had seen. -/

/-- Behind stays behind as more ops arrive. -/
theorem behind_stays {ops ops' : Id → Option Op} (he : Extends ops ops') {x h : Id}
    (hb : Behind C ops x h) : Behind C ops' x h := by
  induction hb with
  | here => exact .here
  | back hv hn _ ih => exact .back (valid_stays he hv) hn ih

/-- On a device's unforked chain, every approval at or before a place is
behind any approval at that place. -/
theorem behind_of_unforked {c : Id} {dv : Key} {x : Id} {fx : Approve.Fact} (hx : V C ops x (.ofApproval fx))
    (hxc : fx.c = c) (hxd : fx.dev = dv)
    (hone : ∀ y y' g g', V C ops y (.ofApproval g) → V C ops y' (.ofApproval g') → g.c = c → g'.c = c →
      g.dev = dv → g'.dev = dv → g.n = g'.n → y = y') :
    ∀ (k : Nat) (h : Id) (fh : Approve.Fact), V C ops h (.ofApproval fh) → fh.c = c → fh.dev = dv →
      fh.n = fx.n + k → Behind C ops x h
  | 0, h, fh, hv, hc, hd, hn => by
    rw [hone h x fh fx hv hx hc hxc hd hxd (by omega)]; exact .here
  | k + 1, h, fh, hv, hc, hd, hn => by
    have hpos : 0 < fh.n := by omega
    obtain ⟨_, _, _, _, hp⟩ := approval_links hv
    obtain ⟨p, hpv, hpn, hpc, hpd⟩ := hp hpos
    exact .back hv hpos (behind_of_unforked hx hxc hxd hone k fh.prev p hpv (hpc.trans hc)
      (hpd.trans hd) (by omega))

/-- Each head `headsOf` reads of a device in its rows, not yet seen, is
among what it gives. -/
theorem headsOf_mem (c : Id) {dv : Key} {hd : Id} {q : ByteArray} {g : Fact}
    (hh : (Engine.eval s (approval.byDev.query [c, dv] (limit := some 1))).rows.head? = some ((q, hd), g)) :
    ∀ (seen : List Key) (rows : List (Pos × Fact)), seen.any (fun k => decide (k = dv)) = false →
      (∃ p c' u e, (p, Fact.admission c' u dv e) ∈ rows) → hd ∈ (headsOf c seen rows).eval s
  | _, [], _, ⟨_, _, _, _, hm⟩ => by cases hm
  | seen, (p, f) :: t, hs, ⟨p', c', u', e', hm⟩ => by
    have tail : ∀ seen', seen'.any (fun k => decide (k = dv)) = false → (p, f) ≠ (p', .admission c' u' dv e') →
        hd ∈ (headsOf c seen' t).eval s := fun seen' hs' hne =>
      headsOf_mem c hh seen' t hs' ⟨p', c', u', e', (List.mem_cons.1 hm).resolve_left (Ne.symm hne)⟩
    cases f with
    | ofAdmission a =>
      obtain ⟨c'', u'', d', e''⟩ := a
      simp only [headsOf]
      split
      · rename_i hc
        have hne : d' ≠ dv := fun he => by subst he; rw [hs] at hc; cases hc
        exact tail seen hs (by simp [hne])
      · simp only [View.eval, View.eval_bind']
        by_cases hdv : d' = dv
        · subst hdv
          rw [hh]; exact List.mem_cons_self ..
        · have hs' : (d' :: seen).any (fun k => decide (k = dv)) = false := by
            simp only [List.any_cons, hs, Bool.or_false, decide_eq_false_iff_not]
            exact hdv
          have := tail (d' :: seen) hs' (by simp [hdv])
          split
          · exact List.mem_cons_of_mem _ this
          · exact this
    | _ => exact tail seen hs (by simp)

/-- A Valid cut names each of its heads with that head's device and place. -/
theorem mem_cutOf {ops : Id → Option Op} {c : Id} :
    ∀ {ys : List Id} {ps : List Approve.Fact} {k : List (Key × Id × Nat)},
      All2 (fun r g => V C ops r g) ys (ps.map .ofApproval) → Remove.cutOf c ys ps = some k →
      ∀ {y : Id} {g : Approve.Fact}, y ∈ ys → V C ops y (.ofApproval g) → (g.dev, y, g.n) ∈ k
  | [], [], _, _, _, _, _, hy, _ => by cases hy
  | y' :: ys, p :: ps, k, hall, hk, y, g, hy, hv => by
    cases hall with
    | cons hp hrest =>
      simp only [Remove.cutOf] at hk
      split at hk
      · obtain ⟨k', hk', rfl⟩ := Option.map_eq_some_iff.1 hk
        rcases List.mem_cons.1 hy with rfl | hy
        · have := spec_det hp hv
          simp only [Verdict.valid.injEq, Fact.ofApproval.injEq] at this
          subst this; exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (mem_cutOf hrest hk' hy hv)
      · cases hk
  | [], _ :: _, _, hall, _, _, _, _, _ => by cases hall
  | _ :: _, [], _, hall, _, _, _, _, _ => by cases hall

/-- **The honest remover keeps what it saw (`removeMember_keeps`).** A
removal the remover flow writes, once Valid, keeps every approval of the
target that the remover's store held: by any device admitted into the
target, whose chain is unforked (one approval at each place, as the
approving intent writes it) and whose places sort (below 2^64), when the
target has at most `maxHeads` devices with approvals. So an honest
removal casts out no one its target had admitted before the remover's
view: no cascade. -/
theorem removeMember_keeps (h : Inv (family C) s) (hq : s.queue = []) {c t : Id} {d : Device}
    (hsig : ∀ m, C.verify d.pk m (edSign d.sk m) = true)
    {o : Op} (ho : o ∈ ((removeMember c t d).eval s).ops)
    {ops' : Id → Option Op} (he : Extends s.ops ops') (hs : ops' o.id = some o)
    (hcap : ((headsOf c [] (Engine.eval s (admission.byUser.query [c, t])).rows).eval s).length ≤ maxHeads)
    {x : Id} {f : Approve.Fact} (hx : V C s.ops x (.ofApproval f)) (hfc : f.c = c) {e : Key}
    (hdt : Admitted C s.ops c t f.dev e)
    (hsmall : ∀ y g, V C s.ops y (.ofApproval g) → g.c = c → g.dev = f.dev → g.n < 2 ^ 64)
    (hone : ∀ y y' g g', V C s.ops y (.ofApproval g) → V C s.ops y' (.ofApproval g') → g.c = c → g'.c = c →
      g.dev = f.dev → g'.dev = f.dev → g.n = g'.n → y = y') :
    ∃ u k, V C ops' o.id (.removal c t u k) ∧ InCut C ops' x f k := by
  obtain ⟨u, k, _, _, hv⟩ := removeMember_valid h hq hsig ho he hs
  refine ⟨u, k, hv, ?_⟩
  -- the cut, as o's validity reads it
  obtain ⟨o', b, fs, ho', _, hr, hck⟩ := valid_inv hv
  rw [hs] at ho'; cases ho'
  obtain ⟨_, _, _, _, _, _, _, _, ps, rfl, rfl, _, _, _, hcut⟩ := check_removal hck
  obtain ⟨_, _, _, tl, hreq, _, _, _, hrest⟩ := all2_cons3 hr
  obtain ⟨y4, ys, rfl, _, hys⟩ : ∃ y ys, tl = y :: ys ∧ V C ops' y _ ∧
      All2 (fun r g => V C ops' r g) ys _ := by
    cases hrest with | cons h1 h2 => exact ⟨_, _, rfl, h1, h2⟩
  have hd4 : o.reqs.drop 4 = ys := by rw [hreq]; rfl
  rw [hd4] at hcut
  -- the head of x's device's chain: its newest approval
  obtain ⟨y', f', hhead, hv', hk', hle⟩ := first_after (r := approval.byDev) (by simp [rels]) h hq hx
    (byDev_args.2 ⟨f, rfl, hfc, rfl⟩)
  obtain ⟨g, rfl, hgc, hgd⟩ := byDev_args.1 hk'
  -- it is among the heads cited
  obtain ⟨y0, hy0⟩ := hdt
  have hrow := (exists_row h hq (r := admission.byUser) (by simp [rels]) [c, t] _).2
    ⟨y0, hy0, admission_byUser_args.2 ⟨f.dev, e, rfl⟩⟩
  obtain ⟨p, hp⟩ := hrow
  have hin := headsOf_mem c hhead [] _ rfl ⟨p, c, t, e, hp⟩
  have hin' : y' ∈ ys := by rw [← hd4, removeMember_reqs ho, List.take_of_length_le hcap]; exact hin
  have hmem := mem_cutOf hys hcut hin' (valid_stays he hv')
  rw [hgd] at hmem
  -- x is at or before the head's place, so behind it
  have hnle : f.n ≤ g.n := by
    simp only [Pos.cmp, ne_eq, Ordering.then_eq_gt, not_or, not_and, sortOf, Approve.sortKey] at hle
    rw [bcmp_eq_lexCmp, lexCmp_be64 (hsmall x f hx hfc rfl) (hsmall y' g hv' hgc hgd)] at hle
    rcases Nat.lt_or_ge g.n f.n with hlt | hge
    · exact absurd (Nat.compare_eq_gt.2 hlt) hle.1
    · exact hge
  exact ⟨y', g.n, hmem, behind_stays he (behind_of_unforked hx hfc rfl hone (g.n - f.n) y' g hv' hgc hgd
    (by omega))⟩

/-- At rest, the ids of a user's removals list are its Valid removals. -/
theorem byUser_ids (h : Inv (family C) s) (hq : s.queue = []) (c u x : Id) :
    x ∈ (Engine.eval s (removal.byUser.query [c, u])).rows.map (·.1.2) ↔
      ∃ by_ k, V C s.ops x (.removal c u by_ k) := by
  simp only [List.mem_map]
  constructor
  · rintro ⟨pf, hm, rfl⟩
    obtain ⟨y, f, rfl, hv, hk⟩ := (mem_rows h hq (by simp [rels]) _).1 hm
    obtain ⟨r, k, rfl⟩ := byUser_args.1 hk
    exact ⟨r, k, hv⟩
  · rintro ⟨r, k, hv⟩
    exact ⟨_, (mem_rows h hq (by simp [rels]) _).2 ⟨x, _, rfl, hv, byUser_args.2 ⟨r, k, rfl⟩⟩, rfl⟩

theorem mem_removalsOf (h : Inv (family C) s) (hq : s.queue = []) (c x : Id) (rows : List (Pos × Fact)) :
    x ∈ (removalsOf c rows).eval s ↔
      ∃ p c' u d e by_ k, (p, .admission c' u d e) ∈ rows ∧ V C s.ops x (.removal c u by_ k) := by
  induction rows with
  | nil => simp [removalsOf, View.eval]
  | cons pf t ih =>
    obtain ⟨p, f⟩ := pf
    cases f with
    | ofAdmission x =>
      obtain ⟨c', u, d, e⟩ := x
      show x ∈ View.eval s ((removalsOf c t).bind _) ↔ _
      rw [View.eval_bind']
      simp only [View.eval, List.mem_append, ih, byUser_ids h hq, List.mem_cons, Prod.mk.injEq]
      constructor
      · rintro (⟨r, k, hv⟩ | ⟨p', c'', u', d', e', r, k, hm, hv⟩)
        · exact ⟨p, c', u, d, e, r, k, Or.inl ⟨rfl, rfl⟩, hv⟩
        · exact ⟨p', c'', u', d', e', r, k, Or.inr hm, hv⟩
      · rintro ⟨p', c'', u', d', e', r, k, ⟨_, he⟩ | hm, hv⟩
        · simp only [Fact.admission.injEq] at he
          obtain ⟨_, rfl, _, _⟩ := he
          exact Or.inl ⟨r, k, hv⟩
        · exact Or.inr ⟨p', c'', u', d', e', r, k, hm, hv⟩
    | _ =>
      show x ∈ (removalsOf c t).eval s ↔ _
      rw [ih]
      constructor
      · rintro ⟨p', c'', u', d', e', r, k, hm, hv⟩; exact ⟨p', c'', u', d', e', r, k, List.mem_cons_of_mem _ hm, hv⟩
      · rintro ⟨p', c'', u', d', e', r, k, hm, hv⟩
        rcases List.mem_cons.1 hm with he | hm
        · simp at he
        · exact ⟨p', c'', u', d', e', r, k, hm, hv⟩

theorem mem_deviceRemovals (h : Inv (family C) s) (hq : s.queue = []) (c x : Id) (rows : List (Pos × Fact)) :
    x ∈ (deviceRemovals c rows).eval s ↔
      ∃ p c' u0 d e, (p, .admission c' u0 d e) ∈ rows ∧
        ∃ u e' by_ k, Admitted C s.ops c u d e' ∧ V C s.ops x (.removal c u by_ k) := by
  have hdev : ∀ d, x ∈ (removalsOf c (Engine.eval s (admission.byDevice.query [c, d])).rows).eval s ↔
      ∃ u e' by_ k, Admitted C s.ops c u d e' ∧ V C s.ops x (.removal c u by_ k) := by
    intro d
    rw [mem_removalsOf h hq]
    constructor
    · rintro ⟨p, c', u, d', e', r, k, hm, hv⟩
      obtain ⟨y, f, he, hy, hk⟩ := (mem_rows h hq (by simp [rels]) _).1 hm
      simp only [Prod.mk.injEq] at he; obtain ⟨_, rfl⟩ := he
      obtain ⟨u'', e'', hf⟩ := byDevice_args.1 hk
      simp only [Fact.admission.injEq] at hf; obtain ⟨rfl, rfl, rfl, rfl⟩ := hf
      exact ⟨u, e', r, k, ⟨y, hy⟩, hv⟩
    · rintro ⟨u, e', r, k, ⟨y, hy⟩, hv⟩
      exact ⟨_, c, u, d, e', r, k, (mem_rows h hq (by simp [rels]) _).2
        ⟨y, _, rfl, hy, byDevice_args.2 ⟨u, e', rfl⟩⟩, hv⟩
  induction rows with
  | nil => simp [deviceRemovals, View.eval]
  | cons pf t ih =>
    obtain ⟨p, f⟩ := pf
    cases f with
    | ofAdmission x =>
      obtain ⟨c', u0, d, e⟩ := x
      show x ∈ View.eval s ((removalsOf c _).bind _) ↔ _
      rw [View.eval_bind', View.eval_bind']
      simp only [View.eval, List.mem_append, ih, hdev, List.mem_cons, Prod.mk.injEq]
      constructor
      · rintro (hm | ⟨p', c'', u0', d', e', hm, rest⟩)
        · exact ⟨p, c', u0, d, e, Or.inl ⟨rfl, rfl⟩, hm⟩
        · exact ⟨p', c'', u0', d', e', Or.inr hm, rest⟩
      · rintro ⟨p', c'', u0', d', e', ⟨_, he⟩ | hm, rest⟩
        · simp only [Fact.admission.injEq] at he
          obtain ⟨_, _, rfl, _⟩ := he
          exact Or.inl rest
        · exact Or.inr ⟨p', c'', u0', d', e', hm, rest⟩
    | _ =>
      show x ∈ (deviceRemovals c t).eval s ↔ _
      refine ih.trans ⟨?_, ?_⟩
      · rintro ⟨p', c'', u0', d', e', hm, rest⟩
        exact ⟨p', c'', u0', d', e', List.mem_cons_of_mem _ hm, rest⟩
      · rintro ⟨p', c'', u0', d', e', hm, rest⟩
        rcases List.mem_cons.1 hm with he | hm
        · simp at he
        · exact ⟨p', c'', u0', d', e', hm, rest⟩

/-- **The notices owed to a node (`removals_at`).** At rest,
`removalsAt c e` lists exactly the Valid removals that cut a device
admitted under e: removals of any user such a device is admitted into,
under any key. -/
theorem removals_at (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (e : Key) (x : Id) :
    x ∈ (removalsAt c e).eval s ↔
      ∃ u0 d u e' by_ k, Admitted C s.ops c u0 d e ∧ Admitted C s.ops c u d e' ∧
        V C s.ops x (.removal c u by_ k) := by
  unfold removalsAt
  rw [View.eval_bind]
  simp only [Rel.read, View.eval_read]
  rw [mem_deviceRemovals h hq]
  constructor
  · rintro ⟨p, c', u0, d, e'', hm, u, e', r, k, ha, hv⟩
    obtain ⟨y, f, he, hy, hk⟩ := (mem_rows h hq (by simp [rels]) _).1 hm
    simp only [Prod.mk.injEq] at he; obtain ⟨_, rfl⟩ := he
    obtain ⟨u'', d'', hf⟩ := byKey_args.1 hk
    simp only [Fact.admission.injEq] at hf; obtain ⟨rfl, rfl, rfl, rfl⟩ := hf
    exact ⟨u0, d, u, e', r, k, ⟨y, hy⟩, ha, hv⟩
  · rintro ⟨u0, d, u, e', r, k, ⟨y, hy⟩, ha, hv⟩
    exact ⟨_, c, u0, d, e, (mem_rows h hq (by simp [rels]) _).2
      ⟨y, _, rfl, hy, byKey_args.2 ⟨u0, d, rfl⟩⟩, u, e', r, k, ha, hv⟩

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
  rintro u e ⟨y, hy⟩
  obtain ⟨p, hp⟩ := (exists_row h hq (by simp [rels]) [c, d] _).2 ⟨y, hy, byDevice_args.2 ⟨u, e, rfl⟩⟩
  rw [List.isEmpty_iff] at he; rw [he] at hp; cases hp

/-- At rest, d's admissions counted are nonzero exactly when d is admitted. -/
theorem admitted_total (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (d : Key) :
    (Engine.eval s (admission.byDevice.query [c, d] (limit := some 0))).total ≠ 0 ↔
      ∃ u e, Admitted C s.ops c u d e := by
  rw [← Nat.pos_iff_ne_zero,
    total_rel (fam := family C) rfl rels_distinct (by simp [rels]) (rels_short _ (by simp [rels])) h hq]
  constructor
  · rintro ⟨y, f, hv, hk⟩
    obtain ⟨u, e, rfl⟩ := byDevice_args.1 hk
    exact ⟨u, e, y, hv⟩
  · rintro ⟨u, e, y, hv⟩
    exact ⟨y, _, hv, byDevice_args.2 ⟨u, e, rfl⟩⟩

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
        ∃ u' d, Trusted C s'.ops c u' d e ∧ Live C s'.ops c d ∧ ∀ e', ¬ Admitted C s'.ops c u d e' := by
  have hr' := removed_stays he hr
  refine ⟨hr', fun d e ha => ⟨⟨u, e, ha, hr'⟩, cut_not_live ⟨u, e, ha, hr'⟩⟩, fun e hp => ?_⟩
  obtain ⟨u', d, ha, hl⟩ := (connect_iff h' hq' c e).1 hp
  exact ⟨u', d, ha, hl, fun e' hu => hl.2 u e' hu hr'⟩
open Engine Engine.View

theorem always_of {α : Type} {P : α → Prop} (h : ∀ a, P a) : ∀ {v : View Fact α}, Always P v
  | .pure a => h a
  | .list _ k => fun a => always_of h (v := k a)

/-- **An approval writes at most three ops**: the approval, the
admission it gives, and one wrap of the key to the new member's node
key, whatever the community holds. -/
theorem approveReq_ops (c req myAdm : Id) (d : Device) (esk : ByteArray) :
    Always (fun w : Write => w.ops.length ≤ 3) (approveReq c req myAdm d esk) := by
  unfold approveReq
  refine always_bind fun _ => always_bind fun _ => always_bind fun _ => always_bind ?_
  refine always_of fun _ => ?_
  show Always _ (_ >>= _)
  refine always_bind fun _ => always_bind fun ks => ?_
  dsimp only
  repeat' split
  all_goals (try simp only [Always, pure_eq])
  all_goals (repeat' split)
  all_goals simp

/-- **An approval wraps the key only beside its admission.** Whatever
the store holds, an approval's write is the approval alone, or the
approval, then the admission citing exactly it (`admit_admits`: Valid
when the approval is), then the rest (at most one wrap: `approveReq_ops`).
So no approval wraps the key to a requester the same write does not
admit. -/
theorem approveReq_wrap_admits (c req myAdm : Id) (d : Device) (esk : ByteArray) :
    Always (fun w : Write => ∃ up prev, w.ops = [approve c req myAdm d up prev] ∨
      ∃ rest, w.ops = approve c req myAdm d up prev :: admit c req (approve c req myAdm d up prev).id :: rest)
      (approveReq c req myAdm d esk) := by
  unfold approveReq
  refine always_bind fun _ => always_bind fun _ => always_bind fun _ => always_bind ?_
  refine always_of fun up => ?_
  show Always _ (_ >>= _)
  refine always_bind fun hd => always_bind fun ks => ?_
  dsimp only
  repeat' split
  all_goals (try simp only [Always, pure_eq])
  all_goals exact ⟨up, hd.rows.head?.map (·.1.2), by simp⟩

/-- **The remover cites at most 64 requirements**, whatever the store
holds: four, then at most `maxHeads` chain heads, however many devices
the target has. So the intake cap (64) refuses none of its writes. -/
theorem removeMember_reqs_le (c t : Id) (d : Device) :
    Always (fun w : Write => ∀ o ∈ w.ops, o.reqs.length ≤ 4 + maxHeads) (removeMember c t d) := by
  unfold removeMember
  refine always_bind fun _ => always_bind fun _ => always_bind fun _ => ?_
  try simp only [Always]
  split
  · refine always_bind fun _ => ?_
    try simp only [Always]
    split
    · refine always_bind ?_
      refine always_of fun hs => ?_
      refine fun o ho => ?_
      simp only [] at ho
      split at ho
      · cases ho
      · simp only [List.mem_singleton] at ho
        subst ho
        simp only [remove, mkOp, Op.make_reqs, List.length_append, List.length_cons, List.length_nil]
        have := List.length_take_le maxHeads hs
        omega
    · intro o ho; cases ho
  · intro o ho; cases ho

/-- **An approval cites at most five requirements**: the community, the
request, its approver's admission, `up` and `prev`. -/
theorem approve_reqs_le (c req adm : Id) (d : Device) (up prev : Option Id) :
    (approve c req adm d up prev).reqs.length ≤ 5 := by
  cases up <;> cases prev <;> simp [approve, mkOp]

/-- The mutant: an approval that wraps the key to every member's node
key (each admission's). -/
def approveWrapAll (c req myAdm : Id) (d : Device) (esk : Key32) : View Fact Write := do
  let ok := approve c req myAdm d
  let ks ← key.byCommunity.read [c] (limit := some 1)
  let rs ← admission.all.read [c]
  return ⟨ok :: (match ks.rows.head? with
    | some (_, .key _ _ k) => match Bytes.of? k with
      | some k => rs.rows.filterMap fun (_, f) => match f with
        | .admission _ _ _ e => some (wrapKey c k esk e)
        | _ => none
      | none => []
    | _ => [])⟩

/-- **Wrapping to every member is over the budget**: a community of
three members makes four ops. -/
theorem wrapAll_over (c req myAdm : Id) (d : Device) (esk : Key32) (p : Pos) (kid : ByteArray) (k : Key32)
    (u₁ u₂ u₃ : Id) (d₁ d₂ d₃ e₁ e₂ e₃ : Key) :
    ¬ Always (fun w : Write => w.ops.length ≤ 3) (approveWrapAll c req myAdm d esk) := by
  intro h
  -- the key; c's admissions
  have := always_runWith [⟨[(p, .key c kid k.1)], 1, 1⟩,
    ⟨[(p, .admission c u₁ d₁ e₁), (p, .admission c u₂ d₂ e₂), (p, .admission c u₃ d₃ e₃)], 3, 3⟩] h (by
      simp only [approveWrapAll, Rel.read, View.read, bind_eq, pure_eq, View.bind, runWith]
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

section

/-
How a node connects, as functions from what it holds and what arrives to
what it then holds and sends. After poc-17's op-as-wire model over TCP
(a hello sealed to the dialed key, an answer that proves the responder
holds it, then sync over the session) and libquiet's join gate, with
these rules:

- **One trust rule, both ends.** A node opens a session for community c
  with the node whose key is p only if it trusts p: a live device of c is
  admitted under p by the node's own ops (`Allowed`, what `allowPeer`
  answers at rest; see `Net.Bridge`), or, while the node is not yet let
  in itself, p is the key its invite link names and its ops say nothing
  about p yet.
  The responder applies the rule to the initiator, and the initiator to
  the responder. `allowPeer` itself has no exception: the link clause
  is the joiner's only, it ends at the joiner's admission, and it never
  outlives what the ops say about p.
- **A request is delivered, not connected.** A hello may carry one op,
  an introduction, read only if it is a Valid request of c. The
  responder stores it and answers only if it now trusts the sender, so
  a request alone opens nothing and earns no reply. The joiner re-sends
  the same hello every tick until approval lets the answer through.
- **Bootstrap facts are local.** What a node accepts (`accepted`, from
  founding or pasting a link), its link (the dial key and the request,
  presented until admitted) and its sessions are node-local, never ops,
  and nothing on the wire can create them. Ops of other communities
  are dropped, and only a session's community's ops are read from it.

Sync is abstracted as "send the session's community's ops"; reconciling
by fingerprints instead of whole sets is its own protocol.

The cryptography of the handshake (the hello is sealed to the dialed
node's key; the answer proves possession of that key) is abstracted: a
hello is read only by its addressee, and an answer is taken only from
the node the node dialed. A node is named by its own key (its
`endpoint`), which the roots and requests of the devices it holds name
as their `enc`: the transport authenticates the node key, and the
admissions tie it to devices (docs/REMOVAL.md).
-/

namespace Net
open Engine Community

/-- The engine's op table over the ops a node holds: each id to its op. -/
def table (L : List Op) : Id → Option Op := fun x => L.find? fun o => decide (o.id = x)

section
variable (C : Crypto)

/-- A live device of c is admitted under node key p, by these ops: what
`allowPeer` answers once they are processed (`Net.Bridge`). -/
def Allowed (L : List Op) (c : Id) (p : Key) : Prop :=
  ∃ u d, Trusted C (table L) c u d p ∧ Live C (table L) c d

/-- These ops say something about node key p: a device was admitted
under it (into a user removed or not). -/
def Known (L : List Op) (c : Id) (p : Key) : Prop := ∃ u d, Admitted C (table L) c u d p

end

/-- A pasted invite link, kept until this node is admitted: the
community, the inviter's node key (whom to dial, and the one node
trusted before any ops arrive), and the request composed once at paste
(libquiet's pending join). -/
structure Link where
  c : Id
  dial : Key
  req : Op
  deriving DecidableEq

/-- A node: its key, the ops it holds, the communities it accepted, its
pending link, and its open sessions (community, peer key). -/
structure Node where
  me : Key
  ops : List Op
  accepted : List Id
  links : List Link
  sessions : List (Id × Key)

/-- What travels: a hello (poc-17's conn.request, sealed to dst) with an
optional introduction; an answer (conn.connection); and ops pushed over a
session. -/
inductive Msg where
  | hello (c : Id) (src dst : Key) (intro : Option Op)
  | answer (c : Id) (src dst : Key)
  | push (c : Id) (src dst : Key) (ops : List Op)
  deriving DecidableEq

def Msg.dst : Msg → Key
  | .hello _ _ d _ => d
  | .answer _ _ d => d
  | .push _ _ d _ => d

/-- An op of community c: its root, or an op whose slot 0 is c. -/
def ofC (c : Id) (o : Op) : Bool :=
  decide (o.reqs.head? = some c) || (o.reqs.isEmpty && decide (o.id = c))

/-- Store an op unless one with its id is held. -/
def add1 (L : List Op) (o : Op) : List Op :=
  if L.any fun p => decide (p.id = o.id) then L else L ++ [o]

def add (L : List Op) (os : List Op) : List Op := os.foldl add1 L

def ins (l : List (Id × Key)) (s : Id × Key) : List (Id × Key) :=
  if l.any fun t => decide (t = s) then l else l ++ [s]

section
open Classical
variable (C : Crypto)

/-- The node key p this node is told to dial for c by its link. -/
def Node.Anchored (n : Node) (c : Id) (p : Key) : Prop := ∃ l ∈ n.links, l.c = c ∧ l.dial = p

/-- **The trust rule.** -/
def Trusts (n : Node) (c : Id) (p : Key) : Prop :=
  c ∈ n.accepted ∧
    (Allowed C n.ops c p ∨
      (n.Anchored c p ∧ ¬ Known C n.ops c p ∧ ¬ Allowed C n.ops c n.me))

/-- The one op read from a peer not trusted: a Valid request of c. -/
def IntroOk (n : Node) (c : Id) (q : Op) : Prop :=
  ofC c q = true ∧ ∃ u d e l, V C (table (add1 n.ops q)) q.id (.request c u d e l)

/-- A hello from i for c: store its introduction if it is a Valid
request; answer, and open the session, only if i is trusted. -/
noncomputable def onHello (n : Node) (c : Id) (i : Key) (intro : Option Op) : Node × List Msg :=
  if c ∈ n.accepted then
    let n1 := match intro with
      | some q => if IntroOk C n c q then { n with ops := add1 n.ops q } else n
      | none => n
    if Trusts C n1 c i then ({ n1 with sessions := ins n1.sessions (c, i) }, [.answer c n.me i])
    else (n1, [])
  else (n, [])

/-- An answer from r for c: open the session if this node dialed r for c
and trusts it. -/
noncomputable def onAnswer (n : Node) (c : Id) (r : Key) : Node :=
  if n.Anchored c r ∧ Trusts C n c r then { n with sessions := ins n.sessions (c, r) } else n

/-- Ops from p for c: stored only over an open session with a peer still
trusted, and only c's. -/
noncomputable def onPush (n : Node) (c : Id) (p : Key) (os : List Op) : Node :=
  if (c, p) ∈ n.sessions ∧ Trusts C n c p then { n with ops := add n.ops (os.filter (ofC c)) }
  else n

/-- The links a tick keeps: those of communities this node is not yet
admitted to. -/
noncomputable def keptLinks (n : Node) : List Link :=
  n.links.filter fun l => !decide (Allowed C n.ops l.c n.me)

/-- A node after a tick's bookkeeping: links of communities it is now
admitted to forgotten, sessions with peers no longer trusted closed. -/
noncomputable def ticked (n : Node) : Node :=
  let n1 := { n with links := keptLinks C n }
  { n1 with sessions := n1.sessions.filter fun s => decide (Trusts C n1 s.1 s.2) }

/-- What a tick sends: each pending link's hello, with its request, until
its session opens; each session's community's ops. -/
def sends (n : Node) : List Msg :=
  (n.links.filter fun l => !n.sessions.any fun s => decide (s = (l.c, l.dial))).map
    (fun l => Msg.hello l.c n.me l.dial (some l.req)) ++
  n.sessions.map fun s => Msg.push s.1 n.me s.2 (n.ops.filter (ofC s.1))

/-- A tick. -/
noncomputable def tick (n : Node) : Node × List Msg := (ticked C n, sends (ticked C n))

/-- A node's reaction to a message addressed to it. -/
noncomputable def recv (n : Node) : Msg → Node × List Msg
  | .hello c i _ q => onHello C n c i q
  | .answer c r _ => (onAnswer C n c r, [])
  | .push c p _ os => (onPush C n c p os, [])

end

end Net

end

section

/-
Two nodes and the socket between them. The socket holds the messages in
flight, as a bag: any one may be delivered next (reordering), and a
re-sent message is a second copy (duplication). On a socket with
failure any message may also be dropped. Nodes act on ticks; the
approver's user approves when it chooses.

Runs are infinite. A run is fair when both nodes tick forever, the
approver keeps acting (approving whatever is pending; doing nothing
otherwise), and the socket is fair-lossy: a message sent at infinitely
many steps is delivered at infinitely many steps. A sent message may be
lost any finite number of times; resending is what overcomes it.
-/

namespace Net
open Engine Community

structure Sys where
  a : Node
  b : Node
  net : List Msg

inductive Act where
  | tickA
  | tickB
  | approve
  | deliver (m : Msg)
  | drop (m : Msg)
  deriving DecidableEq

section
variable (C : Crypto) (approval : Node → Node)

/-- One step: the next state, and the messages sent by it. A message is
read by the node it is addressed to. -/
noncomputable def stepOut (s : Sys) : Act → Sys × List Msg
  | .tickA => let t := tick C s.a; ({ s with a := t.1, net := s.net ++ t.2 }, t.2)
  | .tickB => let t := tick C s.b; ({ s with b := t.1, net := s.net ++ t.2 }, t.2)
  | .approve => ({ s with a := approval s.a }, [])
  | .deliver m =>
    if m.dst = s.a.me then
      let t := recv C s.a m; ({ s with a := t.1, net := s.net.erase m ++ t.2 }, t.2)
    else if m.dst = s.b.me then
      let t := recv C s.b m; ({ s with b := t.1, net := s.net.erase m ++ t.2 }, t.2)
    else ({ s with net := s.net.erase m }, [])
  | .drop m => ({ s with net := s.net.erase m }, [])

noncomputable def step (s : Sys) (act : Act) : Sys := (stepOut C approval s act).1
noncomputable def sent (s : Sys) (act : Act) : List Msg := (stepOut C approval s act).2

/-- Delivering or dropping needs the message in flight. -/
def Enabled (s : Sys) : Act → Prop
  | .deliver m => m ∈ s.net
  | .drop m => m ∈ s.net
  | _ => True

/-- The states reachable from init, over a socket with failure. -/
inductive Reachable (init : Sys) : Sys → Prop
  | init : Reachable init init
  | step {s : Sys} (act : Act) : Reachable init s → Enabled s act →
      Reachable init (step C approval s act)

/-- These actions, taken in order from s, each enabled when taken, end
in t. -/
inductive Path : Sys → List Act → Sys → Prop
  | nil (s : Sys) : Path s [] s
  | cons {s t : Sys} {act : Act} {acts : List Act} : Enabled s act →
      Path (step C approval s act) acts t → Path s (act :: acts) t

/-- An infinite run from init. -/
structure Run (init : Sys) where
  st : Nat → Sys
  act : Nat → Act
  zero : st 0 = init
  next : ∀ i, Enabled (st i) (act i) ∧ st (i + 1) = step C approval (st i) (act i)

def Run.Fair {init : Sys} (r : Run C approval init) : Prop :=
  (∀ N, ∃ i ≥ N, r.act i = .tickA) ∧
  (∀ N, ∃ i ≥ N, r.act i = .tickB) ∧
  (∀ N, ∃ i ≥ N, r.act i = .approve) ∧
  ∀ m, (∀ N, ∃ i ≥ N, m ∈ sent C approval (r.st i) (r.act i)) →
    ∀ N, ∃ i ≥ N, r.act i = .deliver m

/-- The socket never fails. -/
def Run.Ideal {init : Sys} (r : Run C approval init) : Prop := ∀ i m, r.act i ≠ .drop m

end

end Net

end

section

/-
The bootstrap scene: founder A creates community c and invites B with a
member invitation that needs one approval; B pastes the link. The ops
are the real ones, composed by lean-engine's `Community.Compose` (op
ids are SHA-256, signatures Ed25519 through `edSign`), and judged by
the real validators. What is assumed is stated in `Good`: the
five signatures on this scene verify, A and B are
different devices, and the five ops' ids are distinct (SHA-256 does not
collide on them).

Then: among any of these ops a node may hold, what is Valid, who is
admitted, and that nobody is removed. These are what the protocol's
decisions come down to in this scene.
-/

namespace Net
open Engine Community Codec

structure Scene where
  /-- The founder's device. -/
  A : Device
  /-- The joiner's device. -/
  B : Device
  /-- The founder's node key: its dial key, named by the root. -/
  kA : Key
  /-- The joiner's node key, named by its request. -/
  kB : Key
  /-- The bearer seed the invitation's key pair derives from; it is in
  the link. -/
  secret : ByteArray

namespace Scene
variable (x : Scene)

def r : Op := root x.A x.kA
def c : Id := x.r.id
/-- The invitation and its link, as A's app issues them (Community.issue). -/
def issued : Op × Invite := issue x.c x.c x.A x.kA x.secret []
def inv : Op := x.issued.1
def inviteLink : Invite := x.issued.2
/-- The bearer key pair, from the link's seed. -/
def K : Device := x.inviteLink.bearer
/-- B's request, as B's app composes it from the link it parsed
(`parse_text`: the text parses back to `inviteLink`). -/
def req : Op := x.inviteLink.request x.B x.kB
def appr : Op := approve x.c x.req.id x.c x.A
def adm : Op := admit x.c x.req.id x.appr.id
def S : List Op := [x.r, x.inv, x.req, x.appr, x.adm]

/-- B's link: community, A's node key to dial, B's request. -/
def link : Link := ⟨x.c, x.kA, x.req⟩

/-- A after founding and inviting; B after pasting the link. -/
def a0 : Node := ⟨x.kA, [x.r, x.inv], [x.c], [], []⟩
def b0 : Node := ⟨x.kB, [x.req], [x.c], [x.link], []⟩
def init : Sys := ⟨x.a0, x.b0, []⟩

/-- What A's user does on approving B's request, once A holds it: A signs
the approval and composes the admission. -/
def approval (n : Node) : Node :=
  if n.ops.any (fun o => decide (o = x.req)) then { n with ops := add n.ops [x.appr, x.adm] } else n

/-- The four signed payloads in this five-op scene. The request has two
signatures; the final admission is unsigned and checked by its dependencies. -/
def rootMessage : ByteArray := toSign [] (.root x.A.pk x.kA .empty)
def invitationMessage : ByteArray := toSign [x.c,x.c] (.invite x.K.pk false .empty)
def requestMessage : ByteArray := toSign [x.c,x.inv.id] (.request x.B.pk x.kB .empty .empty)
def approvalMessage : ByteArray := toSign [x.c,x.req.id,x.c] (.approve .empty)

/-- Exactly the finite cryptographic premises used by this scene's proofs.
No correctness claim about signatures on other messages is required. -/
structure Good (C : Crypto) : Prop where
  rootSig : C.verify x.A.pk x.rootMessage (edSign x.A.sk x.rootMessage) = true
  invitationSig : C.verify x.A.pk x.invitationMessage (edSign x.A.sk x.invitationMessage) = true
  requestSig : C.verify x.B.pk x.requestMessage (edSign x.B.sk x.requestMessage) = true
  bearerSig : C.verify x.K.pk x.requestMessage (edSign x.K.sk x.requestMessage) = true
  approvalSig : C.verify x.A.pk x.approvalMessage (edSign x.A.sk x.approvalMessage) = true
  AB : x.A.pk ≠ x.B.pk
  kAB : x.kA ≠ x.kB
  distinct : Distinct x.S

/-- Compatibility constructor for callers that already have the stronger,
universal signing-correctness premises of the former scene contract. -/
theorem Good.ofSigning {C : Crypto}
    (sigA : ∀ m, C.verify x.A.pk m (edSign x.A.sk m) = true)
    (sigB : ∀ m, C.verify x.B.pk m (edSign x.B.sk m) = true)
    (sigK : ∀ m, C.verify x.K.pk m (edSign x.K.sk m) = true)
    (AB : x.A.pk ≠ x.B.pk) (kAB : x.kA ≠ x.kB) (distinct : Distinct x.S) : x.Good C :=
  ⟨sigA _,sigA _,sigB _,sigK _,sigA _,AB,kAB,distinct⟩

end Scene

/-! ## The op table -/

theorem table_some {L : List Op} {i : Id} {o : Op} (h : table L i = some o) : o ∈ L ∧ o.id = i := by
  unfold table at h
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  have := List.find?_some h
  exact of_decide_eq_true this

theorem table_of {L : List Op} (hd : Distinct L) {o : Op} (h : o ∈ L) : table L o.id = some o := by
  unfold table
  cases hf : L.find? (fun p => decide (p.id = o.id)) with
  | none =>
    rw [List.find?_eq_none] at hf
    exact absurd (by simp) (hf o h)
  | some o' =>
    have := table_some hf
    rw [hd o' this.1 o h this.2]

theorem table_keyed (L : List Op) : Keyed (table L) := fun _ _ h => (table_some h).2

theorem distinct_sub {L M : List Op} (hd : Distinct M) (h : ∀ o ∈ L, o ∈ M) : Distinct L :=
  fun a ha b hb => hd a (h a ha) b (h b hb)

namespace Scene
variable {x : Scene} {C : Crypto}

theorem body_mk (reqs : List Id) (b : Body) : (decode (mkOp reqs b).body : Option Body) = some b :=
  decode_encode b

theorem c_eq : x.c = x.r.id := rfl

section
variable {L : List Op} (g : x.Good C) (hL : ∀ o ∈ L, o ∈ x.S)
include g hL

theorem hd : Distinct L := distinct_sub g.distinct hL

theorem v_root (h : x.r ∈ L) : V C (table L) x.c (.admission x.c x.c x.A.pk x.kA) := by
  refine spec_valid_of (table_of (hd g hL) h) (fs := []) .nil ?_
  show validate C x.r [] = _
  unfold validate
  rw [show x.r = root x.A x.kA from rfl, root, body_mk]
  simp only [Body.tag, Op.make_kind, ↓reduceIte, check, Root.check, Invitation.check, Request.check, Approve.check, Admit.check, Grant.check, Remove.check, Post.check, Profile.check]
  rw [if_pos]
  · rfl
  · exact g.rootSig

theorem v_inv (h1 : x.r ∈ L) (h2 : x.inv ∈ L) :
    V C (table L) x.inv.id (.invitation x.c x.c x.K.pk false) := by
  refine spec_valid_of (table_of (hd g hL) h2)
    (fs := [.admission x.c x.c x.A.pk x.kA, .admission x.c x.c x.A.pk x.kA]) ?_ ?_
  · exact .cons (v_root g hL h1) (.cons (v_root g hL h1) .nil)
  · show validate C x.inv _ = _
    unfold validate
    rw [show x.inv = invite x.c x.c x.A x.K.pk false from rfl, invite, body_mk]
    simp only [mkOp, Body.tag, Op.make_kind, ↓reduceIte, check, Root.check, Invitation.check, Request.check, Approve.check, Admit.check, Grant.check, Remove.check, Post.check, Profile.check]
    rw [if_pos]
    · rfl
    refine ⟨?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl | exact g.invitationSig | simp

theorem v_req (h1 : x.r ∈ L) (h2 : x.inv ∈ L) (h3 : x.req ∈ L) :
    V C (table L) x.req.id (.request x.c x.req.id x.B.pk x.kB false) := by
  have := request_valid (C := C) (table_keyed L) (table_of (hd g hL) h3)
    (body_mk _ _) rfl rfl (v_root g hL h1) (v_inv g hL h1 h2) g.requestSig g.bearerSig
  have e : x.inviteLink.community = x.c := rfl
  simpa [e] using this

theorem v_appr (h1 : x.r ∈ L) (h2 : x.inv ∈ L) (h3 : x.req ∈ L) (h4 : x.appr ∈ L) :
    V C (table L) x.appr.id (.approval x.c x.req.id x.c x.A.pk x.req.id x.B.pk x.kB .empty 0 .empty 0) :=
  approve_valid (ys := []) (ps := []) (t := (.empty, 0, .empty, 0)) (table_of (hd g hL) h4) (body_mk _ _)
    rfl rfl (v_root g hL h1) (v_req g hL h1 h2 h3) (v_root g hL h1) .nil (by simp [Approve.links])
    (fun h => absurd h (by simp)) g.AB g.approvalSig

theorem v_adm (h : ∀ o ∈ x.S, o ∈ L) :
    V C (table L) x.adm.id (.admission x.c x.req.id x.B.pk x.kB) := by
  have h1 := h x.r (by simp [S]); have h2 := h x.inv (by simp [S])
  have h3 := h x.req (by simp [S]); have h4 := h x.appr (by simp [S])
  have h5 := h x.adm (by simp [S])
  exact admit_admits (table_of (hd g hL) h5) (body_mk _ _) rfl rfl (v_root g hL h1)
    (v_req g hL h1 h2 h3) (v_appr g hL h1 h2 h3 h4) rfl rfl

omit g in
/-- The op stored under an id among these is that one of the scene's. -/
theorem table_S {i : Id} {o : Op} (h : table L i = some o) : o ∈ x.S ∧ o ∈ L ∧ o.id = i :=
  ⟨hL o (table_some h).1, table_some h⟩

/-- **Who is admitted among these ops**: A, under its node key, by the
root; B, under its node key, by the admit. -/
theorem admitted_inv {c' u : Id} {d e : Key} (h : Admitted C (table L) c' u d e) :
    (d = x.A.pk ∧ e = x.kA ∧ x.r ∈ L) ∨ (d = x.B.pk ∧ e = x.kB ∧ x.adm ∈ L) := by
  obtain ⟨y, hy⟩ := h
  obtain ⟨o, b, fs, hx, hb, hr, hv⟩ := valid_inv hy
  obtain ⟨hS, hoL, _⟩ := table_S hL hx
  simp only [S, List.mem_cons, List.mem_nil_iff, or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl
  · rw [show x.r = root x.A x.kA from rfl, root, body_mk] at hb
    cases hb
    rcases check_admission hv with ⟨s, hb, _⟩ | ⟨_, _, _, _, hb, _⟩
    · cases hb; exact Or.inl ⟨rfl, rfl, hoL⟩
    · cases hb
  · rw [show x.inv = invite x.c x.c x.A x.K.pk false from rfl, invite, body_mk] at hb
    cases hb
    rcases check_admission hv with ⟨s, hb, _⟩ | ⟨_, _, _, _, hb, _⟩ <;> cases hb
  · rw [show x.req = request x.c x.inv.id x.B x.kB x.K.sk from rfl, request, body_mk] at hb
    cases hb
    rcases check_admission hv with ⟨s, hb, _⟩ | ⟨_, _, _, _, hb, _⟩ <;> cases hb
  · rw [show x.appr = approve x.c x.req.id x.c x.A from rfl, approve, body_mk] at hb
    cases hb
    rcases check_admission hv with ⟨s, hb, _⟩ | ⟨_, _, _, _, hb, _⟩ <;> cases hb
  · rcases check_admission hv with ⟨s, hb', _⟩ | ⟨d0, e0, l, a, _, rfl, _⟩
    · rw [show x.adm = admit x.c x.req.id x.appr.id from rfl, admit, body_mk] at hb
      rw [hb'] at hb; cases hb
    · obtain ⟨_, ri, _, hreq, _, hri, _⟩ := all2_cons2 hr
      have hri' : ri = x.req.id := by
        have : x.adm.reqs = x.c :: x.req.id :: [x.appr.id] := rfl
        rw [this] at hreq; simp at hreq; exact hreq.2.1.symm
      subst hri'
      obtain ⟨o', b', fs', hx', hb', _, hv'⟩ := valid_inv hri
      obtain ⟨hS', ho'L, hid'⟩ := table_S hL hx'
      have : o' = x.req := g.distinct o' hS' x.req (by simp [S]) hid'
      subst this
      rw [show x.req = request x.c x.inv.id x.B x.kB x.K.sk from rfl, request, body_mk] at hb'
      cases hb'
      obtain ⟨_, _, _, _, _, _, hb'', _⟩ := check_request hv'
      cases hb''
      exact Or.inr ⟨rfl, rfl, hoL⟩

omit g in
/-- **Nobody is removed** among these ops: none is a removal. -/
theorem not_removed {c' u : Id} : ¬ Removed C (table L) c' u := by
  rintro ⟨y, rr, k, hy⟩
  obtain ⟨o, b, fs, hx, hb, _, hv⟩ := valid_inv hy
  obtain ⟨hS, _, _⟩ := table_S hL hx
  obtain ⟨s, _, _, _, _, _, _, _, _, hb', _⟩ := check_removal hv
  subst hb'
  simp only [S, List.mem_cons, List.mem_nil_iff, or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl
  · rw [show x.r = root x.A x.kA from rfl, root, body_mk] at hb; cases hb
  · rw [show x.inv = invite x.c x.c x.A x.K.pk false from rfl, invite, body_mk] at hb; cases hb
  · rw [show x.req = request x.c x.inv.id x.B x.kB x.K.sk from rfl, request, body_mk] at hb; cases hb
  · rw [show x.appr = approve x.c x.req.id x.c x.A from rfl, approve, body_mk] at hb; cases hb
  · rw [show x.adm = admit x.c x.req.id x.appr.id from rfl, admit, body_mk] at hb; cases hb

omit g in
/-- Every admitted device is live: nobody is removed. -/
theorem live_of {c' u : Id} {d e : Key} (h : Admitted C (table L) c' u d e) : Live C (table L) c' d :=
  ⟨⟨u, e, h⟩, fun _ _ _ => not_removed hL⟩

/-- A's node is known, and allowed, exactly when the root is held. -/
theorem knownA : Known C L x.c x.kA ↔ x.r ∈ L := by
  constructor
  · rintro ⟨u, d, h⟩
    rcases admitted_inv g hL h with ⟨_, _, h⟩ | ⟨_, hk, _⟩
    · exact h
    · exact absurd hk g.kAB
  · intro h; exact ⟨_, _, _, v_root g hL h⟩

theorem allowedA : Allowed C L x.c x.kA ↔ x.r ∈ L := by
  constructor
  · rintro ⟨u, d, h, _⟩; exact (knownA g hL).1 ⟨u, d, h.admitted⟩
  · intro h
    have ha : Admitted C (table L) x.c x.c x.A.pk x.kA := ⟨_, v_root g hL h⟩
    exact ⟨_, _, Or.inl (v_root g hL h), live_of hL ha⟩

/-- B's node is known exactly when its admission is held. -/
theorem knownB : Known C L x.c x.kB → x.adm ∈ L := by
  rintro ⟨u, d, h⟩
  rcases admitted_inv g hL h with ⟨_, hk, _⟩ | ⟨_, _, h⟩
  · exact absurd hk.symm g.kAB
  · exact h

/-- B's node is allowed exactly when its admission is held (with what it
cites). -/
theorem allowedB (hall : x.adm ∈ L → ∀ o ∈ x.S, o ∈ L) :
    Allowed C L x.c x.kB ↔ x.adm ∈ L := by
  constructor
  · rintro ⟨u, d, h, _⟩; exact knownB g hL ⟨u, d, h.admitted⟩
  · intro h
    have ha : Admitted C (table L) x.c x.req.id x.B.pk x.kB := ⟨_, v_adm g hL (hall h)⟩
    have hS := hall h
    have hap := v_appr g hL (hS x.r (by simp [S])) (hS x.inv (by simp [S])) (hS x.req (by simp [S]))
      (hS x.appr (by simp [S]))
    have hct : Counts C (table L) x.c x.appr.id :=
      .founder hap rfl rfl fun _ _ z r k _ hz => absurd ⟨z, r, k, hz⟩ (not_removed hL)
    exact ⟨_, _, Or.inr ⟨ha, _, _, hap, rfl, rfl, rfl, rfl, hct⟩, live_of hL ha⟩

end

end Scene

end Net

end

section

/-
What holds in every state of the scene reachable over a socket with
failure (drops, reordering, duplicates). In the scene, each decision a
node makes comes down to which of the five ops it holds (Net.Scene), so
each handler is worked out here under the invariant, and the invariant
is shown to survive every step.
-/

namespace Net
open Engine Community

/-! ## Lists of ops -/

theorem mem_add1 {L : List Op} {q o : Op} : o ∈ add1 L q → o ∈ L ∨ o = q := by
  unfold add1; split
  · exact Or.inl
  · intro h; rcases List.mem_append.1 h with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_singleton.1 h)

theorem mem_add1_of {L : List Op} {q o : Op} (h : o ∈ L) : o ∈ add1 L q := by
  unfold add1; split
  · exact h
  · exact List.mem_append_left _ h

theorem add1_of_mem {L : List Op} {q : Op} (h : q ∈ L) : add1 L q = L := by
  unfold add1; rw [if_pos]; exact List.any_eq_true.2 ⟨q, h, by simp⟩

theorem self_add1 {M L : List Op} {q : Op} (hd : Distinct M) (hL : ∀ o ∈ L, o ∈ M) (hq : q ∈ M) :
    q ∈ add1 L q := by
  unfold add1; split
  · rename_i h; obtain ⟨o, ho, he⟩ := List.any_eq_true.1 h
    have := hd o (hL o ho) q hq (of_decide_eq_true he); subst this; exact ho
  · exact List.mem_append_right _ (List.mem_singleton_self _)

theorem mem_add {L os : List Op} {o : Op} : o ∈ add L os → o ∈ L ∨ o ∈ os := by
  induction os generalizing L with
  | nil => exact Or.inl
  | cons q rest ih =>
    intro h
    rcases ih h with h | h
    · rcases mem_add1 h with h | rfl
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_self ..)
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem mem_add_of {L os : List Op} {o : Op} (h : o ∈ L) : o ∈ add L os := by
  induction os generalizing L with
  | nil => exact h
  | cons q rest ih => exact ih (mem_add1_of h)

theorem add_of_mem {L os : List Op} (h : ∀ o ∈ os, o ∈ L) : add L os = L := by
  induction os with
  | nil => rfl
  | cons q rest ih =>
    show add (add1 L q) rest = L
    rw [add1_of_mem (h q (List.mem_cons_self ..))]
    exact ih fun o ho => h o (List.mem_cons_of_mem _ ho)

theorem self_add {M L os : List Op} (hd : Distinct M) (hL : ∀ o ∈ L, o ∈ M) (hos : ∀ o ∈ os, o ∈ M)
    {o : Op} (h : o ∈ os) : o ∈ add L os := by
  induction os generalizing L with
  | nil => cases h
  | cons q rest ih =>
    show o ∈ add (add1 L q) rest
    have hL' : ∀ p ∈ add1 L q, p ∈ M := fun p hp => by
      rcases mem_add1 hp with hp | rfl
      · exact hL p hp
      · exact hos p (List.mem_cons_self ..)
    rcases List.mem_cons.1 h with rfl | h
    · exact mem_add_of (self_add1 hd hL (hos o (List.mem_cons_self ..)))
    · exact ih hL' (fun p hp => hos p (List.mem_cons_of_mem _ hp)) h

theorem mem_ins {l : List (Id × Key)} {s p : Id × Key} : p ∈ ins l s ↔ p ∈ l ∨ p = s := by
  unfold ins; split
  · rename_i h
    obtain ⟨t, ht, he⟩ := List.any_eq_true.1 h
    have := of_decide_eq_true he; subst this
    exact ⟨Or.inl, fun h => h.elim id (fun e => e ▸ ht)⟩
  · simp

theorem Node.ext' {n m : Node} (h1 : n.me = m.me) (h2 : n.ops = m.ops) (h3 : n.accepted = m.accepted)
    (h4 : n.links = m.links) (h5 : n.sessions = m.sessions) : n = m := by
  cases n; cases m; simp_all

namespace Scene
open Classical
variable (x : Scene) (C : Crypto)

theorem reqs_r : x.r.reqs = [] := rfl
theorem reqs_inv : x.inv.reqs = [x.c, x.c] := rfl
theorem reqs_req : x.req.reqs = [x.c, x.inv.id] := rfl
theorem reqs_appr : x.appr.reqs = [x.c, x.req.id, x.c] := rfl
theorem reqs_adm : x.adm.reqs = [x.c, x.req.id, x.appr.id] := rfl

theorem ofC_S {o : Op} (h : o ∈ x.S) : ofC x.c o = true := by
  simp only [S, List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;>
    simp [ofC, reqs_r, reqs_inv, reqs_req, reqs_appr, reqs_adm, c]

theorem filter_ofC {L : List Op} (hL : ∀ o ∈ L, o ∈ x.S) : L.filter (ofC x.c) = L :=
  List.filter_eq_self.2 fun o ho => x.ofC_S (hL o ho)

theorem kinds : x.r.kind = 0 ∧ x.inv.kind = 1 ∧ x.req.kind = 12 ∧ x.appr.kind = 10 ∧ x.adm.kind = 11 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem adm_ne : x.adm ≠ x.r ∧ x.adm ≠ x.inv ∧ x.adm ≠ x.req := by
  obtain ⟨h0, h1, h2, -, h4⟩ := x.kinds
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> have := congrArg Op.kind h <;> simp_all

theorem mem_S : x.r ∈ x.S ∧ x.inv ∈ x.S ∧ x.req ∈ x.S ∧ x.appr ∈ x.S ∧ x.adm ∈ x.S := by
  simp [S]

/-! ## The invariant -/

def InS (L : List Op) : Prop := ∀ o ∈ L, o ∈ x.S
def Covers (L : List Op) : Prop := ∀ o ∈ x.S, o ∈ L

def hello : Msg := .hello x.c x.kB x.kA (some x.req)
def answer : Msg := .answer x.c x.kA x.kB

/-- The messages that can be in flight: B's hello; A's answer and A's
ops (all five), both sent only over A's open session with B; B's ops. -/
def NetOk (s : Sys) (m : Msg) : Prop :=
  m = x.hello ∨ (m = x.answer ∧ (x.c, x.kB) ∈ s.a.sessions) ∨
  (∃ os, m = .push x.c x.kA x.kB os ∧ x.InS os ∧ x.Covers os ∧ (x.c, x.kB) ∈ s.a.sessions) ∨
  (∃ os, m = .push x.c x.kB x.kA os ∧ x.InS os)

structure Inv (s : Sys) : Prop where
  ame : s.a.me = x.kA
  bme : s.b.me = x.kB
  aacc : s.a.accepted = [x.c]
  bacc : s.b.accepted = [x.c]
  alinks : s.a.links = []
  blinks : s.b.links = [] ∨ s.b.links = [x.link]
  aS : x.InS s.a.ops
  bS : x.InS s.b.ops
  ar : x.r ∈ s.a.ops
  ai : x.inv ∈ s.a.ops
  breq : x.req ∈ s.b.ops
  acov : x.adm ∈ s.a.ops → x.Covers s.a.ops
  bmore : (∃ o ∈ s.b.ops, o ≠ x.req) → x.Covers s.b.ops ∧ (x.c, x.kA) ∈ s.b.sessions
  asess : ∀ p ∈ s.a.sessions, p = (x.c, x.kB) ∧ x.adm ∈ s.a.ops
  bsess : ∀ p ∈ s.b.sessions, p = (x.c, x.kA) ∧ (x.c, x.kB) ∈ s.a.sessions
  bdone : s.b.links = [] → x.adm ∈ s.b.ops
  net : ∀ m ∈ s.net, x.NetOk s m

variable {x C} {s : Sys}

theorem Inv.bcov (hI : x.Inv s) (h : x.adm ∈ s.b.ops) : x.Covers s.b.ops :=
  (hI.bmore ⟨_, h, x.adm_ne.2.2⟩).1

theorem inv_init : x.Inv x.init := by
  have ne := x.adm_ne
  refine { ame := rfl, bme := rfl, aacc := rfl, bacc := rfl, alinks := rfl, blinks := Or.inr rfl,
           aS := ?_, bS := ?_, ar := by simp [init, a0], ai := by simp [init, a0],
           breq := by simp [init, b0], acov := ?_, bmore := ?_, asess := by simp [init, a0],
           bsess := by simp [init, b0], bdone := by simp [init, b0], net := by simp [init] }
  · intro o h; simp [init, a0] at h; rcases h with rfl | rfl <;> simp [S]
  · intro o h; simp [init, b0] at h; subst h; simp [S]
  · intro h; simp [init, a0] at h; rcases h with h | h
    · exact absurd h ne.1
    · exact absurd h ne.2.1
  · rintro ⟨o, h, hne⟩; simp [init, b0] at h; exact absurd h hne

/-! ## Trust, worked out -/

section
variable (g : x.Good C)
include g

/-- A trusts B for c exactly when A holds B's admission. -/
theorem trustsA {n : Node} (hacc : n.accepted = [x.c]) (hl : n.links = []) (hS : x.InS n.ops)
    (hcov : x.adm ∈ n.ops → x.Covers n.ops) : Trusts C n x.c x.kB ↔ x.adm ∈ n.ops := by
  constructor
  · rintro ⟨_, h | ⟨⟨l, hl', _⟩, _⟩⟩
    · exact (allowedB g hS hcov).1 h
    · rw [hl] at hl'; cases hl'
  · intro h; exact ⟨by rw [hacc]; simp, Or.inl ((allowedB g hS hcov).2 h)⟩

/-- B always trusts A: by its link until its ops speak about A, by its
ops after. -/
theorem trustsB {n : Node} (hme : n.me = x.kB) (hacc : n.accepted = [x.c])
    (hl : n.links = [] ∨ n.links = [x.link]) (hS : x.InS n.ops)
    (hcov : x.adm ∈ n.ops → x.Covers n.ops) (hdone : n.links = [] → x.adm ∈ n.ops) :
    Trusts C n x.c x.kA := by
  refine ⟨by rw [hacc]; simp, ?_⟩
  by_cases hr : x.r ∈ n.ops
  · exact Or.inl ((allowedA g hS).2 hr)
  · have hl' : n.links = [x.link] := by
      rcases hl with h | h
      · exact absurd (hcov (hdone h) _ x.mem_S.1) hr
      · exact h
    refine Or.inr ⟨⟨x.link, by rw [hl']; simp, rfl, rfl⟩, fun h => hr ((knownA g hS).1 h), ?_⟩
    rw [hme]; intro h
    exact hr (hcov ((allowedB g hS hcov).1 h) _ x.mem_S.1)

theorem Inv.trustsB (hI : x.Inv s) : Trusts C s.b x.c x.kA :=
  Net.Scene.trustsB g hI.bme hI.bacc hI.blinks hI.bS hI.bcov hI.bdone

/-! ## The handlers, worked out -/

theorem hello_A (hI : x.Inv s) :
    onHello C s.a x.c x.kB (some x.req) =
      if x.adm ∈ s.a.ops then
        ({ s.a with ops := add1 s.a.ops x.req, sessions := ins s.a.sessions (x.c, x.kB) },
          [x.answer])
      else ({ s.a with ops := add1 s.a.ops x.req }, []) := by
  have hS' : x.InS (add1 s.a.ops x.req) := fun o h => by
    rcases mem_add1 h with h | rfl
    · exact hI.aS o h
    · exact x.mem_S.2.2.1
  have hreq : x.req ∈ add1 s.a.ops x.req := self_add1 g.distinct hI.aS x.mem_S.2.2.1
  have hcov : x.adm ∈ add1 s.a.ops x.req → x.Covers (add1 s.a.ops x.req) := fun h o ho => by
    rcases mem_add1 h with h | h
    · exact mem_add1_of (hI.acov h o ho)
    · exact absurd h x.adm_ne.2.2
  have hi : IntroOk C s.a x.c x.req :=
    ⟨x.ofC_S x.mem_S.2.2.1, _, _, _, _,
      v_req g hS' (mem_add1_of hI.ar) (mem_add1_of hI.ai) hreq⟩
  have hadm : x.adm ∈ add1 s.a.ops x.req ↔ x.adm ∈ s.a.ops :=
    ⟨fun h => (mem_add1 h).resolve_right x.adm_ne.2.2, mem_add1_of⟩
  have ht := trustsA (n := { s.a with ops := add1 s.a.ops x.req }) g hI.aacc hI.alinks hS' hcov
  unfold onHello
  rw [if_pos (by rw [hI.aacc]; simp)]
  dsimp only
  refine ite_congr ?_ (fun _ => ?_) (fun _ => ?_)
  · apply propext
    simp only [if_pos hi]
    exact ⟨fun t => hadm.1 (ht.1 t), fun h => ht.2 (hadm.2 h)⟩
  · simp only [if_pos hi, hI.ame]; rfl
  · simp only [if_pos hi]

theorem answer_B (hI : x.Inv s) :
    onAnswer C s.b x.c x.kA =
      if s.b.links = [x.link] then { s.b with sessions := ins s.b.sessions (x.c, x.kA) }
      else s.b := by
  unfold onAnswer
  rcases hI.blinks with h | h
  · rw [if_neg, if_neg]
    · rw [h]; simp
    · rintro ⟨⟨l, hl, _⟩, _⟩; rw [h] at hl; cases hl
  · rw [if_pos ⟨⟨x.link, by rw [h]; simp, rfl, rfl⟩, hI.trustsB g⟩, if_pos h]

theorem push_B (hI : x.Inv s) {os : List Op} (hos : x.InS os) :
    onPush C s.b x.c x.kA os =
      if (x.c, x.kA) ∈ s.b.sessions then { s.b with ops := add s.b.ops os } else s.b := by
  unfold onPush
  rw [x.filter_ofC hos]
  by_cases h : (x.c, x.kA) ∈ s.b.sessions
  · rw [if_pos ⟨h, hI.trustsB g⟩, if_pos h]
  · rw [if_neg (fun t => h t.1), if_neg h]

omit g in
theorem push_A (hI : x.Inv s) {os : List Op} (hos : x.InS os) :
    onPush C s.a x.c x.kB os = s.a := by
  unfold onPush
  split
  · rename_i h
    rw [x.filter_ofC hos, add_of_mem fun o ho => hI.acov (hI.asess _ h.1).2 o (hos o ho)]
  · rfl

theorem ticked_A (hI : x.Inv s) : ticked C s.a = s.a := by
  have hl : keptLinks C s.a = [] := by unfold keptLinks; rw [hI.alinks]; rfl
  refine Node.ext' (n := ticked C s.a) (m := s.a) rfl rfl rfl (hl.trans hI.alinks.symm) ?_
  show List.filter _ s.a.sessions = s.a.sessions
  refine List.filter_eq_self.2 fun p hp => ?_
  obtain ⟨rfl, hadm⟩ := hI.asess p hp
  exact decide_eq_true
    ((trustsA (n := { s.a with links := keptLinks C s.a }) g hI.aacc hl hI.aS hI.acov).2 hadm)

theorem tick_A (hI : x.Inv s) :
    tick C s.a = (s.a, s.a.sessions.map fun _ => Msg.push x.c x.kA x.kB s.a.ops) := by
  unfold tick; rw [ticked_A g hI]
  refine Prod.ext rfl ?_
  show sends s.a = _
  unfold sends; rw [hI.alinks]
  simp only [List.filter_nil, List.map_nil, List.nil_append]
  refine List.map_congr_left fun p hp => ?_
  obtain ⟨rfl, _⟩ := hI.asess p hp
  simp only [hI.ame, x.filter_ofC hI.aS]

theorem keptLinks_B (hI : x.Inv s) :
    keptLinks C s.b = if x.adm ∈ s.b.ops then [] else s.b.links := by
  have hall := allowedB (L := s.b.ops) g hI.bS hI.bcov
  unfold keptLinks
  rcases hI.blinks with h | h
  · rw [h]; split <;> rfl
  · rw [h]
    by_cases ha : x.adm ∈ s.b.ops
    · rw [if_pos ha]; simp [link, hI.bme, hall.2 ha]
    · rw [if_neg ha]; simp [link, hI.bme]; exact fun t => ha (hall.1 t)

theorem ticked_B (hI : x.Inv s) :
    ticked C s.b = { s.b with links := if x.adm ∈ s.b.ops then [] else s.b.links } := by
  have hl := keptLinks_B g hI
  have ht : Trusts C { s.b with links := keptLinks C s.b } x.c x.kA := by
    refine Net.Scene.trustsB g hI.bme hI.bacc ?_ hI.bS hI.bcov ?_
    · show keptLinks C s.b = [] ∨ keptLinks C s.b = [x.link]
      rw [hl]; split
      · exact Or.inl rfl
      · exact hI.blinks
    · show keptLinks C s.b = [] → _
      rw [hl]; split
      · intro _; assumption
      · exact hI.bdone
  refine Node.ext' (n := ticked C s.b) rfl rfl rfl hl ?_
  show List.filter _ s.b.sessions = s.b.sessions
  refine List.filter_eq_self.2 fun p hp => ?_
  obtain ⟨rfl, _⟩ := hI.bsess p hp
  exact decide_eq_true ht

theorem tick_B (hI : x.Inv s) :
    tick C s.b =
      ({ s.b with links := if x.adm ∈ s.b.ops then [] else s.b.links },
        (if s.b.links = [x.link] ∧ x.adm ∉ s.b.ops ∧ (x.c, x.kA) ∉ s.b.sessions then [x.hello]
          else []) ++ s.b.sessions.map fun _ => Msg.push x.c x.kB x.kA s.b.ops) := by
  unfold tick; rw [ticked_B g hI]
  refine Prod.ext rfl ?_
  show sends { s.b with links := if x.adm ∈ s.b.ops then [] else s.b.links } = _
  unfold sends
  dsimp only
  congr 1
  · by_cases ha : x.adm ∈ s.b.ops
    · rw [if_pos ha, if_neg (fun h => h.2.1 ha)]; rfl
    · rw [if_neg ha]
      rcases hI.blinks with h | h
      · rw [if_neg (fun t => by rw [h] at t; cases t.1), h]; rfl
      · rw [h]
        by_cases hs' : (x.c, x.kA) ∈ s.b.sessions
        · have hany : (s.b.sessions.any fun t => decide (t = (x.c, x.kA))) = true :=
            List.any_eq_true.2 ⟨_, hs', by simp⟩
          rw [if_neg (fun t => t.2.2 hs')]
          simp [link, List.filter_cons, hany]
        · have hany : (s.b.sessions.any fun t => decide (t = (x.c, x.kA))) = false := by
            rw [Bool.eq_false_iff]; intro h
            obtain ⟨t, ht, he⟩ := List.any_eq_true.1 h
            exact hs' ((of_decide_eq_true he) ▸ ht)
          rw [if_pos ⟨rfl, ha, hs'⟩]
          simp [link, List.filter_cons, hany, hello, hI.bme]
  · refine List.map_congr_left fun p hp => ?_
    obtain ⟨rfl, _⟩ := hI.bsess p hp
    simp only [hI.bme, x.filter_ofC hI.bS]

omit g in
theorem approval_eq (n : Node) :
    x.approval n = if x.req ∈ n.ops then { n with ops := add n.ops [x.appr, x.adm] } else n := by
  unfold approval
  by_cases h : x.req ∈ n.ops
  · rw [if_pos (List.any_eq_true.2 ⟨_, h, by simp⟩), if_pos h]
  · rw [if_neg (fun t => h (by obtain ⟨o, ho, he⟩ := List.any_eq_true.1 t; simp at he; exact he ▸ ho)),
      if_neg h]

end

end Scene

end Net

end

section

/-
Every step of the scene, worked out under the invariant, and the
invariant kept by every step: ticks, approval, delivery of any message
in flight in any order, and loss of any message.
-/

namespace Net
open Engine Community

theorem NetOk.mono {x : Scene} {s s' : Sys} {m : Msg} (h : x.NetOk s m)
    (ha : (x.c, x.kB) ∈ s.a.sessions → (x.c, x.kB) ∈ s'.a.sessions) : x.NetOk s' m := by
  rcases h with h | ⟨h1, h2⟩ | ⟨os, h1, h2, h3, h4⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨h1, ha h2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨os, h1, h2, h3, ha h4⟩))
  · exact Or.inr (Or.inr (Or.inr h))

namespace Scene
open Classical
variable {x : Scene} {C : Crypto} {s : Sys}

variable (x) in
def pushA (s : Sys) : Msg := .push x.c x.kA x.kB s.a.ops
variable (x) in
def pushB (s : Sys) : Msg := .push x.c x.kB x.kA s.b.ops
variable (x) in
/-- What B's tick sends: its hello while its link is pending and no session is open; its ops
over its session. -/
noncomputable def msgsB (s : Sys) : List Msg :=
  (if s.b.links = [x.link] ∧ x.adm ∉ s.b.ops ∧ (x.c, x.kA) ∉ s.b.sessions then [x.hello] else []) ++
    s.b.sessions.map fun _ => x.pushB s
variable (x) in
/-- B after its tick: the link forgotten once B holds its admission. -/
def bAfter (s : Sys) : Node := { s.b with links := if x.adm ∈ s.b.ops then [] else s.b.links }

section
variable (g : x.Good C)
include g

theorem out_tickA (hI : x.Inv s) :
    stepOut C x.approval s .tickA =
      ({ s with net := s.net ++ s.a.sessions.map fun _ => x.pushA s },
        s.a.sessions.map fun _ => x.pushA s) := by
  simp only [stepOut, tick_A g hI]; rfl

theorem out_tickB (hI : x.Inv s) :
    stepOut C x.approval s .tickB = ({ s with b := x.bAfter s, net := s.net ++ x.msgsB s }, x.msgsB s) := by
  simp only [stepOut, tick_B g hI]; rfl

omit g in
theorem out_approve :
    stepOut C x.approval s .approve = ({ s with a := x.approval s.a }, []) := rfl

omit g in
theorem out_drop {m : Msg} : stepOut C x.approval s (.drop m) = ({ s with net := s.net.erase m }, []) :=
  rfl

theorem out_hello (hI : x.Inv s) :
    stepOut C x.approval s (.deliver x.hello) =
      if x.adm ∈ s.a.ops then
        ({ s with a := { s.a with ops := add1 s.a.ops x.req, sessions := ins s.a.sessions (x.c, x.kB) },
                  net := s.net.erase x.hello ++ [x.answer] }, [x.answer])
      else ({ s with a := { s.a with ops := add1 s.a.ops x.req }, net := s.net.erase x.hello }, []) := by
  have hd : x.hello.dst = s.a.me := by rw [hI.ame]; rfl
  simp only [stepOut, if_pos hd]
  rw [show recv C s.a x.hello = onHello C s.a x.c x.kB (some x.req) from rfl, hello_A g hI]
  split <;> simp

theorem out_answer (hI : x.Inv s) :
    stepOut C x.approval s (.deliver x.answer) =
      ({ s with b := if s.b.links = [x.link] then { s.b with sessions := ins s.b.sessions (x.c, x.kA) }
                     else s.b,
                net := s.net.erase x.answer }, []) := by
  have h1 : x.answer.dst ≠ s.a.me := by rw [hI.ame]; exact fun h => g.kAB h.symm
  have h2 : x.answer.dst = s.b.me := by rw [hI.bme]; rfl
  simp only [stepOut, if_neg h1, if_pos h2]
  rw [show recv C s.b x.answer = (onAnswer C s.b x.c x.kA, []) from rfl, answer_B g hI]; simp

theorem out_pushAB (hI : x.Inv s) {os : List Op} (hos : x.InS os) :
    stepOut C x.approval s (.deliver (.push x.c x.kA x.kB os)) =
      ({ s with b := if (x.c, x.kA) ∈ s.b.sessions then { s.b with ops := add s.b.ops os } else s.b,
                net := s.net.erase (.push x.c x.kA x.kB os) }, []) := by
  have h1 : (Msg.push x.c x.kA x.kB os).dst ≠ s.a.me := by
    rw [hI.ame]; exact fun h => g.kAB h.symm
  have h2 : (Msg.push x.c x.kA x.kB os).dst = s.b.me := by rw [hI.bme]; rfl
  simp only [stepOut, if_neg h1, if_pos h2]
  rw [show recv C s.b (.push x.c x.kA x.kB os) = (onPush C s.b x.c x.kA os, []) from rfl,
    push_B g hI hos]; simp

theorem out_pushBA (hI : x.Inv s) {os : List Op} (hos : x.InS os) :
    stepOut C x.approval s (.deliver (.push x.c x.kB x.kA os)) =
      ({ s with net := s.net.erase (.push x.c x.kB x.kA os) }, []) := by
  have h1 : (Msg.push x.c x.kB x.kA os).dst = s.a.me := by rw [hI.ame]; rfl
  simp only [stepOut, if_pos h1]
  rw [show recv C s.a (.push x.c x.kB x.kA os) = (onPush C s.a x.c x.kB os, []) from rfl,
    push_A hI hos]; simp

/-! ## The invariant is kept -/

theorem covers_add {L os : List Op} (hL : x.InS L) (hos : x.InS os) (h : x.Covers os) :
    x.Covers (add L os) :=
  fun o ho => self_add g.distinct hL hos (h o ho)

theorem inv_step (hI : x.Inv s) {act : Act} (he : Enabled s act) :
    x.Inv (step C x.approval s act) := by
  unfold step
  cases act with
  | tickA =>
    rw [out_tickA g hI]
    refine { hI with net := fun m hm => ?_ }
    rcases List.mem_append.1 hm with hm | hm
    · exact NetOk.mono (hI.net m hm) id
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm
      have := hI.asess p hp
      exact Or.inr (Or.inr (Or.inl ⟨_, rfl, hI.aS, hI.acov this.2, this.1 ▸ hp⟩))
  | tickB =>
    rw [out_tickB g hI]
    refine { hI with blinks := ?_, bdone := ?_, net := fun m hm => ?_ }
    · show (if x.adm ∈ s.b.ops then [] else s.b.links) = [] ∨
        (if x.adm ∈ s.b.ops then [] else s.b.links) = [x.link]
      split
      · exact Or.inl rfl
      · exact hI.blinks
    · show (if x.adm ∈ s.b.ops then [] else s.b.links) = [] → _
      split
      · intro _; assumption
      · exact hI.bdone
    · rcases List.mem_append.1 hm with hm | hm
      · exact NetOk.mono (hI.net m hm) id
      · unfold msgsB at hm
        rcases List.mem_append.1 hm with hm | hm
        · split at hm
          · rw [List.mem_singleton.1 hm]; exact Or.inl rfl
          · cases hm
        · obtain ⟨p, _, rfl⟩ := List.mem_map.1 hm
          exact Or.inr (Or.inr (Or.inr ⟨_, rfl, hI.bS⟩))
  | approve =>
    rw [out_approve, approval_eq]
    by_cases hreq : x.req ∈ s.a.ops
    · rw [if_pos hreq]
      have hS2 : x.InS [x.appr, x.adm] := by
        intro o ho; simp at ho; rcases ho with rfl | rfl
        · exact x.mem_S.2.2.2.1
        · exact x.mem_S.2.2.2.2
      have hadm : x.adm ∈ add s.a.ops [x.appr, x.adm] :=
        self_add g.distinct hI.aS hS2 (by simp)
      refine { hI with aS := ?_, ar := mem_add_of hI.ar, ai := mem_add_of hI.ai, acov := ?_,
                       asess := ?_, net := fun m hm => NetOk.mono (hI.net m hm) id }
      · intro o ho
        rcases mem_add ho with h | h
        · exact hI.aS o h
        · exact hS2 o h
      · intro _ o ho
        simp only [S, List.mem_cons, List.mem_nil_iff, or_false] at ho
        rcases ho with rfl | rfl | rfl | rfl | rfl
        · exact mem_add_of hI.ar
        · exact mem_add_of hI.ai
        · exact mem_add_of hreq
        · exact self_add g.distinct hI.aS hS2 (by simp)
        · exact hadm
      · intro p hp; exact ⟨(hI.asess p hp).1, hadm⟩
    · rw [if_neg hreq]; exact hI
  | drop m =>
    rw [out_drop]
    exact { hI with net := fun m' hm' => NetOk.mono (hI.net m' (List.mem_of_mem_erase hm')) id }
  | deliver m =>
    have hm : m ∈ s.net := he
    rcases hI.net m hm with rfl | ⟨rfl, hab⟩ | ⟨os, rfl, hin, hcov, _⟩ | ⟨os, rfl, hin⟩
    · rw [out_hello g hI]
      have hS' : x.InS (add1 s.a.ops x.req) := fun o h => by
        rcases mem_add1 h with h | rfl
        · exact hI.aS o h
        · exact x.mem_S.2.2.1
      have hadm' : x.adm ∈ add1 s.a.ops x.req → x.adm ∈ s.a.ops :=
        fun h => (mem_add1 h).resolve_right x.adm_ne.2.2
      split
      · rename_i hadm
        refine { hI with aS := hS', ar := mem_add1_of hI.ar, ai := mem_add1_of hI.ai,
                         acov := fun h o ho => mem_add1_of (hI.acov (hadm' h) o ho),
                         asess := ?_, bsess := ?_, net := ?_ }
        · intro p hp
          rcases mem_ins.1 hp with hp | rfl
          · exact ⟨(hI.asess p hp).1, mem_add1_of hadm⟩
          · exact ⟨rfl, mem_add1_of hadm⟩
        · intro p hp
          exact ⟨(hI.bsess p hp).1, mem_ins.2 (Or.inl (hI.bsess p hp).2)⟩
        · intro m' hm'
          rcases List.mem_append.1 hm' with hm' | hm'
          · exact NetOk.mono (hI.net m' (List.mem_of_mem_erase hm')) fun h => mem_ins.2 (Or.inl h)
          · rw [List.mem_singleton.1 hm']; exact Or.inr (Or.inl ⟨rfl, mem_ins.2 (Or.inr rfl)⟩)
      · rename_i hadm
        refine { hI with aS := hS', ar := mem_add1_of hI.ar, ai := mem_add1_of hI.ai,
                         acov := fun h => absurd (hadm' h) hadm,
                         asess := fun p hp => absurd (hI.asess p hp).2 hadm,
                         net := fun m' hm' => NetOk.mono (hI.net m' (List.mem_of_mem_erase hm')) id }
    · rw [out_answer g hI]
      split
      · refine { hI with bmore := ?_, bsess := ?_,
                         net := fun m' hm' => NetOk.mono (hI.net m' (List.mem_of_mem_erase hm')) id }
        · intro h; obtain ⟨h1, h2⟩ := hI.bmore h; exact ⟨h1, mem_ins.2 (Or.inl h2)⟩
        · intro p hp
          rcases mem_ins.1 hp with hp | rfl
          · exact hI.bsess p hp
          · exact ⟨rfl, hab⟩
      · exact { hI with net := fun m' hm' => NetOk.mono (hI.net m' (List.mem_of_mem_erase hm')) id }
    · rw [out_pushAB g hI hin]
      split
      · rename_i hses
        have hS' : x.InS (add s.b.ops os) := fun o h => by
          rcases mem_add h with h | h
          · exact hI.bS o h
          · exact hin o h
        refine { hI with bS := hS', breq := mem_add_of hI.breq,
                         bmore := fun _ => ⟨covers_add g hI.bS hin hcov, hses⟩,
                         bdone := fun h => mem_add_of (hI.bdone h),
                         net := fun m' hm' => NetOk.mono (hI.net m' (List.mem_of_mem_erase hm')) id }
      · exact { hI with net := fun m' hm' => NetOk.mono (hI.net m' (List.mem_of_mem_erase hm')) id }
    · rw [out_pushBA g hI hin]
      exact { hI with net := fun m' hm' => NetOk.mono (hI.net m' (List.mem_of_mem_erase hm')) id }

/-- **The invariant holds in every state reachable over a failing socket.** -/
theorem reachable_inv {t : Sys} (h : Reachable C x.approval x.init t) : x.Inv t := by
  induction h with
  | init => exact inv_init
  | step act _ he ih => exact inv_step g ih he

end

end Scene

end Net

end

section

/-
The laws of the bootstrap, over the real ops and validators (Net.Scene)
and the protocol's own handlers (Net.Node):

- **Safety, over a failing socket** (any interleaving of ticks, approval,
  delivery in any order, duplicates and loss): a request opens nothing
  and earns nothing; A's sessions are only with devices its own ops
  admit; B's only with a device it trusts by the two-clause rule.
- **Possible over an ideal socket**: a run with no loss that ends with
  B connected, admitted and in sync.
- **Inevitable over a failing socket**: every fair run gets there and
  stays there.
-/

namespace Net
open Engine Community

namespace Scene
open Classical
variable {x : Scene} {C : Crypto} {s : Sys}

variable (x C) in
/-- Bootstrapped: both ends hold the session, hold the same ops, and
admit each other by those ops alone (`allowPeer`, with no exception: B
has forgotten its link). -/
def Goal (s : Sys) : Prop :=
  (x.c, x.kB) ∈ s.a.sessions ∧ (x.c, x.kA) ∈ s.b.sessions ∧
  (∀ o, o ∈ s.a.ops ↔ o ∈ s.b.ops) ∧
  Allowed C s.a.ops x.c x.kB ∧ Allowed C s.b.ops x.c x.kA ∧ Allowed C s.b.ops x.c x.kB ∧
  s.b.links = []

section
variable (g : x.Good C)
include g

/-! ## Safety -/

/-- **A request opens nothing.** Until A holds B's admission (A's user
has approved), however B's hellos are lost, duplicated or reordered: A
has no session with B and B none with A, no answer and no ops of A's are
in flight to B, and B holds nothing but its own request. -/
theorem no_connection_before_approval (h : Reachable C x.approval x.init s)
    (hna : x.adm ∉ s.a.ops) :
    (x.c, x.kB) ∉ s.a.sessions ∧ (x.c, x.kA) ∉ s.b.sessions ∧
    x.answer ∉ s.net ∧ (∀ os, Msg.push x.c x.kA x.kB os ∉ s.net) ∧ (∀ o ∈ s.b.ops, o = x.req) := by
  have hI := reachable_inv g h
  have ha : (x.c, x.kB) ∉ s.a.sessions := fun h => hna (hI.asess _ h).2
  refine ⟨ha, fun h => ha (hI.bsess _ h).2, fun h => ?_, fun os h => ?_, fun o ho => ?_⟩
  · rcases hI.net _ h with h | ⟨_, h⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩
    · cases h
    · exact ha h
    · cases h
    · cases h
  · rcases hI.net _ h with h | ⟨h, _⟩ | ⟨_, h, _, _, hs⟩ | ⟨_, h, _⟩
    · cases h
    · cases h
    · exact ha hs
    · injection h with _ h2; exact g.kAB h2
  · apply Classical.byContradiction; intro hne
    exact ha (hI.bsess _ (hI.bmore ⟨o, ho, hne⟩).2).2

/-- **Sessions only with trusted peers.** Every session A holds is with
a device A's own ops admit, as `allowPeer` decides, with no exception;
every session B holds is with a device B trusts by the two-clause rule
(its link's inviter until its ops speak, its ops after). -/
theorem sessions_trusted (h : Reachable C x.approval x.init s) :
    (∀ p ∈ s.a.sessions, Allowed C s.a.ops p.1 p.2) ∧ (∀ p ∈ s.b.sessions, Trusts C s.b p.1 p.2) := by
  have hI := reachable_inv g h
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · obtain ⟨rfl, hadm⟩ := hI.asess p hp
    exact (allowedB g hI.aS hI.acov).2 hadm
  · obtain ⟨rfl, _⟩ := hI.bsess p hp
    exact hI.trustsB g

/-! ## What one step does -/

omit g in
theorem sent_mem {s : Sys} {act : Act} {m : Msg} (h : m ∈ sent C x.approval s act) :
    m ∈ (step C x.approval s act).net := by
  unfold sent at h; unfold step
  cases act with
  | tickA | tickB => exact List.mem_append_right _ h
  | approve | drop => cases h
  | deliver m' =>
    simp only [stepOut] at h ⊢
    split
    · rw [if_pos (by assumption)] at h; exact List.mem_append_right _ h
    · rw [if_neg (by assumption)] at h
      split
      · rw [if_pos (by assumption)] at h; exact List.mem_append_right _ h
      · rw [if_neg (by assumption)] at h; cases h

/-- Monotone across any step: what A and B hold, B's session, B's
forgotten link; and A's ops stop changing once A holds B's admission. -/
theorem step_mono (hI : x.Inv s) {act : Act} (he : Enabled s act) :
    (∀ o ∈ s.a.ops, o ∈ (step C x.approval s act).a.ops) ∧
    (∀ o ∈ s.b.ops, o ∈ (step C x.approval s act).b.ops) ∧
    ((x.c, x.kA) ∈ s.b.sessions → (x.c, x.kA) ∈ (step C x.approval s act).b.sessions) ∧
    (s.b.links = [] → (step C x.approval s act).b.links = []) ∧
    (x.adm ∈ s.a.ops → (step C x.approval s act).a.ops = s.a.ops) := by
  unfold step
  cases act with
  | tickA => rw [out_tickA g hI]; exact ⟨fun _ h => h, fun _ h => h, id, id, fun _ => rfl⟩
  | tickB =>
    rw [out_tickB g hI]
    refine ⟨fun _ h => h, fun _ h => h, id, fun h => ?_, fun _ => rfl⟩
    show (if x.adm ∈ s.b.ops then [] else s.b.links) = []
    split
    · rfl
    · exact h
  | drop m => rw [out_drop]; exact ⟨fun _ h => h, fun _ h => h, id, id, fun _ => rfl⟩
  | approve =>
    rw [out_approve, approval_eq]
    split
    · rename_i hreq
      refine ⟨fun _ h => mem_add_of h, fun _ h => h, id, id, fun hadm => ?_⟩
      exact add_of_mem fun o ho => hI.acov hadm o (by simp at ho; rcases ho with rfl | rfl <;> simp [S])
    · exact ⟨fun _ h => h, fun _ h => h, id, id, fun _ => rfl⟩
  | deliver m =>
    rcases hI.net m he with rfl | ⟨rfl, _⟩ | ⟨os, rfl, hin, _, _⟩ | ⟨os, rfl, hin⟩
    · rw [out_hello g hI]
      split
      · rename_i hadm
        exact ⟨fun _ h => mem_add1_of h, fun _ h => h, id, id,
          fun _ => add1_of_mem (hI.acov hadm _ x.mem_S.2.2.1)⟩
      · rename_i hadm
        exact ⟨fun _ h => mem_add1_of h, fun _ h => h, id, id, fun h => absurd h hadm⟩
    · rw [out_answer g hI]
      split
      · exact ⟨fun _ h => h, fun _ h => h, fun h => mem_ins.2 (Or.inl h), id, fun _ => rfl⟩
      · exact ⟨fun _ h => h, fun _ h => h, id, id, fun _ => rfl⟩
    · rw [out_pushAB g hI hin]
      split
      · exact ⟨fun _ h => h, fun _ h => mem_add_of h, id, id, fun _ => rfl⟩
      · exact ⟨fun _ h => h, fun _ h => h, id, id, fun _ => rfl⟩
    · rw [out_pushBA g hI hin]; exact ⟨fun _ h => h, fun _ h => h, id, id, fun _ => rfl⟩

/-- B's tick re-sends its hello while its link is pending and no session
is open. -/
theorem hello_sent (hI : x.Inv s) (hns : (x.c, x.kA) ∉ s.b.sessions) :
    x.hello ∈ sent C x.approval s .tickB := by
  have hna : x.adm ∉ s.b.ops := fun h => hns (hI.bmore ⟨_, h, x.adm_ne.2.2⟩).2
  have hl : s.b.links = [x.link] := hI.blinks.resolve_left fun h => hna (hI.bdone h)
  unfold sent; rw [out_tickB g hI]
  show x.hello ∈ msgsB x s
  unfold msgsB; rw [if_pos ⟨hl, hna, hns⟩]; simp

/-- Delivering B's hello gives A the request. -/
theorem hello_gives_req (hI : x.Inv s) : x.req ∈ (step C x.approval s (.deliver x.hello)).a.ops := by
  unfold step; rw [out_hello g hI]
  have := self_add1 g.distinct hI.aS x.mem_S.2.2.1
  split <;> exact this

/-- Once A holds B's admission, every hello delivered is answered. -/
theorem hello_answered (hI : x.Inv s) (hadm : x.adm ∈ s.a.ops) :
    x.answer ∈ sent C x.approval s (.deliver x.hello) := by
  unfold sent; rw [out_hello g hI, if_pos hadm]; simp

/-- A's user approving, once A holds the request, gives A B's admission. -/
theorem approve_gives_adm (hI : x.Inv s) (hreq : x.req ∈ s.a.ops) :
    x.adm ∈ (step C x.approval s .approve).a.ops := by
  unfold step; rw [out_approve, approval_eq, if_pos hreq]
  have hS2 : x.InS [x.appr, x.adm] := by
    intro o ho; simp at ho; rcases ho with rfl | rfl
    · exact x.mem_S.2.2.2.1
    · exact x.mem_S.2.2.2.2
  exact self_add g.distinct hI.aS hS2 (by simp)

/-- An answer delivered while B's link is pending opens B's session. -/
theorem answer_opens (hI : x.Inv s) (hl : s.b.links = [x.link]) :
    (x.c, x.kA) ∈ (step C x.approval s (.deliver x.answer)).b.sessions := by
  unfold step; rw [out_answer g hI, if_pos hl]
  exact mem_ins.2 (Or.inr rfl)

/-- A's tick pushes its ops over its session with B. -/
theorem push_sent (hI : x.Inv s) (hs : (x.c, x.kB) ∈ s.a.sessions) :
    Msg.push x.c x.kA x.kB s.a.ops ∈ sent C x.approval s .tickA := by
  unfold sent; rw [out_tickA g hI]
  exact List.mem_map.2 ⟨_, hs, rfl⟩

/-- A's ops delivered over B's session give B its admission. -/
theorem push_gives_adm (hI : x.Inv s) {os : List Op} (hin : x.InS os) (hcov : x.Covers os)
    (hs : (x.c, x.kA) ∈ s.b.sessions) :
    x.adm ∈ (step C x.approval s (.deliver (.push x.c x.kA x.kB os))).b.ops := by
  unfold step; rw [out_pushAB g hI hin, if_pos hs]
  exact self_add g.distinct hI.bS hin (hcov _ x.mem_S.2.2.2.2)

/-- B's tick forgets the link once B holds its admission. -/
theorem tick_forgets (hI : x.Inv s) (hadm : x.adm ∈ s.b.ops) :
    (step C x.approval s .tickB).b.links = [] := by
  unfold step; rw [out_tickB g hI]
  show (if x.adm ∈ s.b.ops then [] else s.b.links) = []
  rw [if_pos hadm]

theorem goal_of (hI : x.Inv s) (hs : (x.c, x.kA) ∈ s.b.sessions) (hadm : x.adm ∈ s.b.ops)
    (hl : s.b.links = []) : x.Goal C s := by
  have hab := (hI.bsess _ hs).2
  have hadmA := (hI.asess _ hab).2
  have hca := hI.acov hadmA
  have hcb := hI.bcov hadm
  refine ⟨hab, hs, fun o => ⟨fun h => hcb o (hI.aS o h), fun h => hca o (hI.bS o h)⟩,
    (allowedB g hI.aS hI.acov).2 hadmA, (allowedA g hI.bS).2 (hcb _ x.mem_S.1),
    (allowedB g hI.bS hI.bcov).2 hadm, hl⟩

/-! ## Possible over an ideal socket -/

/-- **Bootstrap is possible over an ideal socket.** From A having founded
c and invited B, and B having pasted the link: B ticks (its hello, with
its request), the hello arrives (A stores the request and does not
answer), A's user approves, B ticks again (the same hello), it arrives
(now A answers and opens its session), the answer arrives (B opens its
session on its link's word), A ticks (its ops), they arrive (B holds its
admission), B ticks (forgetting the link). No message is lost; each is
in flight when delivered; and then B is connected, admitted by both
ends' ops and in sync. -/
theorem bootstrap_possible :
    ∃ acts t, (∀ act ∈ acts, ∀ m, act ≠ .drop m) ∧ Path C x.approval x.init acts t ∧ x.Goal C t := by
  let st := step C x.approval
  have R0 : Reachable C x.approval x.init x.init := .init
  have I0 := inv_init (x := x)
  -- 1. B ticks: its hello is in flight.
  let s1 := st x.init .tickB
  have R1 : Reachable C x.approval x.init s1 := .step _ R0 trivial
  have I1 := reachable_inv g R1
  have h1 : x.hello ∈ s1.net := sent_mem (hello_sent g I0 (by simp [init, b0]))
  have b1 : s1.b = x.b0 := by
    show (stepOut C x.approval x.init .tickB).1.b = _
    rw [out_tickB g I0]; show x.bAfter x.init = x.b0
    unfold bAfter; rw [if_neg (by simp [init, b0]; exact x.adm_ne.2.2)]; rfl
  -- 2. The hello arrives: A stores the request, and answers nothing.
  let s2 := st s1 (.deliver x.hello)
  have R2 : Reachable C x.approval x.init s2 := .step _ R1 h1
  have I2 := reachable_inv g R2
  have h2 : x.req ∈ s2.a.ops := hello_gives_req g I1
  have b2 : s2.b = x.b0 := by
    show (stepOut C x.approval s1 (.deliver x.hello)).1.b = _
    rw [out_hello g I1]; split <;> exact b1
  -- 3. A's user approves.
  let s3 := st s2 .approve
  have R3 : Reachable C x.approval x.init s3 := .step _ R2 trivial
  have I3 := reachable_inv g R3
  have h3 : x.adm ∈ s3.a.ops := approve_gives_adm g I2 h2
  have b3 : s3.b = x.b0 := b2
  -- 4. B ticks: the same hello again.
  let s4 := st s3 .tickB
  have R4 : Reachable C x.approval x.init s4 := .step _ R3 trivial
  have I4 := reachable_inv g R4
  have h4 : x.hello ∈ s4.net := sent_mem (hello_sent g I3 (by rw [b3]; simp [b0]))
  have a4 : s4.a = s3.a := by
    show (stepOut C x.approval s3 .tickB).1.a = _
    rw [out_tickB g I3]
  have b4 : s4.b.links = [x.link] := by
    show (stepOut C x.approval s3 .tickB).1.b.links = _
    rw [out_tickB g I3]; show (if x.adm ∈ s3.b.ops then [] else s3.b.links) = _
    rw [b3, if_neg (by simp [b0]; exact x.adm_ne.2.2)]; rfl
  -- 5. It arrives: A, now holding B's admission, answers.
  let s5 := st s4 (.deliver x.hello)
  have R5 : Reachable C x.approval x.init s5 := .step _ R4 h4
  have I5 := reachable_inv g R5
  have h5 : x.answer ∈ s5.net := sent_mem (hello_answered g I4 (a4 ▸ h3))
  have b5 : s5.b = s4.b := by
    show (stepOut C x.approval s4 (.deliver x.hello)).1.b = _
    rw [out_hello g I4]; split <;> rfl
  -- 6. The answer arrives: B opens its session.
  let s6 := st s5 (.deliver x.answer)
  have R6 : Reachable C x.approval x.init s6 := .step _ R5 h5
  have I6 := reachable_inv g R6
  have h6 : (x.c, x.kA) ∈ s6.b.sessions := answer_opens g I5 (b5 ▸ b4)
  -- 7. A ticks: its ops, over its session.
  let s7 := st s6 .tickA
  have R7 : Reachable C x.approval x.init s7 := .step _ R6 trivial
  have I7 := reachable_inv g R7
  have hab : (x.c, x.kB) ∈ s6.a.sessions := (I6.bsess _ h6).2
  have h7 : Msg.push x.c x.kA x.kB s6.a.ops ∈ s7.net := sent_mem (push_sent g I6 hab)
  have b7 : s7.b = s6.b := by
    show (stepOut C x.approval s6 .tickA).1.b = _
    rw [out_tickA g I6]
  -- 8. They arrive: B holds its admission.
  let s8 := st s7 (.deliver (.push x.c x.kA x.kB s6.a.ops))
  have R8 : Reachable C x.approval x.init s8 := .step _ R7 h7
  have I8 := reachable_inv g R8
  have h8 : x.adm ∈ s8.b.ops :=
    push_gives_adm g I7 I6.aS (I6.acov (I6.asess _ hab).2) (by rw [b7]; exact h6)
  -- 9. B ticks: it forgets its link.
  let s9 := st s8 .tickB
  have R9 : Reachable C x.approval x.init s9 := .step _ R8 trivial
  have I9 := reachable_inv g R9
  have m8 := step_mono g I7 (act := .deliver (.push x.c x.kA x.kB s6.a.ops)) h7
  have m9 := step_mono g I8 (act := .tickB) trivial
  have h6' : (x.c, x.kA) ∈ s8.b.sessions := m8.2.2.1 (by rw [b7]; exact h6)
  refine ⟨[.tickB, .deliver x.hello, .approve, .tickB, .deliver x.hello, .deliver x.answer, .tickA,
    .deliver (.push x.c x.kA x.kB s6.a.ops), .tickB], s9, by simp, ?_, ?_⟩
  · exact .cons trivial (.cons h1 (.cons trivial (.cons trivial (.cons h4 (.cons h5 (.cons trivial
      (.cons h7 (.cons trivial (.nil s9)))))))))
  · exact goal_of g I9 (m9.2.2.1 h6') (m9.2.1 _ h8) (tick_forgets g I8 h8)

/-! ## Inevitable over a failing socket -/

theorem run_inv (r : Run C x.approval x.init) : ∀ i, x.Inv (r.st i)
  | 0 => by rw [r.zero]; exact inv_init
  | i + 1 => by rw [(r.next i).2]; exact inv_step g (run_inv r i) (r.next i).1

theorem run_stable (r : Run C x.approval x.init) {P : Sys → Prop}
    (hP : ∀ s act, x.Inv s → Enabled s act → P s → P (step C x.approval s act))
    {i j : Nat} (hij : i ≤ j) (h : P (r.st i)) : P (r.st j) := by
  induction hij with
  | refl => exact h
  | step _ ih => rw [(r.next _).2]; exact hP _ _ (run_inv g r _) (r.next _).1 ih

omit g in
theorem run_step (r : Run C x.approval x.init) (i : Nat) :
    r.st (i + 1) = step C x.approval (r.st i) (r.act i) := (r.next i).2

variable {r : Run C x.approval x.init}

/-- B's hello is sent at infinitely many steps while B has no session. -/
theorem hellos_forever (hf : r.Fair) (hno : ∀ i, (x.c, x.kA) ∉ (r.st i).b.sessions) :
    ∀ N, ∃ i ≥ N, x.hello ∈ sent C x.approval (r.st i) (r.act i) := by
  intro N
  obtain ⟨i, hi, ha⟩ := hf.2.1 N
  exact ⟨i, hi, ha ▸ hello_sent g (run_inv g r i) (hno i)⟩

/-- Eventually A holds B's request: B keeps sending its hello, so one
gets through. -/
theorem ev_req (hf : r.Fair) : ∃ N, x.req ∈ (r.st N).a.ops := by
  apply Classical.byContradiction; intro hno
  have hno' : ∀ i, x.req ∉ (r.st i).a.ops := fun i h => hno ⟨i, h⟩
  have hns : ∀ i, (x.c, x.kA) ∉ (r.st i).b.sessions := fun i h => by
    have hI := run_inv g r i
    exact hno' i (hI.acov (hI.asess _ (hI.bsess _ h).2).2 _ x.mem_S.2.2.1)
  obtain ⟨i, _, ha⟩ := hf.2.2.2 _ (hellos_forever g hf hns) 0
  have := hello_gives_req g (run_inv g r i)
  rw [← ha, ← run_step] at this
  exact hno' (i + 1) this

/-- Eventually A holds B's admission: A's user approves. -/
theorem ev_approved (hf : r.Fair) : ∃ N, x.adm ∈ (r.st N).a.ops := by
  obtain ⟨N, hN⟩ := ev_req g hf
  obtain ⟨i, hi, ha⟩ := hf.2.2.1 N
  have hreq := run_stable g r (P := fun s => x.req ∈ s.a.ops)
    (fun _ _ hI he h => (step_mono g hI he).1 _ h) hi hN
  refine ⟨i + 1, ?_⟩
  rw [run_step, ha]
  exact approve_gives_adm g (run_inv g r i) hreq

theorem adm_stays (hf : r.Fair) : ∃ N, ∀ i ≥ N, x.adm ∈ (r.st i).a.ops := by
  obtain ⟨N, hN⟩ := ev_approved g hf
  exact ⟨N, fun i hi => run_stable g r (P := fun s => x.adm ∈ s.a.ops)
    (fun _ _ hI he h => (step_mono g hI he).1 _ h) hi hN⟩

/-- Eventually B's session opens: B keeps sending its hello, A answers
each one that arrives, and one answer gets through. -/
theorem ev_session (hf : r.Fair) : ∃ N, (x.c, x.kA) ∈ (r.st N).b.sessions := by
  obtain ⟨N2, h2⟩ := adm_stays g hf
  apply Classical.byContradiction; intro hno
  have hno' : ∀ i, (x.c, x.kA) ∉ (r.st i).b.sessions := fun i h => hno ⟨i, h⟩
  have hs : ∀ N, ∃ i ≥ N, x.answer ∈ sent C x.approval (r.st i) (r.act i) := by
    intro N
    obtain ⟨i, hi, ha⟩ := hf.2.2.2 _ (hellos_forever g hf hno') (max N N2)
    exact ⟨i, Nat.le_trans (Nat.le_max_left _ _) hi,
      ha ▸ hello_answered g (run_inv g r i) (h2 i (Nat.le_trans (Nat.le_max_right _ _) hi))⟩
  obtain ⟨i, _, ha⟩ := hf.2.2.2 _ hs 0
  have hI := run_inv g r i
  have hna : x.adm ∉ (r.st i).b.ops := fun h => hno' i (hI.bmore ⟨_, h, x.adm_ne.2.2⟩).2
  have hl : (r.st i).b.links = [x.link] := hI.blinks.resolve_left fun h => hna (hI.bdone h)
  have := answer_opens g hI hl
  rw [← ha, ← run_step] at this
  exact hno' (i + 1) this

/-- Eventually B holds its admission: A keeps pushing the same ops over
its session, and one push gets through. -/
theorem ev_admitted (hf : r.Fair) : ∃ N, x.adm ∈ (r.st N).b.ops := by
  obtain ⟨N2, h2⟩ := adm_stays g hf
  obtain ⟨N3, h3⟩ := ev_session g hf
  let M := max N2 N3
  have hs : ∀ i ≥ M, (x.c, x.kA) ∈ (r.st i).b.sessions := fun i hi =>
    run_stable g r (P := fun s => (x.c, x.kA) ∈ s.b.sessions)
      (fun _ _ hI he h => (step_mono g hI he).2.2.1 h) (Nat.le_trans (Nat.le_max_right _ _) hi) h3
  have hfix : ∀ i ≥ M, (r.st i).a.ops = (r.st M).a.ops := fun i hi =>
    run_stable g r (P := fun s => s.a.ops = (r.st M).a.ops)
      (fun _ _ hI he h => by
        rw [(step_mono g hI he).2.2.2.2 (h ▸ h2 M (Nat.le_max_left _ _))]; exact h) hi rfl
  let m := Msg.push x.c x.kA x.kB (r.st M).a.ops
  have hsent : ∀ N, ∃ i ≥ N, m ∈ sent C x.approval (r.st i) (r.act i) := by
    intro N
    obtain ⟨i, hi, ha⟩ := hf.1 (max N M)
    have hiM : i ≥ M := Nat.le_trans (Nat.le_max_right _ _) hi
    have hI := run_inv g r i
    refine ⟨i, Nat.le_trans (Nat.le_max_left _ _) hi, ?_⟩
    rw [ha, show m = Msg.push x.c x.kA x.kB (r.st i).a.ops by rw [hfix i hiM]]
    exact push_sent g hI (hI.bsess _ (hs i hiM)).2
  obtain ⟨i, hi, ha⟩ := hf.2.2.2 _ hsent M
  have hI := run_inv g r i
  have hIM := run_inv g r M
  have hadmM := h2 M (Nat.le_max_left _ _)
  have := push_gives_adm g hI hIM.aS (hIM.acov hadmM) (hs i hi)
  rw [← ha, ← run_step] at this
  exact ⟨_, this⟩

/-- **Bootstrap over a failing socket.** In every fair run, whatever the
socket loses, duplicates or reorders: eventually, and from then on, B is
connected to A, both hold the same ops, each admits the other by its
own ops alone, and B has forgotten its link. -/
theorem bootstrap (hf : r.Fair) : ∃ N, ∀ i ≥ N, x.Goal C (r.st i) := by
  obtain ⟨N4, h4⟩ := ev_admitted g hf
  obtain ⟨N3, h3⟩ := ev_session g hf
  obtain ⟨i, hi, ha⟩ := hf.2.1 (max N3 N4)
  have hadm : ∀ j ≥ N4, x.adm ∈ (r.st j).b.ops := fun j hj =>
    run_stable g r (P := fun s => x.adm ∈ s.b.ops) (fun _ _ hI he h => (step_mono g hI he).2.1 _ h) hj h4
  have hses : ∀ j ≥ N3, (x.c, x.kA) ∈ (r.st j).b.sessions := fun j hj =>
    run_stable g r (P := fun s => (x.c, x.kA) ∈ s.b.sessions)
      (fun _ _ hI he h => (step_mono g hI he).2.2.1 h) hj h3
  have hl : (r.st (i + 1)).b.links = [] := by
    rw [run_step, ha]
    exact tick_forgets g (run_inv g r i) (hadm i (Nat.le_trans (Nat.le_max_right _ _) hi))
  refine ⟨i + 1, fun j hj => goal_of g (run_inv g r j) (hses j ?_) (hadm j ?_) ?_⟩
  · exact Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) hi) (Nat.le_of_succ_le hj)
  · exact Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) hi) (Nat.le_of_succ_le hj)
  · exact run_stable g r (P := fun s => s.b.links = [])
      (fun _ _ hI he h => (step_mono g hI he).2.2.2.1 h) hj hl

end

end Scene

end Net

end

section

/-
The model's `Allowed` is what the engine's own `allowPeer` view answers:
for a node whose engine has received the ops L (in any order, with any
interleaving of processing) and finished processing them, the view, read
as lists over its persisted tables, accepts exactly the devices `Allowed`
names.
So the trust rule in `Net.Node` reads the running query, not a model of
it.
-/

namespace Net
open Engine Community

theorem table_eq_ops {C : Crypto} {L : List Op} {s : DB Fact} (hr : Reach (family C) L s)
    (hd : Distinct L) : s.ops = table L := by
  funext i
  cases h : s.ops i with
  | none =>
    cases h' : table L i with
    | none => rfl
    | some o =>
      have := (reach_ops hr hd i o).2 (table_some h')
      rw [h] at this; cases this
  | some o =>
    have ⟨hm, hi⟩ := (reach_ops hr hd i o).1 h
    rw [← hi]; exact (table_of hd hm).symm

/-- **`Allowed` is `allowPeer` at rest.** -/
theorem allowPeer_iff {C : Crypto} {L : List Op} {s : DB Fact} (hr : Reach (family C) L s)
    (hd : Distinct L) (hq : s.queue = []) (c : Id) (p : Key) :
    (allowPeer c p).eval s = true ↔ Allowed C L c p := by
  rw [connect_iff (reach_inv hr) hq c p, table_eq_ops hr hd]; rfl

/-- And a node's engine always gets there: after enough processing
steps its queue is empty, so `allowPeer` answers `Allowed`. -/
theorem allowPeer_settles {C : Crypto} {L : List Op} {s : DB Fact} (hr : Reach (family C) L s)
    (hd : Distinct L) : ∃ n, ∀ c p,
      (allowPeer c p).eval (drainS (family C) n s) = true ↔ Allowed C L c p := by
  obtain ⟨n, hn⟩ := drain_terminates hd s hr
  exact ⟨n, fun c p => allowPeer_iff (reach_drain hr n) hd hn c p⟩

end Net

end

section

/-
An explicit infinite, ideal and fair execution of the bootstrap model.
Every four steps tick A, tick B, run approval, and deliver the FIFO head
(or tick A if the queue is empty). Fairness follows from queue progress,
without assuming that either node has bootstrapped or that traffic stops.
-/

namespace Net.FairExecution
open Engine Community

/-- The four recurring phases. Empty delivery slots are harmless A ticks. -/
def choose (i : Nat) (s : Sys) : Act :=
  if i % 4 = 0 then .tickA else
  if i % 4 = 1 then .tickB else
  if i % 4 = 2 then .approve else
  match s.net with
  | [] => .tickA
  | m :: _ => .deliver m

def delivered : Act → Option Msg
  | .deliver m => some m
  | _ => none

theorem choose_enabled (i : Nat) (s : Sys) : Enabled s (choose i s) := by
  unfold choose
  split <;> try trivial
  split <;> try trivial
  split <;> try trivial
  cases h : s.net with
  | nil => trivial
  | cons m rest => exact (show m ∈ s.net by rw [h]; exact List.mem_cons_self ..)

theorem choose_ideal (i : Nat) (s : Sys) (m : Msg) : choose i s ≠ .drop m := by
  unfold choose
  split <;> try simp
  split <;> try simp
  split <;> try simp
  cases s.net <;> simp

section
variable (C : Crypto) (approval : Node → Node)

/-- Every handler appends its output after the queue entries it retains. -/
theorem net_after (s : Sys) (act : Act) :
    (step C approval s act).net =
      (match act with | .deliver m | .drop m => s.net.erase m | _ => s.net) ++ sent C approval s act := by
  cases act with
  | tickA | tickB => rfl
  | approve | drop => simp [step, sent, stepOut]
  | deliver m =>
    simp only [step, sent, stepOut]
    split
    · rfl
    · split
      · rfl
      · simp

theorem sent_queued (s : Sys) (act : Act) (m : Msg) (h : m ∈ sent C approval s act) :
    m ∈ (step C approval s act).net := by
  rw [net_after]
  exact List.mem_append_right _ h

theorem choose_advance (i : Nat) (s : Sys) :
    FIFO.Advance s.net (step C approval s (choose i s)).net (delivered (choose i s)) := by
  unfold choose
  split
  · exact .append _ _
  split
  · exact .append _ _
  split
  · simpa [step, stepOut, delivered] using (FIFO.Advance.append s.net [])
  cases h : s.net with
  | nil =>
    simpa only [step, stepOut, delivered, h] using
      (FIFO.Advance.append s.net (tick C s.a).2)
  | cons m rest =>
    rw [net_after, h]
    simpa [delivered] using (FIFO.Advance.pop m rest (sent C approval s (.deliver m)))

noncomputable def state (init : Sys) : Nat → Sys
  | 0 => init
  | i + 1 => step C approval (state init i) (choose i (state init i))

/-- This is a constructed run, from the supplied initial state. -/
noncomputable def run (init : Sys) : Run C approval init where
  st := state C approval init
  act i := choose i (state C approval init i)
  zero := rfl
  next i := ⟨choose_enabled i _,rfl⟩

variable (init : Sys)

theorem advance (i : Nat) :
    FIFO.Advance ((run C approval init).st i).net ((run C approval init).st (i + 1)).net
      (delivered ((run C approval init).act i)) := choose_advance C approval i _

theorem service : ∀ N, ∃ i ≥ N, ((run C approval init).st i).net ≠ [] →
    (delivered ((run C approval init).act i)).isSome = true := by
  intro N
  refine ⟨4*N+3,by omega,?_⟩
  intro hn
  change (delivered (choose (4*N+3) _)).isSome = true
  simp only [choose, show (4*N+3)%4 = 3 by omega, Nat.reduceEqDiff, ite_false]
  cases h : (state C approval init (4*N+3)).net with
  | nil => exact False.elim (hn h)
  | cons m rest => rfl

/-- Every particular queued message is eventually delivered, even if an
unbounded stream of other messages is appended behind it. -/
theorem queued_delivered {n : Nat} {m : Msg} (hm : m ∈ ((run C approval init).st n).net) :
    ∃ i ≥ n, (run C approval init).act i = .deliver m := by
  obtain ⟨i,hi,hd⟩ := FIFO.eventually_delivered
    (fun i => ((run C approval init).st i).net) (fun i => delivered ((run C approval init).act i))
    (advance C approval init) (service C approval init) hm
  refine ⟨i,hi,?_⟩
  cases ha : (run C approval init).act i <;> simp [delivered,ha] at hd ⊢
  exact hd

/-- Fairness is proved from periodic scheduling and FIFO progress, independently
of the scene's cryptography, admission, or eventual bootstrap conclusion. -/
theorem fair : (run C approval init).Fair := by
  refine ⟨?_,?_,?_,?_⟩
  · intro N
    exact ⟨4*N,by omega,by simp [run,choose,show (4*N)%4 = 0 by omega]⟩
  · intro N
    exact ⟨4*N+1,by omega,by simp [run,choose,show (4*N+1)%4 = 1 by omega]⟩
  · intro N
    exact ⟨4*N+2,by omega,by simp [run,choose,show (4*N+2)%4 = 2 by omega]⟩
  · intro m hs N
    obtain ⟨i,hNi,hm⟩ := hs N
    have hq := sent_queued C approval ((run C approval init).st i) ((run C approval init).act i) m hm
    have hnext := ((run C approval init).next i).2
    rw [← hnext] at hq
    obtain ⟨j,hij,hj⟩ := queued_delivered C approval init hq
    exact ⟨j,by omega,hj⟩

theorem ideal : (run C approval init).Ideal := fun i m => choose_ideal i _ m

end
end Net.FairExecution

namespace Net.Scene
open Engine Community

/-- A concrete infinite execution from the bootstrap initial state. Its fair
and ideal proofs do not require any assumption about the scene's signatures. -/
noncomputable def fairExecution (x : Scene) (C : Crypto) : Run C x.approval x.init :=
  FairExecution.run C x.approval x.init

theorem fairExecution_fair (x : Scene) (C : Crypto) : (x.fairExecution C).Fair :=
  FairExecution.fair C x.approval x.init

theorem fairExecution_ideal (x : Scene) (C : Crypto) : (x.fairExecution C).Ideal :=
  FairExecution.ideal C x.approval x.init

/-- The bootstrap theorem now has an explicit inhabited fair-run premise.
Only the separate scene validity assumptions remain here. -/
theorem fairExecution_bootstrap {x : Scene} {C : Crypto} (g : x.Good C) :
    ∃ N, ∀ i ≥ N, x.Goal C ((x.fairExecution C).st i) :=
  bootstrap g (fairExecution_fair x C)

end Net.Scene

end

