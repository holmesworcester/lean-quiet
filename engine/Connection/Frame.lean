/-
Not an op: the sealed frame that session traffic rides in, after
poc-13's and poc-17's connection.frame. Its public form is a version,
the connection id, a random 24-byte nonce, then the bytes sealed with
XChaCha20-Poly1305 under this side's send key for that connection, with
the version and the connection id as associated data.
- **The frame names its session.** The receiver takes the key from the
  header's connection id, so no socket is tied to a session, and one
  socket may carry several.
- **A frame sealed for one session never opens under another**: the id
  is in the associated data.
- **A frame's nonce is its counter, then 16 random bytes** (`Frame.nonce`).
  The counter, 8 bytes big-endian, orders one direction of one session
  (each direction has its own key); the random tail keeps a nonce from
  repeating under a key even if a counter does, as when a node restarts
  and reopens a session with the same keys. The nonce is AEAD input, so
  the counter cannot be changed without the key (`openAt_sealed`).
- **Freshness.** Opened, a frame gives its counter (`openAt`). The
  receiver takes a frame only if its counter is above the highest it has
  taken on that session (`fresh`), so a frame is taken at most once and
  a replayed one is dropped before it changes anything, the session's
  return address included. Where the sender's counter and the
  receiver's mark are kept is the node's (Engine/Sync/Node.lean).

The node puts the discriminator in front (0x01 sealed, 0x00 a bare
handshake op). Laws: `open_seal` (a frame sealed for a connection opens
under the matching key to its connection id and bytes), `cid_seal` (its
header names that connection), `openAt_seal` (and gives the counter it
was sealed with), `openAt_sealed` (a frame that opens was sealed under
that key, with the counter it shows), `ctrOf_nonce`.
-/
import Connection.Types
import Community.Merkle

namespace Connection
open Engine

def Frame.version : UInt8 := 1

def Frame.ad (cid : Id) : B := ⟨#[Frame.version]⟩ ++ cid

/-- Bytes sealed for connection cid with send key `sk` and nonce `n`. -/
def Frame.seal (K : Keys) (cid sk n p : B) : B := ⟨#[Frame.version]⟩ ++ cid ++ n ++ K.fenc sk n (Frame.ad cid) p

/-- A frame's connection id, if it is one. -/
def Frame.cid (b : B) : Option Id :=
  if b.size < 73 ∨ b.get! 0 ≠ Frame.version then none else some (b.extract 1 33)

/-- A frame's connection id and bytes, opened with receive key `rk`. -/
def Frame.open (K : Keys) (rk b : B) : Option (Id × B) :=
  if b.size < 73 ∨ b.get! 0 ≠ Frame.version then none else
  let cid := b.extract 1 33
  (K.fdec rk (b.extract 33 57) (Frame.ad cid) (b.extract 57 b.size)).map (cid, ·)

section
variable {K : Keys}

theorem seal_parts (cid sk n p : B) :
    Frame.seal K cid sk n p = ⟨#[Frame.version]⟩ ++ (cid ++ (n ++ K.fenc sk n (Frame.ad cid) p)) := by
  simp [Frame.seal, ByteArray.append_assoc]

/-- **A frame opens to what was sealed, under the matching key.** -/
theorem open_seal (hd : ∀ k n ad p, K.fdec k n ad (K.fenc k n ad p) = some p)
    (he : ∀ k n ad p, (K.fenc k n ad p).size = p.size + 16)
    {cid sk n p : B} (hc : cid.size = 32) (hn : n.size = 24) :
    Frame.open K sk (Frame.seal K cid sk n p) = some (cid, p) := by
  have h1 : (⟨#[Frame.version]⟩ : B).size = 1 := rfl
  have hs : (Frame.seal K cid sk n p).size = 73 + p.size := by
    rw [seal_parts]; simp only [ByteArray.size_append, h1, hc, hn, he]; omega
  have h0 : (Frame.seal K cid sk n p).get! 0 = Frame.version := by
    rw [seal_parts]; rfl
  have hcid : (Frame.seal K cid sk n p).extract 1 33 = cid := by
    rw [seal_parts, show (33 : Nat) = 1 + 32 from rfl, show (1 : Nat) = 1 + 0 from rfl,
      ByteArray.extract_append_size_add' (by rw [h1])]
    exact ByteArray.extract_append_eq_left (by rw [hc])
  have hn' : (Frame.seal K cid sk n p).extract 33 57 = n := by
    rw [seal_parts, show (33 : Nat) = 1 + (32 + 0) from rfl, show (57 : Nat) = 1 + (32 + 24) from rfl,
      ByteArray.extract_append_size_add' (by rw [h1]), ByteArray.extract_append_size_add' (by rw [hc])]
    exact ByteArray.extract_append_eq_left (by rw [hn])
  have hct : (Frame.seal K cid sk n p).extract 57 (Frame.seal K cid sk n p).size =
      K.fenc sk n (Frame.ad cid) p := by
    rw [hs, seal_parts, show (57 : Nat) = 1 + (32 + 24) from rfl,
      show 73 + p.size = 1 + (32 + (24 + (p.size + 16))) by omega,
      ByteArray.extract_append_size_add' (by rw [h1]), ByteArray.extract_append_size_add' (by rw [hc])]
    exact ByteArray.extract_append_eq_right (by rw [hn]) (by rw [he, hn])
  unfold Frame.open
  rw [hcid, hn', hct, h0]
  simp [hd, hs]

/-- **A frame's header names the connection it was sealed for.** -/
theorem cid_seal (he : ∀ k n ad p, (K.fenc k n ad p).size = p.size + 16)
    {cid sk n p : B} (hc : cid.size = 32) (hn : n.size = 24) :
    Frame.cid (Frame.seal K cid sk n p) = some cid := by
  have h1 : (⟨#[Frame.version]⟩ : B).size = 1 := rfl
  have hs : (Frame.seal K cid sk n p).size = 73 + p.size := by
    rw [seal_parts]; simp only [ByteArray.size_append, h1, hc, hn, he]; omega
  have h0 : (Frame.seal K cid sk n p).get! 0 = Frame.version := by rw [seal_parts]; rfl
  have hcid : (Frame.seal K cid sk n p).extract 1 33 = cid := by
    rw [seal_parts, show (33 : Nat) = 1 + 32 from rfl, show (1 : Nat) = 1 + 0 from rfl,
      ByteArray.extract_append_size_add' (by rw [h1])]
    exact ByteArray.extract_append_eq_left (by rw [hc])
  unfold Frame.cid
  rw [hcid, h0]
  simp [hs]

/-- The nonce bytes 33 to 57 of a sealed frame are its nonce. -/
theorem nonce_seal {cid sk n p : B} (hc : cid.size = 32) (hn : n.size = 24) :
    (Frame.seal K cid sk n p).extract 33 57 = n := by
  have h1 : (⟨#[Frame.version]⟩ : B).size = 1 := rfl
  rw [seal_parts, show (33 : Nat) = 1 + (32 + 0) from rfl, show (57 : Nat) = 1 + (32 + 24) from rfl,
    ByteArray.extract_append_size_add' (by rw [h1]), ByteArray.extract_append_size_add' (by rw [hc])]
  exact ByteArray.extract_append_eq_left (by rw [hn])

end

/-! ## Freshness -/

/-- The nonce of a frame with counter `ctr`: the counter, 8 bytes
big-endian, then 16 random bytes. -/
def Frame.nonce (ctr : Nat) (rnd : B) : B := Community.Merkle.be64 ctr ++ rnd.extract 0 16

/-- The number big-endian bytes name. -/
def Frame.unbe (l : List UInt8) : Nat := l.foldl (fun a x => a * 256 + x.toNat) 0

/-- A nonce's counter: what its first 8 bytes name. -/
def Frame.ctrOf (n : B) : Nat := Frame.unbe (n.extract 0 8).data.toList

/-- These bytes as a frame, opened with receive key `rk`: its connection
id, its counter, its payload. -/
def Frame.openAt (K : Keys) (rk b : B) : Option (Id × Nat × B) :=
  (Frame.open K rk b).map fun (cid, p) => (cid, Frame.ctrOf (b.extract 33 57), p)

/-- A frame with counter `ctr` is fresh on a session whose highest
counter taken is `mark`. -/
def Frame.fresh (mark ctr : Nat) : Bool := decide (mark < ctr)

theorem Frame.foldl_acc (l : List UInt8) (a : Nat) :
    l.foldl (fun a x => a * 256 + x.toNat) a =
      a * 256 ^ l.length + l.foldl (fun a x => a * 256 + x.toNat) 0 := by
  induction l generalizing a with
  | nil => simp
  | cons x t ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, ih (0 * 256 + x.toNat), Nat.pow_succ]
    have e : (a * 256 + x.toNat) * 256 ^ t.length = a * (256 ^ t.length * 256) + x.toNat * 256 ^ t.length := by
      rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm 256 (256 ^ t.length)]
    rw [e]
    simp only [Nat.zero_mul, Nat.zero_add]
    omega

theorem Frame.unbe_digits (n : Nat) :
    ∀ k, Frame.unbe ((List.range k).reverse.map fun i => (n >>> (8 * i)).toUInt8) = n % 256 ^ k
  | 0 => by simp [Frame.unbe, Nat.mod_one]
  | k + 1 => by
    have ih := Frame.unbe_digits n k
    unfold Frame.unbe at ih ⊢
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append, List.map_cons,
      List.foldl_cons, Frame.foldl_acc, ih]
    simp only [List.length_map, List.length_reverse, List.length_range, Nat.zero_mul, Nat.zero_add]
    have hd : (n >>> (8 * k)).toUInt8.toNat = n / 256 ^ k % 256 := by
      simp [Nat.shiftRight_eq_div_pow, Nat.pow_mul]
    rw [hd, Nat.pow_succ, Nat.mod_mul, Nat.mul_comm (n / 256 ^ k % 256)]
    omega

/-- **A nonce's counter is the one it was made with**, mod 2^64. -/
theorem Frame.ctrOf_nonce (ctr : Nat) (rnd : B) : Frame.ctrOf (Frame.nonce ctr rnd) = ctr % 2 ^ 64 := by
  unfold Frame.ctrOf Frame.nonce
  rw [ByteArray.extract_append_eq_left (Community.Merkle.size_be64 ctr).symm]
  exact Frame.unbe_digits ctr 8

theorem Frame.size_nonce (ctr : Nat) {rnd : B} (hr : 16 ≤ rnd.size) : (Frame.nonce ctr rnd).size = 24 := by
  simp only [Frame.nonce, ByteArray.size_append, Community.Merkle.size_be64, ByteArray.size_extract]
  omega

section
variable {K : Keys}

/-- **A frame opens to the counter it was sealed with.** -/
theorem openAt_seal (hd : ∀ k n ad p, K.fdec k n ad (K.fenc k n ad p) = some p)
    (he : ∀ k n ad p, (K.fenc k n ad p).size = p.size + 16)
    {cid sk p rnd : B} {ctr : Nat} (hc : cid.size = 32) (hr : 16 ≤ rnd.size) :
    Frame.openAt K sk (Frame.seal K cid sk (Frame.nonce ctr rnd) p) = some (cid, ctr % 2 ^ 64, p) := by
  have hn := Frame.size_nonce ctr hr
  unfold Frame.openAt
  rw [open_seal hd he hc hn, nonce_seal hc hn, Frame.ctrOf_nonce]
  rfl

/-- **A frame that opens was sealed under that key, with the counter it
shows**, if the AEAD opens only what it sealed: no one without the key
changes a frame's counter or connection id. -/
theorem openAt_sealed (hi : ∀ k n ad c p, K.fdec k n ad c = some p → c = K.fenc k n ad p)
    {rk b cid p : B} {ctr : Nat} (h : Frame.openAt K rk b = some (cid, ctr, p)) :
    ∃ n, b = Frame.seal K cid rk n p ∧ Frame.ctrOf n = ctr := by
  unfold Frame.openAt Frame.open at h
  split at h
  · simp at h
  · rename_i hb
    cases hdec : K.fdec rk (b.extract 33 57) (Frame.ad (b.extract 1 33)) (b.extract 57 b.size) with
    | none => simp [hdec] at h
    | some q =>
      simp only [hdec, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨b.extract 33 57, ?_, rfl⟩
      have hc := hi _ _ _ _ _ hdec
      have hs : 73 ≤ b.size := by omega
      have hv : b.get! 0 = Frame.version := by
        by_cases hv : b.get! 0 = Frame.version
        · exact hv
        · exact absurd (Or.inr hv) hb
      have h0 : b.extract 0 1 = ⟨#[Frame.version]⟩ := by
        have h1 : (⟨#[Frame.version]⟩ : B).size = 1 := rfl
        apply ByteArray.ext_getElem
        · rw [h1]; simp; omega
        · intro i hi hi'
          have : i = 0 := by rw [h1] at hi'; omega
          subst this
          rw [ByteArray.getElem_extract, ← hv]
          simp [ByteArray.get!, show 0 < b.size by omega]
          rfl
      unfold Frame.seal
      rw [← hc, ← h0, ByteArray.extract_append_extract, show min 0 1 = 0 from rfl, show max 1 33 = 33 from rfl,
        ByteArray.extract_append_extract, show min 0 33 = 0 from rfl, show max 33 57 = 57 from rfl,
        ByteArray.extract_append_extract, show min 0 57 = 0 from rfl, Nat.max_eq_right (by omega),
        ByteArray.extract_zero_size]

end

end Connection
