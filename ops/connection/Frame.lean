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
- **Nonces are random**, so neither side keeps a counter. 24 bytes is
  enough that two frames never share one under a key.
- **A replayed frame re-delivers ops already held**, and they dedupe by
  id, so nothing tracks replays.

The node puts the discriminator in front (0x01 sealed, 0x00 a bare
handshake op). Laws: `open_seal` (a frame sealed for a connection opens
under the matching key to its connection id and bytes) and `cid_seal`
(its header names that connection).
-/
import ops.connection.Types

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

end

end Connection
