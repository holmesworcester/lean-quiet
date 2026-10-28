/-
Frames on a TCP stream, after poc-17's tinyd: a 4-byte big-endian
length, then that many bytes. A reader buffers what arrives and takes
whole frames off the front; a frame longer than `maxFrame` ends the
connection instead of being buffered.

Laws: `unframe_frame` (a framed payload, followed by anything, unframes
to exactly that payload and the rest), `unframe_short` (an incomplete
frame asks for more), and `unframe_size` (what unframe returns is never
longer than `maxFrame`). Reads go through `b[i]?` and size-checked
`extract` only.
-/
namespace Quiet.Net

/-- The longest frame accepted: 1 MiB. -/
def maxFrame : Nat := 1 <<< 20

def be32 (n : Nat) : ByteArray :=
  ⟨#[(n / 16777216).toUInt8, (n / 65536).toUInt8, (n / 256).toUInt8, n.toUInt8]⟩

/-- A payload as a frame. -/
def frame (p : ByteArray) : ByteArray := be32 p.size ++ p

/-- What a buffer's front holds. -/
inductive Front where
  /-- A whole frame, and the bytes after it. -/
  | frame (p rest : ByteArray)
  /-- Not yet a whole frame: read more. -/
  | more
  /-- A length over `maxFrame`: end the connection. -/
  | tooBig

def lenAt (b : ByteArray) : Option Nat := do
  let x0 ← b[0]?; let x1 ← b[1]?; let x2 ← b[2]?; let x3 ← b[3]?
  pure (((x0.toNat * 256 + x1.toNat) * 256 + x2.toNat) * 256 + x3.toNat)

/-- Take a whole frame off the front of a buffer. -/
def unframe (b : ByteArray) : Front :=
  match lenAt b with
  | none => .more
  | some n =>
    if maxFrame < n then .tooBig
    else if 4 + n ≤ b.size then .frame (b.extract 4 (4 + n)) (b.extract (4 + n) b.size)
    else .more

/-! ## Laws -/

theorem size_be32 (n : Nat) : (be32 n).size = 4 := rfl

theorem lenAt_frame (p rest : ByteArray) (h : p.size < 4294967296) :
    lenAt (frame p ++ rest) = some p.size := by
  have e : ∀ i (hi : i < 4), (frame p ++ rest)[i]? = (be32 p.size)[i]? := by
    intro i hi
    show (frame p ++ rest).data[i]? = (be32 p.size).data[i]?
    simp only [frame, ByteArray.append_assoc, ByteArray.data_append]
    rw [Array.getElem?_append_left (by show i < 4; exact hi)]
  have h0 : (be32 p.size)[0]? = some (p.size / 16777216).toUInt8 := rfl
  have h1 : (be32 p.size)[1]? = some (p.size / 65536).toUInt8 := rfl
  have h2 : (be32 p.size)[2]? = some (p.size / 256).toUInt8 := rfl
  have h3 : (be32 p.size)[3]? = some p.size.toUInt8 := rfl
  unfold lenAt
  rw [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), h0, h1, h2, h3]
  simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq]
  simp only [Nat.toUInt8, UInt8.toNat_ofNat']
  omega

/-- **A framed payload unframes to exactly itself**, followed by the rest. -/
theorem unframe_frame (p rest : ByteArray) (h : p.size ≤ maxFrame) :
    unframe (frame p ++ rest) = .frame p rest := by
  have hs : p.size < 4294967296 := by unfold maxFrame at h; omega
  have hsize : (frame p ++ rest).size = 4 + p.size + rest.size := by
    simp [frame, ByteArray.size_append, size_be32]
  unfold unframe
  rw [lenAt_frame p rest hs]
  dsimp only
  rw [if_neg (by omega), if_pos (by omega)]
  congr 1
  · show (be32 p.size ++ p ++ rest).extract 4 (4 + p.size) = p
    rw [ByteArray.append_assoc, show (4 : Nat) = 4 + 0 from rfl,
      ByteArray.extract_append_size_add' (size_be32 _).symm]
    exact ByteArray.extract_append_eq_left rfl
  · rw [hsize]
    show (be32 p.size ++ p ++ rest).extract (4 + p.size) (4 + p.size + rest.size) = rest
    rw [ByteArray.append_assoc, Nat.add_assoc, ByteArray.extract_append_size_add' (size_be32 _).symm]
    exact ByteArray.extract_append_eq_right rfl rfl

/-- **No frame is longer than `maxFrame`.** -/
theorem unframe_size {b p rest : ByteArray} (h : unframe b = .frame p rest) : p.size ≤ maxFrame := by
  unfold unframe at h
  split at h
  · cases h
  · rename_i n _
    split at h
    · cases h
    · split at h
      · cases h
        rw [ByteArray.size_extract]
        omega
      · cases h

end Quiet.Net
