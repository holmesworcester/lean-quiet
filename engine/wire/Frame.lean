/-
Frames on a TCP stream, after poc-17's tinyd: a 4-byte big-endian
length, then that many bytes (moved here from lean-quiet-daemon
8c8d092). A reader buffers what arrives and takes
whole frames off the front; a frame longer than `maxFrame` ends the
connection instead of being buffered.

A read is `frames`: the reader appends what it read to its buffer, takes
every whole frame off the front, and keeps the rest for the next read,
or ends the connection.

Laws: `unframe_frame` (a framed payload, followed by anything, unframes
to exactly that payload and the rest), `unframe_size` (what unframe
returns is never longer than `maxFrame`), `buffer_bounded` and
`frames_kept` (what a reader keeps between reads is less than one
maximal frame and its length, whatever the peer's length fields say),
and `frames_tooBig` (a length over `maxFrame` ends the connection in the
read that completes it, keeping nothing). Reads go through `b[i]?` and
size-checked `extract` only.
-/
namespace Engine.Sync

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

theorem lenAt_isSome {b : ByteArray} (h : 4 ≤ b.size) : (lenAt b).isSome := by
  unfold lenAt
  rw [getElem?_pos b 0 (by omega), getElem?_pos b 1 (by omega), getElem?_pos b 2 (by omega),
    getElem?_pos b 3 (by omega)]
  rfl

/-- Taking a frame off the front shortens the buffer. -/
theorem unframe_rest {b p rest : ByteArray} (h : unframe b = .frame p rest) : rest.size < b.size := by
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

/-- What `unframe` waits on: fewer than 4 bytes, or fewer than the
length they declare, which is at most `maxFrame`. -/
theorem unframe_more {b : ByteArray} (h : unframe b = .more) :
    b.size < 4 ∨ ∃ n, lenAt b = some n ∧ n ≤ maxFrame ∧ b.size < 4 + n := by
  unfold unframe at h
  split at h
  · rename_i hl
    left
    refine Nat.lt_of_not_le fun hs => ?_
    have := lenAt_isSome hs
    rw [hl] at this; cases this
  · rename_i n hl
    split at h
    · cases h
    · split at h
      · cases h
      · right; exact ⟨n, hl, by omega, by omega⟩

/-- A reader's buffer after a read: every whole frame off its front, in
order, and what is kept for the next read; none ends the connection
(a length over `maxFrame`). -/
def frames (b : ByteArray) : List ByteArray × Option ByteArray :=
  match _h : unframe b with
  | .frame p rest => let r := frames rest; (p :: r.1, r.2)
  | .more => ([], some b)
  | .tooBig => ([], none)
termination_by b.size
decreasing_by exact unframe_rest ‹_›

/-- **What a read keeps is less than one maximal frame and its
length**, and declares no length over `maxFrame`. -/
theorem frames_kept {b k : ByteArray} (h : (frames b).2 = some k) :
    k.size < 4 + maxFrame ∧ ∀ n, lenAt k = some n → n ≤ maxFrame := by
  induction b using frames.induct with
  | case1 x p rest hu ih =>
    rw [frames, hu] at h
    exact ih h
  | case2 x hu =>
    rw [frames, hu] at h
    cases h
    rcases unframe_more hu with hs | ⟨n, hl, hn, hs⟩
    · refine ⟨by unfold maxFrame; omega, fun n hl => ?_⟩
      unfold lenAt at hl
      rw [getElem?_neg _ 3 (by omega)] at hl
      simp at hl
    · refine ⟨by omega, fun m hm => ?_⟩
      rw [hl] at hm; cases hm; exact hn
  | case3 x hu =>
    rw [frames, hu] at h
    cases h

/-- **A length over `maxFrame` ends the connection**, in the read that
completes it, keeping nothing. -/
theorem frames_tooBig {b : ByteArray} {n : Nat} (hl : lenAt b = some n) (hn : maxFrame < n) :
    frames b = ([], none) := by
  have hu : unframe b = .tooBig := by
    unfold unframe; rw [hl]; simp [hn]
  rw [frames, hu]

/-- Every frame a read takes is at most `maxFrame`. -/
theorem frames_size {b p : ByteArray} (h : p ∈ (frames b).1) : p.size ≤ maxFrame := by
  induction b using frames.induct with
  | case1 x q rest hu ih =>
    rw [frames, hu] at h
    rcases List.mem_cons.1 h with rfl | h
    · exact unframe_size hu
    · exact ih h
  | case2 x hu => rw [frames, hu] at h; cases h
  | case3 x hu => rw [frames, hu] at h; cases h

/-- A framed payload is taken whole, then the rest. -/
theorem frames_frame (p rest : ByteArray) (h : p.size ≤ maxFrame) :
    frames (frame p ++ rest) = (p :: (frames rest).1, (frames rest).2) := by
  rw [frames, unframe_frame p rest h]

/-- The buffers a reader keeps over a sequence of reads, from b, until
it ends the connection. -/
def keeps : ByteArray → List ByteArray → List ByteArray
  | _, [] => []
  | b, c :: cs =>
    match (frames (b ++ c)).2 with
    | some k => k :: keeps k cs
    | none => []

/-- **Bounded buffering.** Over any sequence of reads, each buffer the
reader keeps is less than one maximal frame and its length, whatever
the peer's length fields say; so while it takes a read it holds less
than that and the read. -/
theorem buffer_bounded (reads : List ByteArray) :
    ∀ k ∈ keeps .empty reads, k.size < 4 + maxFrame := by
  suffices ∀ b, ∀ k ∈ keeps b reads, k.size < 4 + maxFrame from this _
  induction reads with
  | nil => intro b k hk; cases hk
  | cons c cs ih =>
    intro b k hk
    unfold keeps at hk
    split at hk
    · rename_i k' hk'
      rcases List.mem_cons.1 hk with rfl | hk
      · exact (frames_kept hk').1
      · exact ih k' k hk
    · cases hk

end Engine.Sync
