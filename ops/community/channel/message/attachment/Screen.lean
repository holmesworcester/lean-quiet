import engine.renderer.Data
import engine.renderer.Row
import ops.community.Community
import ops.community.channel.message.attachment.View
import ops.community.channel.message.attachment.chunk.View

/-!
`community.channel.message.attachment`: components that compose the op types in this folder and below, and their laws.
-/
namespace ArrivalLaws
attribute [local irreducible] Text.oneLine
open _root_.Arrival
open _root_.Row
open _root_.Engine _root_.Community _root_.Data
attribute [local instance] modelReads
section
variable {C : Crypto} {s : DB Fact} (hsize : ∀ x, (sha256 x).size = 32) {ct : ByteArray}
  (hspr : Merkle.NoSecondPreimage sha256 (Merkle.treeInputs sha256 ct))
include hsize hspr

/-- **Complete is every chunk held.** A picture whose counts are its
attachment's progress (as `pic_progress` reads them) is complete exactly
when the store holds a Valid chunk of that attachment at every index. -/
theorem complete_iff_held (h : Inv (family C) s) (hq : s.queue = []) {c att m u : Id} {len : Nat}
    {k x : ByteArray} (ha : V C s.ops att (.attachment c m u (Merkle.fileRoot sha256 ct) len k x))
    {p : Pic} (hp : (p.got, p.total) = (progress c att len).eval s) :
    p.complete = true ↔
      ∀ i < Merkle.nChunks len, ∃ y, V C s.ops y (.chunk c att (Merkle.fileRoot sha256 ct) len i) := by
  have hle := progress_le hsize hspr h hq ha
  have hfull := progress_full hsize hspr h hq ha
  have ht : (progress c att len).eval s = (((progress c att len).eval s).1, Merkle.nChunks len) := by
    unfold progress; simp
  rw [← hp] at hle hfull ht
  simp only [Prod.mk.injEq] at ht
  rw [Pic.complete, done_iff hle (by rw [ht.2]; exact Merkle.one_le_nChunks len)]
  exact hfull

/-- **A picture showing its file holds all of it.** Shown as the file
(`shown_file`), its counts being its attachment's progress, the
attachment's length is the file's and the store holds each of the
file's chunk ops, whose slices are the file. -/
theorem file_whole (h : Inv (family C) s) (hq : s.queue = []) {c att m u : Id} {len : Nat}
    {k x : ByteArray} (ha : V C s.ops att (.attachment c m u (Merkle.fileRoot sha256 ct) len k x))
    {p : Pic} (hp : (p.got, p.total) = (progress c att len).eval s)
    {α : Type} (pre full : Option α) (hs : (p.shown pre full).2 = true) :
    len = ct.size ∧ ∀ i < Merkle.nChunks ct.size,
      V C s.ops (fileChunk c att ct i).id (.chunk c att (Merkle.fileRoot sha256 ct) ct.size i) := by
  have hc := ((shown_file p pre full).1 hs).1
  have hle := progress_le hsize hspr h hq ha
  refine progress_done hsize hspr h hq ha ?_
  rw [← hp] at hle ⊢
  simp only [Pic.complete, done, Bool.and_eq_true, decide_eq_true_eq] at hc
  simp only at hle ⊢
  omega

/-- **The picture the app reads is complete exactly when its file is
held**: `Kinds.File.pic` over the store, composed with `complete_iff_held`. -/
theorem pic_complete_iff_held (h : Inv (family C) s) (hq : s.queue = []) {c att m u : Id} {len : Nat}
    {k x : ByteArray} (ha : V C s.ops att (.attachment c m u (Merkle.fileRoot sha256 ct) len k x))
    (info : FileMeta) (fk fn : ByteArray) (deps : Array Q) :
    ((Kinds.File.pic (m := Model) c att (Merkle.fileRoot sha256 ct) len info fk fn deps).run s).1.complete = true ↔
      ∀ i < Merkle.nChunks len, ∃ y, V C s.ops y (.chunk c att (Merkle.fileRoot sha256 ct) len i) :=
  complete_iff_held hsize hspr h hq ha (pic_progress c att _ len info fk fn deps s)

end
end ArrivalLaws
