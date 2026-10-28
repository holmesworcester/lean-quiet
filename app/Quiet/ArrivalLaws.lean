/-
Download progress displays accurately, over the running code (Arrival,
Row, Kinds.File):

- **Words.** `caption_none_iff`, `caption_some`: the caption is shown
  exactly until the file is here, and says `{⌊100·got/total⌋}% of
  {humanBytes len}`; `percent_lt`: while a chunk is missing it says less
  than 100%, and no pill ever does (`layout_percent_lt`).
- **The ring.** Its lit pixels are `lit R s got total`, a function of the
  counts alone (`ring_counts`). `lit_zero`: none at 0; `lit_mono`: more
  chunks light a superset; `lit_full`: all of the file lights the whole
  ring; `lit_clockwise`: what is lit is an arc from 12 o'clock (a pixel
  less far round than a lit one is lit). Exact integers, no floats.
- **Placement.** `layout_inside`, `ring_inside`, `words_inside`: the pill
  lies inside the picture's box, `inset` from its left and bottom; the
  ring's pixels and the words' box inside the pill, apart. That holds for
  every box (the pill is not drawn in one too small for it);
  `layout_shown` gives the size it needs: the pill's fixed width plus the
  percent's, and a line's height plus padding. `layout_words`: in a box
  wide enough for the caption, the pill's words are the caption.
  `layout_progress`: the row's layout (its height) is the same at any
  progress, so the pill adds no line that disappears.
- **The file replaces the preview.** `shown_file`: a picture shows its
  file only when complete (and decoded), else its preview.
- **From the store.** In the model (every list read is the engine's
  `eval`), a picture's counts are `Community.progress`'s
  (`pic_progress`), and the pill drawn is the one laid out from that
  answer alone (`arrival_progress`); so with the engine's
  `progress_full` and `progress_done`: complete exactly when every chunk
  of the file is held
  (`complete_iff_held`), and a picture showing its file holds every one
  of its file's chunk ops, at the file's length (`file_whole`).
  "100%" is never drawn: complete hides the caption.
-/
import Quiet.Kinds.File

namespace ArrivalLaws
open Arrival

/-! ## Words -/

/-- **Never 100% early.** While a chunk is missing, the percent is below 100. -/
theorem percent_lt {got total : Nat} (h : got < total) : percent got total < 100 := by
  unfold percent
  exact Nat.div_lt_of_lt_mul (by omega)

/-- Complete, for counts that never pass the total (`Community.progress_le`),
is the count reaching the total. -/
theorem done_iff {got total : Nat} (hle : got ≤ total) (hpos : 0 < total) :
    done got total = true ↔ got = total := by
  simp only [done, Bool.and_eq_true, decide_eq_true_eq]; omega

/-- **The caption shows exactly until the file is here.** -/
theorem caption_none_iff (got total len : Nat) :
    caption got total len = none ↔ done got total = true := by
  unfold caption; split <;> simp_all

/-- **The caption's words**, while the file is arriving. -/
theorem caption_some {got total : Nat} (len : Nat) (h : done got total = false) :
    caption got total len = some s!"{percent got total}% of {humanBytes len}" := by
  simp [caption, h]

/-- The percent is ⌊100·got/total⌋. -/
theorem percent_eq (got total : Nat) : percent got total = 100 * got / total := rfl

/-! ## The ring -/

theorem off_pos (R i : Nat) : 0 < off R i := by unfold off; split <;> omega

theorem turn_pos (R i j : Nat) : 0 < (turn R i j).2 := by
  have := off_pos R i
  unfold turn; split <;> split <;> simp only <;> omega

/-- Every direction is less than a whole turn round. -/
theorem turn_lt (R i j : Nat) : (turn R i j).1 < 4 * (turn R i j).2 := by
  have := off_pos R i
  have := off_pos R j
  unfold turn; split <;> split <;> simp only <;> omega

theorem arc_iff (R got total i j : Nat) :
    arc R got total i j = true ↔ (turn R i j).1 * total < 4 * got * (turn R i j).2 := by
  simp [arc]

/-- **No chunk, no arc**: the ring is its bare track. -/
theorem lit_zero (R s total i j : Nat) : lit R s 0 total i j = false := by
  simp [lit, arc]

/-- **More chunks light more**: what is lit stays lit. -/
theorem lit_mono {R s got got' total i j : Nat} (hg : got ≤ got') (h : lit R s got total i j = true) :
    lit R s got' total i j = true := by
  simp only [lit, Bool.and_eq_true, arc_iff] at *
  refine ⟨h.1, Nat.lt_of_lt_of_le h.2 (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 hg))⟩

/-- **All of the file closes the ring**: every pixel of it is lit. -/
theorem lit_full (R s total i j : Nat) (ht : 0 < total) : lit R s total total i j = onRing R s i j := by
  have h := Nat.mul_lt_mul_of_pos_right (turn_lt R i j) ht
  have h' : (turn R i j).1 * total < 4 * total * (turn R i j).2 := by
    rwa [Nat.mul_right_comm 4 total]
  simp [lit, arc_iff, h']

/-- **Lit from 12 o'clock, clockwise**: a ring pixel no further round than
a lit one is lit, so what is lit is one arc starting at 12. -/
theorem lit_clockwise {R s got total i j i' j' : Nat} (h : lit R s got total i j = true)
    (hr : onRing R s i' j' = true)
    (hle : (turn R i' j').1 * (turn R i j).2 ≤ (turn R i j).1 * (turn R i' j').2) :
    lit R s got total i' j' = true := by
  simp only [lit, Bool.and_eq_true, arc_iff] at *
  refine ⟨hr, ?_⟩
  obtain ⟨_, ha⟩ := h
  generalize (turn R i j).1 = n at *
  generalize (turn R i' j').1 = n' at *
  have hm := turn_pos R i j
  have hm' := turn_pos R i' j'
  generalize (turn R i j).2 = m at *
  generalize (turn R i' j').2 = m' at *
  apply Nat.lt_of_mul_lt_mul_right (a := m)
  calc n' * total * m = (n' * m) * total := Nat.mul_right_comm _ _ _
    _ ≤ (n * m') * total := Nat.mul_le_mul_right _ hle
    _ = (n * total) * m' := Nat.mul_right_comm _ _ _
    _ < (4 * got * m) * m' := Nat.mul_lt_mul_of_pos_right ha hm'
    _ = 4 * got * m' * m := Nat.mul_right_comm _ _ _

/-- A ring pixel is in the ring's square. -/
theorem onRing_square {R s i j : Nat} (h : onRing R s i j = true) : i < 2 * R ∧ j < 2 * R := by
  simp only [onRing, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2⟩

/-! ## Placement -/

section
variable {f : Font.Font} {z : Style} {bx by_ bw bh got total len : Nat} {p : Pill}

theorem layout_spec (h : layout f z bx by_ bw bh got total len = some p) :
    ∃ words s l, caption got total len = some words ∧
      (fit f z bw words <|> fit f z bw s!"{percent got total}%") = some (s, l) ∧
      2 * z.inset + z.height f ≤ bh ∧
      p = { x := bx + z.inset, y := by_ + bh - z.inset - z.height f,
            w := 2 * z.padX + 2 * z.ring + z.gap + Paint.Line.width f l, h := z.height f,
            rx := bx + z.inset + z.padX, ry := by_ + bh - z.inset - z.height f + (z.height f - 2 * z.ring) / 2,
            words := s, line := l, tx := bx + z.inset + z.padX + 2 * z.ring + z.gap,
            ty := by_ + bh - z.inset - z.height f + (z.height f - f.cell) / 2, got, total } := by
  unfold layout at h
  split at h
  · cases h
  · rename_i words hw
    split at h
    · cases h
    · rename_i s l hf
      dsimp only at h
      split at h
      · rename_i hb
        exact ⟨words, s, l, hw, hf, hb, (Option.some.inj h).symm⟩
      · cases h

theorem fit_spec {bw : Nat} {w s : String} {l : Text.Line} (h : fit f z bw w = some (s, l)) :
    s = w ∧ l = Text.oneLine f bw w ∧ z.fixed + Paint.Line.width f l ≤ bw := by
  unfold fit at h
  dsimp only at h
  split at h
  · cases h; exact ⟨rfl, rfl, by assumption⟩
  · cases h

theorem pick_spec {bw : Nat} {a b s : String} {l : Text.Line}
    (h : (fit f z bw a <|> fit f z bw b) = some (s, l)) :
    (s = a ∨ s = b) ∧ l = Text.oneLine f bw s ∧ z.fixed + Paint.Line.width f l ≤ bw := by
  cases ha : fit f z bw a with
  | some r =>
    rw [ha] at h; cases h
    obtain ⟨rfl, rfl, hw⟩ := fit_spec ha
    exact ⟨Or.inl rfl, rfl, hw⟩
  | none =>
    rw [ha] at h
    obtain ⟨rfl, rfl, hw⟩ := fit_spec h
    exact ⟨Or.inr rfl, rfl, hw⟩

/-- **The pill is drawn only while the file is arriving.** -/
theorem layout_done (h : done got total = true) : layout f z bx by_ bw bh got total len = none := by
  simp [layout, caption, h]

theorem pick_some {bw : Nat} {a b : String} (h : (fit f z bw b).isSome = true) :
    (fit f z bw a <|> fit f z bw b).isSome = true := by
  cases fit f z bw a
  · exact h
  · rfl

/-- **The pill is drawn while the file is arriving**, in any box with room
for it: the pill's fixed width and the percent's, a line's height and
the padding. -/
theorem layout_shown (h : done got total = false)
    (hw : z.fixed + Paint.Line.width f (Text.oneLine f bw s!"{percent got total}%") ≤ bw)
    (hh : 2 * z.inset + z.height f ≤ bh) :
    (layout f z bx by_ bw bh got total len).isSome = true := by
  have hb : (fit f z bw s!"{percent got total}%").isSome = true := by
    unfold fit; dsimp only; split
    · rfl
    · contradiction
  unfold layout
  rw [caption_some len h]
  dsimp only
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 (pick_some (a := s!"{percent got total}% of {humanBytes len}") hb)
  rw [hr]
  obtain ⟨s, l⟩ := r
  dsimp only
  split
  · rfl
  · contradiction

/-- A pill is only laid out while the file is arriving. -/
theorem layout_arriving (h : layout f z bx by_ bw bh got total len = some p) : done got total = false := by
  obtain ⟨words, _, _, hw, _⟩ := layout_spec h
  cases hd : done got total
  · rfl
  · rw [(caption_none_iff got total len).2 hd] at hw; cases hw

/-- **The pill never says 100%**: for counts that never pass the total
(`Community.progress_le`), the percent any pill shows is below 100. -/
theorem layout_percent_lt (h : layout f z bx by_ bw bh got total len = some p) (hle : got ≤ total) :
    percent got total < 100 := by
  have hnd : ¬ done got total = true := by simp [layout_arriving h]
  simp only [done, Bool.and_eq_true, decide_eq_true_eq] at hnd
  by_cases ht : total = 0
  · subst ht; simp [percent]
  · exact percent_lt (by omega)

/-- **The words are the caption's**, or the percent alone in a box too
narrow for them; the caption's whenever the box is wide enough. -/
theorem layout_words (h : layout f z bx by_ bw bh got total len = some p) :
    p.line = Text.oneLine f bw p.words ∧ p.got = got ∧ p.total = total ∧
    (p.words = s!"{percent got total}% of {humanBytes len}" ∨ p.words = s!"{percent got total}%") ∧
    ((fit f z bw s!"{percent got total}% of {humanBytes len}").isSome = true →
      p.words = s!"{percent got total}% of {humanBytes len}") := by
  have hnd := layout_arriving h
  obtain ⟨words, s, l, hw, hf, _, rfl⟩ := layout_spec h
  rw [caption_some len hnd] at hw
  cases hw
  obtain ⟨hs, hl, _⟩ := pick_spec hf
  refine ⟨hl, rfl, rfl, hs, fun hfull => ?_⟩
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hfull
  rw [hr] at hf
  cases hf
  exact (fit_spec hr).1

/-- **The pill is inside the picture's box**: `inset` from its left and
bottom edges, within its right and top. -/
theorem layout_inside (h : layout f z bx by_ bw bh got total len = some p) :
    p.x = bx + z.inset ∧ p.x + p.w + z.inset ≤ bx + bw ∧
    by_ + z.inset ≤ p.y ∧ p.y + p.h + z.inset = by_ + bh := by
  obtain ⟨words, s, l, _, hf, hb, rfl⟩ := layout_spec h
  obtain ⟨_, _, hw⟩ := pick_spec hf
  simp only [Style.fixed] at hw
  dsimp only
  omega

/-- **The ring is inside the pill**: each of its pixels (`onRing`), at
(rx + i, ry + j), is in the pill's box, left of the words. -/
theorem ring_inside (h : layout f z bx by_ bw bh got total len = some p) {i j : Nat}
    (hr : onRing z.ring z.stroke i j = true) :
    p.x ≤ p.rx + i ∧ p.rx + i < p.tx ∧ p.y ≤ p.ry + j ∧ p.ry + j < p.y + p.h := by
  obtain ⟨hi, hj⟩ := onRing_square hr
  obtain ⟨words, s, l, _, hf, hb, rfl⟩ := layout_spec h
  simp only [Style.height] at *
  have := Nat.le_max_right f.cell (2 * z.ring)
  omega

/-- **The words are inside the pill**, right of the ring: their line's box
(its width, a line high). -/
theorem words_inside (h : layout f z bx by_ bw bh got total len = some p) :
    p.rx + 2 * z.ring ≤ p.tx ∧ p.tx + Paint.Line.width f p.line ≤ p.x + p.w ∧
    p.y ≤ p.ty ∧ p.ty + f.cell ≤ p.y + p.h := by
  obtain ⟨words, s, l, _, hf, hb, rfl⟩ := layout_spec h
  simp only [Style.height] at *
  have := Nat.le_max_left f.cell (2 * z.ring)
  omega

/-- **The ring shows the counts, and only them**: each of its pixels is lit
exactly as `lit` says for the counts the pill was laid out for. -/
theorem ring_counts (h : layout f z bx by_ bw bh got total len = some p) (i j : Nat) :
    lit z.ring z.stroke p.got p.total i j = lit z.ring z.stroke got total i j := by
  obtain ⟨_, hg, ht, _⟩ := layout_words h
  rw [hg, ht]

end

/-! ## In the row -/

open Row

/-- **The row's caption pill shows exactly while the picture is arriving**
(in a box with room for it, `layout_shown`). -/
theorem arrival_none (f : Font.Font) (dm : Dim) (bx : Box) (p : Pic) (h : p.complete = true) :
    arrival f dm bx p = none := layout_done h

theorem arrival_some (f : Font.Font) (dm : Dim) (bx : Box) (p : Pic) (h : p.complete = false)
    (hw : dm.arrival.fixed + Paint.Line.width f (Text.oneLine f bx.w s!"{percent p.got p.total}%") ≤ bx.w)
    (hh : 2 * dm.arrival.inset + dm.arrival.height f ≤ bx.h) :
    (arrival f dm bx p).isSome = true := layout_shown h hw hh

/-- **A picture's box does not depend on how much of it is here.** -/
theorem picBox_progress (dm : Dim) (maxW : Nat) (p : Pic) (g t : Nat) (cs : List ByteArray) :
    picBox dm maxW { p with got := g, total := t, chunks := cs } = picBox dm maxW p := rfl

/-- **Progress moves nothing**: the row's layout, its height included, is
the same whatever its pictures' counts, so the pill (inside the
picture's box) adds no line that disappears when the file lands. -/
theorem layout_progress (f : Font.Font) (dm : Dim) (W : Nat) (d : RowData) (g t : Pic → Nat)
    (cs : Pic → List ByteArray) :
    layout f dm W { d with pics := d.pics.map fun p => { p with got := g p, total := t p, chunks := cs p } } =
      layout f dm W d := by
  simp only [Row.layout, Row.layoutBody, List.forIn_map]
  rfl

/-- **The file replaces the preview only when complete**: a picture shows
its file exactly when every chunk is here and the file is decoded. -/
theorem shown_file {α : Type} (p : Pic) (pre full : Option α) :
    (p.shown pre full).2 = true ↔ p.complete = true ∧ full.isSome = true := by
  unfold Pic.shown
  split
  · split <;> simp_all
  · simp_all

/-- Until then it shows the preview. -/
theorem shown_pre {α : Type} (p : Pic) (pre full : Option α) (h : (p.shown pre full).2 = false) :
    (p.shown pre full).1 = pre := by
  unfold Pic.shown at *
  split <;> (try split) <;> simp_all

/-! ## From the store -/

open Engine Community Data

/-- The model: a list read is the engine's `eval` of a store. -/
abbrev Model := ReaderT (DB Fact) Id

@[instance_reducible] def modelReads : Reads Model where
  read q := fun db => match q with
    | .list q => .list (Engine.eval db q) []
    | .op _ => .bytes none

attribute [local instance] modelReads

/-- The lists a view reads, in order, over a store. -/
def readsOf {α : Type} (db : DB Fact) : View Fact α → Array Q → Array Q
  | .pure _, deps => deps
  | .list q k, deps => readsOf db (k (Engine.eval db q)) (deps.push (.list q))

/-- **A view read through the app's reads is the view's answer.** -/
theorem readView_model {α : Type} (v : View Fact α) (deps : Array Q) (db : DB Fact) :
    (readView (m := Model) v deps).run db = (v.eval db, readsOf db v deps) := by
  induction v generalizing deps with
  | pure a => rfl
  | list q k ih => exact ih _ _

/-- **A picture's counts are the engine's**: `Community.progress` of its
file, read as is. -/
theorem pic_progress (c root : Id) (len : Nat) (info : FileMeta) (fk fn : ByteArray) (deps : Array Q)
    (db : DB Fact) :
    let p := ((Kinds.File.pic (m := Model) c root len info fk fn deps).run db).1
    (p.got, p.total) = (progress c root len).eval db := by
  intro p
  have hv := readView_model (progress c root len) deps db
  simp only [p, Kinds.File.pic, ReaderT.run, bind, ReaderT.bind, pure] at *
  rw [hv]
  generalize (progress c root len).eval db = gt
  obtain ⟨g, t⟩ := gt
  dsimp only
  split <;> rfl

/-- A picture's length is its attachment's. -/
theorem pic_len (c root : Id) (len : Nat) (info : FileMeta) (fk fn : ByteArray) (deps : Array Q)
    (db : DB Fact) : ((Kinds.File.pic (m := Model) c root len info fk fn deps).run db).1.len = len := by
  have hv := readView_model (progress c root len) deps db
  simp only [Kinds.File.pic, ReaderT.run, bind, ReaderT.bind, pure] at *
  rw [hv]
  generalize (progress c root len).eval db = gt
  obtain ⟨g, t⟩ := gt
  dsimp only
  split <;> rfl

/-- **The ring and the caption show exactly `Community.progress`.** The
pill drawn over the picture the app reads, in any box, is the one laid
out from that view's answer (got, total) and the attachment's length,
and from nothing else: its counts, its words (`layout_words`) and its lit
ring pixels (`ring_counts`) are progress's. -/
theorem arrival_progress (f : Font.Font) (dm : Dim) (bx : Box) (c root : Id) (len : Nat)
    (info : FileMeta) (fk fn : ByteArray) (deps : Array Q) (db : DB Fact) :
    Row.arrival f dm bx ((Kinds.File.pic (m := Model) c root len info fk fn deps).run db).1 =
      Arrival.layout f dm.arrival bx.x bx.y bx.w bx.h ((progress c root len).eval db).1
        ((progress c root len).eval db).2 len := by
  have hp := pic_progress c root len info fk fn deps db
  have hl := pic_len c root len info fk fn deps db
  simp only [Prod.ext_iff] at hp
  simp only [Row.arrival, hl, ← hp.1, ← hp.2]

/-- So a drawn pill's counts are progress's answer. -/
theorem arrival_counts {f : Font.Font} {dm : Dim} {bx : Box} {c root : Id} {len : Nat}
    {info : FileMeta} {fk fn : ByteArray} {deps : Array Q} {db : DB Fact} {pl : Arrival.Pill}
    (h : Row.arrival f dm bx ((Kinds.File.pic (m := Model) c root len info fk fn deps).run db).1 = some pl) :
    (pl.got, pl.total) = (progress c root len).eval db := by
  rw [arrival_progress] at h
  obtain ⟨_, hg, ht, _⟩ := layout_words h
  rw [hg, ht]

section
variable {C : Crypto} {s : DB Fact} (hsize : ∀ x, (sha256 x).size = 32) {ct : ByteArray}
  (hspr : Merkle.NoSecondPreimage sha256 (Merkle.treeInputs sha256 ct))
include hsize hspr

/-- **Complete is every chunk held.** A picture whose counts are its
file's progress (as `pic_progress` reads them) is complete exactly when
the store holds a Valid chunk of the file at every index. -/
theorem complete_iff_held (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (len : Nat)
    {p : Pic} (hp : (p.got, p.total) = (progress c (Merkle.fileRoot sha256 ct) len).eval s) :
    p.complete = true ↔
      ∀ i < Merkle.nChunks len, ∃ y, V C s.ops y (.chunk c (Merkle.fileRoot sha256 ct) len i) := by
  have hle := progress_le hsize hspr h hq c len
  have hfull := progress_full hsize hspr h hq c len
  have ht : (progress c (Merkle.fileRoot sha256 ct) len).eval s =
      (((progress c (Merkle.fileRoot sha256 ct) len).eval s).1, Merkle.nChunks len) := by
    unfold progress; simp
  rw [← hp] at hle hfull ht
  simp only [Prod.mk.injEq] at ht
  rw [Pic.complete, done_iff hle (by rw [ht.2]; exact Merkle.one_le_nChunks len)]
  exact hfull

/-- **A picture showing its file holds all of it.** Shown as the file
(`shown_file`), its counts being the file's progress, the attachment's
length is the file's and the store holds each of the file's chunk ops,
whose slices are the file. -/
theorem file_whole (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (len : Nat)
    {p : Pic} (hp : (p.got, p.total) = (progress c (Merkle.fileRoot sha256 ct) len).eval s)
    {α : Type} (pre full : Option α) (hs : (p.shown pre full).2 = true) :
    len = ct.size ∧ ∀ i < Merkle.nChunks ct.size,
      V C s.ops (fileChunk c ct i).id (.chunk c (Merkle.fileRoot sha256 ct) ct.size i) := by
  have hc := ((shown_file p pre full).1 hs).1
  have hle := progress_le hsize hspr h hq c len
  refine progress_done hsize hspr h hq c len ?_
  rw [← hp] at hle ⊢
  simp only [Pic.complete, done, Bool.and_eq_true, decide_eq_true_eq] at hc
  simp only at hle ⊢
  omega

/-- **The picture the app reads is complete exactly when its file is
held**: `Kinds.File.pic` over the store, composed with `complete_iff_held`. -/
theorem pic_complete_iff_held (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (len : Nat)
    (info : FileMeta) (fk fn : ByteArray) (deps : Array Q) :
    ((Kinds.File.pic (m := Model) c (Merkle.fileRoot sha256 ct) len info fk fn deps).run s).1.complete = true ↔
      ∀ i < Merkle.nChunks len, ∃ y, V C s.ops y (.chunk c (Merkle.fileRoot sha256 ct) len i) :=
  complete_iff_held hsize hspr h hq c len (pic_progress c _ len info fk fn deps s)

end

end ArrivalLaws
