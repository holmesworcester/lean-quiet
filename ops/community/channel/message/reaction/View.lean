import ops.Commands
import engine.renderer.Row
import ops.community.Proofs

/-!
`community.channel.message.reaction`: its component, which reads its own facts, and the component's laws.
-/
namespace Kinds.React
open _root_.Engine _root_.Community _root_.Data

/-- A list's distinct elements, each at its first place. -/
def uniq {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | x :: t => x :: uniq (t.filter fun y => !decide (y = x))
termination_by l => l.length
decreasing_by all_goals (simp_wf; exact Nat.lt_succ_of_le (Nat.le_trans (List.length_filter_le _ _) (by simp)))

/-- Reactions (emoji, reactor) into tallies: each emoji once, in the order
it first arrived, with the distinct people who reacted with it. Laws
(RowLaws): `tally_nodup`, `tally_mem`. -/
def tally (xs : List (String × Id)) : List (String × List Id) :=
  (uniq (xs.map (·.1))).map fun e => (e, uniq ((xs.filter fun p => decide (p.1 = e)).map (·.2)))
variable {m : Type → Type} [Monad m] [Reads m]

/-- The reaction block discovers distinct emoji identities, not counts. -/
def emojis (c msg : Id) : m (List String × Array Q) :=
  readSet (react.byMessage.query [c, msg] (desc := false))
    (fun | .react _ _ _ e _ => String.fromUTF8? e | _ => none) #[]

def read (c msg me : Id) (deps : Array Q) : m (List Row.Tally × Array Q) := do
  let (a, _, deps) ← readList (react.byMessage.query [c, msg] (limit := some 500) (desc := false)) deps
  let xs := a.rows.filterMap fun (_, f) => match f with
    | .react _ who _ e _ => some ((String.fromUTF8? e).getD "?", who)
    | _ => none
  return ((tally xs).map fun (e, us) => ⟨e, us.length, us.any (fun x => decide (x = me))⟩, deps)

/-- One emoji component owns its set of reactors. Duplicate ops by one
person count once; membership gives the current user's selected state. -/
def one (c msg me : Id) (emoji : String) : m (Row.Tally × Array Q) := do
  let (users, deps) ← readSet (react.byMessageEmoji.query [c, msg, emoji.toUTF8] (desc := false))
    (fun | .react _ who _ _ _ => some who | _ => none) #[]
  return (⟨emoji, users.length, users.contains me⟩, deps)
end Kinds.React
namespace RowLaws
open _root_.Row _root_.Engine

/-- **A picture keeps its shape.** Its box has one side at its bound (240
dp high, or 280 dp and the text's width wide) and the other that side
scaled by the picture's aspect (floored, at least 1 px). -/
theorem picBox_aspect (dm : Dim) (maxW : Nat) (p : Pic) :
    ((picBox dm maxW p).2 = dm.px 240 ∧
      (picBox dm maxW p).1 = max 1 (max p.w 1 * dm.px 240 / max p.h 1) ∧
      max p.w 1 * dm.px 240 ≤ max p.h 1 * min (dm.px 280) maxW) ∨
    ((picBox dm maxW p).1 = min (dm.px 280) maxW ∧
      (picBox dm maxW p).2 = max 1 (max p.h 1 * min (dm.px 280) maxW / max p.w 1) ∧
      max p.h 1 * min (dm.px 280) maxW < max p.w 1 * dm.px 240) := by
  unfold picBox
  by_cases hc : max p.w 1 * dm.px 240 ≤ max p.h 1 * min (dm.px 280) maxW
  · left; simp [hc]
  · right; simp only [hc, if_false]; exact ⟨trivial, trivial, by omega⟩
open _root_.Kinds.React

theorem uniq_mem {α : Type} [DecidableEq α] (x : α) : ∀ l : List α, x ∈ uniq l ↔ x ∈ l
  | [] => by simp [uniq]
  | y :: t => by
    rw [uniq]
    have ih := uniq_mem x (t.filter fun z => !decide (z = y))
    simp only [List.mem_cons, ih, List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not]
    by_cases h : x = y <;> simp [h]
termination_by l => l.length
decreasing_by all_goals (simp_wf; exact Nat.lt_succ_of_le (Nat.le_trans (List.length_filter_le _ _) (by simp)))

theorem uniq_nodup {α : Type} [DecidableEq α] : ∀ l : List α, (uniq l).Nodup
  | [] => by simp [uniq]
  | y :: t => by
    rw [uniq]
    refine List.nodup_cons.2 ⟨?_, uniq_nodup _⟩
    rw [uniq_mem]
    simp
termination_by l => l.length
decreasing_by all_goals (simp_wf; exact Nat.lt_succ_of_le (Nat.le_trans (List.length_filter_le _ _) (by simp)))

/-- **A pill's reactors are distinct**, so its count is how many people
reacted with its emoji, not how many reactions; and **each emoji has one
pill.** -/
theorem tally_nodup (xs : List (String × Id)) :
    ((tally xs).map (·.1)).Nodup ∧ ∀ p ∈ tally xs, p.2.Nodup := by
  refine ⟨?_, ?_⟩
  · simpa [tally, Function.comp_def] using uniq_nodup (xs.map (·.1))
  · intro p hp
    simp only [tally, List.mem_map] at hp
    obtain ⟨e, _, rfl⟩ := hp
    exact uniq_nodup _

/-- **A pill's reactors are exactly who reacted with its emoji**, and
every emoji reacted with has a pill. -/
theorem tally_mem (xs : List (String × Id)) (e : String) (w : Id) :
    (∃ us, (e, us) ∈ tally xs ∧ w ∈ us) ↔ (e, w) ∈ xs := by
  simp only [tally, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨us, ⟨e', _, rfl, rfl⟩, hw⟩
    rw [uniq_mem] at hw
    simp only [List.mem_map, List.mem_filter, decide_eq_true_eq] at hw
    obtain ⟨⟨e'', w'⟩, ⟨hm, rfl⟩, rfl⟩ := hw
    exact hm
  · intro h
    refine ⟨_, ⟨e, ?_, rfl, rfl⟩, ?_⟩
    · rw [uniq_mem]; exact List.mem_map.2 ⟨(e, w), h, rfl⟩
    · rw [uniq_mem]; exact List.mem_map.2 ⟨(e, w), List.mem_filter.2 ⟨h, by simp⟩, rfl⟩

/-- **The row's clock is the message's claimed time** (or "pending"
while its op waits in the outbox): what layout places is `oneLine` of it. -/
theorem time_shown (f : Font.Font) (dm : Dim) (W : Nat) (d : RowData) :
    (layout f dm W d).time = if d.clump.isSome then #[] else
      Text.oneLineFine (f.atSize (dm.px 14)) (min (dm.px 80) ((W - dm.textX - dm.pad) / 3)) (if d.pending then "pending" else clock d.time) := rfl

/-- **The row's name is the author's name as read**, cut as `oneLine`
cuts (a logical prefix: Text.oneLine_prefix), flushed to the box's start. -/
theorem name_placed (f : Font.Font) (dm : Dim) (W : Nat) (d : RowData) :
    (layout f dm W d).name = if d.clump.isSome then #[] else
      flush (Text.oneLineFine (f.atSize (dm.px 16)) (nameWidth f dm W d) d.name) := by
  -- by rewriting, not `rfl`: a defeq check would unfold the bidi under
  -- `oneLine` (out of heartbeats); `simp only` reaches the field directly
  simp only [layout]

/-- Flushing keeps a line's glyphs, in order. -/
theorem flush_shows (l : Text.Line) : (flush l).toList.map (·.c) = l.toList.map (·.c) := by
  unfold flush; split <;> simp

/-- **A flushed line starts at its box's start edge**: its leftmost glyph
is at 0, whatever the line's direction. -/
theorem flush_start (l : Text.Line) (h : l.size ≠ 0) :
    (∃ g ∈ (flush l).toList, g.x = 0) ∧ ∀ g ∈ (flush l).toList, ∃ g' ∈ l.toList, g.x + (l.toList.map (·.x)).min?.getD 0 = g'.x := by
  unfold flush
  split
  · next m hm =>
    have hmem := List.min?_mem hm
    have hle : ∀ x ∈ l.toList.map (·.x), m ≤ x := fun x hx => (List.min?_eq_some_iff.1 hm).2 x hx
    refine ⟨?_, ?_⟩
    · obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hmem
      exact ⟨{ g with x := g.x - g.x }, by simp; exact ⟨g, by simpa using hg, by simp⟩, by simp⟩
    · intro g hg
      simp only [Array.toList_map, List.mem_map] at hg
      obtain ⟨g', hg', rfl⟩ := hg
      have := hle g'.x (List.mem_map.2 ⟨g', hg', rfl⟩)
      exact ⟨g', hg', by simp [hm]; omega⟩
  · next hm =>
    simp only [List.min?_eq_none_iff, List.map_eq_nil_iff, Array.toList_eq_nil_iff] at hm
    exact absurd (by simp [hm]) h

/-- **The row's name starts next to the avatar**, in either direction:
its line's leftmost glyph is at the name box's start. -/
theorem name_starts (f : Font.Font) (dm : Dim) (W : Nat) (d : RowData)
    (h : (layout f dm W d).name.size ≠ 0) : ∃ g ∈ (layout f dm W d).name.toList, g.x = 0 := by
  rw [name_placed] at h ⊢
  split at h
  · simp at h
  · next hc =>
    simp only [hc, ite_false]
    generalize Text.oneLineFine (f.atSize (dm.px 16)) (nameWidth f dm W d) d.name = line at h ⊢
    have h' : line.size ≠ 0 := by
      unfold flush at h
      split at h <;> simpa only [Array.size_map] using h
    exact (flush_start _ h').1

/-- **The row is labelled "⚠ Duplicate" exactly when its name has a
namesake** (the row's `namesake`, read as NamesakeLaws.row_marked says),
after the name and before the time. -/
theorem twin_shown (f : Font.Font) (dm : Dim) (W : Nat) (d : RowData) :
    (layout f dm W d).twin.map (·.2) = if d.namesake && d.clump.isNone then some (Text.oneLine (f.atSize (dm.px 16)) (min ((W - dm.textX - dm.pad) / 3) (dm.cell * 8 + dm.px 12) - dm.px 12) twinText) else none := by
  simp only [layout]; split <;> rfl

/-- The label sits between the name and the time: it starts after the
name ends and ends before the time starts. -/
theorem twin_before_time (f : Font.Font) (dm : Dim) (W : Nat) (d : RowData) {bx : Box} {l : Text.Line}
    (h : (layout f dm W d).twin = some (bx, l)) :
    dm.textX + Paint.Line.width (f.atSize (dm.px 16)) (layout f dm W d).name ≤ bx.x ∧ bx.x + bx.w ≤ (layout f dm W d).timeX := by
  simp only [layout] at h ⊢
  split at h
  · next hn =>
    simp only [Option.some.injEq, twinPill, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [hn, ite_true, twinPill]
    omega
  · cases h

/-- **A tap on the label lands on it** (it opens Quiet's warning). -/
theorem hit_twin {l : Layout} {bx : Box} {ln : Text.Line} {x y : Nat}
    (h : l.twin = some (bx, ln)) (hb : bx.has x y = true) : hit l x y = .twin := by
  simp [hit, h, hb]
end RowLaws
namespace Kinds.Profile
open _root_.Engine _root_.Community _root_.Data
variable {m : Type → Type} [Monad m] [Reads m]

/-- The users of these live admissions, each once (in admission order),
with the node keys their devices are admitted under: what a session
names its peer by. -/
def byUser (ls : List (Id × Key × Key)) : List (Id × List Key) :=
  (React.uniq (ls.map (·.1))).map fun u => (u, (ls.filter fun l => decide (l.1 = u)).map (·.2.2))

end Kinds.Profile
