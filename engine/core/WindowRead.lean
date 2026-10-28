/-
A read's window (`ListQ.win`) changes exactly when its rows do.

A list read newest first with limit n answers the n newest rows in its
range. Its window runs from the last of them up: a row filed below it (a
backfilled old message under the newest 50) is outside, and changes no
row of the answer; a row filed inside it, or one inside it unfiled,
changes the answer. Oldest first, the same from the top down. A read
whose answer the limit did not cut answers its whole range, which is its
window.

`read_rows_iff`: between any two states, the read's rows are the same
exactly when its window (from the first state's answer) holds the same
rows. With `notice_iff`, a subscriber watching exactly that window is
notified exactly when the read's rows changed (`read_notice_iff`).
-/
import engine.core.WindowLaws

namespace Engine

/-! ## Cutting a strictly ordered list -/

section
variable {α : Type} (r : Pos → Pos → Prop)

theorem mem_last_or {l : List (Pos × α)} (h : l.Pairwise fun a b => r a.1 b.1) {y : Pos × α}
    (hy : l.getLast? = some y) {x : Pos × α} (hx : x ∈ l) : x = y ∨ r x.1 y.1 := by
  obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.1 hy
  rw [List.pairwise_append] at h
  rcases List.mem_append.1 hx with hx | hx
  · exact Or.inr (h.2.2 x hx y (List.mem_singleton_self _))
  · exact Or.inl (List.mem_singleton.1 hx)

/-- Rows at or ahead of a threshold come first. -/
theorem partition_thr {thr : Pos → Bool} (hc : ∀ a b, r a b → thr b = true → thr a = true) :
    ∀ {l : List (Pos × α)}, (l.Pairwise fun a b => r a.1 b.1) →
      l.filter (fun x => thr x.1) ++ l.filter (fun x => !thr x.1) = l
  | [], _ => rfl
  | a :: t, h => by
    rw [List.pairwise_cons] at h
    by_cases ha : thr a.1 = true
    · simp only [List.filter_cons, ha, ite_true, Bool.not_true, Bool.false_eq_true, ite_false,
        List.cons_append]
      rw [partition_thr hc h.2]
    · have hall : ∀ b ∈ t, thr b.1 = false := fun b hb => by
        cases e : thr b.1
        · rfl
        · exact absurd (hc _ _ (h.1 b hb) e) ha
      have h1 : t.filter (fun x => thr x.1) = [] := List.filter_eq_nil_iff.2 fun b hb => by simp [hall b hb]
      have h2 : t.filter (fun x => !thr x.1) = t := List.filter_eq_self.2 fun b hb => by simp [hall b hb]
      simp only [List.filter_cons, ha, Bool.false_eq_true, ite_false, Bool.not_false, ite_true, h1, h2,
        List.nil_append]

/-- **A cut list is its rows at or ahead of its last.** -/
theorem cut_top (hirr : ∀ a, ¬ r a a) (htr : ∀ a b c, r a b → r b c → r a c) {thr : Pos → Bool}
    {l : List (Pos × α)} (h : l.Pairwise fun a b => r a.1 b.1) {n : Nat} {P : Pos × α}
    (hlast : (l.take n).getLast? = some P) (hthr : ∀ x, thr x = true ↔ x = P.1 ∨ r x P.1) :
    l.take n = l.filter fun x => thr x.1 := by
  have hl := h
  rw [← List.take_append_drop n l, List.pairwise_append] at hl
  conv => rhs; rw [← List.take_append_drop n l]
  rw [List.filter_append]
  have hP : P ∈ l.take n := List.mem_of_getLast? hlast
  have e1 : (l.take n).filter (fun x => thr x.1) = l.take n := by
    apply List.filter_eq_self.2
    intro x hx
    rcases mem_last_or r hl.1 hlast hx with rfl | hr
    · exact (hthr _).2 (Or.inl rfl)
    · exact (hthr _).2 (Or.inr hr)
  have e2 : (l.drop n).filter (fun x => thr x.1) = [] := by
    apply List.filter_eq_nil_iff.2
    intro y hy hty
    have hPy := hl.2.2 P hP y hy
    rcases (hthr _).1 hty with e | hr
    · rw [e] at hPy; exact hirr _ hPy
    · exact hirr _ (htr _ _ _ hPy hr)
  rw [e1, e2, List.append_nil]

end

/-! ## Newest first and oldest first -/

/-- Newest first: a is ahead of b when it sorts after it. -/
def aheadD (a b : Pos) : Prop := b.cmp a = .lt
/-- Oldest first: a is ahead of b when it sorts before it. -/
def aheadA (a b : Pos) : Prop := a.cmp b = .lt

theorem aheadD_irr (a : Pos) : ¬ aheadD a a := by simp [aheadD, Pos.cmp_self]
theorem aheadA_irr (a : Pos) : ¬ aheadA a a := by simp [aheadA, Pos.cmp_self]
theorem aheadD_trans (a b c : Pos) (h1 : aheadD a b) (h2 : aheadD b c) : aheadD a c :=
  Pos.cmp_lt_trans h2 h1
theorem aheadA_trans (a b c : Pos) (h1 : aheadA a b) (h2 : aheadA b c) : aheadA a c :=
  Pos.cmp_lt_trans h1 h2

/-- At or after P. -/
def geP (P x : Pos) : Bool := x.cmp P != .lt
/-- At or before P. -/
def leP (P x : Pos) : Bool := x.cmp P != .gt

theorem geP_iff (P x : Pos) : geP P x = true ↔ x = P ∨ aheadD x P := by
  unfold geP aheadD
  have hs := Pos.cmp_swap P x
  rcases e : P.cmp x with _ | _ | _
  · rw [e] at hs; simp [hs, Ordering.swap]
  · have := (Pos.cmp_eq_iff _ _).1 e; subst this; simp [Pos.cmp_self]
  · rw [e] at hs
    simp only [hs, Ordering.swap, bne_iff_ne, ne_eq, not_true_eq_false, reduceCtorEq, or_false,
      false_iff]
    intro h; subst h; rw [Pos.cmp_self] at e; cases e

theorem leP_iff (P x : Pos) : leP P x = true ↔ x = P ∨ aheadA x P := by
  unfold leP aheadA
  rcases e : x.cmp P with _ | _ | _
  · simp
  · simp [(Pos.cmp_eq_iff _ _).1 e]
  · simp only [bne_iff_ne, ne_eq, not_true_eq_false, reduceCtorEq, or_false, false_iff]
    intro h; subst h; rw [Pos.cmp_self] at e; cases e

theorem geP_closed (P : Pos) (a b : Pos) (h : aheadD a b) (hb : geP P b = true) : geP P a = true := by
  rw [geP_iff] at hb ⊢
  rcases hb with rfl | hb
  · exact Or.inr h
  · exact Or.inr (aheadD_trans _ _ _ h hb)

theorem leP_closed (P : Pos) (a b : Pos) (h : aheadA a b) (hb : leP P b = true) : leP P a = true := by
  rw [leP_iff] at hb ⊢
  rcases hb with rfl | hb
  · exact Or.inr h
  · exact Or.inr (aheadA_trans _ _ _ h hb)

/-! ## A read's rows and its window -/

section
variable {F : Type} [SortKey F]

/-- A read's rows in its range, ascending. -/
def inRange (s : DB F) (q : ListQ) : List (Pos × F) := (matching s q).filter fun r => q.inside r.1

theorem eval_rows (s : DB F) (q : ListQ) :
    (eval s q).rows = q.cut (if q.desc then (inRange s q).reverse else inRange s q) := rfl

theorem matching_key {s : DB F} {q : ListQ} (hq : q.also = []) : matching s q = matching s { key := q.key } := by
  unfold matching; rw [hq]

/-- Past the read's after bound. -/
def afterOk (q : ListQ) (p : Pos) : Bool := match q.after with | some a => p.cmp a == .gt | none => true
/-- Before the read's before bound. -/
def beforeOk (q : ListQ) (p : Pos) : Bool := match q.before with | some b => p.cmp b == .lt | none => true

theorem inside_eq (q : ListQ) (p : Pos) : q.inside p = (afterOk q p && beforeOk q p) := by
  unfold ListQ.inside afterOk beforeOk; rfl

theorem above_after (q : ListQ) (p : Pos) : above (q.after.map (·, false)) p = afterOk q p := by
  unfold afterOk
  cases q.after with
  | none => rfl
  | some a => simp only [Option.map_some, above]; cases p.cmp a <;> rfl

theorem below_before (q : ListQ) (p : Pos) : below (q.before.map (·, false)) p = beforeOk q p := by
  unfold beforeOk
  cases q.before with
  | none => rfl
  | some b => simp only [Option.map_some, below]; cases p.cmp b <;> rfl

theorem rangeWin_inside (q : ListQ) (p : Pos) : q.rangeWin.inside p = q.inside p := by
  simp only [ListQ.rangeWin, Win.inside, above_after, below_before, inside_eq]

theorem window_range {s : DB F} {q : ListQ} (hq : q.also = []) : window s q.rangeWin = inRange s q := by
  unfold window inRange
  rw [matching_key hq]
  congr 1
  funext r
  rw [rangeWin_inside]

theorem inRange_strict {fam : Family F} {s : DB F} (h : Inv fam s) {q : ListQ} (hq : q.also = []) :
    (inRange s q).Pairwise fun a b => a.1.cmp b.1 = .lt := by
  rw [← window_range hq]; exact window_strict h _

/-- Past the after bound, at or after a row inside the range. -/
theorem after_of_ge {q : ListQ} {P p : Pos} (hP : q.inside P = true) (hp : geP P p = true) :
    afterOk q p = true := by
  rw [inside_eq, Bool.and_eq_true] at hP
  have h1 := hP.1
  unfold afterOk at h1 ⊢
  cases ha : q.after with
  | none => rfl
  | some a =>
    rw [ha] at h1
    simp only [beq_iff_eq] at h1 ⊢
    rw [geP_iff] at hp
    rcases hp with rfl | hp
    · exact h1
    · exact Pos.lt_swap (Pos.cmp_lt_trans (Pos.gt_swap h1) hp)

theorem before_of_le {q : ListQ} {P p : Pos} (hP : q.inside P = true) (hp : leP P p = true) :
    beforeOk q p = true := by
  rw [inside_eq, Bool.and_eq_true] at hP
  have h2 := hP.2
  unfold beforeOk at h2 ⊢
  cases hb : q.before with
  | none => rfl
  | some b =>
    rw [hb] at h2
    simp only [beq_iff_eq] at h2 ⊢
    rw [leP_iff] at hp
    rcases hp with rfl | hp
    · exact h2
    · exact Pos.cmp_lt_trans hp h2

theorem window_cutD {s : DB F} {q : ListQ} (hq : q.also = []) {P : Pos} (hP : q.inside P = true) :
    window s { key := q.key, lo := some (P, true), hi := q.before.map (·, false) } =
      (inRange s q).filter fun x => geP P x.1 := by
  unfold window inRange
  rw [matching_key hq, List.filter_filter]
  congr 1
  funext r
  simp only [Win.inside, below_before]
  have ha : above (some (P, true)) r.1 = geP P r.1 := by
    simp only [above, geP]; cases r.1.cmp P <;> rfl
  rw [ha, inside_eq]
  cases hg : geP P r.1
  · simp
  · rw [after_of_ge hP hg]; simp

theorem window_cutA {s : DB F} {q : ListQ} (hq : q.also = []) {P : Pos} (hP : q.inside P = true) :
    window s { key := q.key, lo := q.after.map (·, false), hi := some (P, true) } =
      (inRange s q).filter fun x => leP P x.1 := by
  unfold window inRange
  rw [matching_key hq, List.filter_filter]
  congr 1
  funext r
  simp only [Win.inside, above_after]
  have hb : below (some (P, true)) r.1 = leP P r.1 := by
    simp only [below, leP]; cases r.1.cmp P <;> rfl
  rw [hb, inside_eq]
  cases hl : leP P r.1
  · simp
  · rw [before_of_le hP hl]; simp

/-- The cut case, ordered by `ahead`, for either direction: the read's
rows are the first n of an ordered list exactly when its rows at or
ahead of P are the first n of the other's. -/
theorem cut_iff {α : Type} {r : Pos → Pos → Prop} (hirr : ∀ a, ¬ r a a) (htr : ∀ a b c, r a b → r b c → r a c)
    {thr : Pos → Bool} (hc : ∀ a b, r a b → thr b = true → thr a = true)
    {Ls Lt : List (Pos × α)} (hs : Ls.Pairwise fun a b => r a.1 b.1) (ht : Lt.Pairwise fun a b => r a.1 b.1)
    {n : Nat} {P : Pos × α} (hlen : (Ls.take n).length = n) (hlast : (Ls.take n).getLast? = some P)
    (hthr : ∀ x, thr x = true ↔ x = P.1 ∨ r x P.1) :
    Lt.take n = Ls.take n ↔ Lt.filter (fun x => thr x.1) = Ls.filter (fun x => thr x.1) := by
  have es := cut_top r hirr htr hs hlast hthr
  constructor
  · intro e
    rw [← es]
    rw [← e] at hlast
    rw [← cut_top r hirr htr ht hlast hthr, e]
  · intro e
    rw [es, ← e]
    conv => lhs; rw [← partition_thr r hc ht]
    apply List.take_left'
    rw [e, ← es, hlen]

end

/-! ## The law -/

section
variable {F : Type} [SortKey F]

theorem win_none {q : ListQ} (hlim : q.limit = none) (a : Answer F) : q.win a = q.rangeWin := by
  unfold ListQ.win; rw [hlim]; rfl

theorem win_uncut {q : ListQ} {n : Nat} (hlim : q.limit = some n) {a : Answer F} (hlen : a.rows.length ≠ n) :
    q.win a = q.rangeWin := by
  unfold ListQ.win; rw [hlim]
  cases a.rows.getLast? with
  | none => rfl
  | some P => obtain ⟨_, _⟩ := P; simp only [hlen, ite_false]; rfl

theorem win_cut {q : ListQ} {n : Nat} (hlim : q.limit = some n) {a : Answer F} (hlen : a.rows.length = n)
    {Pp : Pos} {Pf : F} (hlast : a.rows.getLast? = some (Pp, Pf)) :
    q.win a = if q.desc then { key := q.key, lo := some (Pp, true), hi := q.before.map (·, false) }
      else { key := q.key, lo := q.after.map (·, false), hi := some (Pp, true) } := by
  unfold ListQ.win; rw [hlim, hlast]; simp only [hlen, ite_true]

/-- **A read's rows change exactly when its window's do.** For a read of
one key (no conjuncts) that answers rows (a limit other than 0), its
window from state s's answer holds the same rows in s and t exactly when
the read answers the same rows in both. -/
theorem read_rows_iff {fam : Family F} {s t : DB F} (hs : Inv fam s) (ht : Inv fam t) {q : ListQ}
    (hq : q.also = []) (hl : q.limit ≠ some 0) :
    (eval t q).rows = (eval s q).rows ↔ window t (q.win (eval s q)) = window s (q.win (eval s q)) := by
  have Ss := inRange_strict hs hq
  have St := inRange_strict ht hq
  have Ds : (inRange s q).reverse.Pairwise fun a b => aheadD a.1 b.1 :=
    List.pairwise_reverse.2 (Ss.imp fun h => h)
  have Dt : (inRange t q).reverse.Pairwise fun a b => aheadD a.1 b.1 :=
    List.pairwise_reverse.2 (St.imp fun h => h)
  have As : (inRange s q).Pairwise fun a b => aheadA a.1 b.1 := Ss
  have At : (inRange t q).Pairwise fun a b => aheadA a.1 b.1 := St
  have hrange : window t q.rangeWin = window s q.rangeWin ↔ inRange t q = inRange s q := by
    rw [window_range hq, window_range hq]
  have hOiff : (if q.desc then (inRange t q).reverse else inRange t q) =
      (if q.desc then (inRange s q).reverse else inRange s q) ↔ inRange t q = inRange s q := by
    cases q.desc
    · simp
    · simp
  cases hlim : q.limit with
  | none =>
    rw [win_none hlim, hrange, eval_rows, eval_rows]
    simp only [ListQ.cut, hlim]
    exact hOiff
  | some n =>
    have hn : n ≠ 0 := fun e => hl (by rw [hlim, e])
    by_cases hlen : (eval s q).rows.length = n
    · -- cut: the answer's last row bounds the window
      obtain ⟨⟨Pp, Pf⟩, hlast⟩ : ∃ P, (eval s q).rows.getLast? = some P := by
        apply Option.isSome_iff_exists.1
        apply List.getLast?_isSome.2
        intro e; rw [e] at hlen; exact hn hlen.symm
      rw [win_cut hlim hlen hlast]
      have hPin : q.inside Pp = true := by
        have hm := List.mem_of_getLast? hlast
        rw [eval_rows] at hm
        simp only [ListQ.cut, hlim] at hm
        have hm' := List.mem_of_mem_take hm
        have : (Pp, Pf) ∈ inRange s q := by
          cases hd : q.desc
          · simpa [hd] using hm'
          · simpa [hd] using hm'
        exact (List.mem_filter.1 this).2
      rw [eval_rows] at hlen hlast
      rw [eval_rows, eval_rows]
      simp only [ListQ.cut, hlim] at hlen hlast ⊢
      cases hd : q.desc
      · simp only [hd, Bool.false_eq_true, ite_false] at hlen hlast ⊢
        rw [window_cutA hq hPin, window_cutA hq hPin]
        exact cut_iff aheadA_irr aheadA_trans (leP_closed Pp) As At hlen hlast (leP_iff Pp)
      · simp only [hd, ite_true] at hlen hlast ⊢
        rw [window_cutD hq hPin, window_cutD hq hPin]
        rw [cut_iff aheadD_irr aheadD_trans (geP_closed Pp) Ds Dt hlen hlast (geP_iff Pp),
          List.filter_reverse, List.filter_reverse, List.reverse_inj]
    · -- uncut: the answer is its whole range
      rw [win_uncut hlim hlen, hrange, ← hOiff, eval_rows, eval_rows]
      rw [eval_rows] at hlen
      simp only [ListQ.cut, hlim] at hlen ⊢
      generalize (if q.desc then (inRange s q).reverse else inRange s q) = Os at hlen ⊢
      generalize (if q.desc then (inRange t q).reverse else inRange t q) = Ot
      have hlt : Os.length < n := by rw [List.length_take] at hlen; omega
      rw [List.take_of_length_le (Nat.le_of_lt hlt)]
      constructor
      · intro e
        have : (Ot.take n).length = Os.length := by rw [e]
        rw [List.length_take] at this
        have : Ot.length < n := by omega
        rwa [List.take_of_length_le (Nat.le_of_lt this)] at e
      · intro e; rw [e, List.take_of_length_le (Nat.le_of_lt hlt)]

/-- **A read's window holds exactly its rows.** At the state it was read
in, the window of a read of one key with rows holds the answer's rows
and no other: a list window adds no row the screen did not load. -/
theorem window_rows {fam : Family F} {s : DB F} (hs : Inv fam s) {q : ListQ} (hq : q.also = [])
    (hl : q.limit ≠ some 0) (r : Pos × F) :
    r ∈ window s (q.win (eval s q)) ↔ r ∈ (eval s q).rows := by
  have Ss := inRange_strict hs hq
  have Ds : (inRange s q).reverse.Pairwise fun a b => aheadD a.1 b.1 :=
    List.pairwise_reverse.2 (Ss.imp fun h => h)
  have As : (inRange s q).Pairwise fun a b => aheadA a.1 b.1 := Ss
  have hord : ∀ l : List (Pos × F), r ∈ (if q.desc then l.reverse else l) ↔ r ∈ l := by
    intro l; cases q.desc <;> simp
  cases hlim : q.limit with
  | none =>
    rw [win_none hlim, window_range hq, eval_rows]
    simp only [ListQ.cut, hlim]
    exact (hord _).symm
  | some n =>
    have hn : n ≠ 0 := fun e => hl (by rw [hlim, e])
    by_cases hlen : (eval s q).rows.length = n
    · obtain ⟨⟨Pp, Pf⟩, hlast⟩ : ∃ P, (eval s q).rows.getLast? = some P := by
        apply Option.isSome_iff_exists.1
        apply List.getLast?_isSome.2
        intro e; rw [e] at hlen; exact hn hlen.symm
      rw [win_cut hlim hlen hlast]
      have hPin : q.inside Pp = true := by
        have hm := List.mem_of_getLast? hlast
        rw [eval_rows] at hm
        simp only [ListQ.cut, hlim] at hm
        have hm' := List.mem_of_mem_take hm
        have : (Pp, Pf) ∈ inRange s q := by
          cases hd : q.desc
          · simpa [hd] using hm'
          · simpa [hd] using hm'
        exact (List.mem_filter.1 this).2
      rw [eval_rows] at hlast ⊢
      simp only [ListQ.cut, hlim] at hlast ⊢
      cases hd : q.desc
      · simp only [hd, Bool.false_eq_true, ite_false] at hlast ⊢
        rw [window_cutA hq hPin, cut_top aheadA aheadA_irr aheadA_trans As hlast (leP_iff Pp)]
      · simp only [hd, ite_true] at hlast ⊢
        rw [window_cutD hq hPin, cut_top aheadD aheadD_irr aheadD_trans Ds hlast (geP_iff Pp),
          List.filter_reverse, List.mem_reverse]
    · rw [win_uncut hlim hlen, window_range hq]
      rw [eval_rows] at hlen ⊢
      simp only [ListQ.cut, hlim] at hlen ⊢
      have hlt : (if q.desc then (inRange s q).reverse else inRange s q).length < n := by
        rw [List.length_take] at hlen; omega
      rw [List.take_of_length_le (Nat.le_of_lt hlt)]
      exact (hord _).symm

/-- **A read's notices are exact.** A subscriber whose one window is the
read's (from its answer in s) is notified of a batch exactly when the
read's rows changed: a row filed outside the window (below a newest-n
answer, say) notifies nothing.

Known gap: a union of reads (`Community.readable`, one read per key)
watches each read's own window, so its notices are complete but not
precise for the union's own cut: each key's window is cut at that key's
last row, not at the union's. -/
theorem read_notice_iff {S : Type} {fam : Family F} {s : DB F} (hs : Inv fam s) {cs : List Change}
    (ho : OneOpPerId s cs) {I : Subs S} (hI : I.WF) {x : S} {q : ListQ} (hq : q.also = [])
    (hl : q.limit ≠ some 0) (hx : ∀ w, I.Has x w ↔ w = q.win (eval s q)) :
    x ∈ I.notify (runJ fam cs s).2.toArray ↔ (eval (runJ fam cs s).1 q).rows ≠ (eval s q).rows := by
  rw [notice_iff hs ho hI, ne_eq, read_rows_iff hs (run_inv cs hs) hq hl]
  constructor
  · rintro ⟨w, hw, hne⟩ he
    rw [(hx w).1 hw] at hne
    exact hne he.symm
  · intro hne
    exact ⟨_, (hx _).2 rfl, fun he => hne he.symm⟩

end

/-! ## A read's watch -/

section
variable {F : Type} [SortKey F]

theorem eval_eq (s : DB F) (q : ListQ) :
    eval s q = ⟨q.cut (if q.desc then (inRange s q).reverse else inRange s q),
      capped q.cap (inRange s q).length, (matching s q).length, true⟩ := rfl

theorem window_all {s : DB F} (k : ByteArray) : window s (Win.all k) = matching s { key := k } := by
  unfold window
  apply List.filter_eq_self.2
  intro r _
  rfl

/-- **A read's watch covers what its reader uses.** For a read of one key,
if its watch (`ListQ.watch`, from its answer in s) holds the same rows in
s and t, the read answers the same in both, but for the counts no reader
of it uses (`ListQ.kept`). So, with `notice_iff`, a subscriber watching
it misses no change its reader can see. -/
theorem watch_stable {fam : Family F} {s t : DB F} (hs : Inv fam s) (ht : Inv fam t) {q : ListQ}
    (hq : q.also = []) (h : window t (q.watch (eval s q)) = window s (q.watch (eval s q))) :
    q.kept (eval t q) = q.kept (eval s q) := by
  unfold ListQ.watch at h
  unfold ListQ.kept
  have hal : q.also.isEmpty = true := by rw [hq]; rfl
  by_cases h0 : q.limit = some 0
  · have hc : (q.limit == some 0 || !q.also.isEmpty) = true := by simp [h0]
    rw [if_pos hc] at h
    rw [if_pos hc, if_pos hc]
    rw [window_all, window_all, ← matching_key hq, ← matching_key hq] at h
    rw [eval_eq, eval_eq]
    unfold inRange
    rw [h]
  · have hc : ¬ ((q.limit == some 0 || !q.also.isEmpty) = true) := by simp [h0, hal]
    rw [if_neg hc] at h
    rw [if_neg hc, if_neg hc]
    have hr := (read_rows_iff hs ht hq h0).2 h
    rw [eval_eq, eval_eq] at hr ⊢
    simp only at hr ⊢
    rw [hr]

end

end Engine
