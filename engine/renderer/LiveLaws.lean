/-
One moment: the live answers a frame reads are all of one state of the
store, over the running cache (Live.answer, Live.store, Live.notice,
Live.keep).

A frame runs in one read transaction (App's `step`). Two things are
assumed of SQLite, and only these:

- **snapshot**: inside one read transaction, every read answers as one
  state of the store (SQLite's snapshot isolation, a WAL reader); a
  moment `ans : Q → Ans` is those answers (with the outbox);
- **journal**: the rows and verdicts the journal hands a frame
  (`takeChanges`, the frame's first read), netted and matched against
  the windows the cache watches (`Live.hit`), reach every instance whose
  answer changed since the last moment. Over the engine's model this is
  a theorem for a read of rows: its rows change exactly when its window
  does (Engine.read_notice_iff, for a batch of commits and purges);
  SQLite's triggers are tested against it (tests/engine/WindowCheck.lean).

From them: `Agrees l ans`, that every answer the cache holds unstaled is
the moment's and its window is watched (in an index kept well formed),
holds from the empty cache (`agrees_empty`), through a read that asks
the store (`agrees_store`), a notice of the journal's rows
(`agrees_notice`, moving to the next moment) and a pruning
(`agrees_keep`); and a read the cache answers returns the moment's
answer (`answer_agrees`). So every answer a frame reads, cached or not,
is of the frame's one moment (`read_one_moment`): no part of the screen
is newer than another. And the cache watches nothing it does not hold:
every window it watches is a fresh answer's (`watched_held`), so no
notice reaches a read the frame has dropped.
-/
import engine.renderer.Data
import engine.core.WindowIndex

namespace LiveLaws
open Engine Data

theorem byteArray_lawful : LawfulBEq ByteArray where
  eq_of_beq {a b} h := ByteArray.ext (eq_of_beq (show a.data == b.data from h))
  rfl {a} := show a.data == a.data from beq_self_eq_true a.data

attribute [local instance] byteArray_lawful

theorem listQ_lawful : LawfulBEq ListQ where
  eq_of_beq {a b} h := by
    cases a; cases b
    unfold BEq.beq instBEqListQ at h
    dsimp only at h
    unfold instBEqListQ.beq at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
    rfl
  rfl {a} := by
    cases a
    unfold BEq.beq instBEqListQ
    dsimp only
    unfold instBEqListQ.beq
    simp

attribute [local instance] listQ_lawful

theorem q_lawful : LawfulBEq Q where
  eq_of_beq {a b} h := by
    cases a <;> cases b <;> unfold BEq.beq instBEqQ at h <;> dsimp only at h <;> unfold instBEqQ.beq at h
    all_goals simp_all
  rfl {a} := by
    cases a <;> unfold BEq.beq instBEqQ <;> dsimp only <;> unfold instBEqQ.beq <;> simp

attribute [local instance] q_lawful

/-- **The cache agrees with moment `ans`:** its index is well formed, and
every answer it holds that no notice has made stale is the moment's, and
its window is watched (so a notice of a row in it reaches it). -/
def Agrees (l : Live) (ans : Q → Ans) : Prop :=
  l.subs.WF ∧ ∀ q e, l.entries[q]? = some e → e.stale = false →
    e.ans = ans q ∧ l.subs.Has q (q.win e.ans)

theorem agrees_empty (ans : Q → Ans) : Agrees {} ans :=
  ⟨Subs.wf_empty, fun q e he => by simp at he⟩

/-- **A read the cache answers is the moment's.** -/
theorem answer_agrees {l : Live} {ans : Q → Ans} {q : Q} {a : Ans} (h : Agrees l ans)
    (ha : l.answer q = some a) : a = ans q := by
  unfold Live.answer at ha
  split at ha
  · next e he =>
    split at ha
    · cases ha
    · next hs => simp only [Option.some.injEq] at ha; subst ha; exact (h.2 q e he (by simpa using hs)).1
  · cases ha

/-- **A read that asks the store keeps the cache in agreement**, when
the store answers as the moment (snapshot). -/
theorem agrees_store {l : Live} {ans : Q → Ans} (h : Agrees l ans) (q : Q) :
    Agrees (l.store q (ans q)) ans := by
  have hk : (if l.fresh q then l.subs.keep (· != q) else l.subs).WF := by
    split
    · exact Subs.keep_wf h.1 _
    · exact h.1
  refine ⟨Subs.add_wf hk _ _, fun q' e he hs => ?_⟩
  simp only [Live.store, Std.HashMap.getElem?_insert, beq_iff_eq] at he ⊢
  by_cases hq : q = q'
  · subst hq
    rw [if_pos (beq_self_eq_true q), Option.some.injEq] at he
    subst he
    exact ⟨rfl, (Subs.has_add _ _ _ _).2 (Or.inr ⟨rfl, rfl⟩)⟩
  · rw [if_neg (fun hb => hq (eq_of_beq hb))] at he
    obtain ⟨hans, hw⟩ := h.2 q' e he hs
    refine ⟨hans, (Subs.has_add _ _ _ _).2 (Or.inl ?_)⟩
    split
    · exact (Subs.has_keep _ _ _).2 ⟨hw, by simpa using Ne.symm hq⟩
    · exact hw

/-! ## Notices -/

theorem staleAll_entries (qs : List Q) : ∀ (l : Live) {q : Q} {e : Entry},
    (qs.foldl Live.staleOne l).entries[q]? = some e → e.stale = false →
      l.entries[q]? = some e ∧ q ∉ qs := by
  induction qs with
  | nil => intro l q e he _; exact ⟨he, by simp⟩
  | cons q0 t ih =>
    intro l q e he hs
    obtain ⟨h1, hn⟩ := ih (l.staleOne q0) he hs
    unfold Live.staleOne at h1
    split at h1
    · next e0 h0 =>
      simp only [Std.HashMap.getElem?_insert, beq_iff_eq] at h1
      by_cases hq : q0 = q
      · subst hq; rw [if_pos (beq_self_eq_true q0), Option.some.injEq] at h1; subst h1; simp at hs
      · rw [if_neg (fun hb => hq (eq_of_beq hb))] at h1
        exact ⟨h1, by simp [Ne.symm hq, hn]⟩
    · next h0 =>
      refine ⟨h1, ?_⟩
      intro hm
      rcases List.mem_cons.1 hm with rfl | hm
      · rw [h0] at h1; cases h1
      · exact hn hm

/-- **A notice of the journal's rows moves the cache to the next
moment.** If every instance whose answer changed from `ans` to `ans'` is
one the rows reach (journal), the cache after the notice agrees with
`ans'`. -/
theorem agrees_notice {l : Live} {ans ans' : Q → Ans} (h : Agrees l ans) (fs : Array Filing) (vs : Array Id)
    (hj : ∀ q, (l.hit fs vs).contains q = false → ans' q = ans q) : Agrees (l.notice fs vs) ans' := by
  unfold Live.notice
  simp only
  generalize l.hit fs vs = hit at hj ⊢
  split
  · next hem =>
    refine ⟨h.1, fun q e he hs => ?_⟩
    obtain ⟨hans, hw⟩ := h.2 q e he hs
    have : hit.contains q = false := by
      cases hc : hit.contains q
      · rfl
      · exact absurd (Std.HashSet.contains_iff_mem.1 hc) ((Std.HashSet.isEmpty_iff_forall_not_mem.1 hem) q)
    exact ⟨hans.trans (hj q this).symm, hw⟩
  · constructor
    · show (l.subs.keep fun q => !hit.contains q).WF
      exact Subs.keep_wf h.1 _
    · intro q e he hs
      change (Std.HashSet.fold Live.staleOne l hit).entries[q]? = some e at he
      show e.ans = ans' q ∧ (l.subs.keep fun q => !hit.contains q).Has q (q.win e.ans)
      rw [Std.HashSet.fold_eq_foldl_toList] at he
      obtain ⟨h1, hn⟩ := staleAll_entries _ l he hs
      have hc : hit.contains q = false := by
        cases hc : hit.contains q
        · rfl
        · exact absurd (Std.HashSet.mem_toList.2 (Std.HashSet.contains_iff_mem.1 hc)) hn
      obtain ⟨hans, hw⟩ := h.2 q e h1 hs
      exact ⟨hans.trans (hj q hc).symm, (Subs.has_keep _ _ _).2 ⟨hw, by simp [hc]⟩⟩

/-- **Forgetting instances keeps the rest in agreement.** -/
theorem agrees_keep {l : Live} {ans : Q → Ans} (h : Agrees l ans) (want : Q → Bool) :
    Agrees (l.keep want) ans := by
  refine ⟨Subs.keep_wf h.1 want, fun q e he hs => ?_⟩
  simp only [Live.keep, Std.HashMap.getElem?_filter, Std.HashMap.getKey_eq] at he ⊢
  simp only [Option.pfilter_eq_some_iff] at he
  obtain ⟨he1, hw⟩ := he
  obtain ⟨hans, hh⟩ := h.2 q e he1 hs
  exact ⟨hans, (Subs.has_keep _ _ _).2 ⟨hh, hw⟩⟩

/-- **Unmounting keeps the cache in agreement.** A component unmounts:
the reads it alone made (`qs`) are forgotten, and their windows are no
longer watched; every other answer the cache holds is still the
moment's, and watched. -/
theorem agrees_unmount {l : Live} {ans : Q → Ans} (h : Agrees l ans) (qs : Std.HashSet Q) :
    Agrees (l.keep fun q => !qs.contains q) ans ∧
      ∀ q, qs.contains q = true → ∀ w, ¬ (l.keep fun q => !qs.contains q).subs.Has q w := by
  refine ⟨agrees_keep h _, fun q hq w hw => ?_⟩
  have h2 : (!qs.contains q) = true := ((Subs.has_keep (I := l.subs) (fun q => !qs.contains q) q w).1 hw).2
  rw [hq] at h2
  cases h2

/-- **What the cache watches, it keeps:** after forgetting the instances
nobody wants, no window of one is watched (so no notice reaches a read
the frame dropped: Screen.screen_subs on the cache). -/
theorem watched_held {l : Live} (want : Q → Bool) {q : Q} {w : Win} (hw : (l.keep want).subs.Has q w) :
    want q = true := ((Subs.has_keep _ _ _).1 hw).2

/-- **One moment.** A read in a frame whose cache agrees with the
frame's moment (and whose store answers as it, snapshot) returns the
moment's answer, cached or not, and leaves the cache in agreement: App's
`read`, its two branches. -/
theorem read_one_moment {l : Live} {ans : Q → Ans} (h : Agrees l ans) (q : Q) :
    (match l.answer q with
      | some a => (a, l)
      | none => (ans q, l.store q (ans q))) |> fun r => r.1 = ans q ∧ Agrees r.2 ans := by
  split
  · next a ha => exact ⟨answer_agrees h ha, h⟩
  · exact ⟨rfl, agrees_store h q⟩

end LiveLaws
