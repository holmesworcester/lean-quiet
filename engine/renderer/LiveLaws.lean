/-
One moment: the live answers a frame reads are all of one state of the
store, over the running cache (Live.answer, Live.store, Live.notice,
Live.keep).

A frame runs in one read transaction (App's `step`). Two things are
assumed of SQLite, and only these:

- **snapshot**: inside one read transaction, every read answers as one
  state of the store (SQLite's snapshot isolation, a WAL reader); a
  moment `ans : Q → Ans` is those answers (with the outbox);
- **journal**: the keys the journal hands a frame (`takeChanges`, the
  frame's first read) name every watch whose answer changed since the
  last moment (the triggers on idx and status, Db.journal).

From them: `Agrees l ans`, that every answer the cache holds unstaled is
the moment's and is armed on its watch, holds from the empty cache
(`agrees_empty`), through a read that asks the store (`agrees_store`),
a notice of the journal's keys (`agrees_notice`, moving to the next
moment) and a pruning (`agrees_keep`); and a read the cache answers
returns the moment's answer (`answer_agrees`). So every answer a frame
reads, cached or not, is of the frame's one moment (`read_one_moment`):
no part of the screen is newer than another.
-/
import engine.renderer.Data

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

/-- **The cache agrees with moment `ans`:** every answer it holds that
no notice has made stale is the moment's, and is armed on its watch (so
a notice of that key reaches it). -/
def Agrees (l : Live) (ans : Q → Ans) : Prop :=
  ∀ q e, l.entries[q]? = some e → e.stale = false →
    e.ans = ans q ∧ ∃ qs, l.armed[q.watch]? = some qs ∧ q ∈ qs

theorem agrees_empty (ans : Q → Ans) : Agrees {} ans := by
  intro q e he; simp at he

/-- **A read the cache answers is the moment's.** -/
theorem answer_agrees {l : Live} {ans : Q → Ans} {q : Q} {a : Ans} (h : Agrees l ans)
    (ha : l.answer q = some a) : a = ans q := by
  unfold Live.answer at ha
  split at ha
  · next e he =>
    split at ha
    · cases ha
    · next hs => simp only [Option.some.injEq] at ha; subst ha; exact (h q e he (by simpa using hs)).1
  · cases ha

/-- **A read that asks the store keeps the cache in agreement**, when
the store answers as the moment (snapshot). -/
theorem agrees_store {l : Live} {ans : Q → Ans} (h : Agrees l ans) (q : Q) :
    Agrees (l.store q (ans q)) ans := by
  intro q' e he hs
  simp only [Live.store, Std.HashMap.getElem?_insert, beq_iff_eq] at he
  by_cases hq : q = q'
  · subst hq
    rw [if_pos (beq_self_eq_true q), Option.some.injEq] at he
    subst he
    refine ⟨rfl, ?_⟩
    simp only [Live.store]
    split
    · next hc =>
      cases ha : l.armed[q.watch]? with
      | none => simp [Std.HashMap.getD_eq_getD_getElem?, ha] at hc
      | some qs =>
        refine ⟨qs, rfl, ?_⟩
        simpa [Std.HashMap.getD_eq_getD_getElem?, ha] using hc
    · exact ⟨_, Std.HashMap.getElem?_insert_self, by simp⟩
  · rw [if_neg (fun hb => hq (eq_of_beq hb))] at he
    obtain ⟨hans, qs, ha, hm⟩ := h q' e he hs
    refine ⟨hans, ?_⟩
    simp only [Live.store]
    split
    · exact ⟨qs, ha, hm⟩
    · by_cases hk : q.watch = q'.watch
      · refine ⟨_, by rw [← hk]; exact Std.HashMap.getElem?_insert_self, ?_⟩
        rw [← hk] at ha
        simp [Std.HashMap.getD_eq_getD_getElem?, ha, hm]
      · refine ⟨qs, ?_, hm⟩
        rw [Std.HashMap.getElem?_insert, if_neg (fun hb => hk (eq_of_beq hb))]
        exact ha

/-! ## Notices -/

theorem staleOne_entries (l : Live) (q0 q : Q) {e : Entry} (he : (l.staleOne q0).entries[q]? = some e)
    (hs : e.stale = false) : l.entries[q]? = some e ∧ q ≠ q0 := by
  unfold Live.staleOne at he
  split at he
  · next e0 h0 =>
    simp only [Std.HashMap.getElem?_insert, beq_iff_eq] at he
    by_cases hq : q0 = q
    · subst hq; rw [if_pos (beq_self_eq_true q0), Option.some.injEq] at he; subst he; simp at hs
    · rw [if_neg (fun hb => hq (eq_of_beq hb))] at he; exact ⟨he, Ne.symm hq⟩
  · next h0 =>
    refine ⟨he, ?_⟩
    rintro rfl; rw [h0] at he; cases he

theorem staleAll_entries (qs : List Q) : ∀ (l : Live) {q : Q} {e : Entry},
    (qs.foldl Live.staleOne l).entries[q]? = some e → e.stale = false →
      l.entries[q]? = some e ∧ q ∉ qs ∧ (qs.foldl Live.staleOne l).armed = l.armed := by
  induction qs with
  | nil => intro l q e he _; exact ⟨he, by simp, rfl⟩
  | cons q0 t ih =>
    intro l q e he hs
    obtain ⟨h1, hn, ha⟩ := ih (l.staleOne q0) he hs
    obtain ⟨h2, hne⟩ := staleOne_entries l q0 q h1 hs
    refine ⟨h2, by simp [hne, hn], ?_⟩
    rw [List.foldl_cons, ha]
    unfold Live.staleOne; split <;> rfl

/-- A notice of key k: what stays unstaled was so before, and is not
watched on k; the other watches are as they were. -/
theorem notice1_fresh {l : Live} {ans : Q → Ans} (h : Agrees l ans) (k : ByteArray) {q : Q} {e : Entry}
    (he : (l.notice1 k).entries[q]? = some e) (hs : e.stale = false) :
    l.entries[q]? = some e ∧ q.watch ≠ k ∧ (l.notice1 k).armed[q.watch]? = l.armed[q.watch]? := by
  unfold Live.notice1 at he ⊢
  split at he
  · next hk =>
    refine ⟨he, ?_, rfl⟩
    intro hw
    obtain ⟨_, qs, ha, _⟩ := h q e he hs
    rw [hw, hk] at ha; cases ha
  · next qs hk =>
    rw [← Array.foldl_toList] at he ⊢
    obtain ⟨h1, hn, ha⟩ := staleAll_entries qs.toList _ he hs
    have hw : q.watch ≠ k := by
      intro hw
      obtain ⟨_, qs', ha', hm⟩ := h q e h1 hs
      rw [hw, hk] at ha'
      simp only [Option.some.injEq] at ha'
      subst ha'
      exact hn (by simpa using hm)
    refine ⟨h1, hw, ?_⟩
    rw [ha]
    simp [Std.HashMap.getElem?_erase, Ne.symm hw]

theorem agrees_notice1 {l : Live} {ans : Q → Ans} (h : Agrees l ans) (k : ByteArray) :
    Agrees (l.notice1 k) ans := by
  intro q e he hs
  obtain ⟨h1, -, ha⟩ := notice1_fresh h k he hs
  rw [ha]; exact h q e h1 hs

theorem notice_fresh (keys : List ByteArray) : ∀ {l : Live} {ans : Q → Ans}, Agrees l ans →
    Agrees (keys.foldl Live.notice1 l) ans ∧
      ∀ (q : Q) (e : Entry), (keys.foldl Live.notice1 l).entries[q]? = some e → e.stale = false → q.watch ∉ keys := by
  induction keys with
  | nil => intro l ans h; exact ⟨h, by simp⟩
  | cons k t ih =>
    intro l ans h
    have h1 := agrees_notice1 h k
    obtain ⟨h2, hn⟩ := ih h1
    refine ⟨h2, fun q e he hs => ?_⟩
    have hnt := hn q e he hs
    -- what is unstaled after the rest was unstaled after k's notice
    have : ∀ (ks : List ByteArray) (l' : Live) {ans' : Q → Ans}, Agrees l' ans' →
        (ks.foldl Live.notice1 l').entries[q]? = some e → l'.entries[q]? = some e := by
      intro ks
      induction ks with
      | nil => intro l' _ _ h; exact h
      | cons k' t' ih' =>
        intro l' ans' hl' h
        exact (notice1_fresh hl' k' (ih' _ (agrees_notice1 hl' k') h) hs).1
    have hk := (notice1_fresh h k (this t _ h1 he) hs).2.1
    simp [hk, hnt]

/-- **A notice of the journal's keys moves the cache to the next
moment.** If the keys name every watch whose answer changed from `ans`
to `ans'` (journal), the cache after the notice agrees with `ans'`. -/
theorem agrees_notice {l : Live} {ans ans' : Q → Ans} (h : Agrees l ans) (keys : Array ByteArray)
    (hj : ∀ q, q.watch ∉ keys → ans' q = ans q) : Agrees (l.notice keys) ans' := by
  unfold Live.notice
  rw [← Array.foldl_toList]
  obtain ⟨h1, hn⟩ := notice_fresh keys.toList h
  intro q e he hs
  obtain ⟨hans, rest⟩ := h1 q e he hs
  exact ⟨hans.trans (hj q (by simpa using hn q e he hs)).symm, rest⟩

/-- **Forgetting instances keeps the rest in agreement.** -/
theorem agrees_keep {l : Live} {ans : Q → Ans} (h : Agrees l ans) (want : Q → Bool) :
    Agrees (l.keep want) ans := by
  intro q e he hs
  simp only [Live.keep] at he ⊢
  simp only [Std.HashMap.getElem?_filter, Std.HashMap.getElem?_filterMap, Std.HashMap.getKey_eq] at he ⊢
  simp only [Option.pfilter_eq_some_iff] at he
  obtain ⟨he1, hw⟩ := he
  obtain ⟨hans, qs, ha, hm⟩ := h q e he1 hs
  have hf : q ∈ qs.filter want := Array.mem_filter.2 ⟨hm, hw⟩
  refine ⟨hans, qs.filter want, ?_, hf⟩
  simp [ha]
  exact ⟨q, hm, hw⟩

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
