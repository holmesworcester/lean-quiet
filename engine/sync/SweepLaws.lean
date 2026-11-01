import engine.sync.Sweep

namespace Engine.Sync.Sweep

theorem offer_sent {s : Sweep} {input : Option Op} {shows : Op → Bool} {room : Nat} {o : Op}
    (h : (s.offer input shows room).2 = some o) :
    input = some o ∧ shows o = true ∧ cost o ≤ maxFrame ∧ cost o ≤ room := by
  cases input with
  | none => cases h
  | some p =>
    simp only [offer] at h
    split at h
    · cases h
    · rename_i hv
      split at h
      · have he : p = o := Option.some.inj h
        subst p
        simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, not_or] at hv
        exact ⟨rfl, by cases hs : shows o <;> simp_all, by omega, by assumption⟩
      · cases h

theorem next_sent {s : Sweep} {input : Option Op} {shows : Op → Bool} {room : Nat} {o : Op}
    (h : (s.next input shows room).2 = some o) :
    input = some o ∧ shows o = true ∧ cost o ≤ maxFrame ∧ cost o ≤ room := by
  unfold next at h
  split at h
  · cases h
  · exact offer_sent h

/-- Countdown to a target position, including finishing a current sweep
which has already passed it. A captured ceiling is never reread mid-sweep. -/
def rank (target : Nat) (s : Sweep) : Nat :=
  if !s.active then target + 1
  else if s.after < target ∧ target ≤ s.high then target - s.after
  else s.high - s.after + target + 2

private theorem advance_rank (j : Nat) (s : Sweep) (ha : s.active = true)
    (hn : s.after < s.high) (hj : s.after + 1 ≠ j) :
    rank j s.advance < rank j s := by
  simp only [rank, advance, ha, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  split <;> split <;> omega

private theorem begin_rank {j ceiling : Nat} {s : Sweep} (hj : 0 < j) (hc : s.active = false → j ≤ ceiling) :
    rank j (s.begin ceiling) ≤ rank j s := by
  unfold begin
  split
  · exact Nat.le_refl _
  · rename_i ha
    have hf : s.active = false := by cases hs : s.active <;> simp_all
    simp [rank, hf, hj, hc hf]

/-- One reserved service opportunity either emits the fixed retained op or
strictly reduces the executable cursor's finite countdown. No bound on later
catalog growth appears in the theorem. -/
theorem step_progress {j ceiling room : Nat} {s : Sweep} {input : Option Op}
    {shows : Op → Bool} {o : Op} (hj : 0 < j) (hc : s.active = false → j ≤ ceiling)
    (row : (s.begin ceiling).after < (s.begin ceiling).high →
      (s.begin ceiling).after + 1 = j → input = some o)
    (shown : shows o = true) (fits : cost o ≤ maxFrame) (budget : maxFrame ≤ room) :
    (step s ceiling input shows room).2 = some o ∨
      rank j (step s ceiling input shows room).1 < rank j s := by
  have hb := begin_rank (s := s) hj hc
  have active : (s.begin ceiling).active = true := by
    unfold begin; split <;> simp_all
  unfold step next
  split
  · right
    rename_i done
    have : rank j (s.begin ceiling).finish < rank j (s.begin ceiling) := by
      simp only [rank, finish]
      simp only [active, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      split <;> omega
    exact Nat.lt_of_lt_of_le this hb
  · rename_i hn
    by_cases hit : (s.begin ceiling).after + 1 = j
    · left
      rw [row (by omega) hit]
      simp [offer, shown, Nat.not_lt.mpr fits, Nat.le_trans fits budget]
    · right
      have dec := advance_rank j (s.begin ceiling) active (by omega) hit
      cases input with
      | none => exact Nat.lt_of_lt_of_le dec hb
      | some p =>
        simp only [offer]
        split
        · exact Nat.lt_of_lt_of_le dec hb
        · rename_i allowed
          have fitp : cost p ≤ maxFrame := by
            simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, not_or] at allowed
            omega
          simp only [Nat.le_trans fitp budget, ↓reduceIte]
          exact Nat.lt_of_lt_of_le dec hb

/-- Every execution of the cursor with repeated reserved service visits any
fixed retained position after every starting time. Each step may observe a
larger catalog and a different unrelated op; there is no quiescence premise.
The source-row and room premises are storage/transport interfaces, not an
assumption that a request is admitted or that the wanted op is emitted. -/
theorem retried (states : Nat → Sweep) (ceilings rooms : Nat → Nat)
    (inputs : Nat → Option Op) (shows : Nat → Op → Bool) (o : Op) (j : Nat)
    (hj : 0 < j) (fits : cost o ≤ maxFrame)
    (transition : ∀ n, states (n + 1) = (step (states n) (ceilings n) (inputs n) (shows n) (rooms n)).1)
    (ceiling : ∀ n, (states n).active = false → j ≤ ceilings n)
    (row : ∀ n, ((states n).begin (ceilings n)).after < ((states n).begin (ceilings n)).high →
      ((states n).begin (ceilings n)).after + 1 = j → inputs n = some o)
    (shown : ∀ n, shows n o = true)
    (budget : ∀ n, maxFrame ≤ rooms n) :
    ∀ start, ∃ n, start ≤ n ∧
      (step (states n) (ceilings n) (inputs n) (shows n) (rooms n)).2 = some o := by
  intro start
  suffices ∀ k n, rank j (states n) = k → ∃ t, n ≤ t ∧
      (step (states t) (ceilings t) (inputs t) (shows t) (rooms t)).2 = some o by
    exact this _ start rfl
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro n hk
    rcases step_progress hj (ceiling n) (row n) (shown n) fits (budget n) with sent | lower
    · exact ⟨n, Nat.le_refl _, sent⟩
    · rw [← transition n, hk] at lower
      obtain ⟨t, ht, hs⟩ := ih _ lower (n + 1) rfl
      exact ⟨t, by omega, hs⟩

/-- A tick with no output room cannot erase the target's place in the sweep. -/
theorem step_nonincrease {j ceiling room : Nat} {s : Sweep} {input : Option Op}
    {shows : Op → Bool} {o : Op} (hj : 0 < j) (hc : s.active = false → j ≤ ceiling)
    (row : (s.begin ceiling).after < (s.begin ceiling).high →
      (s.begin ceiling).after + 1 = j → input = some o)
    (shown : shows o = true) (fits : cost o ≤ maxFrame)
    (unsent : (step s ceiling input shows room).2 ≠ some o) :
    rank j (step s ceiling input shows room).1 ≤ rank j s := by
  have hb := begin_rank (s := s) hj hc
  have active : (s.begin ceiling).active = true := by
    unfold begin; split <;> simp_all
  unfold step next at unsent ⊢
  by_cases done : (s.begin ceiling).high ≤ (s.begin ceiling).after
  · simp only [done, ↓reduceIte] at unsent ⊢
    have lower : rank j (s.begin ceiling).finish < rank j (s.begin ceiling) := by
      simp only [rank, finish]
      simp only [active, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      split <;> omega
    exact Nat.le_trans (Nat.le_of_lt lower) hb
  · simp only [done, ↓reduceIte] at unsent ⊢
    have hn := done
    by_cases hit : (s.begin ceiling).after + 1 = j
    · rw [row (by omega) hit] at unsent ⊢
      simp only [offer, shown, Bool.not_true, Bool.false_or, decide_eq_true_eq,
        Nat.not_lt.mpr fits, ↓reduceIte] at unsent ⊢
      by_cases roomok : cost o ≤ room
      · simp only [roomok, ↓reduceIte] at unsent
        exact False.elim (unsent rfl)
      · simpa only [roomok, ↓reduceIte] using hb
    · have dec := advance_rank j (s.begin ceiling) active (by omega) hit
      cases input with
      | none => exact Nat.le_trans (Nat.le_of_lt dec) hb
      | some p =>
        simp only [offer]
        split
        · exact Nat.le_trans (Nat.le_of_lt dec) hb
        · split
          · exact Nat.le_trans (Nat.le_of_lt dec) hb
          · exact hb

/-- Full reserved room need only recur, not be available at every tick. This
separates internal writer/queue service from fair-loss transport: infinitely
many emissions are proved before asking the link to deliver a retry. -/
theorem retried_fair (states : Nat → Sweep) (ceilings rooms : Nat → Nat)
    (inputs : Nat → Option Op) (shows : Nat → Op → Bool) (o : Op) (j : Nat)
    (hj : 0 < j) (fits : cost o ≤ maxFrame)
    (transition : ∀ n, states (n + 1) = (step (states n) (ceilings n) (inputs n) (shows n) (rooms n)).1)
    (ceiling : ∀ n, (states n).active = false → j ≤ ceilings n)
    (row : ∀ n, ((states n).begin (ceilings n)).after < ((states n).begin (ceilings n)).high →
      ((states n).begin (ceilings n)).after + 1 = j → inputs n = some o)
    (shown : ∀ n, shows n o = true)
    (budget : ∀ start, ∃ n, start ≤ n ∧ maxFrame ≤ rooms n) :
    ∀ start, ∃ n, start ≤ n ∧
      (step (states n) (ceilings n) (inputs n) (shows n) (rooms n)).2 = some o := by
  intro start
  classical
  apply Classical.byContradiction
  intro absent
  have unsent : ∀ n, start ≤ n →
      (step (states n) (ceilings n) (inputs n) (shows n) (rooms n)).2 ≠ some o := by
    intro n hn hs; exact absent ⟨n, hn, hs⟩
  have mono : ∀ n t, start ≤ n → n ≤ t → rank j (states t) ≤ rank j (states n) := by
    intro n t hn ht
    induction ht with
    | refl => exact Nat.le_refl _
    | @step t ht ih =>
      rw [transition t]
      exact Nat.le_trans (step_nonincrease hj (ceiling t) (row t) (shown t) fits
        (unsent t (Nat.le_trans hn ht))) ih
  suffices ∀ k n, start ≤ n → rank j (states n) = k → False by
    exact this _ start (Nat.le_refl _) rfl
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro n hn hk
    obtain ⟨t, ht, hb⟩ := budget n
    rcases step_progress hj (ceiling t) (row t) (shown t) fits hb with sent | lower
    · exact unsent t (Nat.le_trans hn ht) sent
    · rw [← transition t] at lower
      have dec : rank j (states (t + 1)) < k := by
        have hm := mono n t hn ht
        omega
      exact ih _ dec (t + 1) (by omega) rfl

/-- Semantic fair-loss for operation bytes, not ciphertext equality: fresh
nonces may change every retry's frame. The link is permitted to lose any
finite number of attempts. Scheduling and internal admission are separate. -/
def FairLoss (emitted delivered : Nat → Op → Prop) : Prop :=
  ∀ o, (∀ start, ∃ n, start ≤ n ∧ emitted n o) → ∃ n, delivered n o

/-- A fair-loss link consumes the infinitely repeated output proved above;
no premise requires delivery of each emission, a have, or a want. -/
theorem fair_loss_delivered {emitted delivered : Nat → Op → Prop} {o : Op}
    (retry : ∀ start, ∃ n, start ≤ n ∧ emitted n o) (fairLoss : FairLoss emitted delivered) :
    ∃ n, delivered n o := fairLoss o retry

end Engine.Sync.Sweep
