/-
A FIFO queue makes progress even when every step appends more messages.
This lemma is independent of the bootstrap model and its goal: a step
appends messages, or removes the head and appends messages; recurring
service therefore eventually removes every message already queued.
-/
import Std

namespace Net.FIFO

variable {M : Type} [DecidableEq M]

/-- A step may append new arrivals, and may deliver only the oldest message. -/
inductive Advance : List M → List M → Option M → Prop
  | append (queue added : List M) : Advance queue (queue ++ added) none
  | pop (head : M) (tail added : List M) : Advance (head :: tail) (tail ++ added) (some head)

/-- Until a particular message is delivered, it stays queued and its first
position never increases. Any delivery moves it strictly toward the head. -/
theorem pending {q q' : List M} {delivered : Option M} {m : M}
    (h : Advance q q' delivered) (hm : m ∈ q) (hne : delivered ≠ some m) :
    m ∈ q' ∧ q'.idxOf m ≤ q.idxOf m ∧ (delivered.isSome = true → q'.idxOf m < q.idxOf m) := by
  cases h with
  | append queue added =>
    exact ⟨List.mem_append_left _ hm, by simp [List.idxOf_append, hm], by simp⟩
  | pop head tail added =>
    have hne' : head ≠ m := fun he => hne (congrArg some he)
    have ht : m ∈ tail := (List.mem_cons.1 hm).resolve_left (Ne.symm hne')
    refine ⟨List.mem_append_left _ ht, ?_, ?_⟩
    · simp [List.idxOf_append, ht, List.idxOf_cons, hne']
    · simp [List.idxOf_append, ht, List.idxOf_cons, hne']

section
variable (queue : Nat → List M) (delivery : Nat → Option M)
variable (advance : ∀ i, Advance (queue i) (queue (i + 1)) (delivery i))
include advance

/-- Queue position is monotone over an arbitrary finite interval with no
matching delivery. New arrivals and duplicate messages cannot jump ahead. -/
theorem pending_until {m : M} {n k : Nat} (hnk : n ≤ k) (hm : m ∈ queue n)
    (hno : ∀ i, n ≤ i → i < k → delivery i ≠ some m) :
    m ∈ queue k ∧ (queue k).idxOf m ≤ (queue n).idxOf m := by
  induction hnk with
  | refl => exact ⟨hm, Nat.le_refl _⟩
  | @step k hnk ih =>
    have hp := ih (fun i hi hik => hno i hi (by omega))
    have hs := pending (advance k) hp.1 (hno k hnk (by omega))
    exact ⟨hs.1, Nat.le_trans hs.2.1 hp.2⟩

/-- Recurring service suffices to deliver every queued message. The queue
need never become empty and no bound on the rate of new arrivals is assumed. -/
theorem eventually_delivered
    (service : ∀ N, ∃ i ≥ N, queue i ≠ [] → (delivery i).isSome = true)
    {m : M} {n : Nat} (hm : m ∈ queue n) :
    ∃ i ≥ n, delivery i = some m := by
  have progress : ∀ rank n, (queue n).idxOf m = rank → m ∈ queue n →
      ∃ i ≥ n, delivery i = some m := by
    intro rank
    induction rank using Nat.strongRecOn with
    | ind rank ih =>
      intro n hr hm
      obtain ⟨k,hnk,hserve⟩ := service n
      classical
      by_cases he : ∃ i, n ≤ i ∧ i < k ∧ delivery i = some m
      · obtain ⟨i,hni,_,hi⟩ := he
        exact ⟨i,hni,hi⟩
      · have hno : ∀ i, n ≤ i → i < k → delivery i ≠ some m := by
          intro i hni hik hi
          exact he ⟨i,hni,hik,hi⟩
        have hp := pending_until queue delivery advance hnk hm hno
        by_cases hd : delivery k = some m
        · exact ⟨k,hnk,hd⟩
        · have hs := pending (advance k) hp.1 hd
          have hnonempty : queue k ≠ [] := by intro he; rw [he] at hp; cases hp.1
          have hlt := hs.2.2 (hserve hnonempty)
          have hrank : (queue (k + 1)).idxOf m < rank := by omega
          obtain ⟨i,hki,hi⟩ := ih _ hrank (k + 1) rfl hs.1
          exact ⟨i,by omega,hi⟩
  exact progress _ n rfl hm

/-- Infinitely often enqueued messages are delivered infinitely often. -/
theorem fair_loss (sent : Nat → List M)
    (sent_queued : ∀ i m, m ∈ sent i → m ∈ queue (i + 1))
    (service : ∀ N, ∃ i ≥ N, queue i ≠ [] → (delivery i).isSome = true)
    (m : M) (hs : ∀ N, ∃ i ≥ N, m ∈ sent i) :
    ∀ N, ∃ i ≥ N, delivery i = some m := by
  intro N
  obtain ⟨i,hNi,hm⟩ := hs N
  obtain ⟨j,hij,hj⟩ := eventually_delivered queue delivery advance service (sent_queued i m hm)
  exact ⟨j,by omega,hj⟩

end
end Net.FIFO
