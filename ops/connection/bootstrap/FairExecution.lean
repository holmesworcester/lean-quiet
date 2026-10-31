/-
An explicit infinite, ideal and fair execution of the bootstrap model.
Every four steps tick A, tick B, run approval, and deliver the FIFO head
(or tick A if the queue is empty). Fairness follows from queue progress,
without assuming that either node has bootstrapped or that traffic stops.
-/
import ops.connection.bootstrap.FIFO
import ops.connection.bootstrap.Laws

namespace Net.FairExecution
open Engine Community

/-- The four recurring phases. Empty delivery slots are harmless A ticks. -/
def choose (i : Nat) (s : Sys) : Act :=
  if i % 4 = 0 then .tickA else
  if i % 4 = 1 then .tickB else
  if i % 4 = 2 then .approve else
  match s.net with
  | [] => .tickA
  | m :: _ => .deliver m

def delivered : Act → Option Msg
  | .deliver m => some m
  | _ => none

theorem choose_enabled (i : Nat) (s : Sys) : Enabled s (choose i s) := by
  unfold choose
  split <;> try trivial
  split <;> try trivial
  split <;> try trivial
  cases h : s.net with
  | nil => trivial
  | cons m rest => exact (show m ∈ s.net by rw [h]; exact List.mem_cons_self ..)

theorem choose_ideal (i : Nat) (s : Sys) (m : Msg) : choose i s ≠ .drop m := by
  unfold choose
  split <;> try simp
  split <;> try simp
  split <;> try simp
  cases s.net <;> simp

section
variable (C : Crypto) (approval : Node → Node)

/-- Every handler appends its output after the queue entries it retains. -/
theorem net_after (s : Sys) (act : Act) :
    (step C approval s act).net =
      (match act with | .deliver m | .drop m => s.net.erase m | _ => s.net) ++ sent C approval s act := by
  cases act with
  | tickA | tickB => rfl
  | approve | drop => simp [step, sent, stepOut]
  | deliver m =>
    simp only [step, sent, stepOut]
    split
    · rfl
    · split
      · rfl
      · simp

theorem sent_queued (s : Sys) (act : Act) (m : Msg) (h : m ∈ sent C approval s act) :
    m ∈ (step C approval s act).net := by
  rw [net_after]
  exact List.mem_append_right _ h

theorem choose_advance (i : Nat) (s : Sys) :
    FIFO.Advance s.net (step C approval s (choose i s)).net (delivered (choose i s)) := by
  unfold choose
  split
  · exact .append _ _
  split
  · exact .append _ _
  split
  · simpa [step, stepOut, delivered] using (FIFO.Advance.append s.net [])
  cases h : s.net with
  | nil =>
    simpa only [step, stepOut, delivered, h] using
      (FIFO.Advance.append s.net (tick C s.a).2)
  | cons m rest =>
    rw [net_after, h]
    simpa [delivered] using (FIFO.Advance.pop m rest (sent C approval s (.deliver m)))

noncomputable def state (init : Sys) : Nat → Sys
  | 0 => init
  | i + 1 => step C approval (state init i) (choose i (state init i))

/-- This is a constructed run, from the supplied initial state. -/
noncomputable def run (init : Sys) : Run C approval init where
  st := state C approval init
  act i := choose i (state C approval init i)
  zero := rfl
  next i := ⟨choose_enabled i _,rfl⟩

variable (init : Sys)

theorem advance (i : Nat) :
    FIFO.Advance ((run C approval init).st i).net ((run C approval init).st (i + 1)).net
      (delivered ((run C approval init).act i)) := choose_advance C approval i _

theorem service : ∀ N, ∃ i ≥ N, ((run C approval init).st i).net ≠ [] →
    (delivered ((run C approval init).act i)).isSome = true := by
  intro N
  refine ⟨4*N+3,by omega,?_⟩
  intro hn
  change (delivered (choose (4*N+3) _)).isSome = true
  simp only [choose, show (4*N+3)%4 = 3 by omega, Nat.reduceEqDiff, ite_false]
  cases h : (state C approval init (4*N+3)).net with
  | nil => exact False.elim (hn h)
  | cons m rest => rfl

/-- Every particular queued message is eventually delivered, even if an
unbounded stream of other messages is appended behind it. -/
theorem queued_delivered {n : Nat} {m : Msg} (hm : m ∈ ((run C approval init).st n).net) :
    ∃ i ≥ n, (run C approval init).act i = .deliver m := by
  obtain ⟨i,hi,hd⟩ := FIFO.eventually_delivered
    (fun i => ((run C approval init).st i).net) (fun i => delivered ((run C approval init).act i))
    (advance C approval init) (service C approval init) hm
  refine ⟨i,hi,?_⟩
  cases ha : (run C approval init).act i <;> simp [delivered,ha] at hd ⊢
  exact hd

/-- Fairness is proved from periodic scheduling and FIFO progress, independently
of the scene's cryptography, admission, or eventual bootstrap conclusion. -/
theorem fair : (run C approval init).Fair := by
  refine ⟨?_,?_,?_,?_⟩
  · intro N
    exact ⟨4*N,by omega,by simp [run,choose,show (4*N)%4 = 0 by omega]⟩
  · intro N
    exact ⟨4*N+1,by omega,by simp [run,choose,show (4*N+1)%4 = 1 by omega]⟩
  · intro N
    exact ⟨4*N+2,by omega,by simp [run,choose,show (4*N+2)%4 = 2 by omega]⟩
  · intro m hs N
    obtain ⟨i,hNi,hm⟩ := hs N
    have hq := sent_queued C approval ((run C approval init).st i) ((run C approval init).act i) m hm
    have hnext := ((run C approval init).next i).2
    rw [← hnext] at hq
    obtain ⟨j,hij,hj⟩ := queued_delivered C approval init hq
    exact ⟨j,by omega,hj⟩

theorem ideal : (run C approval init).Ideal := fun i m => choose_ideal i _ m

end
end Net.FairExecution

namespace Net.Scene
open Engine Community

/-- A concrete infinite execution from the bootstrap initial state. Its fair
and ideal proofs do not require any assumption about the scene's signatures. -/
noncomputable def fairExecution (x : Scene) (C : Crypto) : Run C x.approval x.init :=
  FairExecution.run C x.approval x.init

theorem fairExecution_fair (x : Scene) (C : Crypto) : (x.fairExecution C).Fair :=
  FairExecution.fair C x.approval x.init

theorem fairExecution_ideal (x : Scene) (C : Crypto) : (x.fairExecution C).Ideal :=
  FairExecution.ideal C x.approval x.init

/-- The bootstrap theorem now has an explicit inhabited fair-run premise.
Only the separate scene validity assumptions remain here. -/
theorem fairExecution_bootstrap {x : Scene} {C : Crypto} (g : x.Good C) :
    ∃ N, ∀ i ≥ N, x.Goal C ((x.fairExecution C).st i) :=
  bootstrap g (fairExecution_fair x C)

theorem fairExecution_bootstrap_ideal {x : Scene} {C : Crypto} (g : x.Good C) :
    ∃ N, ∀ i ≥ N, x.Goal C ((x.fairExecution C).st i) :=
  bootstrap_ideal g (fairExecution_fair x C) (fairExecution_ideal x C)

end Net.Scene
