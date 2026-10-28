/-
Two nodes and the socket between them. The socket holds the messages in
flight, as a bag: any one may be delivered next (reordering), and a
re-sent message is a second copy (duplication). On a socket with
failure any message may also be dropped. Nodes act on ticks; the
approver's user approves when it chooses.

Runs are infinite. A run is fair when both nodes tick forever, the
approver keeps acting (approving whatever is pending; doing nothing
otherwise), and the socket is fair-lossy: a message sent at infinitely
many steps is delivered at infinitely many steps. A sent message may be
lost any finite number of times; resending is what overcomes it.
-/
import Net.Node

namespace Net
open Engine Community

structure Sys where
  a : Node
  b : Node
  net : List Msg

inductive Act where
  | tickA
  | tickB
  | approve
  | deliver (m : Msg)
  | drop (m : Msg)
  deriving DecidableEq

section
variable (C : Crypto) (approval : Node → Node)

/-- One step: the next state, and the messages sent by it. A message is
read by the node it is addressed to. -/
noncomputable def stepOut (s : Sys) : Act → Sys × List Msg
  | .tickA => let t := tick C s.a; ({ s with a := t.1, net := s.net ++ t.2 }, t.2)
  | .tickB => let t := tick C s.b; ({ s with b := t.1, net := s.net ++ t.2 }, t.2)
  | .approve => ({ s with a := approval s.a }, [])
  | .deliver m =>
    if m.dst = s.a.me then
      let t := recv C s.a m; ({ s with a := t.1, net := s.net.erase m ++ t.2 }, t.2)
    else if m.dst = s.b.me then
      let t := recv C s.b m; ({ s with b := t.1, net := s.net.erase m ++ t.2 }, t.2)
    else ({ s with net := s.net.erase m }, [])
  | .drop m => ({ s with net := s.net.erase m }, [])

noncomputable def step (s : Sys) (act : Act) : Sys := (stepOut C approval s act).1
noncomputable def sent (s : Sys) (act : Act) : List Msg := (stepOut C approval s act).2

/-- Delivering or dropping needs the message in flight. -/
def Enabled (s : Sys) : Act → Prop
  | .deliver m => m ∈ s.net
  | .drop m => m ∈ s.net
  | _ => True

/-- The states reachable from init, over a socket with failure. -/
inductive Reachable (init : Sys) : Sys → Prop
  | init : Reachable init init
  | step {s : Sys} (act : Act) : Reachable init s → Enabled s act →
      Reachable init (step C approval s act)

/-- These actions, taken in order from s, each enabled when taken, end
in t. -/
inductive Path : Sys → List Act → Sys → Prop
  | nil (s : Sys) : Path s [] s
  | cons {s t : Sys} {act : Act} {acts : List Act} : Enabled s act →
      Path (step C approval s act) acts t → Path s (act :: acts) t

/-- An infinite run from init. -/
structure Run (init : Sys) where
  st : Nat → Sys
  act : Nat → Act
  zero : st 0 = init
  next : ∀ i, Enabled (st i) (act i) ∧ st (i + 1) = step C approval (st i) (act i)

def Run.Fair {init : Sys} (r : Run C approval init) : Prop :=
  (∀ N, ∃ i ≥ N, r.act i = .tickA) ∧
  (∀ N, ∃ i ≥ N, r.act i = .tickB) ∧
  (∀ N, ∃ i ≥ N, r.act i = .approve) ∧
  ∀ m, (∀ N, ∃ i ≥ N, m ∈ sent C approval (r.st i) (r.act i)) →
    ∀ N, ∃ i ≥ N, r.act i = .deliver m

/-- The socket never fails. -/
def Run.Ideal {init : Sys} (r : Run C approval init) : Prop := ∀ i m, r.act i ≠ .drop m

end

end Net
