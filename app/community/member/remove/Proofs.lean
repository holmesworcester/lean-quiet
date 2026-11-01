import app.community.Family

namespace Community
open Engine Codec
section
variable (C : Crypto) (ops : Id → Option Op)

/-- User u of community c has been removed (by anyone allowed to). -/
def Removed (c u : Id) : Prop := ∃ x r k, V C ops x (.removal c u r k)

/-- A member: an admitted user not removed. -/
def Member (c u : Id) : Prop := (∃ d e, Admitted C ops c u d e) ∧ ¬ Removed C ops c u

/-- Device d is live in c: admitted, and none of the users it is
admitted into (under any key) removed. A device may be admitted into
several users; removing any of them cuts it (docs/REMOVAL.md). -/
def Live (c : Id) (d : Key) : Prop :=
  (∃ u e, Admitted C ops c u d e) ∧ ∀ u e, Admitted C ops c u d e → ¬ Removed C ops c u

/-- Device d is cut in c: admitted into a user that is removed. -/
def Cut (c : Id) (d : Key) : Prop := ∃ u e, Admitted C ops c u d e ∧ Removed C ops c u

/-! ## The causal cut: which approvals keep admitting

A removal cites, for each device of the removed user its author holds,
the head of that device's approval chain (`Approve.Fact.prev`). The
approvals at or behind a head it cites are its cut: what its author had
seen. Hashes fix them, so an approval its device signs later, even one
naming an old place in the chain, is behind no head it cites. -/

/-- Approval x is h, or behind h's previous approval: in h's chain, at
or before h. -/
inductive Behind (x : Id) : Id → Prop
  | here : Behind x x
  | back {h : Id} {f : Approve.Fact} : V C ops h (.ofApproval f) → 0 < f.n → Behind x f.prev → Behind x h

/-- Approval x (fact f) is inside cut k: behind a head k names for x's
device. -/
def InCut (x : Id) (f : Approve.Fact) (k : List (Key × Id × Nat)) : Prop :=
  ∃ h m, (f.dev, h, m) ∈ k ∧ Behind C ops x h

/-- Approval x (fact f) is kept: inside the cut of every removal of every
user its device is admitted into. Taking every removal's cut, not any,
makes later removals only narrow it: a removed member cannot widen its
own cut with a removal of its own (docs/REMOVAL.md). -/
def Kept (c x : Id) (f : Approve.Fact) : Prop :=
  ∀ u e z r k, Admitted C ops c u f.dev e → V C ops z (.removal c u r k) → InCut C ops x f k

/-- Approval x counts in c: it is kept, and so is the approval that
admitted its approver (`up`), and so on to the founder's device's. An
approval of a removed member outside a cut counts for nothing, and
neither does any approval above it. -/
inductive Counts (c : Id) : Id → Prop
  | founder {x : Id} {f : Approve.Fact} : V C ops x (.ofApproval f) → f.c = c → f.depth = 0 →
      Kept C ops c x f → Counts c x
  | up {x : Id} {f : Approve.Fact} : V C ops x (.ofApproval f) → f.c = c → 0 < f.depth →
      Counts c f.up → Kept C ops c x f → Counts c x

/-- Approval x is y, or above it: the approval that admitted y's
approver (`up`), and so on toward the founder's device's. -/
inductive Above (x : Id) : Id → Prop
  | here : Above x x
  | up {y : Id} {f : Approve.Fact} : V C ops y (.ofApproval f) → 0 < f.depth → Above x f.up → Above x y

/-- Admission (c, u, d, e) is trusted: it is the root's, or an approval
of a request for it counts. The trust rule lets a node key in only
through a trusted admission of a live device (`connect_iff`). -/
def Trusted (c u : Id) (d e : Key) : Prop :=
  V C ops c (.admission c u d e) ∨
    (Admitted C ops c u d e ∧ ∃ x f, V C ops x (.ofApproval f) ∧ f.c = c ∧ f.ru = u ∧ f.rd = d ∧
      f.re = e ∧ Counts C ops c x)
end
open Engine Codec
variable {C : Crypto} {ops : Id → Option Op}

/-- **Removal is permanent.** More ops never restore a removed user:
redelivery, delay and reordering cannot undo a removal. -/
theorem removed_stays {ops' : Id → Option Op} (he : Extends ops ops') {c u : Id}
    (h : Removed C ops c u) : Removed C ops' c u := by
  obtain ⟨x, r, k, hx⟩ := h
  exact ⟨x, r, k, spec_extends he hx⟩
open Engine
variable {s : DB Fact} {C : Crypto}

theorem byUser_args {c u : Id} {f : Fact} :
    removal.byUser.args f = some [c, u] ↔ ∃ r k, f = .removal c u r k := by
  cases f <;> (try (rename_i x; cases x)) <;> simp [removal.byUser, Remove.byUser, Rel.comap, Fact.removal?, eq_comm]

/-- A cut device is not live. -/
theorem cut_not_live {ops : Id → Option Op} {c : Id} {d : Key} (h : Cut C ops c d) :
    ¬ Live C ops c d := by
  obtain ⟨u, e, ha, hr⟩ := h
  exact fun ⟨_, hall⟩ => hall u e ha hr
open Engine
variable {C : Crypto}

/-- **Cut stays cut (`cut_stays`).** More ops never make a cut device
live again: no later admission, of any id into any user, undoes it. -/
theorem cut_stays {ops ops' : Id → Option Op} {c : Id} {d : Key} (he : Extends ops ops')
    (h : Cut C ops c d) : Cut C ops' c d ∧ ¬ Live C ops' c d := by
  obtain ⟨u, e, ⟨y, hy⟩, hr⟩ := h
  have hc : Cut C ops' c d := ⟨u, e, ⟨y, valid_stays he hy⟩, removed_stays he hr⟩
  exact ⟨hc, cut_not_live hc⟩

end Community
