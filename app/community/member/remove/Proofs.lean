import app.community.Family

namespace Community
open Engine Codec
section
variable (C : Crypto) (ops : Id → Option Op)

/-- User u of community c has been removed (by anyone allowed to). -/
def Removed (c u : Id) : Prop := ∃ x r, V C ops x (.removal c u r)

/-- A member: an admitted user not removed. -/
def Member (c u : Id) : Prop := (∃ d e, Admitted C ops c u d e) ∧ ¬ Removed C ops c u

/-- Device d is live in c: admitted, and none of the users it is
admitted into (under any key) removed. A device may be admitted into
several users; removing any of them cuts it (docs/REMOVAL.md). -/
def Live (c : Id) (d : Key) : Prop :=
  (∃ u e, Admitted C ops c u d e) ∧ ∀ u e, Admitted C ops c u d e → ¬ Removed C ops c u

/-- Device d is cut in c: admitted into a user that is removed. -/
def Cut (c : Id) (d : Key) : Prop := ∃ u e, Admitted C ops c u d e ∧ Removed C ops c u
end
open Engine Codec
variable {C : Crypto} {ops : Id → Option Op}

/-- **Removal is permanent.** More ops never restore a removed user:
redelivery, delay and reordering cannot undo a removal. -/
theorem removed_stays {ops' : Id → Option Op} (he : Extends ops ops') {c u : Id}
    (h : Removed C ops c u) : Removed C ops' c u := by
  obtain ⟨x, r, hx⟩ := h
  exact ⟨x, r, spec_extends he hx⟩
open Engine
variable {s : DB Fact} {C : Crypto}

theorem byUser_args {c u : Id} {f : Fact} :
    removal.byUser.args f = some [c, u] ↔ ∃ r, f = .removal c u r := by
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
  obtain ⟨u, e, ⟨y, k, hy⟩, hr⟩ := h
  have hc : Cut C ops' c d := ⟨u, e, ⟨y, k, valid_stays he hy⟩, removed_stays he hr⟩
  exact ⟨hc, cut_not_live hc⟩

end Community
