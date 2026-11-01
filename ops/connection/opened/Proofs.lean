import ops.connection.Family

/-!
`connection.opened`'s laws.
-/

namespace Connection
open Engine

/-- The family's validator judges an opened by its op type's: the facts it
cites are these, typed. -/
theorem check_opened {K : Keys} {o : Op} {fs : List F} {f : Fact} (h : check K o .opened fs = some f) :
    ∃ q e a, fs = [.inr (.ofRequest q), .inl (.ofEndpoint e)] ∧ Opened.check K o {} q e = some a ∧ f = .ofOpened a := by
  unfold check at h
  split at h <;> (try (simp_all; done))
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨_, _, a, rfl, ha, rfl⟩

end Connection
