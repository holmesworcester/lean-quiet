import ops.connection.Family

/-!
`connection.established`'s laws.
-/

namespace Connection
open Engine

/-- The family's validator judges an established by its op type's: the facts it
cites are these, typed. -/
theorem check_established {K : Keys} {o : Op} {fs : List F} {f : Fact} (h : check K o .established fs = some f) :
    ∃ cn rq ep en a, fs = [.inr (.ofConnection cn), .inr (.ofRequest rq), .inr (.ofEph ep), .inl (.ofEndpoint en)] ∧
      Established.check K o {} cn rq ep en = some a ∧ f = .ofEstablished a := by
  unfold check at h
  split at h <;> (try (simp_all; done))
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨_, _, _, _, a, rfl, ha, rfl⟩

end Connection
