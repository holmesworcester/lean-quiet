import ops.connection.Family
import ops.connection.opened.Commands
import ops.sync.NoticeLaws

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

namespace Connection
open Engine Engine.Sync Codec
section
variable [fr : Fresh (Model F)]

theorem openEach_body (epOp : Id) : ∀ (rs : List (Id × Fact)) (s : DB F),
    ∀ o ∈ ((openEach epOp rs : Model F (List Op)).run s).1, (decode o.body : Option Body) = some .opened
  | [], _, _, h => by cases h
  | (r, _) :: t, s, o, h => by
    simp only [openEach, Model.run_bind, Model.run_pure] at h
    by_cases hz : ((count opened.byRequest [r] : Model F Nat).run s).1 = 0
    · rw [if_pos hz] at h
      rcases List.mem_cons.1 h with rfl | h
      · exact body_conn _ _
      · exact openEach_body epOp t s o h
    · rw [if_neg hz] at h
      exact openEach_body epOp t s o h

end
end Connection
