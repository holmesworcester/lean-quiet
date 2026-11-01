import ops.connection.Family
import ops.connection.connection.Commands
import engine.sync.NoticeLaws

/-!
`connection.connection`: laws about the op types in this folder and below.
-/
namespace Connection
open Engine Engine.Sync Codec
section
variable [fr : Fresh (Model F)]

theorem reply_conn {K : Keys} {r sk frm m1 f : B} {co : Op} (h : Reply.op K r sk frm m1 f = some co) :
    ConnOp co := by
  unfold Reply.op at h
  simp only [Option.bind_eq_bind] at h
  cases h1 : Noise.read1 K.suite prologue sk frm m1 with
  | none => simp [h1] at h
  | some x =>
    obtain ⟨st, re, _⟩ := x
    simp only [h1, Option.bind_some] at h
    cases h2 : Noise.write2 K.suite st f frm re .empty with
    | none => simp [h2] at h
    | some y =>
      simp only [h2, Option.bind_some, Option.some.injEq, pure] at h
      exact ⟨_, _, h.symm⟩

theorem reply_reqs {K : Keys} {r sk frm m1 f : B} {co : Op} (h : Reply.op K r sk frm m1 f = some co) :
    co.reqs = [r] ∧ ∃ m2, co = mkOp [r] (.connection m2) := by
  unfold Reply.op at h
  simp only [Option.bind_eq_bind] at h
  cases h1 : Noise.read1 K.suite prologue sk frm m1 with
  | none => simp [h1] at h
  | some x =>
    obtain ⟨st, re, _⟩ := x
    simp only [h1, Option.bind_some] at h
    cases h2 : Noise.write2 K.suite st f frm re .empty with
    | none => simp [h2] at h
    | some y =>
      simp only [h2, Option.bind_some, Option.some.injEq, pure] at h
      subst h; exact ⟨rfl, _, rfl⟩

end
end Connection
