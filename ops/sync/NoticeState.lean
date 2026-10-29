/-
Notice delivery preserves the session phase and silence clock, and never
ends a session. The wrappers keep the filed/tick transition laws intact.
-/
import ops.sync.Notice
import engine.wire.WorldLaws

namespace Engine.Sync
variable {F : Type} (fam : Family F) (cfg : Config)

theorem give_shape (h : Held F) : ∀ ns (c : Conn),
    let s := ((c.give fam cfg ns : HeldM F Step) h).1
    s.conn.session = c.session ∧ s.conn.heard = c.heard ∧ s.drop = false
  | [], _ => ⟨rfl, rfl, rfl⟩
  | (r, x) :: rest, c => by
    unfold Conn.give
    split
    · exact give_shape h rest c
    · simp only [HeldM.bind_apply, HeldM.pure_apply]
      exact give_shape _ rest _

end Engine.Sync
