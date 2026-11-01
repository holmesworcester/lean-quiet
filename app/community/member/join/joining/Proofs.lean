import app.community.Family
import app.community.member.join.joining.Commands

namespace Community
open Engine
variable {C : Crypto}
section
variable {s : DB Fact}

theorem dormant_none {c : Id} :
    ∀ {rows : List (Pos × Fact)},
      (∀ p k hs r nm d n, (p, Fact.joining c k hs r nm d n) ∈ rows →
        (Engine.eval s (admission.byDevice.query [c, d] (limit := some 0))).total ≠ 0) →
      (dormant c rows).eval s = none
  | [], _ => rfl
  | (p, f) :: t, hall => by
    have ht := dormant_none (rows := t) fun p k hs r nm d n hm =>
      hall p k hs r nm d n (List.mem_cons_of_mem _ hm)
    cases f with
    | ofJoining x =>
      obtain ⟨c', k, hs, r, nm, d, n⟩ := x
      by_cases hc : c' = c
      · subst hc
        show View.eval s (if c' = c' then _ else _) = none
        rw [if_pos rfl]
        show View.eval s ((dormant c' t).bind _) = none
        rw [View.eval_bind', ht]
        show (if _ ≠ 0 then none else _) = none
        rw [if_pos (hall p k hs r nm d n (List.mem_cons_self ..))]
      · show View.eval s (if c' = c then _ else _) = none
        rw [if_neg hc]; exact ht
    | _ => exact ht

end
end Community
