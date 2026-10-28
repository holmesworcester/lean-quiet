/-
Removing a member, as libquiet's remover flow has it (#1112): asked twice,
nothing written until the second yes, each attempt starting over, one at
a time, a failure kept and retried. The flow is a step function over
taps; the app writes the engine's removal intent exactly when it says.

Laws:
- `writes_only_after_two`: a step writes a removal only on the second
  confirmation (or a retry of a failed one), and only of its target;
- `cancel_writes_nothing`: cancel writes nothing;
- `open_fresh`: opening a target starts at the first confirmation, so a
  yes for one person never carries to another;
- `no_replace`: while one removal is being sent, another cannot replace it;
- `offered_only`: Remove is offered only to an admin, on a present member
  who is not you.
-/
import Engine

namespace Remove
open Engine

/-- Where the flow is. -/
inductive Step where
  | idle
  /-- Asked once: "Remove …?" -/
  | first (u : Id)
  /-- Asked twice: "This can't be undone." -/
  | second (u : Id)
  /-- The removal is written; waiting for it to be decided. -/
  | sending (u : Id)
  /-- It was refused: the reason stays on screen, and it can be retried. -/
  | failed (u : Id) (why : String)
  deriving BEq, Inhabited

inductive Ev where
  | start (u : Id)
  | yes
  | cancel
  | done
  | refused (why : String)

/-- One tap or outcome: the next step, and the user whose removal to
write now, if any. -/
def step : Step → Ev → Step × Option Id
  | .sending u, .start _ => (.sending u, none)
  | _, .start u => (.first u, none)
  | .first u, .yes => (.second u, none)
  | .second u, .yes => (.sending u, some u)
  | .failed u _, .yes => (.sending u, some u)
  | .sending u, .cancel => (.sending u, none)
  | _, .cancel => (.idle, none)
  | .sending _, .done => (.idle, none)
  | .sending u, .refused why => (.failed u why, none)
  | s, _ => (s, none)

/-- **A removal is written only on the second yes** (or a retry after a
refusal, which had both), and only of the target asked about. -/
theorem writes_only_after_two (s : Step) (e : Ev) (u : Id) (h : (step s e).2 = some u) :
    (s = .second u ∨ ∃ why, s = .failed u why) ∧ (match e with | .yes => True | _ => False) := by
  cases s <;> cases e <;> simp [step] at h ⊢ <;> first | (subst h; simp) | exact ⟨_, rfl⟩ | skip
  all_goals (first | (subst h; exact ⟨_, rfl⟩) | trivial)

/-- **Cancel writes nothing.** -/
theorem cancel_writes_nothing (s : Step) : (step s .cancel).2 = none := by
  cases s <;> rfl

/-- **Each attempt starts over:** opening a target starts at the first
confirmation, whatever was confirmed before. -/
theorem open_fresh (s : Step) (u : Id) (h : ∀ v, s ≠ .sending v) : step s (.start u) = (.first u, none) := by
  cases s with
  | sending v => exact absurd rfl (h v)
  | _ => rfl

/-- **One at a time:** while a removal is being sent, opening another
changes nothing. -/
theorem no_replace (u v : Id) : step (.sending u) (.start v) = (.sending u, none) := rfl

/-- Whether Remove is offered: to an admin, on a present member who is
not this user. -/
def offered (admin present : Bool) (me target : Id) : Bool :=
  admin && present && !decide (target = me)

/-- **Remove is offered only to an admin, on a present member, not on
yourself.** -/
theorem offered_only (admin present : Bool) (me target : Id) (h : offered admin present me target = true) :
    admin = true ∧ present = true ∧ target ≠ me := by
  simp [offered] at h; exact ⟨h.1.1, h.1.2, h.2⟩

end Remove
