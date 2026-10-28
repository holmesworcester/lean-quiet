/-
What an approval writes, however large the community (docs/PERF.md: key
wraps per approval).

`View.Always P v`: every answer v can give, whatever its lists answer,
has P; so P holds of what v computes on every store (`always_eval`) and
of every run of it where it runs (`always_run`, a `Sat` the cost laws
can use).

- `approveReq_ops`: an approval writes at most three ops, the approval,
  the admission, and one wrap of the community's key to the new member's
  device: O(1), not O(members).
- The mutant control, `approveWrapAll`, wraps the key to every member
  (`recipients`) as a rotation would: three members make four ops
  (`wrapAll_over`).
-/
import ops.community.Intents

namespace Engine.View
variable {F α β : Type}

/-- Every answer v can give has P, whatever its lists answer. -/
def Always (P : α → Prop) : View F α → Prop
  | .pure a => P a
  | .list _ k => ∀ a, Always P (k a)

theorem always_bind {P : β → Prop} : ∀ {v : View F α} {f : α → View F β},
    Always (fun a => Always P (f a)) v → Always P (v >>= f)
  | .pure _, _, h => h
  | .list _ k, f, h => fun a => always_bind (v := k a) (f := f) (h a)

theorem always_eval [SortKey F] {P : α → Prop} (s : DB F) : ∀ {v : View F α}, Always P v → P (v.eval s)
  | .pure _, h => h
  | .list q k, h => always_eval s (v := k (Engine.eval s q)) (h _)

/-- Where it runs, every run's value has P. -/
theorem always_run {m : Type → Type} [Monad m] [LawfulMonad m] [Lists F m] {P : α → Prop} :
    ∀ {v : View F α}, Always P v → Sat P (v.run (m := m))
  | .pure a, h => ⟨Pure.pure ⟨a, h⟩, by simp [View.run]⟩
  | .list q k, h => by
    have : ∀ a, ∃ z : m { x // P x }, Subtype.val <$> z = (k a).run := fun a => always_run (h a)
    refine ⟨Lists.list q >>= fun a => Classical.choose (this a), ?_⟩
    simp only [View.run, map_bind]
    exact congrArg (Lists.list q >>= ·) (funext fun a => Classical.choose_spec (this a))

/-- What v answers when its lists answer these, in order (none if they
run out). -/
def runWith : List (Answer F) → View F α → Option α
  | _, .pure a => some a
  | [], .list _ _ => none
  | a :: as, .list _ k => runWith as (k a)

/-- What v answers along any answers has P. -/
theorem always_runWith {P : α → Prop} : ∀ (as : List (Answer F)) {v : View F α} {x : α},
    Always P v → v.runWith as = some x → P x
  | _, .pure _, _, h, e => by simp only [runWith, Option.some.injEq] at e; exact e ▸ h
  | [], .list _ _, _, _, e => by simp [runWith] at e
  | _ :: as, .list _ k, _, h, e => always_runWith as (h _) e

@[simp] theorem bind_eq (v : View F α) (f : α → View F β) : v >>= f = v.bind f := rfl
@[simp] theorem pure_eq (a : α) : (Pure.pure a : View F α) = View.pure a := rfl

end Engine.View

namespace Community
open Engine Engine.View

/-- **An approval writes at most three ops**: the approval, the
admission when it completes the tally, and one wrap of the key to the
new member's device, whatever the community holds. -/
theorem approveReq_ops (c req myAdm : Id) (d : Device) (esk : ByteArray) :
    Always (fun w : Write => w.ops.length ≤ 3) (approveReq c req myAdm d esk) := by
  unfold approveReq
  refine always_bind fun _ => always_bind fun _ => always_bind fun _ => always_bind fun ks => ?_
  dsimp only
  repeat' split
  all_goals (try simp only [Always, pure_eq])
  all_goals (repeat' split)
  all_goals simp

/-- The mutant: an approval that wraps the key to every member. -/
def approveWrapAll (c req myAdm : Id) (d : Device) (esk : ByteArray) : View Fact Write := do
  let ok := approve c req myAdm d
  let ks ← key.byCommunity.read [c] (limit := some 1)
  let rs ← recipients c
  return ⟨ok :: (match ks.rows.head? with
    | some (_, .key _ _ k) => rs.map (wrapKey c k esk)
    | _ => [])⟩

/-- **Wrapping to every member is over the budget**: a community of
three members makes four ops. -/
theorem wrapAll_over (c req myAdm : Id) (d : Device) (esk : ByteArray) (p : Pos) (kid k : ByteArray)
    (u₁ u₂ u₃ : Id) (d₁ d₂ d₃ e₁ e₂ e₃ : Key) :
    ¬ Always (fun w : Write => w.ops.length ≤ 3) (approveWrapAll c req myAdm d esk) := by
  intro h
  let none0 : Answer Fact := ⟨[], 0, 0, true⟩
  have := always_runWith [⟨[(p, .key c kid k)], 1, 1, true⟩,
    ⟨[(p, .admission c u₁ d₁ e₁), (p, .admission c u₂ d₂ e₂), (p, .admission c u₃ d₃ e₃)], 3, 3, true⟩,
    none0, none0, none0] h (by
      simp only [approveWrapAll, recipients, live, removals, Rel.read, View.read, bind_eq, pure_eq,
        View.bind, ite_true, runWith, none0]
      rfl)
  simp at this

end Community
