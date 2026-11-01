import app.community.Family

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

theorem bind_eq (v : View F α) (f : α → View F β) : v >>= f = v.bind f := rfl

theorem pure_eq (a : α) : (Pure.pure a : View F α) = View.pure a := rfl

end Engine.View
