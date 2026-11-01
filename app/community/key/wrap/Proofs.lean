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

/-- Every view's answers have a property every value has. -/
theorem always_true {P : α → Prop} (hP : ∀ a, P a) : ∀ {v : View F α}, Always P v
  | .pure a => hP a
  | .list _ k => fun a => always_true hP (v := k a)

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

namespace Community
open Engine Codec

/-- What a Valid wrap's validator saw: its body; the root, whose key id
the wrap carries; its author's admission, whose device signed it; and
its recipient's admission, whose node key it goes to. -/
theorem check_wrap {C : Crypto} {o : Op} {b : Body} {fs : List Fact} {c : Id} {kid e bx : ByteArray}
    (h : check C o b fs = some (.wrap c kid e bx)) :
    ∃ s d0 e0 ua da ea ka ut dt kt, b = .wrap bx s ∧
      fs = [.admission c c d0 e0 kid, .admission c ua da ea ka, .admission c ut dt e kt] ∧
      o.reqs.head? = some c ∧ C.verify da (signed o b) s = true := by
  unfold check at h
  split at h <;> (try (simp at h; done))
  rename_i b r a t
  rcases b with ⟨bx', s⟩; rcases r with ⟨c0, u0, d0, e0, k0⟩; rcases a with ⟨c1, ua, da, ea, ka⟩
  rcases t with ⟨c2, ut, dt, et, kt⟩
  simp only [Wrap.check] at h
  split at h
  · rename_i hc
    simp only [Option.map_some, Option.some.injEq, Fact.ofWrap.injEq, Wrap.Fact.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    obtain ⟨h1, rfl, rfl, rfl, h5⟩ := hc
    exact ⟨_, _, _, _, _, _, _, _, _, _, rfl, rfl, h1, h5⟩
  · simp at h

end Community
