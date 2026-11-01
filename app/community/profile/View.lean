import app.Commands
import engine.renderer.Row
import app.community.Proofs

/-!
`community.profile`: its component, which reads its own facts, and the component's laws.
-/
namespace Kinds.Profile
open _root_.Engine _root_.Community _root_.Data

def bytesStr (b : ByteArray) : String := (String.fromUTF8? b).getD "?"

structure Data where
  name : String
  deriving BEq, Inhabited
variable {m : Type → Type} [Monad m] [Reads m]

def read (c u : Id) (deps : Array Q) : m (Data × Array Q) := do
  let (a, _, deps) ← readList (profile.byUser.query [c, u] (limit := some 1)) deps
  match a.rows.head? with
  | some (_, .profile _ _ n _) => return (⟨bytesStr n⟩, deps)
  | _ => return (⟨"…"⟩, deps)

/-- Whether a user other than u, among these rows, has a newest name
that looks as k. -/
def others (c u : Id) (k : ByteArray) : List (Pos × Fact) → Array Q → m (Bool × Array Q)
  | [], deps => pure (false, deps)
  | (_, .profile _ u' _ _) :: t, deps => do
    if u' = u then others c u k t deps else
    let (p, deps) ← read c u' deps
    if nameLook p.name = k then pure (true, deps) else others c u k t deps
  | _ :: t, deps => others c u k t deps

/-- Whether u, named `name`, has a namesake: another user whose newest
name looks the same (`nameLook`: invisible characters and kinds of space
do not tell names apart). Both are marked, as Quiet marks a duplicate
name. Reads the profiles filed under the look, and each author's newest. -/
def namesake (c u : Id) (name : String) (deps : Array Q) : m (Bool × Array Q) := do
  let (a, _, deps) ← readList (profile.byLook.query [c, nameLook name]) deps
  others c u (nameLook name) a.rows deps
end Kinds.Profile
namespace ViewLaws
open _root_.Engine _root_.Community _root_.Data _root_.Kinds

/-- A person's name, as the store holds it. -/
def nameIn (db : DB Fact) (c u : Id) : String :=
  match (Engine.eval db (profile.byUser.query [c, u] (limit := some 1))).rows.head? with
  | some (_, .profile _ _ n _) => Profile.bytesStr n
  | _ => "…"
variable {s : DB Fact} {C : Crypto}

theorem eval_one (r : Rel Fact) (as : List ByteArray) :
    (Engine.eval s (r.query as (some 1))).rows = (Engine.eval s (r.query as none)).rows.take 1 := by
  simp [Engine.eval, ListQ.cut, ListQ.inside, Rel.query, matching]

theorem byUser_args {c u : Id} {f : Fact} :
    profile.byUser.args f = some [c, u] ↔ ∃ n tm, f = .profile c u n tm := by
  cases f <;> (try (rename_i x; cases x)) <;> simp [profile.byUser, eq_comm]

theorem byLook_args {c k : Id} {f : Fact} :
    profile.byLook.args f = some [c, k] ↔
      ∃ u n tm, f = .profile c u n tm ∧ nameLook ((String.fromUTF8? n).getD "?") = k := by
  cases f
  case ofProfile x =>
    obtain ⟨c', u, n, tm⟩ := x
    simp only [profile.byLook, Rel.comap_args, Fact.profile?, Option.bind_some, Profile.byLook_args, Option.some.injEq, List.cons.injEq, and_true, Fact.profile.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩; exact ⟨u, n, tm, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩
    · rintro ⟨_, _, _, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩; exact ⟨rfl, rfl⟩
  all_goals simp [profile.byLook]

/-- At rest, a user with a Valid profile has a newest one: their name is
a Valid profile's. -/
theorem newest (h : Inv (family C) s) (hq : s.queue = []) {c u : Id} {y : Id} {n : ByteArray} {tm : Nat}
    (hv : V C s.ops y (.profile c u n tm)) :
    ∃ (p : Pos) (n' : ByteArray) (tm' : Nat), V C s.ops p.2 (.profile c u n' tm') ∧ nameIn s c u = Profile.bytesStr n' := by
  have hm := at_row (C := C) (r := profile.byUser) (as := [c, u]) (desc := true) (by simp [rels]) h hq hv
    (by simp [profile.byUser])
  have hne : (Engine.eval s (profile.byUser.query [c, u] none)).rows ≠ [] := List.ne_nil_of_mem hm
  obtain ⟨x, t, ht⟩ := List.exists_cons_of_ne_nil hne
  have hx : x ∈ (Engine.eval s (profile.byUser.query [c, u] none)).rows := ht ▸ List.mem_cons_self ..
  obtain ⟨hvx, ha⟩ := row_filed (C := C) (by simp [rels]) h hq hx
  obtain ⟨n', tm', hf⟩ := byUser_args.1 ha
  refine ⟨x.1, n', tm', hf ▸ hvx, ?_⟩
  unfold nameIn
  rw [eval_one, ht]
  obtain ⟨px, fx⟩ := x
  dsimp only at hf
  subst hf
  rfl

end ViewLaws
