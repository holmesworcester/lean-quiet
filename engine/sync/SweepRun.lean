/- The sweep as it runs: `Node.sweep` calls `Sweep.run` over the SQLite
catalog (`Catalog.sql`, engine/wire/Tcp.lean). One such call is the pure
cursor transition `Sweep.step` that `Sweep.retried_fair` is proved over,
at the ceiling and row SQLite returned, and it changes no table. -/
import engine.sync.SweepLaws
import engine.core.SqliteLaws

namespace Engine.Sync.Sweep
open Trust

variable {F : Type} {holds : Db → Void IO.RealWorld → DB F → Prop}

/-- **`x` on SQLite reads tables `s`**: from a world where the database
holds `s`, if `x` returns, its answer satisfies `P` and the database
still holds `s`. -/
def Reads (holds : Db → Void IO.RealWorld → DB F → Prop) (s : DB F) {α : Type}
    (x : SqlM F α) (P : α → Prop) : Prop :=
  ∀ db w, holds db w s → ∀ v w', x db w = .ok v w' → P v ∧ holds db w' s

theorem Reads.pure {s : DB F} {α : Type} {a : α} {P : α → Prop} (h : P a) :
    Reads holds s (pure a : SqlM F α) P := by
  intro db w hs v w' hx
  rw [sql_pure] at hx
  cases hx
  exact ⟨h, hs⟩

theorem Reads.bind {s : DB F} {α β : Type} {x : SqlM F α} {f : α → SqlM F β}
    {P : α → Prop} {Q : β → Prop}
    (hx : Reads holds s x P) (hf : ∀ a, P a → Reads holds s (f a) Q) : Reads holds s (x >>= f) Q := by
  intro db w hs v w' h
  rw [sql_bind] at h
  unfold EST.bind at h
  split at h
  · rename_i a w₁ ha
    obtain ⟨hp, h1⟩ := hx db w hs a w₁ ha
    exact hf a hp db w₁ h1 v w' h
  · cases h

/-- A read the contract says changes no table. -/
theorem Reads.readOnly {s : DB F} {α : Type} {x : SqlM F α}
    (h : ∀ db, ReadOnly (sqlAct db x) (holds db)) : Reads holds s x (fun _ => True) := by
  intro db w hs v w' hx
  exact ⟨trivial, h db w s hs v w' (by simp only [sqlAct, hx])⟩

/-- Reading an op on SQLite returns the model's op and changes no table. -/
theorem Reads.getOp [Codec F] [SortKey F] (t : SqliteStore F holds) {s : DB F} (x : Id) :
    Reads holds s (Store.getOp (F := F) x : SqlM F (Option Op)) (fun v => v = s.ops x) := by
  intro db w hs v w' hx
  exact Sim.op t (.getOp x) db w s hs v w' hx

/-- **A sweep step on SQLite is the proved cursor transition.** From a
database that holds tables `s`, if `Node.sweep`'s `Sweep.run` over the
SQLite catalog returns, its cursor and offer are `Sweep.step` at some
ceiling, and at the op the catalog's row names in `s` (none for a hole
or a finished sweep); and the database still holds `s`. So the sweep's
laws (`step_progress`, `retried_fair`), proved for every ceiling and
row, are about the running sweep. -/
theorem sql_run_step [Codec F] [SortKey F] (t : SqliteStore F holds) (s : DB F) (cursor : Sweep)
    (shows : Op → Bool) (room : Nat) :
    Reads holds s (cursor.run (Catalog.sql (F := F)) shows room)
      (fun v => ∃ (ceiling : Nat) (row : Option Id), v = cursor.step ceiling (row.bind s.ops) shows room) := by
  unfold Sweep.run
  dsimp only
  have rest : ∀ c, Reads holds s
      (if (cursor.begin c).high ≤ (cursor.begin c).after then pure (cursor.step c none shows room)
       else do
         let r ← (Catalog.sql (F := F)).read ((cursor.begin c).after + 1)
         match r with
         | none => do
           let op ← pure none
           pure (cursor.step c op shows room)
         | some id => do
           let op ← Store.getOp (F := F) id
           pure (cursor.step c op shows room))
      (fun v => ∃ (ceiling : Nat) (row : Option Id), v = cursor.step ceiling (row.bind s.ops) shows room) := by
    intro c
    split
    · exact Reads.pure ⟨c, none, rfl⟩
    · refine Reads.bind (Reads.readOnly fun db => (t.catalog db).2 _) fun r _ => ?_
      cases r with
      | none =>
        refine Reads.bind (Reads.pure (P := fun v => v = none) rfl) fun o ho => ?_
        exact Reads.pure ⟨c, none, by rw [ho]; rfl⟩
      | some id =>
        refine Reads.bind (Reads.getOp t id) fun o ho => ?_
        exact Reads.pure ⟨c, some id, by rw [ho]; rfl⟩
  split
  · exact Reads.bind (Reads.pure (P := fun _ => True) trivial) fun c _ => rest c
  · exact Reads.bind (Reads.readOnly fun db => (t.catalog db).1) fun c _ => rest c

end Engine.Sync.Sweep
