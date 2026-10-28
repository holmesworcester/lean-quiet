/-
Taking an op in twice is taking it in once: over the running intake
(`ingest`, which every write turn runs for each of its ops,
Sqlite.receive), read in the store model (`run_ingest`).

- `ingestS_known`: an op the store holds changes nothing;
- `ingestS_twice`: the same op twice is the same store as once;
- `ingest_twice`: so the running `ingest`, run twice, is run once;
- `ingestAll_again`: after a write turn's ops, any of them again (a
  retried write, a peer's resend, an op both written here and synced
  back) changes nothing.

So a write re-offered, re-sent or received again is harmless: nothing is
stored twice or queued twice, and every verdict stays (the store is the
same).
-/
import engine.core.Run

namespace Engine
variable {F : Type}

/-- **An op the store holds changes nothing.** -/
theorem ingestS_known {o o' : Op} {s : DB F} (h : s.ops o.id = some o') : ingestS o s = s := by
  unfold ingestS; rw [h]

/-- After an op is taken in, the store holds an op under its id. -/
theorem ingestS_holds (o : Op) (s : DB F) : ∃ o', (ingestS o s).ops o.id = some o' := by
  unfold ingestS
  cases h : s.ops o.id with
  | some o' => exact ⟨o', by simp [h]⟩
  | none => exact ⟨o, by simp [DB.putOp, DB.push]⟩

/-- Taking in an op keeps every op already held. -/
theorem ingestS_keeps (o : Op) {s : DB F} {x : Id} {o' : Op} (h : s.ops x = some o') :
    ∃ o'', (ingestS o s).ops x = some o'' := by
  unfold ingestS
  cases hs : s.ops o.id with
  | some _ => exact ⟨o', by simp [h]⟩
  | none =>
    by_cases hx : x = o.id
    · exact ⟨o, by simp [DB.putOp, DB.push, hx]⟩
    · exact ⟨o', by simp [DB.putOp, DB.push, hx, h]⟩

/-- **The same op twice is the same store as once.** -/
theorem ingestS_twice (o : Op) (s : DB F) : ingestS o (ingestS o s) = ingestS o s := by
  obtain ⟨o', h⟩ := ingestS_holds o s
  exact ingestS_known h

/-- **The running intake, run twice, is run once.** -/
theorem ingest_twice (o : Op) (s : DB F) :
    (do ingest (m := Model F) o; ingest (m := Model F) o).run s = (ingest (m := Model F) o).run s := by
  simp only [Model.run_bind, run_ingest, ingestS_twice]

/-- A write turn's intake: each of its ops in order. -/
def ingestAll (s : DB F) (L : List Op) : DB F := L.foldl (fun s o => ingestS o s) s

theorem ingestAll_holds : ∀ (L : List Op) (s : DB F) {x : Id} {o' : Op}, s.ops x = some o' →
    ∃ o'', (ingestAll s L).ops x = some o''
  | [], _, _, o', h => ⟨o', h⟩
  | o :: t, s, _, _, h => by
    obtain ⟨o'', h'⟩ := ingestS_keeps o h
    exact ingestAll_holds t (ingestS o s) h'

theorem ingestAll_mem : ∀ (L : List Op) (s : DB F) {o : Op}, o ∈ L → ∃ o', (ingestAll s L).ops o.id = some o'
  | [], _, _, h => by cases h
  | a :: t, s, o, h => by
    rcases List.mem_cons.1 h with rfl | h
    · obtain ⟨o', h'⟩ := ingestS_holds o s
      exact ingestAll_holds t _ h'
    · exact ingestAll_mem t (ingestS a s) h

/-- **A write turn's intake is `ingestAll`**: the loop Sqlite.receive
runs over its ops, read in the store model. -/
theorem run_ingestEach : ∀ (L : List Op) (s : DB F),
    (forIn (m := Model F) L PUnit.unit fun o _ => do ingest (m := Model F) o; pure (ForInStep.yield PUnit.unit)).run s =
      (PUnit.unit, ingestAll s L)
  | [], s => rfl
  | o :: t, s => by
    simp only [List.forIn_cons, Model.run_bind, run_ingest, Model.run_pure]
    exact run_ingestEach t (ingestS o s)

/-- **After a write turn's ops, any of them again changes nothing.** -/
theorem ingestAll_again (L : List Op) (s : DB F) {o : Op} (h : o ∈ L) :
    ingestS o (ingestAll s L) = ingestAll s L := by
  obtain ⟨o', h'⟩ := ingestAll_mem L s h
  exact ingestS_known h'

end Engine
