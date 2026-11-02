/-
**The engine's code on SQLite runs as on the model**, given the store's
trust file (engine/core/StoreTrust.lean, `Trust.SqliteStore`).

The proofs run the engine on the model. The app runs the same generic
code (`ingest`, `step`, `drain`) on SQLite, inside `receive`'s one
transaction. These laws carry the contract, one operation at a time,
through that code: if a write turn on SQLite commits, the database holds
the tables the same turn leaves on the model (`receive_as_model`): the
capped turn's (`receive_model`), and its rows show them
(`receive_shows_model`). A refused write turn changes no table
(`receive_refused`). So the model's laws about a write turn
(`turn_waiting`, `carry_bounded`) are laws about SQLite's.

`Sim holds x y` reads: `x` on SQLite runs as `y` on the model. It is
built from three facts: `pure` runs as `pure`, a bind runs as a bind of
parts that do, and each store operation runs as the model's (the
contract).
-/
import engine.core.StoreTrust
import engine.core.TurnLaws

namespace Trust
open Engine

variable {F : Type}

/-! ## How SQLite's monad and the model's run -/

theorem sql_bind {α β : Type} (x : SqlM F α) (f : α → SqlM F β) (db : Db) (w : Void IO.RealWorld) :
    (x >>= f) db w = EST.bind (x db) (fun a => f a db) w := rfl

theorem sql_pure {α : Type} (a : α) (db : Db) (w : Void IO.RealWorld) :
    (pure a : SqlM F α) db w = .ok a w := rfl

theorem model_bind {α β : Type} (x : Model F α) (f : α → Model F β) (s : DB F) :
    (x >>= f) s = f (x s).1 (x s).2 := rfl

theorem model_pure {α : Type} (a : α) (s : DB F) : (pure a : Model F α) s = (a, s) := rfl

theorem sql_tryCatch {α : Type} (x : SqlM F α) (k : IO.Error → SqlM F α) (db : Db) (w : Void IO.RealWorld) :
    (tryCatch x k : SqlM F α) db w = EST.tryCatch (x db) (fun e => k e db) w := rfl

theorem sql_liftM {α : Type} (x : IO α) (db : Db) (w : Void IO.RealWorld) :
    (liftM x : SqlM F α) db w = x w := rfl

theorem sql_getDb (db : Db) (w : Void IO.RealWorld) : (getDb : SqlM F Db) db w = .ok db w := rfl

theorem sql_throw {α : Type} (e : IO.Error) (db : Db) (w : Void IO.RealWorld) :
    (throw e : SqlM F α) db w = .error e w := rfl

theorem sql_earlyReturn {ρ β : Type} (a : ρ) (db : Db) (w : Void IO.RealWorld) :
    (EarlyReturnT.return a : EarlyReturnT ρ (SqlM F) β) db w = .ok (Except.error a) w := rfl


variable [Codec F] {holds : Db → Void IO.RealWorld → DB F → Prop}

/-! ## Building `Sim` -/

theorem Sim.pure {α : Type} {a : α} : Sim holds (pure a : SqlM F α) (pure a : Model F α) := by
  intro db w s hs v w' hx
  rw [sql_pure] at hx
  cases hx
  exact ⟨rfl, hs⟩

theorem Sim.bind {α β : Type} {x : SqlM F α} {y : Model F α} {f : α → SqlM F β} {g : α → Model F β}
    (hx : Sim holds x y) (hf : ∀ a, Sim holds (f a) (g a)) : Sim holds (x >>= f) (y >>= g) := by
  intro db w s hs v w' h
  rw [sql_bind] at h
  unfold EST.bind at h
  split at h
  · rename_i a w₁ ha
    obtain ⟨rfl, h1⟩ := hx db w s hs a w₁ ha
    rw [model_bind]
    exact hf _ db w₁ _ h1 v w' h
  · cases h

theorem Sim.ite {α : Type} (c : Prop) [Decidable c] {a b : SqlM F α} {a' b' : Model F α}
    (ha : Sim holds a a') (hb : Sim holds b b') :
    Sim holds (if c then a else b) (if c then a' else b') := by
  by_cases hc : c
  · simp only [hc, ite_true]; exact ha
  · simp only [hc, ite_false]; exact hb

/-- `Sim` only reads its model program's runs. -/
theorem Sim.congr {α : Type} {x : SqlM F α} {y y' : Model F α} (hy : ∀ s, y s = y' s)
    (hx : Sim holds x y) : Sim holds x y' := by
  intro db w s hs v w' h
  rw [← hy s]
  exact hx db w s hs v w' h

theorem Sim.forIn {γ β : Type} (l : List γ) (b : β) {f : γ → β → SqlM F (ForInStep β)}
    {g : γ → β → Model F (ForInStep β)} (hf : ∀ a b, Sim holds (f a b) (g a b)) :
    Sim holds (forIn l b f) (forIn l b g) := by
  induction l generalizing b with
  | nil => simp only [List.forIn_nil]; exact Sim.pure
  | cons a t ih =>
    rw [List.forIn_cons, List.forIn_cons]
    refine Sim.bind (hf a b) fun r => ?_
    cases r with
    | done c => exact Sim.pure
    | yield c => exact ih c

variable [SortKey F]

/-- Each store operation runs as the model's: the contract's `answers`. -/
theorem Sim.op (h : SqliteStore F holds) {α : Type} (op : StoreOp F α) :
    Sim holds (op.run (m := SqlM F)) (op.run (m := Model F)) := by
  intro db w s hs v w' hx
  exact h.answers db op w s hs v w' (by simp only [sqlStep, hx])

/-! ## The engine's generic code -/

theorem statuses_sim (h : SqliteStore F holds) :
    ∀ l : List Id, Sim holds (statuses (m := SqlM F) l) (statuses (m := Model F) l)
  | [] => by unfold statuses; exact Sim.pure
  | r :: rest => by
    unfold statuses
    exact Sim.bind (Sim.op h (.getStatus r)) fun _ =>
      Sim.bind (statuses_sim h rest) fun _ => Sim.pure

theorem waitOn_sim (h : SqliteStore F holds) (x : Id) :
    ∀ l : List Id, Sim holds (waitOn (F := F) (m := SqlM F) x l) (waitOn (F := F) (m := Model F) x l)
  | [] => by unfold waitOn; exact Sim.pure
  | r :: rest => by
    unfold waitOn
    refine Sim.bind (Sim.op h (.getStatus r)) fun st => ?_
    dsimp only
    exact Sim.ite _ (Sim.bind (Sim.op h (.addWait r x)) fun _ => waitOn_sim h x rest)
      (waitOn_sim h x rest)

theorem pushAll_sim (h : SqliteStore F holds) :
    ∀ l : List Id, Sim holds (pushAll (F := F) (m := SqlM F) l) (pushAll (F := F) (m := Model F) l)
  | [] => by unfold pushAll; exact Sim.pure
  | w :: rest => by
    unfold pushAll
    exact Sim.bind (Sim.op h (.push w)) fun _ => pushAll_sim h rest

theorem indexAll_sim (h : SqliteStore F holds) (x : Id) :
    ∀ l : List ByteArray, Sim holds (indexAll (F := F) (m := SqlM F) x l) (indexAll (F := F) (m := Model F) x l)
  | [] => by unfold indexAll; exact Sim.pure
  | k :: rest => by
    unfold indexAll
    exact Sim.bind (Sim.op h (.index k x)) fun _ => indexAll_sim h x rest

theorem ingest_sim (h : SqliteStore F holds) (o : Op) :
    Sim holds (ingest (F := F) (m := SqlM F) o) (ingest (F := F) (m := Model F) o) := by
  unfold ingest
  refine Sim.bind (Sim.op h (.getOp o.id)) fun r => ?_
  cases r with
  | some _ => exact Sim.pure
  | none => exact Sim.bind (Sim.op h (.putOp o)) fun _ => Sim.op h (.push o.id)

theorem decide_sim (h : SqliteStore F holds) (fam : Family F) (x : Id) (v : Verdict F) :
    Sim holds (Engine.decide (m := SqlM F) fam x v) (Engine.decide (m := Model F) fam x v) := by
  unfold Engine.decide
  refine Sim.bind (Sim.op h (.setStatus x v)) fun _ => ?_
  have jp : ∀ u : Unit, Sim holds
      (do let ws ← Store.waiters (F := F) (m := SqlM F) x; Store.clearWaiters (F := F) (m := SqlM F) x;
          pushAll (F := F) (m := SqlM F) ws)
      (do let ws ← Store.waiters (F := F) (m := Model F) x; Store.clearWaiters (F := F) (m := Model F) x;
          pushAll (F := F) (m := Model F) ws) := fun _ =>
    Sim.bind (Sim.op h (.waiters x)) fun ws =>
      Sim.bind (Sim.op h (.clearWaiters x)) fun _ => pushAll_sim h ws
  cases v with
  | valid f => exact Sim.bind (indexAll_sim h x _) jp
  | invalid => exact jp ()

theorem step_sim (h : SqliteStore F holds) (fam : Family F) :
    Sim holds (step (m := SqlM F) fam) (step (m := Model F) fam) := by
  unfold step
  refine Sim.bind (Sim.op h .pop) fun r => ?_
  cases r with
  | none => exact Sim.pure
  | some x =>
    refine Sim.bind (Sim.op h (.getStatus x)) fun st => ?_
    cases st with
    | some _ => exact Sim.pure
    | none =>
      refine Sim.bind (Sim.op h (.getOp x)) fun r => ?_
      cases r with
      | none => exact Sim.pure
      | some o =>
        refine Sim.bind (statuses_sim h o.reqs) fun sts => ?_
        cases judge fam o sts with
        | some v => exact Sim.bind (decide_sim h fam x v) fun _ => Sim.pure
        | none => exact Sim.bind (waitOn_sim h x o.reqs) fun _ => Sim.pure

theorem drain_sim (h : SqliteStore F holds) (fam : Family F) :
    ∀ n, Sim holds (drain (m := SqlM F) fam n) (drain (m := Model F) fam n)
  | 0 => by unfold drain; exact Sim.pure
  | n + 1 => by
    unfold drain
    exact Sim.bind (step_sim h fam) fun b => Sim.ite _ (drain_sim h fam n) Sim.pure

/-! ## Transactions -/

/-- A transaction that commits began, ran its body, and committed. -/
theorem transact_ok {α : Type} {act : SqlM F α} {db : Db} {w : Void IO.RealWorld} {v : α} {w'}
    (h : transact act db w = .ok v w') :
    ∃ w₁ w₂, db.exec "BEGIN IMMEDIATE" w = .ok () w₁ ∧ act db w₁ = .ok v w₂ ∧
      db.exec "COMMIT" w₂ = .ok () w' := by
  unfold transact at h
  simp only [sql_bind, sql_tryCatch, sql_liftM, sql_getDb, EST.bind, EST.tryCatch] at h
  cases hb : db.exec "BEGIN IMMEDIATE" w with
  | error e s => simp [hb] at h
  | ok u w₁ =>
    simp only [hb] at h
    cases ha : act db w₁ with
    | error e s =>
      simp only [ha] at h
      cases hr : db.exec "ROLLBACK" s with
      | error e s => simp [hr] at h
      | ok u s => simp [hr, sql_throw] at h
    | ok a w₂ =>
      simp only [ha] at h
      cases hc : db.exec "COMMIT" w₂ with
      | error e s =>
        simp only [hc] at h
        cases hr : db.exec "ROLLBACK" s with
        | error e s => simp [hr] at h
        | ok u s => simp [hr, sql_throw] at h
      | ok u w₃ =>
        simp only [hc, sql_earlyReturn, EarlyReturn.runK, sql_pure] at h
        cases h
        refine ⟨w₁, w₂, ?_, ?_, ?_⟩ <;> first | rfl | assumption

/-- A transaction runs as its body: beginning and committing change no
table (the contract's `brackets`). -/
theorem Sim.transact (h : SqliteStore F holds) {α : Type} {act : SqlM F α} {y : Model F α}
    (hx : Sim holds act y) : Sim holds (transact act) y := by
  intro db w s hs v w' ht
  obtain ⟨w₁, w₂, hb, ha, hc⟩ := transact_ok ht
  have hs1 := h.brackets "BEGIN IMMEDIATE" (by simp) db w s hs w₁ hb
  obtain ⟨rfl, hs2⟩ := hx db w₁ s hs1 v w₂ ha
  exact ⟨rfl, h.brackets "COMMIT" (by simp) db w₂ _ hs2 w' hc⟩

/-! ## A write turn -/

theorem judgeAhead_sim (h : SqliteStore F holds) (fam : Family F) (b : Bool) (x : Id) :
    Sim holds (judgeAhead (m := SqlM F) fam b x) (judgeAhead (m := Model F) fam b x) := by
  unfold judgeAhead
  refine Sim.bind (Sim.op h (.getStatus x)) fun st => ?_
  cases st with
  | some _ => exact Sim.pure
  | none =>
    refine Sim.bind (Sim.op h (.getOp x)) fun r => ?_
    cases r with
    | none => exact Sim.pure
    | some o =>
      refine Sim.ite _ Sim.pure ?_
      refine Sim.bind (statuses_sim h o.reqs) fun sts => ?_
      cases judge fam o sts with
      | some v =>
        exact Sim.bind (Sim.op h (.waiters x)) fun _ => Sim.bind (decide_sim h fam x v) fun _ => Sim.pure
      | none => exact Sim.bind (waitOn_sim h x o.reqs) fun _ => Sim.pure

theorem judgeJob_sim (h : SqliteStore F holds) (fam : Family F) :
    ∀ xs : List Id, Sim holds (judgeJob (m := SqlM F) fam xs) (judgeJob (m := Model F) fam xs)
  | [] => by unfold judgeJob; exact Sim.pure
  | x :: xs => by
    unfold judgeJob
    exact Sim.bind (judgeAhead_sim h fam false x) fun _ =>
      Sim.bind (judgeJob_sim h fam xs) fun _ => Sim.pure

theorem urgentClose_sim (h : SqliteStore F holds) (fam : Family F) :
    ∀ (n : Nat) (xs : List Id), Sim holds (urgentClose (m := SqlM F) fam n xs) (urgentClose (m := Model F) fam n xs)
  | 0, _ => by unfold urgentClose; exact Sim.pure
  | _ + 1, [] => by unfold urgentClose; exact Sim.pure
  | n + 1, x :: xs => by
    unfold urgentClose
    exact Sim.bind (judgeAhead_sim h fam true x) fun _ =>
      Sim.bind (urgentClose_sim h fam n _) fun _ => Sim.pure

theorem turnCapped_sim (h : SqliteStore F holds) (fam : Family F) (cap : Nat) (ops : List Op) :
    Sim holds (turnCapped (m := SqlM F) fam cap ops) (turnCapped (m := Model F) fam cap ops) := by
  unfold turnCapped
  exact Sim.bind (Sim.forIn ops _ fun o _ => Sim.bind (ingest_sim h o) fun _ => Sim.pure) fun _ =>
    Sim.bind (judgeJob_sim h fam _) fun _ => Sim.bind (Sim.op h .countOps) fun _ =>
      Sim.bind (urgentClose_sim h fam _ _) fun _ => Sim.bind (drain_sim h fam cap) fun _ => Sim.pure

/-- **A write turn on SQLite runs as the model's.** `receive` takes in
`ops` and runs the capped turn, in one transaction. If it commits, the
database holds the tables that the same code leaves on the model. -/
theorem receive_as_model (h : SqliteStore F holds) (fam : Family F) (ops : List Op) :
    Sim holds (receive fam ops) (turnCapped (m := Model F) fam drainCap ops >>= fun _ => pure ()) := by
  unfold receive
  exact Sim.transact h (Sim.bind (turnCapped_sim h fam drainCap ops) fun _ => Sim.pure)

/-- **The model's write turn is the capped turn on the tables**
(`turnCappedS`). -/
theorem receive_model (fam : Family F) (ops : List Op) (s : DB F) :
    ((turnCapped (m := Model F) fam drainCap ops >>= fun _ => pure ()) s).2 = turnCappedS fam drainCap ops s := by
  rw [model_bind, model_pure]
  exact run_turnCapped drainCap ops s

/-- **After a write turn commits, SQLite's rows show the model's write
turn**: the five tables, as the dumps read them, are the capped turn's
on the model. -/
theorem receive_shows_model (h : SqliteStore F holds) (fam : Family F) (ops : List Op)
    {db : Db} {w w' : Void IO.RealWorld} {s : DB F} (hs : holds db w s)
    (hr : receive fam ops db w = .ok () w') :
    ShowsAt db w' (turnCappedS fam drainCap ops s) := by
  rw [← receive_model fam ops s]
  exact h.shows _ _ _ (receive_as_model h fam ops db w s hs () w' hr).2

/-- **A refused write turn changes no table**: if `receive` fails, the
database holds the tables it held before. -/
theorem receive_refused (h : SqliteStore F holds) (fam : Family F) (ops : List Op)
    {db : Db} {w w' : Void IO.RealWorld} {s : DB F} {e : IO.Error} (hs : holds db w s)
    (hr : receive fam ops db w = .error e w') : holds db w' s := by
  unfold receive at hr
  exact h.rollback _ db w s hs e w' hr

/-! ## A purge -/

/-- An action that only fails runs as anything. -/
theorem Sim.throw {α : Type} (e : IO.Error) {y : Model F α} : Sim holds (throw e : SqlM F α) y := by
  intro db w s _ v w' hx
  rw [sql_throw] at hx
  cases hx

theorem walkDeps_sim (h : SqliteStore F holds) :
    ∀ (n : Nat) (todo found : List Id) (seen : Std.HashSet Id),
      Sim holds (walkDeps (F := F) (m := SqlM F) n todo found seen)
        (walkDeps (F := F) (m := Model F) n todo found seen)
  | _, [], found, seen => by unfold walkDeps; exact Sim.pure
  | 0, _ :: _, _, _ => by unfold walkDeps; exact Sim.pure
  | n + 1, x :: todo, found, seen => by
    unfold walkDeps
    exact Sim.bind (Sim.op h (.dependents x)) fun ys => walkDeps_sim h n _ _ _

theorem unsettle_sim (h : SqliteStore F holds) (fam : Family F) :
    ∀ (xs gone again : List Id),
      Sim holds (unsettle (m := SqlM F) fam xs gone again) (unsettle (m := Model F) fam xs gone again)
  | [], gone, again => by unfold unsettle; exact Sim.pure
  | x :: xs, gone, again => by
    unfold unsettle
    refine Sim.bind (Sim.op h (.undecide x)) fun _ => Sim.bind (Sim.op h (.getOp x)) fun r => ?_
    cases r with
    | none => exact unsettle_sim h fam xs gone again
    | some o => exact Sim.ite _ (unsettle_sim h fam xs gone _) (unsettle_sim h fam xs _ again)

theorem deleteAll_sim (h : SqliteStore F holds) :
    ∀ l : List Id, Sim holds (deleteAll (F := F) (m := SqlM F) l) (deleteAll (F := F) (m := Model F) l)
  | [] => by unfold deleteAll; exact Sim.pure
  | x :: rest => by
    unfold deleteAll
    exact Sim.bind (Sim.op h (.deleteOp x)) fun _ => deleteAll_sim h rest

theorem purge_sim (h : SqliteStore F holds) (fam : Family F) (ids : List Id) :
    Sim holds (purge (m := SqlM F) fam ids) (purge (m := Model F) fam ids) := by
  unfold purge
  refine Sim.bind (Sim.op h .countOps) fun n => Sim.bind (walkDeps_sim h _ _ _ _) fun r => ?_
  cases r with
  | none => exact Sim.pure
  | some c =>
    exact Sim.bind (unsettle_sim h fam c [] []) fun p =>
      Sim.bind (deleteAll_sim h p.1) fun _ => Sim.bind (pushAll_sim h p.2) fun _ => Sim.pure

/-- A purge's `VACUUM` and checkpoint change no table (the contract's
`scrub`). -/
theorem scrub_sim (h : SqliteStore F holds) (vacuum : Bool) :
    Sim holds (scrubSql (F := F) vacuum) (pure ()) := by
  intro db w s hs v w' hx
  have := h.scrub vacuum db w s hs
  rw [hx] at this
  exact ⟨rfl, this⟩

theorem purgeCapped_sim (h : SqliteStore F holds) (fam : Family F) (cap : Nat) (ids : List Id) :
    Sim holds (purgeCapped (m := SqlM F) fam cap ids) (purgeCapped (m := Model F) fam cap ids) := by
  unfold purgeCapped
  refine Sim.bind (purge_sim h fam ids) fun r => ?_
  cases r with
  | none => exact Sim.pure
  | some p =>
    exact Sim.bind (Sim.op h .countOps) fun _ => Sim.bind (urgentClose_sim h fam _ _) fun _ =>
      Sim.bind (drain_sim h fam cap) fun _ => Sim.pure

/-- **A purge on SQLite runs as the model's purge.** `purgeSql` runs the
engine's capped purge (`purgeCapped`: the purge, the urgent closure over
what it requeued, then at most `drainCap` queued) in one transaction,
then (with `scrub`) rewrites the file. If it returns, the database holds
the tables the same capped purge leaves on the model (`purgeCappedS`,
`run_purgeCapped`). -/
theorem purge_as_model (h : SqliteStore F holds) (fam : Family F) (ids : List Id) (scrub : Bool) :
    Sim holds (purgeSql fam ids scrub)
      (purgeCapped (m := Model F) fam drainCap ids >>= fun _ => pure ()) := by
  have key : Sim holds (purgeSql fam ids scrub)
      ((do match ← purgeCapped (m := Model F) fam drainCap ids with
            | some g => pure g
            | none => pure ([] : List Id)) >>= fun _ => pure ()) := by
    unfold purgeSql purgeTx
    refine Sim.bind (Sim.transact h (Sim.bind (purgeCapped_sim h fam drainCap ids) fun r => ?_)) fun _ => ?_
    · cases r with
      | some g => exact Sim.pure
      | none => exact Sim.throw _
    · cases scrub
      · exact Sim.pure
      · exact scrub_sim h _
  refine Sim.congr (fun s => ?_) key
  simp only [model_bind]
  cases (purgeCapped (m := Model F) fam drainCap ids s).1 <;> rfl

end Trust
