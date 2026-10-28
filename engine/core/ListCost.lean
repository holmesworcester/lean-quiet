/-
What a list read costs, as it runs (docs/PERF.md): one list door, whose
charge is SQLite's plan for the answer (`listCost`, engine/core/CostStore.lean),
so a list of limit L and count cap C costs at most L + C rows and 3 + L
seeks, whatever the store holds, on a store whose answers keep the
list's limit and cap (`Fits`).

- `list_costs`: that bound, over every store whose answers fit.
- `eval_fits`, `model_fits`: the model's answers fit, for every list
  and every store. SQLite's are the model's (tests/engine/QueryDiff.lean
  checks them against `eval` on random stores), so they fit too.
- `view_lists`: a view costs one list door per list it reads, its
  depth along the answers the store gives (`View.depth`).

The mutant control (tests/engine/CostCheck.lean) is the same list with
no cap (`cap := 0`): its range count steps over every row in range, so
its rows grow with the store.
-/
import engine.core.CostStore
import engine.core.View

namespace Engine
open CostT

/-- An answer keeps its list's limit and its count's cap. -/
def Fits {F : Type} (q : ListQ) (a : Answer F) : Prop :=
  (∀ n, q.limit = some n → a.rows.length ≤ n) ∧ (0 < q.cap → a.inRange ≤ q.cap)

section
variable {F : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Lists F m]

/-- **A list read costs at most limit + cap rows and 3 + limit seeks**,
on a store whose answers fit, however many rows it holds. -/
theorem list_costs (q : ListQ) (hq : q.also = []) {L C : Nat} (hL : q.limit = some L)
    (hC : 0 < q.cap) (hCC : q.cap ≤ C) (hS : Sat (Fits q) (Lists.list (F := F) (m := m) q)) :
    Costs { lists := 1, seeks := 3 + L, rows := L + C } (Lists.list (F := F) (m := CostT m) q) := by
  have : Costs ({ lists := 1, seeks := 3 + L, rows := L + C } + 0)
      (CostT.chargedBy (listCost q) (Lists.list (F := F) (m := m) q) >>= pure) :=
    costs_bindP hS (fun a ha => by
      have h1 := ha.1 L hL
      have h2 := ha.2 hC
      have hs : (splitOf q []).isSome = false := by
        simp [splitOf, Nat.pos_iff_ne_zero.1 hC]
      simp only [listCost, countCost, hs, hq, List.length_nil, List.isEmpty_nil, ite_true, Nat.add_zero,
        Bool.false_eq_true, ite_false]
      split <;> meter_le) (fun a _ => costs_pure a)
  rw [bind_pure, Meter.add_zero] at this
  exact this

end

section
variable {F : Type} [SortKey F]

theorem eval_fits (s : DB F) (q : ListQ) : Fits q (eval s q) := by
  refine ⟨fun n hn => ?_, fun hc => ?_⟩
  · simp only [eval, ListQ.cut, hn]
    exact List.length_take_le _ _
  · simp only [eval, capped, Nat.pos_iff_ne_zero.1 hc, ite_false]
    exact Nat.min_le_left _ _

/-- **The model's answers fit**, for every list. -/
theorem model_fits (q : ListQ) : Sat (Fits q) (Lists.list (F := F) (m := Model F) q) :=
  ⟨fun s => (⟨eval s q, eval_fits s q⟩, s), rfl⟩

end

/-! ## A view: a list door per list it reads -/

namespace View
variable {F α : Type}

/-- How many lists a view reads, on every path: at most n. -/
def DepthLe : Nat → View F α → Prop
  | _, .pure _ => True
  | 0, .list _ _ => False
  | n + 1, .list _ k => ∀ a, DepthLe n (k a)

variable {m : Type → Type} [Monad m] [LawfulMonad m] [Lists F m]

/-- **A view of depth at most n costs at most n list doors** on every
store, each charged its own plan (`listCost`). -/
theorem view_lists : ∀ (n : Nat) (v : View F α), DepthLe n v →
    Within Meter.lists n (v.run (m := CostT m))
  | _, .pure a, _ => (within_pure a).mono (Nat.zero_le _)
  | 0, .list _ _, h => absurd h id
  | n + 1, .list q k, h => by
    show Within Meter.lists (n + 1) (Lists.list q >>= fun a => (k a).run)
    refine within_bind_le (A := 1) (B := n) (within_charged_by q) (fun a => view_lists n (k a) (h a))
      (by omega)
where
  within_charged_by (q : ListQ) : Within Meter.lists 1 (Lists.list (F := F) (m := CostT m) q) :=
    ⟨(fun a => ⟨(a, listCost q a), by simp [listCost]⟩) <$> Lists.list (F := F) (m := m) q, by
      show _ = (do let a ← Lists.list (F := F) (m := m) q; Pure.pure (a, listCost q a))
      rw [Functor.map_map, map_eq_pure_bind]⟩

end View

end Engine
