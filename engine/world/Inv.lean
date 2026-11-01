/-
Invariants of every plain node in every execution, proven of the running
node: what the per-link laws take of a node's state at a step.

- **No managed sessions** (`managed_nil`): a plain node's sessions all
  come from the harness's `connect`; the family establishes none, so
  `Node.follow` never adds one and every entry point ends with none.
-/
import engine.world.Owed
import engine.world.Good

namespace Engine.World
open Engine Engine.Sync

variable {F : Type}

/-- Serving a queue changes a node's sessions only. -/
theorem serveOwed_managed (x : Sync F (HeldM F)) (n : Node) (cid : Id) (now : Nat) (h : Held F) :
    ((n.serveOwed x cid now).run h).1.1.managed = n.managed := by
  unfold Node.serveOwed
  split
  · rfl
  · split
    · rfl
    · simp only [HeldM.run_bind, HeldM.run_pure]

/-- With no catalog, a sweep does nothing. -/
theorem sweep_none (x : Sync F (HeldM F)) (hx : x.catalog = none) (n : Node) (cid : Id) (h : Held F) :
    (n.sweep x cid).run h = ((n, {}), h) := by
  unfold Node.sweep; rw [hx]; rfl

theorem drop_managed (n : Node) (cid : Id) (hm : n.managed = []) : (n.drop cid).managed = [] := by
  simp [Node.drop, Node.close, hm]

section
variable (S : Engine.Sync.Setup F) (s : Who)

theorem apply_managed (n : Node) (cid : Id) (st : Step) (now : Nat) (h : Held F) (hm : n.managed = []) :
    ((n.apply (S.sync s) cid st now).run h).1.1.managed = [] := by
  have hfold : ∀ (L : List Op), L.foldl (fun b (_ : Op) => b) ([] : List Op) = [] := by
    intro L; induction L with
    | nil => rfl
    | cons _ _ ih => exact ih
  unfold Node.apply
  split
  · exact drop_managed n cid hm
  · simp only [HeldM.run_bind, recordGiven_run]
    rw [forIn_yield _ _ (fun _ acc => acc) _ (fun o _ acc => by
      simp only [sync_recv, HeldM.run_bind, HeldM.run_pure, List.append_nil]), hfold, store_nil]
    simp only [HeldM.run_pure]
    rw [(store_facts S s _ st.take false h).2.1]; exact hm

theorem finish_managed (n : Node) (out : Acts) (now : Nat) (h : Held F) (hm : n.managed = []) :
    ((n.finish (S.sync s) out now).run h).1.1.managed = [] := by
  rw [finish_run S s n out now h hm]; exact hm

theorem onWrite_managed (n : Node) (ops : List Op) (now : Nat) (h : Held F) (hm : n.managed = []) :
    ((n.onWrite (S.sync s) ops now).run h).1.1.managed = [] := by
  unfold Node.onWrite
  simp only [HeldM.run_bind]
  exact finish_managed S s _ _ now _ (by rw [heat_managed, store_keeps]; exact hm)

theorem onClose_managed (n : Node) (addr : ByteArray) (now : Nat) (h : Held F) (hm : n.managed = []) :
    ((n.onClose (S.sync s) addr now).run h).1.1.managed = [] := by
  unfold Node.onClose
  apply finish_managed
  have : ∀ (L : List Id) (m : Node), m.managed = [] → (L.foldl Node.drop m).managed = [] := by
    intro L
    induction L with
    | nil => intro m h; exact h
    | cons a t ih => intro m h; exact ih _ (drop_managed m a h)
  exact this _ n hm

theorem connect_managed (n : Node) (cid : Id) (a : ByteArray) (dialer : Bool) (now : Nat) (h : Held F)
    (hm : n.managed = []) : ((n.connect (S.sync s) cid a dialer now).run h).1.1.managed = [] := by
  unfold Node.connect Node.open
  simp only [HeldM.run_bind, sync_rooms, HeldM.run_pure]
  apply finish_managed
  simp [Node.close, Node.setAddr, hm]

theorem onSealed_managed (n : Node) (addr : ByteArray) (opened : Option (Id × ByteArray)) (now : Nat) (h : Held F)
    (hm : n.managed = []) : ((n.onSealed (S.sync s) addr opened now).run h).1.1.managed = [] := by
  unfold Node.onSealed
  split
  · exact hm
  · split
    · simp only [HeldM.run_bind]
      generalize hR : HeldM.run (forIn (m := HeldM F) (_ : List ByteArray)
        ((n.setAddr _ addr, {}) : Node × Acts) _) h = R
      have pR := forIn_inv hR (fun _ (st : Node × Acts) => st.1.managed = []) hm (fun b _ st h' hst => by
        split
        · simp only [HeldM.run_bind, refresh_run, HeldM.run_pure, ForInStep.value]
          exact apply_managed S s _ _ _ now _ hst
        · exact hst)
      exact finish_managed S s _ _ now _ (by rw [serveOwed_managed]; exact pR)
    · exact hm

theorem onFrame_managed (n : Node) (addr bytes : ByteArray) (now : Nat) (h : Held F) (hm : n.managed = []) :
    ((n.onFrame (S.sync s) addr bytes now).run h).1.1.managed = [] := by
  unfold Node.onFrame
  split
  · dsimp only
    split
    · exact hm
    · split
      · exact hm
      · simp only [HeldM.run_bind]
        exact finish_managed S s _ _ now _ (by rw [store_keeps, write_keeps]; exact hm)
  · simp only [HeldM.run_bind]
    exact onSealed_managed S s _ _ _ now _ hm
  · exact hm

theorem onTick_managed (n : Node) (now : Nat) (h : Held F) (hm : n.managed = []) :
    ((n.onTick (S.sync s) now).run h).1.1.managed = [] := by
  have hd : (S.sync s).deferredRetries = false := rfl
  unfold Node.onTick
  rw [hd]
  unfold Node.onTickDirect
  simp only [Bool.false_eq_true, ↓reduceIte, HeldM.run_bind]
  have hA := store_keeps S s n (((S.sync s).hooks.dial now).run h).1 true (((S.sync s).hooks.dial now).run h).2
  generalize HeldM.run (Node.store (S.sync s) n (((S.sync s).hooks.dial now).run h).1 true)
    (((S.sync s).hooks.dial now).run h).2 = A at hA ⊢
  generalize hR : HeldM.run (forIn (m := HeldM F) A.1.1.conns ((A.1.1, A.1.2) : Node × Acts) _) A.2 = R
  have pR := forIn_inv hR (fun _ (st : Node × Acts) => st.1.managed = []) (by rw [hA]; exact hm)
    (fun b _ st h' hst => by
      split
      · exact hst
      · simp only [HeldM.run_bind, refresh_run]
        split
        · exact hst
        · simp only [HeldM.run_bind]
          generalize HeldM.run (Conn.tickGive _ _ _ _ now) h' = S1
          have g1 := apply_managed S s st.1 b.1 S1.1 now S1.2 hst
          generalize HeldM.run (Node.apply (S.sync s) st.1 b.1 S1.1 now) S1.2 = B at g1 ⊢
          rw [sweep_none _ rfl]
          simp only [HeldM.run_pure]
          simp only [ForInStep.value]
          rw [serveOwed_managed]
          exact g1)
  exact finish_managed S s _ _ now _ pR

end

/-! ## Over every execution -/

namespace Plain
variable {Q : Plain F}

/-- **Everything the World runs at a plain node keeps it managing no
session**: every entry point, and a restart, which boots with none. -/
theorem managed_local : Local Q.setup (fun _ n _ => n.managed = []) (fun _ n _ => n.managed = []) where
  runs i f hf nd h hm := by
    cases hf with
    | frame addr bytes t => exact onFrame_managed (Q.two i) .a nd addr bytes t h hm
    | tick t => exact onTick_managed (Q.two i) .a nd t h hm
    | write ops t _ => exact onWrite_managed (Q.two i) .a nd ops t h hm
    | close addr t => exact onClose_managed (Q.two i) .a nd addr t h hm
    | connect j cid dialer t _ => exact connect_managed (Q.two i) .a nd cid _ dialer t h hm
  boot _ _ _ _ := rfl

/-- **No plain node ever manages a session**, in any execution against
any attacker, from nodes that manage none. -/
theorem managed_nil {adv : World (Held F) Q.n → ByteArray → Prop} {w₀ : World (Held F) Q.n}
    (E : Exec Q.setup adv w₀) (h0 : ∀ i, (w₀.node i).managed = []) : ∀ k i, ((E.world k).node i).managed = [] :=
  managed_local.keeps.always h0 E

end Plain

end Engine.World
