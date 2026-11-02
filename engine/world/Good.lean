/-
**Good worlds: the skeleton of the top theorem** (docs/GOOD.md).

    Good w → Legal P adv w a → Good (w.step P a)      so      Good w₀ → ∀ k, Good (E.world k)

for any World setup `P`: any node monad, any hooks, any attacker. `Good`
is a conjunction of two kinds of conjunct:

- **node-local** (`Local`): a property of one node and its box, kept by
  every entry point the World runs at that node (`Runs`) and restored by
  a restart. It is about the node alone, so it holds whichever World runs
  the node and whatever bytes reach it.
- **world-level** (`Keeps`): a property of the network or the wire, kept
  by every legal step.

Each conjunct may assume all of them before the step (assume-guarantee):
`Local.and` and `Keeps.and` assemble conjuncts, each proven under the
whole, and `good_keeps` joins the two kinds. `Keeps.reach` and
`Keeps.always` lift the result to every reachable world and every
execution. A step guarantee (`Guar`: how a world relates to the next,
such as "stores move only by turns and purges") rides along
(`Guar.always`); `Boxes` is its node-local form.

All of it rests on one fact about the step (`step_touch`): a step
touches at most one node, by one entry point or a restart.

`Sent` is the first world-level conjunct, for any setup: every packet in
flight was sent no later than the world's clock.
-/
import engine.world.World

namespace Engine.World
open Engine Engine.Sync

variable {F : Type} {M : Type → Type} {S : Type} [Monad M] [Store F M] [Turn F M]

/-! ## What a step does to a node -/

/-- **What the World runs at node i**: the entry points `World.step`
hands `World.enter`, with what `Legal` asks of them (an honest write, the
harness's connect). -/
inductive Runs (P : Setup F M S) (i : Fin P.n) : (Node → M (Node × Effects)) → Prop
  | frame (addr bytes : ByteArray) (t : Nat) : Runs P i fun nd => nd.onFrame (P.sync i) addr bytes t
  | tick (t : Nat) : Runs P i fun nd => nd.onTick (P.sync i) t
  | write (ops : List Op) (t : Nat) : P.honest i ops → Runs P i fun nd => nd.onWrite (P.sync i) ops t
  | close (addr : ByteArray) (t : Nat) : Runs P i fun nd => nd.onClose (P.sync i) addr t
  | connect (j : Fin P.n) (cid : Id) (dialer : Bool) (t : Nat) : P.harness = true →
      Runs P i fun nd => nd.connect (P.sync i) cid (P.addr j) dialer t

/-- Node i booted again from what survives a crash of box s. -/
def Setup.reboot (P : Setup F M S) (i : Fin P.n) (s : S) : Node :=
  Node.boot (P.sync i).fam (P.held (P.crash s)).log (P.floor i)

/-- What a step may do to node i and its box: nothing, run one entry
point there, or restart it. -/
inductive Touch (P : Setup F M S) (i : Fin P.n) : Node × S → Node × S → Prop
  | same (x : Node × S) : Touch P i x x
  | runs (f : Node → M (Node × Effects)) (nd : Node) (s : S) : Runs P i f →
      Touch P i (nd, s) ((P.run (f nd) s).1.1, (P.run (f nd) s).2)
  | boot (nd : Node) (s : S) : Touch P i (nd, s) (P.reboot i s, P.crash s)

theorem enter_touch {P : Setup F M S} (w : World S P.n) (i : Fin P.n) (t : Nat)
    (f : Node → M (Node × Effects)) (hf : Runs P i f) (l : Fin P.n) :
    Touch P l (w.node l, w.box l) ((w.enter P i t f).node l, (w.enter P i t f).box l) := by
  simp only [World.enter]
  by_cases e : l = i
  · subst e; simp only [upd_same]; exact .runs f _ _ hf
  · rw [upd_other _ _ e, upd_other _ _ e]; exact .same _

/-- **A legal step touches each node at most by one entry point or a
restart**: deliveries and injections run `onFrame`, ticks `onTick`,
writes `onWrite`, closes `onClose`, the harness `connect`; duplicates and
drops touch no node. -/
theorem step_touch {P : Setup F M S} {adv : World S P.n → ByteArray → Prop} (w : World S P.n)
    (a : Act P.n) (hl : Legal P adv w a) (l : Fin P.n) :
    Touch P l (w.node l, w.box l) ((w.step P a).node l, (w.step P a).box l) := by
  cases a with
  | deliver k t =>
    simp only [World.step]
    cases w.flight[k]? with
    | none => exact .same _
    | some p =>
      dsimp only
      cases P.at? p.dst with
      | none => exact .same _
      | some j => exact enter_touch _ j t _ (.frame p.origin p.bytes t) l
  | dup k => simp only [World.step]; cases w.flight[k]? <;> exact .same _
  | drop k => exact .same _
  | tick i t => exact enter_touch w i t _ (.tick t) l
  | write i ops t => exact enter_touch w i t _ (.write ops t hl.2) l
  | restart i t =>
    simp only [World.step]
    by_cases e : l = i
    · subst e; simp only [upd_same]; exact .boot _ _
    · rw [upd_other _ _ e, upd_other _ _ e]; exact .same _
  | close i addr t => exact enter_touch w i t _ (.close addr t) l
  | connect i j cid dialer t => exact enter_touch w i t _ (.connect j cid dialer t hl.1) l
  | inject i origin b t => exact enter_touch w i t _ (.frame origin b t) l

/-! ## Conjuncts and their lifting -/

section
variable {P : Setup F M S} {adv : World S P.n → ByteArray → Prop}

/-- **A node-local conjunct** Φ, kept under G: every entry point the
World runs at node i takes a node and box satisfying G to ones satisfying
Φ, and so does a restart. `Local P G G` is a node invariant. -/
structure Local (P : Setup F M S) (G Φ : Fin P.n → Node → S → Prop) : Prop where
  runs : ∀ i f, Runs P i f → ∀ nd s, G i nd s → Φ i (P.run (f nd) s).1.1 (P.run (f nd) s).2
  boot : ∀ i nd s, G i nd s → Φ i (P.reboot i s) (P.crash s)

/-- Every node of w, with its box, satisfies Φ. -/
def Nodes (P : Setup F M S) (Φ : Fin P.n → Node → S → Prop) (w : World S P.n) : Prop :=
  ∀ i, Φ i (w.node i) (w.box i)

/-- **A world-level conjunct** C, kept under G: every legal step from a
world satisfying G reaches one satisfying C. -/
def Keeps (P : Setup F M S) (adv : World S P.n → ByteArray → Prop) (G C : World S P.n → Prop) : Prop :=
  ∀ w a, G w → Legal P adv w a → C (w.step P a)

/-- **A step guarantee** R, under G: every legal step from a world
satisfying G relates it to the next by R. -/
def Guar (P : Setup F M S) (adv : World S P.n → ByteArray → Prop) (G : World S P.n → Prop)
    (R : World S P.n → World S P.n → Prop) : Prop :=
  ∀ w a, G w → Legal P adv w a → R w (w.step P a)

/-- **A node-local step guarantee** R, under G: R relates a box to itself,
and a box to the box after any entry point the World runs there, or after
a crash, from a node and box satisfying G. -/
structure Boxes (P : Setup F M S) (G : Fin P.n → Node → S → Prop) (R : Fin P.n → S → S → Prop) : Prop where
  refl : ∀ i s, R i s s
  runs : ∀ i f, Runs P i f → ∀ nd s, G i nd s → R i s (P.run (f nd) s).2
  crash : ∀ i nd s, G i nd s → R i s (P.crash s)

theorem Local.mono {G G' Φ : Fin P.n → Node → S → Prop} (L : Local P G Φ) (h : ∀ i nd s, G' i nd s → G i nd s) :
    Local P G' Φ :=
  ⟨fun i f hf nd s g => L.runs i f hf nd s (h i nd s g), fun i nd s g => L.boot i nd s (h i nd s g)⟩

theorem Local.and {G Φ Ψ : Fin P.n → Node → S → Prop} (L₁ : Local P G Φ) (L₂ : Local P G Ψ) :
    Local P G fun i nd s => Φ i nd s ∧ Ψ i nd s :=
  ⟨fun i f hf nd s g => ⟨L₁.runs i f hf nd s g, L₂.runs i f hf nd s g⟩,
   fun i nd s g => ⟨L₁.boot i nd s g, L₂.boot i nd s g⟩⟩

theorem Keeps.mono {G G' C : World S P.n → Prop} (hk : Keeps P adv G C) (h : ∀ w, G' w → G w) :
    Keeps P adv G' C :=
  fun w a g hl => hk w a (h w g) hl

theorem Keeps.and {G C D : World S P.n → Prop} (h₁ : Keeps P adv G C) (h₂ : Keeps P adv G D) :
    Keeps P adv G fun w => C w ∧ D w :=
  fun w a g hl => ⟨h₁ w a g hl, h₂ w a g hl⟩

/-- **A node invariant is a world invariant**: node by node, by
`step_touch`. -/
theorem Local.keeps {G : Fin P.n → Node → S → Prop} (L : Local P G G) : Keeps P adv (Nodes P G) (Nodes P G) := by
  intro w a hw hl i
  generalize ht : ((w.step P a).node i, (w.step P a).box i) = y
  have h := step_touch w a hl i
  rw [ht] at h
  obtain ⟨nd', s'⟩ := y
  have e1 : (w.step P a).node i = nd' := congrArg Prod.fst ht
  have e2 : (w.step P a).box i = s' := congrArg Prod.snd ht
  rw [e1, e2]
  cases h with
  | same => exact hw i
  | runs f nd s hf => exact L.runs i f hf _ _ (hw i)
  | boot nd s => exact L.boot i _ _ (hw i)

/-- **A node-local step guarantee is a world step guarantee.** -/
theorem Boxes.guar {G : Fin P.n → Node → S → Prop} {R : Fin P.n → S → S → Prop} (B : Boxes P G R) :
    Guar P adv (Nodes P G) fun w w' => ∀ i, R i (w.box i) (w'.box i) := by
  intro w a hw hl i
  generalize ht : ((w.step P a).node i, (w.step P a).box i) = y
  have h := step_touch w a hl i
  rw [ht] at h
  obtain ⟨nd', s'⟩ := y
  have e2 : (w.step P a).box i = s' := congrArg Prod.snd ht
  rw [e2]
  cases h with
  | same => exact B.refl i _
  | runs f nd s hf => exact B.runs i f hf _ _ (hw i)
  | boot nd s => exact B.crash i _ _ (hw i)

/-- **A world kept good is good everywhere a legal run reaches.** -/
theorem Keeps.reach {G : World S P.n → Prop} {w₀ w : World S P.n} (hk : Keeps P adv G G) (h0 : G w₀)
    (hr : Reachable P adv w₀ w) : G w := by
  induction hr with
  | init => exact h0
  | step _ hl ih => exact hk _ _ ih hl

/-- **... and at every step of every execution.** -/
theorem Keeps.always {G : World S P.n → Prop} {w₀ : World S P.n} (hk : Keeps P adv G G) (h0 : G w₀)
    (E : Exec P adv w₀) (k : Nat) : G (E.world k) :=
  hk.reach h0 (E.reachable k)

/-- **A step guarantee holds of every step of every execution** whose
worlds stay good. -/
theorem Guar.always {G : World S P.n → Prop} {R : World S P.n → World S P.n → Prop} {w₀ : World S P.n}
    (hk : Keeps P adv G G) (hR : Guar P adv G R) (h0 : G w₀) (E : Exec P adv w₀) (k : Nat) :
    R (E.world k) (E.world (k + 1)) :=
  hR _ _ (hk.always h0 E k) (E.legal k)

/-- **A good world**: every node good (the node-local conjuncts N), and
the world-level conjuncts W. -/
def Good (P : Setup F M S) (N : Fin P.n → Node → S → Prop) (W : World S P.n → Prop) (w : World S P.n) : Prop :=
  Nodes P N w ∧ W w

/-- **The top theorem's shape: a good world steps to a good world.**
Node-local conjuncts kept by every entry point and restart, and
world-level conjuncts kept by every legal step from a good world. -/
theorem good_keeps {N : Fin P.n → Node → S → Prop} {W : World S P.n → Prop} (L : Local P N N)
    (hW : Keeps P adv (Good P N W) W) : Keeps P adv (Good P N W) (Good P N W) :=
  fun w a g hl => ⟨L.keeps w a g.1 hl, hW w a g hl⟩

end

/-! ## The first world-level conjunct: packets were sent in the past -/

/-- Every packet in flight was sent no later than the world's clock. -/
def Sent {n : Nat} (w : World S n) : Prop := ∀ p ∈ w.flight, p.sent ≤ w.now

theorem mem_packets_sent {n : Nat} (i : Fin n) (origin : ByteArray) (t : Nat) :
    ∀ (s : Nat) (L : List (ByteArray × ByteArray)) (p : Packet n), p ∈ packets i origin t s L → p.sent = t
  | _, [], _, h => by cases h
  | s, _ :: rest, p, h => by
    simp only [packets, List.mem_cons] at h
    rcases h with rfl | h
    · rfl
    · exact mem_packets_sent i origin t (s + 1) rest p h

theorem enter_sent {P : Setup F M S} (w : World S P.n) (i : Fin P.n) (t : Nat) (f : Node → M (Node × Effects))
    (hw : ∀ p ∈ w.flight, p.sent ≤ t) : Sent (w.enter P i t f) := by
  intro p hp
  simp only [World.enter] at hp ⊢
  rcases List.mem_append.1 hp with hp | hp
  · exact hw p hp
  · exact Nat.le_of_eq (mem_packets_sent i _ t _ _ p hp)

/-- **Every legal step keeps packets sent in the past**, in any World:
time never goes back, a duplicate is sent now, and an entry point's
packets are sent at its time. -/
theorem sent_keeps {P : Setup F M S} {adv : World S P.n → ByteArray → Prop} : Keeps P adv Sent Sent := by
  intro w a hw hl
  have up : ∀ t, w.now ≤ t → ∀ p ∈ w.flight, p.sent ≤ t := fun t ht p hp => Nat.le_trans (hw p hp) ht
  cases a with
  | deliver k t =>
    simp only [World.step]
    cases w.flight[k]? with
    | none => exact hw
    | some p =>
      dsimp only
      have hk : ∀ q ∈ w.flight.eraseIdx k, q.sent ≤ t := fun q hq => up t hl.2 q (List.mem_of_mem_eraseIdx hq)
      cases P.at? p.dst with
      | none => exact hk
      | some j =>
        exact enter_sent { w with flight := w.flight.eraseIdx k } j t
          (fun nd => nd.onFrame (P.sync j) p.origin p.bytes t) hk
  | dup k =>
    simp only [World.step]
    cases w.flight[k]? with
    | none => exact hw
    | some p =>
      intro q hq
      rcases List.mem_append.1 hq with hq | hq
      · exact hw q hq
      · simp only [List.mem_singleton] at hq; subst hq; exact Nat.le_refl _
  | drop k => intro q hq; exact hw q (List.mem_of_mem_eraseIdx hq)
  | tick i t => exact enter_sent w i t _ (up t hl)
  | write i ops t => exact enter_sent w i t (fun nd => nd.onWrite (P.sync i) ops t) (up t hl.1)
  | restart i t => exact up t hl
  | close i addr t => exact enter_sent w i t _ (up t hl)
  | connect i j cid dialer t => exact enter_sent w i t _ (up t hl.2)
  | inject i origin b t => exact enter_sent w i t (fun nd => nd.onFrame (P.sync i) origin b t) (up t hl.2)

end Engine.World
