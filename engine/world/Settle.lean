/-
Waiting ops close, proven of the running code (`waiting_closure_proof`):
at every world reached, every node's store is at rest and its verdicts
are the spec's over the ops it holds, so an op that waited on a missing
requirement is judged in the very step that brings the last of them.
Then two nodes holding the same ops judge alike (`local_verdicts`), and
a node holding another's closure of x judges x alike
(`closure_agree_proof`).

- A held store is a state the engine reaches from its log
  (`Settled`), and every write turn drains it to rest: the turn's budget
  is the engine's `budget` over the log (`budget_congr`), so holmes-a3's
  and the engine's `drain_bounded` applies (`turnH_settled`).
- Only write turns change a store, so every entry point keeps `Settled`
  (`Settles`, the `settles` tactic, as `grows` does for growth).
-/
import engine.world.Idem
import engine.core.Termination
import engine.core.Locality
namespace Engine.World
open Engine Engine.Sync
variable {F : Type}

/-! ## The engine's view of a held store -/

theorem nodup_eraseDups : ∀ (n : Nat) (l : List Op), l.length ≤ n → l.eraseDups.Nodup
  | _, [], _ => by simp
  | 0, _ :: _, h => by simp at h
  | n + 1, a :: as, h => by
    rw [List.eraseDups_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_eraseDups n _ (by
      have := List.length_filter_le (fun b => !b == a) as; simp at h; omega)⟩
    rw [List.mem_eraseDups, List.mem_filter] at hm
    simp at hm

/-- The budget reads only which ops a list names. -/
theorem budget_congr (fam : Family F) {A B : List Op} (s : DB F) (hab : ∀ o, o ∈ A ↔ o ∈ B) :
    budget A s = budget B s := by
  have hp : A.eraseDups.Perm B.eraseDups := by
    rw [List.perm_ext_iff_of_nodup (nodup_eraseDups _ A (Nat.le_refl _)) (nodup_eraseDups _ B (Nat.le_refl _))]
    intro o; rw [List.mem_eraseDups, List.mem_eraseDups]; exact hab o
  unfold budget undecided
  rw [hp.length_eq, (hp.filter _).length_eq]

theorem reach_foldl_ingest (fam : Family F) (ops : List Op) : ∀ (L : List Op) (s : DB F), Engine.Reach fam L s →
    Engine.Reach fam (ops.reverse ++ L) (ops.foldl (fun s o => ingestS o s) s) := by
  induction ops with
  | nil => intro L s h; simpa using h
  | cons o t ih =>
    intro L s h
    have := ih (o :: L) _ (Engine.Reach.ingest o h)
    simpa [List.reverse_cons, List.append_assoc] using this

/-- A held store the engine reaches from its log, at rest whenever its
log has no collision. -/
def Settled (fam : Family F) (h : Held F) : Prop :=
  Engine.Reach fam h.log.reverse h.db ∧ (CollisionFree h.log → h.db.queue = [])

theorem collisionFree_reverse {L : List Op} (h : CollisionFree L) : CollisionFree L.reverse :=
  fun a ha b hb e => h a (List.mem_reverse.1 ha) b (List.mem_reverse.1 hb) e

/-- **A write turn keeps a held store settled.** -/
theorem turnH_settled (fam : Family F) (ops : List Op) (h : Held F) (hs : Settled fam h) :
    Settled fam (turnH fam ops h) := by
  have hr : Engine.Reach fam (h.log ++ ops).reverse (ops.foldl (fun s o => ingestS o s) h.db) := by
    rw [List.reverse_append]; exact reach_foldl_ingest fam ops _ _ hs.1
  refine ⟨reach_drain hr _, fun hc => ?_⟩
  simp only [turnH] at hc ⊢
  apply drain_bounded (distinct_of_collisionFree (collisionFree_reverse hc)) _ _ hr
  rw [budget_congr fam _ (fun o => List.mem_reverse)]
  exact Nat.le_refl _

/-! ## Every entry point keeps a store settled -/

/-- p keeps a settled store settled. -/
def Settles (fam : Family F) {α} (p : HeldM F α) : Prop := ∀ h, Settled fam h → Settled fam (p.run h).2

theorem Keeps.settles (fam : Family F) {α} {p : HeldM F α} (hp : Keeps p) : Settles fam p := fun h hs => by
  rw [hp h]; exact hs
theorem Settles.pure' (fam : Family F) {α} (a : α) : Settles fam (pure a : HeldM F α) := fun _ h => h
theorem Settles.bind' (fam : Family F) {α β} {m : HeldM F α} {k : α → HeldM F β} (hm : Settles fam m)
    (hk : ∀ a, Settles fam (k a)) : Settles fam (m >>= k) := fun h hs => by
  simp only [HeldM.run_bind]; exact hk _ _ (hm h hs)
theorem Settles.forIn' (fam : Family F) {α β} (l : List α) (b : β) {f : α → β → HeldM F (ForInStep β)}
    (hf : ∀ a b, Settles fam (f a b)) : Settles fam (forIn l b f) := by
  induction l generalizing b with
  | nil => exact Settles.pure' fam b
  | cons a t ih =>
    intro h hs
    rw [List.forIn_cons, HeldM.run_bind]
    have h1 := hf a b h hs
    cases ((f a b).run h).1 with
    | done b' => exact h1
    | yield b' => exact ih b' _ h1
theorem Settles.range' (fam : Family F) {β} (r : Std.Legacy.Range) (b : β) {f : Nat → β → HeldM F (ForInStep β)}
    (hf : ∀ a b, Settles fam (f a b)) : Settles fam (forIn r b f) := by
  intro h; rw [Std.Legacy.Range.forIn_eq_forIn_range']; exact Settles.forIn' fam _ b hf h
theorem Settles.getOp' (fam : Family F) (x : Id) : Settles fam (Store.getOp (F := F) x : HeldM F _) :=
  Keeps.settles fam (Keeps.getOp' x)
theorem Settles.getStatus' (fam : Family F) (x : Id) : Settles fam (Store.getStatus (F := F) x : HeldM F _) :=
  Keeps.settles fam (Keeps.getStatus' x)
theorem Settles.read' (fam : Family F) {α} (f : Held F → α) : Settles fam (readH f) :=
  Keeps.settles fam (Keeps.read' f)
theorem Settles.turn' (fam : Family F) (ops : List Op) : Settles fam (Turn.turn fam ops : HeldM F Unit) := fun h hs => by
  rw [HeldM.run_turn]; exact turnH_settled fam ops h hs

/-- Prove `Settles` of a do block from its structure, with these lemmas
for the calls in it. -/
syntax "settles" "[" term,* "]" : tactic

macro_rules
  | `(tactic| settles [$ts,*]) => do
    let mut tac : Lean.TSyntax `tactic ← `(tactic| first | split | intro)
    for t in ts.getElems.reverse do
      tac ← `(tactic| first | with_reducible_and_instances apply $t | $tac:tactic)
    `(tactic| repeat' (concrete_goal; first
      | dsimp only | with_reducible_and_instances apply Settles.bind'
      | with_reducible_and_instances apply Settles.pure' | with_reducible_and_instances apply Settles.forIn'
      | with_reducible_and_instances apply Settles.range'
      | with_reducible_and_instances apply Settles.getOp' | with_reducible_and_instances apply Settles.getStatus'
      | with_reducible_and_instances apply Settles.turn' | with_reducible_and_instances apply Settles.read'
      | $tac:tactic))

section
variable (fam : Family F) (cfg : Config) (rms : Held F → Id → List Id)

theorem write_settles (n : Node) (ops : List Op) : Settles fam (n.write (psync fam cfg rms) ops) := by
  unfold Node.write; simp only [psync_fam]; settles []

theorem put_settles (n : Node) (ops : List Op) (mine : Bool) : Settles fam (n.put (psync fam cfg rms) ops mine) :=
  write_settles fam cfg rms n _

theorem settle_settles (n : Node) (st : List (Id × Status)) : Settles fam (n.settle (psync fam cfg rms) st) := by
  unfold Node.settle; settles [put_settles]

theorem fanout_settles (n : Node) (ids : List Id) : Settles fam (n.fanout (psync fam cfg rms) ids) := by
  unfold Node.fanout; simp only [psync_rooms, Node.refresh, psync_fam, psync_cfg]
  settles [settle_settles, Keeps.settles fam (filed_keeps fam cfg _ _)]

theorem store_settles (n : Node) (ops : List Op) (mine : Bool) : Settles fam (n.store (psync fam cfg rms) ops mine) := by
  unfold Node.store; simp only [psync_react]
  settles [put_settles, fanout_settles]

theorem apply_settles (n : Node) (cid : Id) (s : Step) (now : Nat) : Settles fam (n.apply (psync fam cfg rms) cid s now) := by
  unfold Node.apply; simp only [psync_recv]
  settles [settle_settles, store_settles]

theorem seal_settles (n : Node) (out : Acts) : Settles fam (n.seal (psync fam cfg rms) out) := by
  unfold Node.seal; simp only [psync_sealFor]; settles []

theorem open_settles (n : Node) (cid : Id) (a : ByteArray) (d : Bool) (now : Nat) :
    Settles fam (n.open (psync fam cfg rms) cid a d now) := by
  unfold Node.open; simp only [psync_rooms]; settles []

theorem finish_settles (n : Node) (out : Acts) (now : Nat) : Settles fam (n.finish (psync fam cfg rms) out now) := by
  unfold Node.finish Node.follow Node.flush Node.endSession
  simp only [psync_established, psync_outbox, psync_retired, psync_closing, HeldM.pure_bind,
    List.isEmpty_nil, ite_true, List.append_nil, Bool.not_true, Bool.false_eq_true, ite_false]
  settles [seal_settles, open_settles]

theorem onWrite_settles (n : Node) (ops : List Op) (now : Nat) : Settles fam (n.onWrite (psync fam cfg rms) ops now) := by
  unfold Node.onWrite; settles [store_settles, finish_settles]

theorem connect_settles (n : Node) (cid : Id) (a : ByteArray) (d : Bool) (now : Nat) :
    Settles fam (n.connect (psync fam cfg rms) cid a d now) := by
  unfold Node.connect; settles [open_settles, finish_settles]

variable (hw : WalkLaws (F := F) fam cfg)
include hw

theorem onSealed_settles (n : Node) (a : ByteArray) (o : Option (Id × ByteArray)) (now : Nat) :
    Settles fam (n.onSealed (psync fam cfg rms) a o now) := by
  unfold Node.onSealed; simp only [Node.refresh, psync_rooms, psync_fam, psync_cfg]
  settles [finish_settles, apply_settles, Keeps.settles fam (recv_keeps fam cfg hw _ _ _ _)]

theorem onFrame_settles (n : Node) (a b : ByteArray) (now : Nat) : Settles fam (n.onFrame (psync fam cfg rms) a b now) := by
  unfold Node.onFrame; simp only [psync_openFrame, psync_recv]
  settles [write_settles, store_settles, finish_settles, onSealed_settles fam cfg rms hw]

theorem onTick_settles (n : Node) (now : Nat) : Settles fam (n.onTick (psync fam cfg rms) now) := by
  unfold Node.onTick; simp only [psync_dial, Node.refresh, psync_rooms, psync_fam, psync_cfg]
  settles [store_settles, finish_settles, apply_settles, Keeps.settles fam (tick_keeps fam cfg hw _ _ _)]

end


/-! ## In every reachable world -/

theorem enter_settled (Q : Plain F) (w : World (Held F) Q.n) (i : Fin Q.n) (t : Nat)
    (f : Node → HeldM F (Node × Effects)) (hf : Settles Q.fam (f (w.node i)))
    (hs : ∀ j, Settled Q.fam (w.box j)) : ∀ j, Settled Q.fam ((w.enter Q.setup i t f).box j) := by
  intro j
  simp only [World.enter, upd]
  by_cases e : j = i
  · subst e; simp only [ite_true]; exact hf _ (hs j)
  · simp only [e, ite_false]; exact hs j

theorem reach_settled' (Q : Plain F) (hw : WalkLaws (F := F) Q.fam Q.cfg)
    (adv : World (Held F) Q.setup.n → ByteArray → Prop) (w₀ w : World (Held F) Q.setup.n)
    (h0 : ∀ i, Settled Q.fam (w₀.box i)) (hr : Reachable Q.setup adv w₀ w) : ∀ i, Settled Q.fam (w.box i) := by
  induction hr with
  | init => exact h0
  | @step w a _ _ ih =>
    cases a with
    | deliver k t =>
      simp only [World.step]
      split
      · exact ih
      · rename_i p _
        split
        · exact ih
        · rename_i j' _
          exact enter_settled Q { w with flight := w.flight.eraseIdx k } j' t
            (fun nd => nd.onFrame (psync Q.fam Q.cfg (Q.rooms j')) p.origin p.bytes t)
            (onFrame_settles Q.fam Q.cfg (Q.rooms j') hw _ _ _ _) ih
    | dup k => simp only [World.step]; split <;> exact ih
    | drop k => exact ih
    | tick i t =>
      exact enter_settled Q w i t (fun nd => nd.onTick (psync Q.fam Q.cfg (Q.rooms i)) t)
        (onTick_settles Q.fam Q.cfg (Q.rooms i) hw _ _) ih
    | write i ops t =>
      exact enter_settled Q w i t (fun nd => nd.onWrite (psync Q.fam Q.cfg (Q.rooms i)) ops t)
        (onWrite_settles Q.fam Q.cfg (Q.rooms i) _ _ _) ih
    | restart i t =>
      intro j
      simp only [World.step, upd]
      by_cases e : j = i
      · subst e; simp only [ite_true]; exact ih j
      · simp only [e, ite_false]; exact ih j
    | connect i j cid d t =>
      exact enter_settled Q w i t (fun nd => nd.connect (psync Q.fam Q.cfg (Q.rooms i)) cid (Q.setup.addr j) d t)
        (connect_settles Q.fam Q.cfg (Q.rooms i) _ _ _ _ _) ih
    | inject i o b t =>
      exact enter_settled Q w i t (fun nd => nd.onFrame (psync Q.fam Q.cfg (Q.rooms i)) o b t)
        (onFrame_settles Q.fam Q.cfg (Q.rooms i) hw _ _ _ _) ih

/-- **Every node's store, in every world the plain world reaches, is a
state the engine reaches from its log, at rest when the log has no
collision.** -/
theorem reach_settled (Q : Plain F) (adv : World (Held F) Q.n → ByteArray → Prop) (w : World (Held F) Q.n)
    (hr : Q.Reach adv w) : ∀ i, Settled Q.fam (w.box i) :=
  reach_settled' Q (walk_proof F Q.fam Q.cfg) adv Q.start w (fun _ => ⟨Engine.Reach.empty, fun _ => rfl⟩) hr

/-- **Waiting ops close, proven of the running code.** -/
theorem waiting_closure_proof : waiting_closure_stmt := by
  intro F Q adv w hr i hc
  have hs := reach_settled Q adv w hr i
  have hq := hs.2 hc
  exact ⟨hq, fun x v => status_iff_spec (reach_inv hs.1) hq x v⟩

/-- **Nodes holding a closure judge alike, proven of the running code.** -/
theorem closure_agree_proof : closure_agree_stmt := by
  intro F Q adv w hr i j x v hci hcj hold hv
  have si := reach_settled Q adv w hr i
  have sj := reach_settled Q adv w hr j
  have hspec := (status_iff_spec (reach_inv si.1) (si.2 hci) x v).1 hv
  exact (status_iff_spec (reach_inv sj.1) (sj.2 hcj) x v).2 (spec_local (fam := Q.fam) hspec hold)

/-- **Two nodes holding the same ops judge every op alike** (L-local's
verdict half). -/
theorem local_verdicts (Q : Plain F) (adv : World (Held F) Q.n → ByteArray → Prop) (w : World (Held F) Q.n)
    (hr : Q.Reach adv w) (i j : Fin Q.n) (hci : CollisionFree (w.box i).log) (hcj : CollisionFree (w.box j).log)
    (he : ∀ x, (w.box i).db.ops x = (w.box j).db.ops x) : ∀ x, (w.box i).db.status x = (w.box j).db.status x := by
  have si := reach_settled Q adv w hr i
  have sj := reach_settled Q adv w hr j
  have hops : (w.box i).db.ops = (w.box j).db.ops := funext he
  intro x
  cases ei : (w.box i).db.status x with
  | none =>
    cases ej : (w.box j).db.status x with
    | none => rfl
    | some v =>
      have := (status_iff_spec (reach_inv sj.1) (sj.2 hcj) x v).1 ej
      rw [← hops] at this
      rw [(status_iff_spec (reach_inv si.1) (si.2 hci) x v).2 this] at ei; cases ei
  | some v =>
    have := (status_iff_spec (reach_inv si.1) (si.2 hci) x v).1 ei
    rw [hops] at this
    exact ((status_iff_spec (reach_inv sj.1) (sj.2 hcj) x v).2 this).symm

end Engine.World
