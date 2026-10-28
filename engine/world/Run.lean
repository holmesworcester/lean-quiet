/-
Running node code on a held store, as rewrite rules: each entry point
run on a `Held` store is rewritten lemma by lemma (`HeldM.run_bind` and
the loop lemmas) until its result is a term. Most of what a node does
leaves the store as it is (`Keeps`); the `keeps` tactic proves that from
a do block's structure. After holmes-a3's two-node world (a3/world,
WorldLaws.lean), on which these are modelled.
-/
import engine.world.World

namespace Engine.World
open Engine Engine.Sync

variable {F : Type}

@[simp] theorem HeldM.run_bind {α β} (m : HeldM F α) (k : α → HeldM F β) (h : Held F) :
    (m >>= k).run h = (k (m.run h).1).run (m.run h).2 := rfl
@[simp] theorem HeldM.run_pure {α} (a : α) (h : Held F) : (pure a : HeldM F α).run h = (a, h) := rfl
@[simp] theorem HeldM.pure_bind {α β} (a : α) (k : α → HeldM F β) : (pure a >>= k) = k a := rfl
@[simp] theorem HeldM.run_getOp (x : Id) (h : Held F) :
    (Store.getOp (F := F) x : HeldM F _).run h = (h.db.ops x, h) := rfl
@[simp] theorem HeldM.run_getStatus (x : Id) (h : Held F) :
    (Store.getStatus (F := F) x : HeldM F _).run h = (h.db.status x, h) := rfl

/-- The held store after a write turn of these ops. -/
def turnH (fam : Family F) (ops : List Op) (h : Held F) : Held F :=
  let s := ops.foldl (fun s o => ingestS o s) h.db
  { log := h.log ++ ops, db := drainS fam (budget (h.log ++ ops) s) s }

@[simp] theorem HeldM.run_turn (fam : Family F) (ops : List Op) (h : Held F) :
    (Turn.turn fam ops : HeldM F Unit).run h = ((), turnH fam ops h) := rfl

@[simp] theorem Conn.finish_send (s : Step) : (Conn.finish s).send = s.send := rfl
@[simp] theorem Conn.finish_take (s : Step) : (Conn.finish s).take = s.take := rfl
@[simp] theorem Conn.finish_drop (s : Step) : (Conn.finish s).drop = s.drop := rfl

/-! ## Loops -/

/-- A loop whose every turn keeps the store keeps it. -/
theorem forIn_keeps {α β} (l : List α) (f : α → β → HeldM F (ForInStep β)) (h : Held F)
    (hf : ∀ a ∈ l, ∀ b, ((f a b).run h).2 = h) (b : β) : ((forIn l b f).run h).2 = h := by
  induction l generalizing b with
  | nil => rfl
  | cons a t ih =>
    rw [List.forIn_cons, HeldM.run_bind, hf a (List.mem_cons_self ..)]
    cases ((f a b).run h).1 with
    | done b => rfl
    | yield b => exact ih (fun a ha => hf a (List.mem_cons_of_mem _ ha)) b

/-! ## Steps that keep the store -/

/-- A step that leaves the store as it is, from any store. -/
def Keeps {α} (p : HeldM F α) : Prop := ∀ h, (p.run h).2 = h

theorem Keeps.pure' {α} (a : α) : Keeps (pure a : HeldM F α) := fun _ => rfl
theorem Keeps.bind' {α β} {m : HeldM F α} {k : α → HeldM F β} (hm : Keeps m) (hk : ∀ a, Keeps (k a)) :
    Keeps (m >>= k) := by
  intro h; simp only [HeldM.run_bind]; rw [hk, hm]
theorem Keeps.forIn' {α β} (l : List α) (b : β) {f : α → β → HeldM F (ForInStep β)}
    (hf : ∀ a b, Keeps (f a b)) : Keeps (forIn l b f) :=
  fun h => forIn_keeps l f h (fun a _ b => hf a b h) b
theorem Keeps.range' {β} (r : Std.Legacy.Range) (b : β) {f : Nat → β → HeldM F (ForInStep β)}
    (hf : ∀ a b, Keeps (f a b)) : Keeps (forIn r b f) := by
  intro h; rw [Std.Legacy.Range.forIn_eq_forIn_range']; exact Keeps.forIn' _ b hf h
theorem Keeps.getOp' (x : Id) : Keeps (Store.getOp (F := F) x : HeldM F _) := fun _ => rfl
theorem Keeps.getStatus' (x : Id) : Keeps (Store.getStatus (F := F) x : HeldM F _) := fun _ => rfl

/-- Prove `Keeps` of a do block from its structure, with these `Keeps`
lemmas for the calls in it. -/
syntax "keeps" "[" term,* "]" : tactic

macro_rules
  | `(tactic| keeps [$ts,*]) => do
    let mut tac : Lean.TSyntax `tactic ← `(tactic| first | split | intro)
    for t in ts.getElems.reverse do
      tac ← `(tactic| first | with_reducible_and_instances apply $t | $tac:tactic)
    `(tactic| repeat' (first
      | dsimp only | with_reducible_and_instances apply Keeps.bind'
      | with_reducible_and_instances apply Keeps.pure' | with_reducible_and_instances apply Keeps.forIn'
      | with_reducible_and_instances apply Keeps.range'
      | with_reducible_and_instances apply Keeps.getOp' | with_reducible_and_instances apply Keeps.getStatus'
      | $tac:tactic))

section
variable (fam : Family F) (cfg : Config)

/-- **The closure walk only reads**, now that it is a loop over a range. -/
theorem walk_keeps (c : Conn) : Keeps (c.walk fam cfg : HeldM F (Conn × List Id)) := by
  unfold Conn.walk; keeps []

theorem filed_keeps (c : Conn) (ids : List Id) : Keeps (c.filed fam cfg ids : HeldM F Step) := by
  unfold Conn.filed; keeps []

theorem onHold_keeps (c : Conn) (ids : List Id) : Keeps (c.onHold cfg ids : HeldM F Step) := by
  unfold Conn.onHold; keeps []

/-- Reading ops by id, in order, keeping those found. -/
theorem filterMapM_getOp (ids : List Id) (h : Held F) :
    ((ids.filterMapM fun i => Store.getOp (F := F) i : HeldM F (List Op))).run h = (ids.filterMap h.db.ops, h) := by
  have : ∀ (l : List Id) (acc : List Op),
      ((List.filterMapM.loop (fun i => Store.getOp (F := F) i : Id → HeldM F (Option Op)) l acc)).run h =
        (acc.reverse ++ l.filterMap h.db.ops, h) := by
    intro l
    induction l with
    | nil => intro acc; simp [List.filterMapM.loop]
    | cons a t ih =>
      intro acc
      simp only [List.filterMapM.loop, HeldM.run_bind, HeldM.run_getOp]
      cases e : h.db.ops a with
      | none => simp [ih, e]
      | some o => simp [ih, e]
  simpa [List.filterMapM] using this ids []

theorem filterMapM_keeps (ids : List Id) :
    Keeps ((ids.filterMapM fun i => Store.getOp (F := F) i : HeldM F (List Op))) := fun h => by
  rw [filterMapM_getOp]

theorem onWant_keeps (c : Conn) (ids : List Id) : Keeps (c.onWant fam cfg ids : HeldM F Step) := by
  unfold Conn.onWant; keeps [walk_keeps, filterMapM_keeps]

theorem tick_keeps (ix : Index) (c : Conn) (now : Nat) : Keeps (c.tick fam cfg ix now : HeldM F Step) := by
  unfold Conn.tick; keeps [walk_keeps]

/-- A walk with nothing on its frontier offers nothing. -/
theorem walk_idle (c : Conn) (hf : c.frontier = []) (h : Held F) :
    (c.walk fam cfg : HeldM F (Conn × List Id)).run h = ((c, []), h) := by
  unfold Conn.walk
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', HeldM.run_bind, Std.Legacy.Range.size]
  cases cfg.walk with
  | zero => simp
  | succ k => simp [List.range', hf]

end

end Engine.World

namespace Engine.World
open Engine Engine.Sync
variable {F : Type}

/-- A loop's state keeps any property every turn keeps. -/
theorem forIn_inv {α β} (l : List α) (f : α → β → HeldM F (ForInStep β)) (Q : β → Prop)
    (hf : ∀ a b h, Q b → Q ((f a b).run h).1.value) : ∀ b h, Q b → Q ((forIn l b f).run h).1 := by
  induction l with
  | nil => intro b h hb; exact hb
  | cons a t ih =>
    intro b h hb
    rw [List.forIn_cons, HeldM.run_bind]
    have := hf a b h hb
    cases e : ((f a b).run h).1 with
    | done b' => rw [e] at this; exact this
    | yield b' => rw [e] at this; exact ih b' _ this

/-- What the walk leaves as it was: everything but its frontier, what it
offered, and the closures it closed. -/
structure Conn.Same (c c' : Conn) : Prop where
  dialer : c'.dialer = c.dialer
  rooms : c'.rooms = c.rooms
  peerFloor : c'.peerFloor = c.peerFloor
  round : c'.round = c.round
  lastRound : c'.lastRound = c.lastRound
  snaps : c'.snaps = c.snaps
  asked : c'.asked = c.asked
  known : c'.known = c.known
  heard : c'.heard = c.heard

theorem Conn.Same.refl (c : Conn) : Conn.Same c c := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The walk touches only its frontier, offers and closures.** -/
theorem walk_same (fam : Family F) (cfg : Config) (c : Conn) (h : Held F) :
    Conn.Same c ((c.walk fam cfg : HeldM F (Conn × List Id)).run h).1.1 := by
  unfold Conn.walk
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', HeldM.run_bind, HeldM.run_pure]
  apply forIn_inv _ _ (fun st : Conn × List Id => Conn.Same c st.1)
  · intro a st h hs
    obtain ⟨c', off⟩ := st
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hs
    dsimp only at *
    split
    · exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    · split
      · simp only [HeldM.run_bind]
        split
        · exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
        · split
          · split <;> (simp only [HeldM.run_bind, HeldM.run_getStatus]; split <;> exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩)
          · exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
      · exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  · exact Conn.Same.refl c

end Engine.World
