/-
Running node code on a held store, as rewrite rules: each entry point
run on a `Held` store is rewritten lemma by lemma (`HeldM.run_bind` and
the loop lemmas) until its result is a term. Most of what a node does
leaves the store as it is (`Keeps`); the `keeps` tactic proves that from
a do block's structure. After holmes-a3's two-node world (a3/world,
WorldLaws.lean), on which these are modelled.
-/
import engine.world.World
import Lean.Elab.Tactic.Basic

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
theorem Keeps.read' {α} (f : Held F → α) : Keeps (readH f) := fun _ => rfl

/-- Fails on a goal that still has metavariables. `keeps` and `grows`
apply bind rules, and on a goal whose program is not yet known each
application makes the program a bind of two unknown programs, forever:
that is what ran a build of engine/world/Plain.lean to 70 GB
(docs/PROOFS.md, finding 5). -/
elab "concrete_goal" : tactic => do
  let t ← Lean.Elab.Tactic.getMainTarget
  if (← Lean.instantiateMVars t).hasExprMVar then
    throwError "the goal's program is not known yet: state the loop or the call first"

/-- Prove `Keeps` of a do block from its structure, with these `Keeps`
lemmas for the calls in it. Only on a goal with no metavariables. -/
syntax "keeps" "[" term,* "]" : tactic

macro_rules
  | `(tactic| keeps [$ts,*]) => do
    let mut tac : Lean.TSyntax `tactic ← `(tactic| first | split | intro)
    for t in ts.getElems.reverse do
      tac ← `(tactic| first | with_reducible_and_instances apply $t | $tac:tactic)
    `(tactic| repeat' (concrete_goal; first
      | dsimp only | with_reducible_and_instances apply Keeps.bind'
      | with_reducible_and_instances apply Keeps.pure' | with_reducible_and_instances apply Keeps.forIn'
      | with_reducible_and_instances apply Keeps.range'
      | with_reducible_and_instances apply Keeps.getOp' | with_reducible_and_instances apply Keeps.getStatus'
      | with_reducible_and_instances apply Keeps.read'
      | $tac:tactic))

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

/-- **What the laws need of the closure walk:** it only reads, touches
only its frontier, offers and closures, and does nothing on an empty
frontier. `walk_proof` proves it of main's structural `Conn.walkN`
(finding 3's fix); the laws that run a tick or answer a want take it as
a premise, so they read the same over any walk with these laws. -/
structure WalkLaws (fam : Family F) (cfg : Config) : Prop where
  /-- The walk only reads. -/
  keeps : ∀ c : Conn, Keeps (c.walk fam cfg : HeldM F (Conn × List (Id × Id)))
  /-- It touches only its frontier, offers and closures. -/
  same : ∀ (c : Conn) (h : Held F), Conn.Same c ((c.walk fam cfg : HeldM F (Conn × List (Id × Id))).run h).1.1
  /-- With nothing on its frontier it offers nothing and changes nothing. -/
  idle : ∀ (c : Conn) (h : Held F), c.frontier = [] →
    (c.walk fam cfg : HeldM F (Conn × List (Id × Id))).run h = ((c, []), h)

/-- **The walk's laws, for every family and settings.** -/
def walk_stmt : Prop := ∀ (F : Type) (fam : Family F) (cfg : Config), WalkLaws fam cfg

theorem Conn.Same.trans {a b c : Conn} (h1 : Conn.Same a b) (h2 : Conn.Same b c) : Conn.Same a c :=
  ⟨h2.1.trans h1.1, h2.2.trans h1.2, h2.3.trans h1.3, h2.4.trans h1.4, h2.5.trans h1.5, h2.6.trans h1.6,
    h2.7.trans h1.7, h2.8.trans h1.8, h2.9.trans h1.9⟩

/-- The walk, step by step: it only reads, and keeps all but its
frontier, offers and closures. -/
theorem walkN_laws (fam : Family F) (h : Held F) : ∀ (k : Nat) (c : Conn) (offer : List (Id × Id)),
    ((c.walkN fam offer k : HeldM F _).run h).2 = h ∧ Conn.Same c ((c.walkN fam offer k : HeldM F _).run h).1.1 := by
  intro k
  induction k with
  | zero => intro c offer; exact ⟨rfl, Conn.Same.refl c⟩
  | succ k ih =>
    intro c offer
    have leaf : ∀ (c' : Conn) (offer' : List (Id × Id)), Conn.Same c c' →
        ((c'.walkN fam offer' k : HeldM F _).run h).2 = h ∧
          Conn.Same c ((c'.walkN fam offer' k : HeldM F _).run h).1.1 := fun c' offer' e =>
      ⟨(ih c' offer').1, e.trans (ih c' offer').2⟩
    rw [Conn.walkN]
    cases hf : c.frontier with
    | nil => exact ⟨rfl, Conn.Same.refl c⟩
    | cons x rest =>
      dsimp only
      have s0 : Conn.Same c { c with frontier := rest } := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      by_cases h1 : (!c.closed.contains x) = true
      · simp only [h1, ↓reduceIte, HeldM.run_bind, HeldM.run_getOp]
        cases hx : h.db.ops x with
        | none => exact leaf _ _ s0
        | some o =>
          dsimp only
          by_cases hsh : Conn.shows fam { c with frontier := rest } o = true
          · simp only [hsh, ↓reduceIte]
            by_cases h2 : (!c.known.contains x && !c.offered.contains x) = true
            · simp only [h2, ↓reduceIte, HeldM.run_bind, HeldM.run_getStatus]
              rcases h.db.status x with _ | ⟨_⟩ | _ <;>
                exact leaf _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
            · simp only [h2, Bool.false_eq_true, ↓reduceIte, HeldM.run_bind, HeldM.run_getStatus]
              rcases h.db.status x with _ | ⟨_⟩ | _ <;>
                exact leaf _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
          · simp only [hsh, Bool.false_eq_true, ↓reduceIte]; exact leaf _ _ s0
      · simp only [h1, Bool.false_eq_true, ↓reduceIte]; exact leaf _ _ s0

/-- **The walk's laws hold of main's `Conn.walk`** (`walkN` over the
budget `cfg.walk`). -/
theorem walk_proof : walk_stmt := by
  intro F fam cfg
  refine ⟨fun c h => (walkN_laws fam h _ c []).1, fun c h => (walkN_laws fam h _ c []).2, fun c h hf => ?_⟩
  unfold Conn.walk
  cases cfg.walk with
  | zero => rfl
  | succ k => rw [Conn.walkN]; simp [hf]

section
variable (fam : Family F) (cfg : Config)

theorem filed_keeps (c : Conn) (ids : List Id) : Keeps (c.filed fam cfg ids : HeldM F Step) := by
  unfold Conn.filed; keeps []

theorem holdsIn_keeps (r i : Id) : Keeps (holdsIn (F := F) fam r i : HeldM F Bool) := by
  unfold holdsIn; keeps []

theorem onHold_keeps (c : Conn) (r : Id) (ids : List Id) : Keeps (c.onHold fam cfg r ids : HeldM F Step) := by
  unfold Conn.onHold; keeps [holdsIn_keeps]

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

end

section
variable (fam : Family F) (cfg : Config) (hw : WalkLaws (F := F) fam cfg)
include hw

theorem onWant_keeps (c : Conn) (ids : List Id) : Keeps (c.onWant fam cfg ids : HeldM F Step) := by
  unfold Conn.onWant; keeps [hw.keeps, filterMapM_keeps]

theorem tick_keeps (ix : Index) (c : Conn) (now : Nat) : Keeps (c.tick fam cfg ix now : HeldM F Step) := by
  unfold Conn.tick; keeps [hw.keeps]

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

/-- A loop whose every turn yields, keeping the store, is a fold. -/
theorem forIn_yield {α β} (l : List α) (f : α → β → HeldM F (ForInStep β)) (g : β → α → β) (h : Held F)
    (hf : ∀ a b, (f a b).run h = (.yield (g b a), h)) : ∀ b, (forIn l b f).run h = (l.foldl g b, h) := by
  induction l with
  | nil => intro b; rfl
  | cons a t ih => intro b; rw [List.forIn_cons, HeldM.run_bind, hf]; exact ih _

/-- `Node.write`'s first loop: the ops not stored, each id once, newest first. -/
def absentStep (db : DB F) (acc : List Op) (o : Op) : List Op :=
  if (!acc.any (·.id == o.id)) && (db.ops o.id).isNone then o :: acc else acc

/-- Its second loop: each op now stored joins the index. -/
def addStep (fam : Family F) (db : DB F) (st : Index × List Id) (o : Op) : Index × List Id :=
  if (db.ops o.id).isSome then (st.1.add fam o, o.id :: st.2) else st

/-- **`Node.write` on a held store, as a term.** -/
theorem write_run (x : Sync F (HeldM F)) (n : Node) (ops : List Op) (h : Held F) :
    (n.write x ops).run h =
      let ab := ops.foldl (absentStep h.db) []
      let h' := turnH x.fam ab.reverse h
      let st := ab.reverse.foldl (addStep x.fam h'.db) (n.ix, [])
      if ab.isEmpty then ((n, []), h)
      else (({ n with ix := st.1, fresh := n.fresh ++ st.2.reverse }, st.2.reverse), h') := by
  unfold Node.write
  rw [HeldM.run_bind, forIn_yield _ _ (absentStep h.db) h (fun o acc => by
    unfold absentStep
    by_cases e : (!acc.any (·.id == o.id)) = true
    · cases hop : h.db.ops o.id <;> simp [e, hop] <;> rfl
    · simp only [Bool.not_eq_true] at e
      simp [e])]
  dsimp only
  split
  · rfl
  · simp only [HeldM.run_bind, HeldM.run_turn]
    rw [forIn_yield _ _ (addStep x.fam (turnH x.fam (ops.foldl (absentStep h.db) []).reverse h).db) _
      (fun o st => by
        unfold addStep
        cases hop : (turnH x.fam (ops.foldl (absentStep h.db) []).reverse h).db.ops o.id <;> simp [hop] <;> rfl)]
    rfl
end Engine.World
