/-
**Shared stores only grow**, proven of the running node, for every
execution of the plain world, against any attacker (`grows`): an op of a
room that a node holds, it holds at every later step.

The node does the work, through main's `entry_fresh`
(engine/wire/EgressLaws.lean): every entry point changes its store only
by write turns and purges (`Moves`). A turn only adds ops (`ingestS`
keeps what is stored, and judging leaves the ops as they are); a purge
takes only ops of no room (`mem_purgeSet_iff`: local ops, such as a
session's secrets and the handshake's couriers). So every move keeps
every op of a room (`moves_keep`), and a world's step moves at most the
one node it runs at; a restart keeps the store (`crash` is the identity
in the plain world).

The plain nodes are ReadOnly (`plain_readOnly`: their hooks are fixed
rooms and frames in the clear), which is all `entry_fresh` asks.
-/
import engine.world.Epidemic
import engine.wire.EgressLaws

namespace Engine.World
open Engine Engine.Sync

variable {F : Type}

/-! ## Every move keeps the ops of every room -/

/-- Store h' holds every op of a room that h holds, under the same id. -/
def KeepsRooms (fam : Family F) (h h' : Held F) : Prop :=
  ∀ x o r, h.db.ops x = some o → fam.room o = some r → h'.db.ops x = some o

theorem KeepsRooms.refl (fam : Family F) (h : Held F) : KeepsRooms fam h h := fun _ _ _ hx _ => hx

theorem KeepsRooms.trans {fam : Family F} {a b c : Held F} (hab : KeepsRooms fam a b) (hbc : KeepsRooms fam b c) :
    KeepsRooms fam a c := fun x o r hx hr => hbc x o r (hab x o r hx hr) hr

/-- Taking an op in keeps every op stored. -/
theorem ingestS_some (o : Op) {s : DB F} {x : Id} {o' : Op} (h : s.ops x = some o') :
    (ingestS o s).ops x = some o' := by
  unfold ingestS
  cases hs : s.ops o.id with
  | some _ => exact h
  | none =>
    have hne : x ≠ o.id := fun e => by rw [e, hs] at h; cases h
    simp [DB.putOp, DB.push, hne, h]

theorem foldl_ingestS_some (ops : List Op) : ∀ {s : DB F} {x : Id} {o' : Op}, s.ops x = some o' →
    (ops.foldl (fun s o => ingestS o s) s).ops x = some o' := by
  induction ops with
  | nil => intro s x o' h; exact h
  | cons o t ih => intro s x o' h; exact ih (ingestS_some o h)

/-- **A write turn keeps every op stored.** -/
theorem turn_keeps (fam : Family F) (ops : List Op) (h : Held F) :
    KeepsRooms fam h ((Turn.turn fam ops : HeldM F Unit).run h).2 := by
  intro x o r hx _
  show (turnCappedS fam drainCap ops h.db).ops x = some o
  rw [turnCappedS_ops]
  exact foldl_ingestS_some ops hx

/-- **A purge keeps every op of a room**: it takes only ops of no room. -/
theorem purge_keeps (fam : Family F) (ids : List Id) (scrub : Bool) (h : Held F) :
    KeepsRooms fam h ((Turn.purge fam ids scrub : HeldM F Unit).run h).2 := by
  intro x o r hx hr
  show (purgeCappedS fam drainCap ids h.db).ops x = some o
  rw [purgeCappedS_ops]
  simp only [purgeS]
  have hn : has (purgeSet fam h.db ids) x = false := by
    cases e : has (purgeSet fam h.db ids) x with
    | false => rfl
    | true =>
      obtain ⟨-, o', ho', hr'⟩ := (mem_purgeSet_iff (fam := fam)).1 ((Engine.has_iff _ _).1 e)
      rw [hx] at ho'; cases ho'; rw [hr] at hr'; cases hr'
  rw [hn]; exact hx

theorem move_keeps {fam : Family F} {h h' : Held F} (hm : Move fam h h') : KeepsRooms fam h h' := by
  cases hm with
  | turn ops h => exact turn_keeps fam ops h
  | purge ids scrub h => exact purge_keeps fam ids scrub h

/-- **Every run of moves keeps every op of a room.** -/
theorem moves_keep {fam : Family F} {h h' : Held F} (hm : Moves fam h h') : KeepsRooms fam h h' := by
  induction hm with
  | refl => exact KeepsRooms.refl fam _
  | tail _ hm ih => exact ih.trans (move_keeps hm)

/-! ## The plain nodes -/

namespace Plain
variable (Q : Plain F)

/-- **The plain nodes' hooks only read**: fixed rooms, frames in the
clear, nothing else. -/
theorem plain_readOnly (i : Fin Q.n) : ReadOnly ((Q.two i).sync .a) where
  rooms _ _ := rfl
  recv _ _ _ _ _ := rfl
  outbox _ := rfl
  closing _ _ := rfl
  retired _ := rfl
  react _ := rfl
  dial _ _ := rfl
  established _ := rfl
  sealFor _ _ _ := rfl
  openFrame _ _ := rfl
  catalog _ h := by cases h
  retryKey _ _ := rfl
  retryStore _ h := by cases h

/-- Opening a session moves the store only by moves (it moves it not at
all, after the hello). -/
theorem connect_moves (i : Fin Q.n) (n : Node) (cid : Id) (a : ByteArray) (dialer : Bool) (now : Nat)
    (h : Held F) : Moves Q.fam h ((n.connect ((Q.two i).sync .a) cid a dialer now).run h).2 := by
  have hr := Q.plain_readOnly i
  unfold Node.connect
  simp only [HeldM.run_bind]
  obtain ⟨m1, ok1⟩ := open_ok hr n cid a dialer now h
  exact m1.trans (finish_ok hr _ _ now m1 ok1).1

/-- Every entry point the world runs at a node moves its store only by
moves. -/
theorem enter_moves (i : Fin Q.n) (f : Node → HeldM F (Node × Effects))
    (hf : (∃ E, Entry ((Q.two i).sync .a) E ∧ f = E) ∨
      ∃ cid a dialer now, f = fun n => n.connect ((Q.two i).sync .a) cid a dialer now)
    (n : Node) (h : Held F) : Moves Q.fam h ((f n).run h).2 := by
  rcases hf with ⟨E, hE, rfl⟩ | ⟨cid, a, dialer, now, rfl⟩
  · exact (entry_fresh (Q.plain_readOnly i) hE n h).1
  · exact Q.connect_moves i n cid a dialer now h

variable {Q}

/-- A node's entry point keeps every node's room ops: its own by its
moves, the others' as they are. -/
theorem enter_keeps (w : World (Held F) Q.n) (i : Fin Q.n) (t : Nat) (f : Node → HeldM F (Node × Effects))
    (hf : ∀ n h, Moves Q.fam h ((f n).run h).2) (l : Fin Q.n) :
    KeepsRooms Q.fam (w.box l) ((w.enter Q.setup i t f).box l) := by
  simp only [World.enter]
  by_cases e : l = i
  · subst e; simp only [upd_same]; exact moves_keep (hf _ _)
  · rw [upd_other _ _ e]; exact KeepsRooms.refl _ _

/-- **One step of the plain world keeps every node's room ops**, whatever
the act, legal or not, the attacker's included. -/
theorem step_keeps (w : World (Held F) Q.n) (a : Act Q.n) (l : Fin Q.n) :
    KeepsRooms Q.fam (w.box l) ((w.step Q.setup a).box l) := by
  have hE : ∀ i (E : Node → HeldM F (Node × Effects)), Entry ((Q.two i).sync .a) E →
      ∀ n h, Moves Q.fam h ((E n).run h).2 := fun i E hE n h => Q.enter_moves i E (Or.inl ⟨E, hE, rfl⟩) n h
  cases a with
  | deliver k t =>
    simp only [World.step]
    cases hp : w.flight[k]? with
    | none => exact KeepsRooms.refl _ _
    | some p =>
      dsimp only
      cases hj : Q.setup.at? p.dst with
      | none => exact KeepsRooms.refl _ _
      | some j =>
        dsimp only
        exact enter_keeps { w with flight := w.flight.eraseIdx k } j t
          (fun nd => nd.onFrame ((Q.two j).sync .a) p.origin p.bytes t) (hE j _ (.frame p.origin p.bytes t)) l
  | dup k =>
    simp only [World.step]
    cases w.flight[k]? with
    | none => exact KeepsRooms.refl _ _
    | some p => exact KeepsRooms.refl _ _
  | drop k => exact KeepsRooms.refl _ _
  | tick i t =>
    simp only [World.step]
    exact enter_keeps w i t (fun nd => nd.onTick ((Q.two i).sync .a) t) (hE i _ (.tick t)) l
  | write i ops t =>
    simp only [World.step]
    exact enter_keeps w i t (fun nd => nd.onWrite ((Q.two i).sync .a) ops t) (hE i _ (.write ops t)) l
  | restart i t =>
    simp only [World.step]
    by_cases e : l = i
    · subst e; simp only [upd_same]; exact KeepsRooms.refl _ _
    · rw [upd_other _ _ e]; exact KeepsRooms.refl _ _
  | close i addr t =>
    simp only [World.step]
    exact enter_keeps w i t (fun nd => nd.onClose ((Q.two i).sync .a) addr t) (hE i _ (.close addr t)) l
  | connect i j cid dialer t =>
    simp only [World.step]
    exact enter_keeps w i t (fun nd => nd.connect ((Q.two i).sync .a) cid (Q.addr j) dialer t)
      (fun n h => Q.enter_moves i _ (Or.inr ⟨cid, Q.addr j, dialer, t, rfl⟩) n h) l
  | inject i origin b t =>
    simp only [World.step]
    exact enter_keeps w i t (fun nd => nd.onFrame ((Q.two i).sync .a) origin b t) (hE i _ (.frame origin b t)) l

/-- **Shared stores only grow.** In every execution of the plain world,
against any attacker, an op of room r that a node holds, it holds at the
next step: no entry point, crash, drop, duplicate or injection takes an
op of a room out of a store. -/
theorem grows {adv : World (Held F) Q.n → ByteArray → Prop} {w₀ : World (Held F) Q.n}
    (E : Exec Q.setup adv w₀) (r : Id) : Grows E r := by
  intro k i x ⟨o, ho, hr⟩
  exact ⟨o, step_keeps (E.world k) (E.act k) i x o r ho hr, hr⟩

/-- **Every member converges, from per-edge progress**, in every
execution of the plain World: over a knows-graph of diameter d, an op of
room r any node holds, every node holds from some step on, within d · B,
and keeps (`converge_of_edge` with `grows` discharged by the running
node). -/
theorem converge {adv : World (Held F) Q.n → ByteArray → Prop} {w₀ : World (Held F) Q.n}
    (E : Exec Q.setup adv w₀) {N : Net Q.n} {r : Id} {k₀ B d : Nat} (hE : Edge E N r k₀ B) (hd : Diam N.G d) :
    ∀ k i j x, k₀ ≤ k → N.gst ≤ (E.world k).now → N.Calm (E.world k).now ((E.world k).now + d * B) →
      Engine.World.Holds Q.setup (E.world k) i r x →
      ∃ k', k ≤ k' ∧ (E.world k').now ≤ (E.world k).now + d * B ∧
        ∀ k'', k' ≤ k'' → Engine.World.Holds Q.setup (E.world k'') j r x :=
  converge_of_edge E hE (grows E r) hd

/-- **Offline catch-up and the outbox**, in every execution of the plain
World: a node back from offline (or a restart, or a partition) gets
everything any node holds, and everyone gets what it wrote away, all at
one step within d · B (`offline_of` with `grows` discharged). -/
theorem offline {adv : World (Held F) Q.n → ByteArray → Prop} {w₀ : World (Held F) Q.n}
    (E : Exec Q.setup adv w₀) {N : Net Q.n} {r : Id} {k₀ B d : Nat} (hE : Edge E N r k₀ B) (hd : Diam N.G d) :
    ∀ k, k₀ ≤ k → N.gst ≤ (E.world k).now → N.Calm (E.world k).now ((E.world k).now + d * B) →
      ∀ j x, Engine.World.Holds Q.setup (E.world k) j r x →
        ∃ k', k ≤ k' ∧ (E.world k').now ≤ (E.world k).now + d * B ∧ ∀ l, Engine.World.Holds Q.setup (E.world k') l r x :=
  offline_of E hE (grows E r) hd

end Plain

end Engine.World
