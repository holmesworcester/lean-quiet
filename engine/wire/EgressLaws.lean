/-
**Every connection step reads its rooms afresh**, proven of `Node`'s
entry points (`onFrame`, `onTick`, `onWrite`, `onClose`) run on held
data (`HeldM`), for any hooks that only read (`ReadOnly`: what a hook
would store it returns, and the node writes it through the engine).

A node changes its store only by its own moves (`Moves`): write turns
and purges. Each op an entry point sends on a session is a send of a
connection step (`Sent`) that the node ran, at a store between the
entry point's start and end, on the session's connection as that store
gives its rooms (`Node.refresh`): a frame's payload (`Conn.recv`), ops
just stored (`filedGive`), the clock (`tickGive`), the session's queue
(`serveOwed`), or its hello (`Conn.open`). Every frame the entry point
sends is a bare op, or a bundle of such sends sealed for that session
(`FramesOk`): `onFrame_fresh`, `onTick_fresh`, `onWrite_fresh`,
`onClose_fresh`.

So a law of one connection step, read at the store the step ran at, is
a law of everything the node sends: a removal stored before a step
reaches that step (app/Proofs.lean).
-/
import engine.wire.WorldLaws
import engine.sync.OfferLaws
import engine.sync.SweepLaws

namespace Engine.Sync

section
variable {F : Type}

/-! ## Moves: how a node changes its store -/

/-- One change a node makes to its store: a write turn, or a purge. -/
inductive Move (fam : Family F) : Held F → Held F → Prop
  | turn (ops : List Op) (h : Held F) : Move fam h ((Turn.turn fam ops : HeldM F Unit).run h).2
  | purge (ids : List Id) (scrub : Bool) (h : Held F) :
      Move fam h ((Turn.purge fam ids scrub : HeldM F Unit).run h).2

/-- The stores a node's own changes reach from h: none or more moves. -/
inductive Moves (fam : Family F) : Held F → Held F → Prop
  | refl (h : Held F) : Moves fam h h
  | tail {a b c : Held F} : Moves fam a b → Move fam b c → Moves fam a c

theorem Moves.trans {fam : Family F} {a b c : Held F} (hab : Moves fam a b) (hbc : Moves fam b c) :
    Moves fam a c := by
  induction hbc with
  | refl => exact hab
  | tail _ hm ih => exact .tail ih hm

theorem Moves.single {fam : Family F} {a b : Held F} (h : Move fam a b) : Moves fam a b :=
  .tail (.refl a) h

theorem Moves.of_eq {fam : Family F} {a b : Held F} (h : a = b) : Moves fam a b := h ▸ .refl a

/-- Run from any store, p changes it only by moves. -/
def Goes (fam : Family F) {α} (p : HeldM F α) : Prop := ∀ h, Moves fam h (p.run h).2

theorem Reads.goes {fam : Family F} {α} {p : HeldM F α} (hp : Reads p) : Goes fam p :=
  fun h => .of_eq (hp h).symm

theorem Goes.pure' (fam : Family F) {α} (a : α) : Goes fam (pure a : HeldM F α) := fun h => .refl h

theorem Goes.bind' {fam : Family F} {α β} {m : HeldM F α} {k : α → HeldM F β} (hm : Goes fam m)
    (hk : ∀ a, Goes fam (k a)) : Goes fam (m >>= k) := by
  intro h; simp only [HeldM.run_bind]; exact (hm h).trans (hk _ _)

theorem Goes.forIn' {fam : Family F} {α β} (l : List α) (b : β) {f : α → β → HeldM F (ForInStep β)}
    (hf : ∀ a b, Goes fam (f a b)) : Goes fam (forIn l b f) := by
  induction l generalizing b with
  | nil => exact Goes.pure' fam b
  | cons a t ih =>
    intro h
    rw [List.forIn_cons, HeldM.run_bind]
    refine (hf a b h).trans ?_
    cases ((f a b).run h).1 with
    | done b => exact .refl _
    | yield b => exact ih b _

theorem Goes.getOp' (fam : Family F) (x : Id) : Goes fam (Store.getOp (F := F) x : HeldM F _) :=
  (Reads.getOp' x).goes
theorem Goes.getStatus' (fam : Family F) (x : Id) : Goes fam (Store.getStatus (F := F) x : HeldM F _) :=
  (Reads.getStatus' x).goes
theorem Goes.turn' (fam : Family F) (ops : List Op) : Goes fam (Turn.turn fam ops : HeldM F Unit) :=
  fun h => .single (.turn ops h)
theorem Goes.purge' (fam : Family F) (ids : List Id) (scrub : Bool) :
    Goes fam (Turn.purge fam ids scrub : HeldM F Unit) :=
  fun h => .single (.purge ids scrub h)

end

/-- Prove `Goes` of a do block from its structure, with these `Goes`
lemmas for the calls in it. -/
syntax "goes" "[" term,* "]" : tactic

macro_rules
  | `(tactic| goes [$ts,*]) => do
    let mut tac : Lean.TSyntax `tactic ← `(tactic| first | split | intro)
    for t in ts.getElems.reverse do
      tac ← `(tactic| first | with_reducible_and_instances apply $t | $tac:tactic)
    `(tactic| repeat' (first
      | dsimp only | with_reducible_and_instances apply Goes.bind'
      | with_reducible_and_instances apply Goes.pure' | with_reducible_and_instances apply Goes.forIn'
      | with_reducible_and_instances apply Goes.getOp' | with_reducible_and_instances apply Goes.getStatus'
      | with_reducible_and_instances apply Goes.turn' | with_reducible_and_instances apply Goes.purge'
      | $tac:tactic))

section
variable {F : Type}

/-! ## Hooks that only read -/

/-- Hooks that only read the store: what a hook would store it returns,
and the node writes it through the engine. -/
structure ReadOnly (x : Sync F (HeldM F)) : Prop where
  rooms : ∀ cid, Reads (x.hooks.rooms cid)
  recv : ∀ via a o t, Reads (x.hooks.recv via a o t)
  outbox : Reads x.hooks.outbox
  closing : ∀ cid, Reads (x.hooks.closing cid)
  retired : Reads x.hooks.retired
  react : Reads x.hooks.react
  dial : ∀ t, Reads (x.hooks.dial t)
  established : Reads x.hooks.established
  sealFor : ∀ cid b, Reads (x.hooks.sealFor cid b)
  openFrame : ∀ b, Reads (x.hooks.openFrame b)
  catalog : ∀ cat, x.catalog = some cat → Reads cat.ceiling ∧ ∀ i, Reads (cat.read i)
  retryKey : ∀ cid, Reads (x.hooks.retryKey cid)
  retryStore : ∀ store, x.retryStore = some store →
    (∀ peer, Reads (store.load peer)) ∧ (∀ peer cursor, Reads (store.save peer cursor))
  stale : Reads x.hooks.stale

/-! ## Connection steps, run where the node runs them -/

/-- **Op o is a fresh step's send on session cid at store h:** a send
of a connection step the node runs, run at h on the session's
connection as h gives its rooms (`Node.refresh`): a frame's payload, ops
just stored, the clock, the session's queue, or its hello. -/
def Sent (x : Sync F (HeldM F)) (h : Held F) (cid : Id) (o : Op) : Prop :=
  (∃ (c : Conn) (ix : Index) (bytes : ByteArray) (now : Nat), o ∈ ((Conn.recv x.fam x.cfg ix (c.carry (((x.hooks.rooms cid).run h).1)) bytes now :
      HeldM F Step).run h).1.send) ∨
  (∃ (c : Conn) (ids : List Id), o ∈ (((c.carry (((x.hooks.rooms cid).run h).1)).filedGive x.fam x.cfg ids : HeldM F Step).run h).1.send) ∨
  (∃ (c : Conn) (ix : Index) (now : Nat), o ∈ ((Conn.tickGive x.fam x.cfg ix (c.carry (((x.hooks.rooms cid).run h).1)) now :
      HeldM F Step).run h).1.send) ∨
  (∃ (c : Conn) (budget : Nat) (first : List Id),
      o ∈ (((c.carry (((x.hooks.rooms cid).run h).1)).serveOwed x.fam x.cfg budget first : HeldM F _).run h).1.2.1 ∨
      o ∈ (((c.carry (((x.hooks.rooms cid).run h).1)).serveOwed x.fam x.cfg budget first : HeldM F _).run h).1.2.2) ∨
  (∃ (dialer : Bool) (floor now : Nat), o ∈ (Conn.open dialer (Room.syncs (((x.hooks.rooms cid).run h).1)) floor now).send) ∨
  (∃ (c : Conn) (cat : Catalog (HeldM F)) (cursor : Sweep) (room : Nat),
    x.catalog = some cat ∧ o ∈ ((Sweep.run cat cursor
      ((c.carry (((x.hooks.rooms cid).run h).1)).shows x.fam) room : HeldM F _).run h).1.2.toList)

/-- Every session send in out, run from h0 to h1, is the bytes of a fresh
step's send at a store on the way. -/
def ActsOk (x : Sync F (HeldM F)) (h0 h1 : Held F) (out : Acts) : Prop :=
  ∀ cid b, ((Route.conn cid, b) ∈ out.send ∨ (Route.conn cid, b) ∈ out.serve) →
    ∃ o h, b = o.bytes ∧ Moves x.fam h0 h ∧ Moves x.fam h h1 ∧ Sent x h cid o

variable {x : Sync F (HeldM F)}

/-- Flow-control reservations change no store hook or authorization input. -/
theorem ReadOnly.afterActs {x : Sync F (HeldM F)} (hr : ReadOnly x) (n : Node) (out : Acts) :
    ReadOnly (n.afterActs x out) :=
  ⟨hr.rooms, hr.recv, hr.outbox, hr.closing, hr.retired, hr.react, hr.dial,
    hr.established, hr.sealFor, hr.openFrame, hr.catalog, hr.retryKey, hr.retryStore, hr.stale⟩

theorem sent_afterActs (x : Sync F (HeldM F)) (n : Node) (out : Acts) (h : Held F) (cid : Id) (o : Op) :
    Sent (n.afterActs x out) h cid o ↔ Sent x h cid o := Iff.rfl


theorem ActsOk.empty (h0 h1 : Held F) : ActsOk x h0 h1 {} := by
  intro cid b hb; rcases hb with hb | hb <;> exact absurd hb (List.not_mem_nil)

theorem ActsOk.append {h0 h1 : Held F} {a b : Acts} (ha : ActsOk x h0 h1 a) (hb : ActsOk x h0 h1 b) :
    ActsOk x h0 h1 (a ++ b) := by
  intro cid p hp
  simp only [Acts.append_def, List.mem_append] at hp
  rcases hp with (hp | hp) | (hp | hp)
  · exact ha cid p (Or.inl hp)
  · exact hb cid p (Or.inl hp)
  · exact ha cid p (Or.inr hp)
  · exact hb cid p (Or.inr hp)

theorem ActsOk.right {h0 h1 h2 : Held F} {a : Acts} (ha : ActsOk x h0 h1 a) (hm : Moves x.fam h1 h2) :
    ActsOk x h0 h2 a := by
  intro cid p hp
  obtain ⟨o, h, e, m0, m1, hs⟩ := ha cid p hp
  exact ⟨o, h, e, m0, m1.trans hm, hs⟩

theorem ActsOk.left {h h0 h1 : Held F} {a : Acts} (ha : ActsOk x h0 h1 a) (hm : Moves x.fam h h0) :
    ActsOk x h h1 a := by
  intro cid p hp
  obtain ⟨o, h', e, m0, m1, hs⟩ := ha cid p hp
  exact ⟨o, h', e, hm.trans m0, m1, hs⟩

/-- Acts with no session sends. -/
theorem ActsOk.noConn {h0 h1 : Held F} {a : Acts}
    (hs : ∀ cid b, (Route.conn cid, b) ∉ a.send) (hv : ∀ cid b, (Route.conn cid, b) ∉ a.serve) :
    ActsOk x h0 h1 a := by
  intro cid b hb
  rcases hb with hb | hb
  · exact absurd hb (hs cid b)
  · exact absurd hb (hv cid b)

/-- Ops each a fresh step's send on cid at a store on the way, sent on cid. -/
theorem ActsOk.sends {h0 h h1 : Held F} {cid : Id} {ops : List Op} (m0 : Moves x.fam h0 h)
    (m1 : Moves x.fam h h1) (hs : ∀ o ∈ ops, Sent x h cid o) : ActsOk x h0 h1 (sends cid ops) := by
  intro c b hb
  rcases hb with hb | hb
  · obtain ⟨o, ho, e⟩ := List.mem_map.1 hb
    simp only [Prod.mk.injEq, Route.conn.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨o, h, rfl, m0, m1, hs o ho⟩
  · exact absurd hb List.not_mem_nil

/-- The same, in their lanes. -/
theorem ActsOk.split {h0 h h1 : Held F} {cid : Id} {ops : List Op} (lane : Op → Lane)
    (m0 : Moves x.fam h0 h) (m1 : Moves x.fam h h1) (hs : ∀ o ∈ ops, Sent x h cid o) :
    ActsOk x h0 h1 (Engine.Sync.split lane cid ops) := by
  intro c b hb
  simp only [Engine.Sync.split, List.mem_map, List.mem_filter] at hb
  rcases hb with ⟨o, ⟨ho, _⟩, e⟩ | ⟨o, ⟨ho, _⟩, e⟩ <;>
  · simp only [Prod.mk.injEq] at e
    obtain ⟨ec, rfl⟩ := e
    cases ec
    exact ⟨o, h, rfl, m0, m1, hs o ho⟩

end

/-! ## The node's pieces -/

section
variable {F : Type} (x : Sync F (HeldM F))

theorem write_goes (n : Node) (ops : List Op) : Goes x.fam (n.write x ops) := by
  unfold Node.write; goes []

theorem put_goes (n : Node) (ops : List Op) (mine : Bool) : Goes x.fam (n.put x ops mine) :=
  write_goes x n _

theorem recordGiven_goes (n : Node) (st : List (Id × Id)) : Goes x.fam (n.recordGiven x st) := by
  unfold Node.recordGiven; goes [put_goes]

variable {x}

/-- What a loop keeps: an invariant of the store and the loop's state
that each turn keeps holds at its end. -/
theorem forIn_inv {α β} {l : List α} {b : β} {f : α → β → HeldM F (ForInStep β)} {h : Held F}
    {R : β × Held F} (hR : (forIn l b f).run h = R) (P : Held F → β → Prop) (hb : P h b)
    (hf : ∀ a ∈ l, ∀ b h, P h b → P ((f a b).run h).2 ((f a b).run h).1.value) : P R.2 R.1 := by
  subst hR
  induction l generalizing b h with
  | nil => exact hb
  | cons a t ih =>
    rw [List.forIn_cons, HeldM.run_bind]
    have h1 := hf a (List.mem_cons_self ..) b h hb
    cases e : ((f a b).run h).1 with
    | done b' => rw [e] at h1; exact h1
    | yield b' =>
      rw [e] at h1
      exact ih h1 (fun a ha => hf a (List.mem_cons_of_mem _ ha))

theorem refresh_carry (hr : ReadOnly x) (cid : Id) (c : Conn) (h : Held F) :
    (Node.refresh x cid c).run h = (c.carry (((x.hooks.rooms cid).run h).1), h) := by
  simp only [Node.refresh, HeldM.run_bind, HeldM.run_pure, hr.rooms cid h]

end

/-! ## Egress: what the node's pieces send -/

section
variable {F : Type} {x : Sync F (HeldM F)}

/-- Run from any store, p moves it only by the node's own changes, and
every session send in its acts is a fresh step's send at a store on the
way. -/
def Egress (x : Sync F (HeldM F)) (p : HeldM F (Node × Acts)) : Prop :=
  ∀ h, Moves x.fam h (p.run h).2 ∧ ActsOk x h (p.run h).2 (p.run h).1.2

theorem tick_reads (fam : Family F) (cfg : Config) (ix : Index) (c : Conn) (now : Nat) :
    Reads (c.tick fam cfg ix now : HeldM F Step) := by
  have hw : ∀ c : Conn, Reads (c.walk fam cfg : HeldM F _) := fun c h => (walk_keeps fam cfg h c).1
  unfold Conn.tick Conn.work; keeps [hw]

theorem tickGive_reads (fam : Family F) (cfg : Config) (ix : Index) (c : Conn) (now : Nat) :
    Reads (Conn.tickGive fam cfg ix c now : HeldM F Step) := by
  unfold Conn.tickGive Conn.notify; keeps [give_reads, tick_reads]

theorem recv_reads (fam : Family F) (cfg : Config) (ix : Index) (c : Conn) (bytes : ByteArray) (now : Nat) :
    Reads (Conn.recv fam cfg ix c bytes now : HeldM F Step) := by
  unfold Conn.recv; keeps [onHold_reads]

theorem serveOwed_reads' (fam : Family F) (cfg : Config) (c : Conn) (budget : Nat) (first : List Id) :
    Reads (c.serveOwed fam cfg budget first : HeldM F _) :=
  fun h => (serveOwed_run fam cfg c budget first h).2.2

theorem sweep_reads (cat : Catalog (HeldM F)) (hc : Reads cat.ceiling)
    (hr : ∀ i, Reads (cat.read i)) (cursor : Sweep) (shows : Op → Bool) (room : Nat) :
    Reads (Sweep.run cat cursor shows room : HeldM F _) := by
  unfold Sweep.run
  keeps [hc, hr]

theorem sweep_step_shown (cursor : Sweep) (ceiling : Nat) (op : Option Op) (shows : Op → Bool) (room : Nat)
    {o : Op} (ho : o ∈ (cursor.step ceiling op shows room).2.toList) : shows o = true := by
  have he : (cursor.step ceiling op shows room).2 = some o := by simpa using ho
  exact (Sweep.next_sent he).2.1

private theorem result_bind {α β : Type} (p : HeldM F α) (k : α → HeldM F β)
    (P : β → Prop) (hk : ∀ a h, P ((k a).run h).1) :
    ∀ h, P (((p >>= k).run h).1) := fun h => hk _ _

theorem sweep_shown (cat : Catalog (HeldM F)) (cursor : Sweep) (shows : Op → Bool)
    (room : Nat) (h : Held F) {o : Op}
    (ho : o ∈ ((Sweep.run cat cursor shows room : HeldM F _).run h).1.2.toList) : shows o = true := by
  have result : ∀ h, ∀ o ∈ ((Sweep.run cat cursor shows room : HeldM F _).run h).1.2.toList,
      shows o = true := by
    unfold Sweep.run
    dsimp only
    split <;> apply result_bind (P := fun r : Sweep × Option Op => ∀ o ∈ r.2.toList, shows o = true)
    all_goals
      intro ceiling
      split
      · intro h o ho
        exact sweep_step_shown _ _ _ _ _ ho
      · apply result_bind (P := fun r : Sweep × Option Op => ∀ o ∈ r.2.toList, shows o = true)
        intro found
        cases found <;>
          apply result_bind (P := fun r : Sweep × Option Op => ∀ o ∈ r.2.toList, shows o = true)
        all_goals
          intro op h o ho
          exact sweep_step_shown _ _ _ _ _ ho
  exact result h o ho

/-- An actual catalog retry reads the current rooms and emits only that
Sweep.run call's result, without changing the store. -/
theorem sweep_ok (hr : ReadOnly x) (n : Node) (cid : Id) : Egress x (n.sweep x cid) := by
  intro h
  cases hcat : x.catalog with
  | none =>
    simp only [Node.sweep, hcat]
    exact ⟨.refl _, ActsOk.empty _ _⟩
  | some cat =>
    cases hconn : n.conn? cid with
    | none =>
      simp only [Node.sweep, hcat, hconn]
      exact ⟨.refl _, ActsOk.empty _ _⟩
    | some c =>
      obtain ⟨hc, hrd⟩ := hr.catalog cat hcat
      simp only [Node.sweep, hcat, hconn, HeldM.run_bind, refresh_carry hr, hr.retryKey cid h]
      cases hkey : ((x.hooks.retryKey cid).run h).1 with
      | none => exact ⟨.refl _, ActsOk.empty _ _⟩
      | some peer =>
        dsimp only
        cases hstore : x.retryStore with
        | none =>
          simp only [HeldM.run_bind, HeldM.run_pure]
          have he := sweep_reads cat hc hrd (((n.sweeps.find? (fun p => p.1 == cid)).map Prod.snd).getD {})
            ((c.carry (((x.hooks.rooms cid).run h).1)).shows x.fam)
            (if x.deferredRetries then ((n.addr? cid).bind x.retryRoom).getD 0
              else ((n.addr? cid).bind x.room).getD maxFrame) h
          generalize hs : HeldM.run (Sweep.run cat _ _ _) h = result at he ⊢
          obtain ⟨⟨cursor, offered⟩, h'⟩ := result
          dsimp only at he
          subst he
          refine ⟨.refl _, ?_⟩
          intro other b hb
          simp only [HeldM.run_pure, List.mem_map, Prod.mk.injEq, Route.conn.injEq] at hb
          rcases hb with hb | ⟨o, ho, rfl, rfl⟩
          · exact absurd hb List.not_mem_nil
          · exact ⟨o, h', rfl, .refl _, .refl _, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              ⟨c, cat, _, _, hcat, by rw [hs]; exact ho⟩))))⟩
        | some store =>
          simp only [HeldM.run_bind, HeldM.run_pure, (hr.retryStore store hstore).1 peer h]
          have he := sweep_reads cat hc hrd ((store.load peer).run h).1
            ((c.carry (((x.hooks.rooms cid).run h).1)).shows x.fam)
            (if x.deferredRetries then ((n.addr? cid).bind x.retryRoom).getD 0
              else ((n.addr? cid).bind x.room).getD maxFrame) h
          generalize hs : HeldM.run (Sweep.run cat _ _ _) h = result at he ⊢
          obtain ⟨⟨cursor, offered⟩, h'⟩ := result
          dsimp only at he
          subst he
          split
          all_goals
            simp only [HeldM.run_bind, HeldM.run_pure, (hr.retryStore store hstore).2 peer cursor h']
            refine ⟨.refl _, ?_⟩
            intro other b hb
            simp only [HeldM.run_pure, List.mem_map, Prod.mk.injEq, Route.conn.injEq] at hb
            rcases hb with hb | ⟨o, ho, rfl, rfl⟩
            · exact absurd hb List.not_mem_nil
            · exact ⟨o, h', rfl, .refl _, .refl _, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                ⟨c, cat, _, _, hcat, by rw [hs]; exact ho⟩))))⟩

theorem fanout_ok (hr : ReadOnly x) (n : Node) (ids : List Id) : Egress x (n.fanout x ids) := by
  intro h
  unfold Node.fanout
  simp only [HeldM.run_bind]
  generalize hR : HeldM.run (forIn (m := HeldM F) n.conns
    (([], {}, []) : List (Id × Conn) × Acts × List (Id × Id)) _) h = R
  have hP := forIn_inv hR (fun h' (st : List (Id × Conn) × Acts × List (Id × Id)) =>
      h' = h ∧ ActsOk x h h st.2.1) ⟨rfl, ActsOk.empty _ _⟩ (fun a _ st h' ⟨e, hok⟩ => by
    subst e
    have hs := filedGive_reads x.fam x.cfg (a.2.carry (((x.hooks.rooms a.1).run h').1)) ids h'
    refine ⟨by simp only [HeldM.run_bind, refresh_carry hr, HeldM.run_pure, hs], ?_⟩
    simp only [HeldM.run_bind, refresh_carry hr, HeldM.run_pure, ForInStep.value, hs]
    exact hok.append (ActsOk.sends (.refl _) (.refl _)
      (fun o ho => Or.inr (Or.inl ⟨a.2, ids, ho⟩))))
  obtain ⟨e, hok⟩ := hP
  subst e
  simp only [HeldM.run_pure]
  have hm := recordGiven_goes x { n with conns := R.1.1.reverse } R.1.2.2 R.2
  exact ⟨hm, hok.right hm⟩

theorem store_ok (hr : ReadOnly x) (n : Node) (ops : List Op) (mine : Bool) :
    Egress x (n.store x ops mine) := by
  intro h
  unfold Node.store
  simp only [HeldM.run_bind]
  have hp := put_goes x n ops mine h
  generalize (Node.put x n ops mine).run h = P at hp ⊢
  split
  · exact ⟨hp, ActsOk.empty _ _⟩
  · simp only [HeldM.run_bind]
    obtain ⟨hf1, hf2⟩ := fanout_ok hr P.1.1 P.1.2 P.2
    generalize (Node.fanout x P.1.1 P.1.2).run P.2 = Q at hf1 hf2 ⊢
    rw [Std.Legacy.Range.forIn_eq_forIn_range']
    generalize hR : HeldM.run (forIn (m := HeldM F) (List.range' _ _ _) ((Q.1.1, Q.1.2) : Node × Acts) _)
      Q.2 = R
    have hP := forIn_inv hR (fun h' (st : Node × Acts) => Moves x.fam h h' ∧ ActsOk x h h' st.2)
      ⟨hp.trans hf1, hf2.left hp⟩ (fun a _ st h' ⟨hm, hok⟩ => by
        simp only [HeldM.run_bind, hr.react h']
        split
        · exact ⟨hm, hok⟩
        · simp only [HeldM.run_bind]
          have hq := put_goes x st.1 ((x.hooks.react).run h').1 true h'
          generalize (Node.put x st.1 ((x.hooks.react).run h').1 true).run h' = Q2 at hq ⊢
          split
          · exact ⟨hm.trans hq, hok.right hq⟩
          · simp only [HeldM.run_bind]
            obtain ⟨g1, g2⟩ := fanout_ok hr Q2.1.1 Q2.1.2 Q2.2
            exact ⟨hm.trans (hq.trans g1), (hok.right (hq.trans g1)).append (g2.left (hm.trans hq))⟩)
    obtain ⟨hm, hok⟩ := hP
    exact ⟨hm, hok⟩

/-- A step's sends, each fresh at the store the node applies it at: the
node's acts from it, through what it takes and the family's arrival
records, all fresh too. -/
theorem apply_ok (hr : ReadOnly x) (n : Node) (cid : Id) (st : Step) (now : Nat) (h : Held F)
    (hs : ∀ o ∈ st.send, Sent x h cid o) :
    Moves x.fam h ((n.apply x cid st now).run h).2 ∧
      ActsOk x h ((n.apply x cid st now).run h).2 ((n.apply x cid st now).run h).1.2 := by
  unfold Node.apply
  split
  · exact ⟨.refl _, ActsOk.noConn (fun _ _ hb => List.not_mem_nil hb) (fun _ _ hb => List.not_mem_nil hb)⟩
  · simp only [HeldM.run_bind]
    have g1 := recordGiven_goes x { n with conns := n.conns.map fun p => if p.1 = cid then (cid, st.conn) else p }
      (st.given.map (cid, ·)) h
    generalize HeldM.run (Node.recordGiven x _ _) h = A at g1 ⊢
    obtain ⟨g2, g3⟩ := store_ok hr A.1 st.take false A.2
    generalize HeldM.run (Node.store x A.1 st.take false) A.2 = B at g2 g3 ⊢
    generalize hR : HeldM.run (forIn (m := HeldM F) st.take ([] : List Op) _) B.2 = R
    have hP := forIn_inv hR (fun h' (_ : List Op) => h' = B.2) rfl (fun a _ l h' e => by
      subst e; simp only [HeldM.run_bind, HeldM.run_pure]
      exact hr.recv _ _ _ _ _)
    rw [hP]
    obtain ⟨g4, g5⟩ := store_ok hr B.1.1 R.1 true B.2
    have m1 : Moves x.fam h B.2 := g1.trans g2
    simp only [HeldM.run_pure]
    refine ⟨m1.trans g4, ?_⟩
    exact ((ActsOk.split _ (.refl _) (m1.trans g4) hs).append ((g3.left g1).right g4)).append (g5.left m1)

theorem serveOwed_ok (hr : ReadOnly x) (n : Node) (cid : Id) (now : Nat) :
    Egress x (n.serveOwed x cid now) := by
  intro h
  unfold Node.serveOwed
  split
  · exact ⟨.refl _, ActsOk.empty _ _⟩
  · rename_i c _
    split
    · exact ⟨.refl _, ActsOk.empty _ _⟩
    · simp only [HeldM.run_bind, refresh_carry hr]
      have e := serveOwed_reads' x.fam x.cfg (c.carry (((x.hooks.rooms cid).run h).1))
        (((n.addr? cid).bind x.room).getD x.cfg.burst) (n.hotIds x now) h
      generalize hS : HeldM.run (Conn.serveOwed x.fam x.cfg (c.carry (((x.hooks.rooms cid).run h).1))
        (((n.addr? cid).bind x.room).getD x.cfg.burst) (n.hotIds x now)) h = S at e
      obtain ⟨⟨c', urgent, bulk⟩, h'⟩ := S
      simp only at e
      subst e
      refine ⟨.refl _, ?_⟩
      intro cid' b hb
      simp only [HeldM.run_pure, List.mem_map, Prod.mk.injEq, Route.conn.injEq] at hb
      rcases hb with ⟨o, ho, rfl, rfl⟩ | ⟨o, ho, rfl, rfl⟩
      · exact ⟨o, h', rfl, .refl _, .refl _, Or.inr (Or.inr (Or.inr (Or.inl
          ⟨c, _, _, Or.inl (by rw [hS]; exact ho)⟩)))⟩
      · exact ⟨o, h', rfl, .refl _, .refl _, Or.inr (Or.inr (Or.inr (Or.inl
          ⟨c, _, _, Or.inr (by rw [hS]; exact ho)⟩)))⟩

theorem open_ok (hr : ReadOnly x) (n : Node) (cid : Id) (addr : ByteArray) (dialer : Bool) (now : Nat) :
    Egress x (n.open x cid addr dialer now) := by
  intro h
  unfold Node.open
  simp only [HeldM.run_bind, HeldM.run_pure]
  have e := hr.rooms cid h
  refine ⟨.of_eq e.symm, ActsOk.sends (.refl _) (.of_eq e.symm) fun o ho =>
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨dialer, n.floor, now, ho⟩))))⟩

theorem follow_ok (hr : ReadOnly x) (n : Node) (now : Nat) : Egress x (n.follow x now) := by
  intro h
  unfold Node.follow
  simp only [HeldM.run_bind, hr.established h]
  generalize hR1 : HeldM.run (forIn (m := HeldM F) n.managed ((n, {}) : Node × Acts) _) h = R1
  have p1 := forIn_inv hR1 (fun h' (st : Node × Acts) => h' = h ∧ ActsOk x h h st.2)
    ⟨rfl, ActsOk.empty _ _⟩ (fun a _ st h' ⟨e, hok⟩ => by
      subst e
      split
      · exact ⟨rfl, hok.append (ActsOk.noConn (fun _ _ hb => List.not_mem_nil hb)
          (fun _ _ hb => List.not_mem_nil hb))⟩
      · exact ⟨rfl, hok⟩)
  obtain ⟨e1, ok1⟩ := p1
  rw [e1]
  generalize hR2 : HeldM.run (forIn (m := HeldM F) ((x.hooks.established).run h).1
    ((R1.1.1, R1.1.2) : Node × Acts) _) h = R2
  have p2 := forIn_inv hR2 (fun h' (st : Node × Acts) => h' = h ∧ ActsOk x h h st.2)
    ⟨rfl, ok1⟩ (fun a _ st h' ⟨e, hok⟩ => by
      subst e
      split
      · simp only [HeldM.run_bind, HeldM.run_pure]
        obtain ⟨g1, g2⟩ := open_ok hr st.1 a.1 a.2.1 a.2.2 now h'
        have e2 : ((st.1.open x a.1 a.2.1 a.2.2 now).run h').2 = h' := by
          unfold Node.open; simp only [HeldM.run_bind, HeldM.run_pure]; exact hr.rooms _ _
        rw [e2] at g2 ⊢
        exact ⟨rfl, hok.append g2⟩
      · exact ⟨rfl, hok⟩)
  obtain ⟨e2, ok2⟩ := p2
  simp only [HeldM.run_pure]
  rw [e2]
  exact ⟨.refl _, ok2⟩

/-- A frame `seal` sends at h from out: a bare op of out's, or a bundle
of out's payloads for a session, sealed for it at h. -/
def SealedOk (x : Sync F (HeldM F)) (h : Held F) (out : Acts) (e : ByteArray × ByteArray) : Prop :=
  (∃ b, (Route.bare e.1, b) ∈ out.send ∧ e.2 = tagged bareTag b) ∨
  ∃ (cid : Id) (g : List ByteArray) (f : ByteArray), e.2 = tagged sealedTag f ∧
    ((x.hooks.sealFor cid (Codec.encode g)).run h).1 = some f ∧ ∀ q ∈ g, (Route.conn cid, q) ∈ out.send

/-- Changing grouping or transport lanes cannot authorize new payloads. -/
theorem SealedOk.mono {h : Held F} {a b : Acts} {e : ByteArray × ByteArray}
    (ok : SealedOk x h a e) (subset : ∀ p ∈ a.send, p ∈ b.send) : SealedOk x h b e := by
  rcases ok with ⟨p, hp, he⟩ | ⟨cid, g, f, he, hf, hg⟩
  · exact Or.inl ⟨p, subset _ hp, he⟩
  · exact Or.inr ⟨cid, g, f, he, hf, fun q hq => subset _ (hg q hq)⟩

theorem seal_ok (hr : ReadOnly x) (n : Node) (out : Acts) (h : Held F) :
    ((n.seal x out).run h).2 = h ∧ ∀ e ∈ ((n.seal x out).run h).1, SealedOk x h out e := by
  unfold Node.seal
  simp only [HeldM.run_bind]
  generalize hR1 : HeldM.run (forIn (m := HeldM F) out.send
    (([], []) : List (ByteArray × ByteArray) × List Id) _) h = R1
  have p1 := forIn_inv hR1 (fun h' (st : List (ByteArray × ByteArray) × List Id) =>
      h' = h ∧ ∀ e ∈ st.1, SealedOk x h out e) ⟨rfl, fun e he => absurd he List.not_mem_nil⟩
    (fun a ha st h' ⟨e, hok⟩ => by
      subst e
      obtain ⟨r, b⟩ := a
      cases r with
      | bare a' =>
        refine ⟨rfl, fun e he => ?_⟩
        rcases List.mem_cons.1 he with rfl | he
        · exact Or.inl ⟨b, ha, rfl⟩
        · exact hok e he
      | conn cid => dsimp only; split <;> exact ⟨rfl, hok⟩)
  obtain ⟨e1, ok1⟩ := p1
  rw [e1]
  generalize hR2 : HeldM.run (forIn (m := HeldM F) R1.1.2.reverse R1.1.1 _) h = R2
  have p2 := forIn_inv hR2 (fun h' (st : List (ByteArray × ByteArray)) =>
      h' = h ∧ ∀ e ∈ st, SealedOk x h out e) ⟨rfl, ok1⟩ (fun cid _ st h' ⟨e, hok⟩ => by
    subst e
    split
    · rename_i a _
      simp only [HeldM.run_bind]
      generalize hR3 : HeldM.run (forIn (m := HeldM F) (bundles x.cfg.bundle _) st _) h' = R3
      have p3 := forIn_inv hR3 (fun h'' (st : List (ByteArray × ByteArray)) =>
          h'' = h' ∧ ∀ e ∈ st, SealedOk x h' out e) ⟨rfl, hok⟩ (fun g hg st2 h'' ⟨e3, hok3⟩ => by
        subst e3
        simp only [HeldM.run_bind, hr.sealFor _ _ h'']
        split
        · rename_i f hf
          refine ⟨rfl, fun e he => ?_⟩
          rcases List.mem_cons.1 he with rfl | he
          · refine Or.inr ⟨cid, g, f, rfl, hf, fun q hq => ?_⟩
            obtain ⟨⟨r, b⟩, hm, hfe⟩ := List.mem_filterMap.1 (mem_bundles _ _ g hg q hq)
            cases r with
            | bare _ => cases hfe
            | conn c =>
              dsimp only at hfe
              split at hfe
              · rename_i hc; cases hfe; subst hc; exact hm
              · cases hfe
          · exact hok3 e he
        · exact ⟨rfl, hok3⟩)
      obtain ⟨e3, ok3⟩ := p3
      simp only [HeldM.run_pure]
      rw [e3]
      exact ⟨rfl, ok3⟩
    · exact ⟨rfl, hok⟩)
  obtain ⟨e2, ok2⟩ := p2
  simp only [HeldM.run_pure]
  rw [e2]
  exact ⟨rfl, fun e he => ok2 e (List.mem_reverse.1 he)⟩

/-- The reserved lane seals only supplied, already authorized payloads.
Ticket bookkeeping leaves Held unchanged and adds no alternate emitter. -/
theorem sealRetries_ok (hr : ReadOnly x) (n : Node) (retries : List RetryOffer)
    (out : Acts) (h : Held F)
    (authorized : ∀ r ∈ retries, (Route.conn r.cid, r.payload) ∈ out.send) :
    ((n.sealRetries x retries).run h).2 = h ∧
      ∀ e ∈ ((n.sealRetries x retries).run h).1.1, SealedOk x h out e := by
  unfold Node.sealRetries
  simp only [HeldM.run_bind]
  generalize hR : HeldM.run (forIn (m := HeldM F) retries
    (([], []) : List (ByteArray × ByteArray) × List RetryTicket) _) h = R
  have pR := forIn_inv hR (fun h' (st : List (ByteArray × ByteArray) × List RetryTicket) =>
      h' = h ∧ ∀ e ∈ st.1, SealedOk x h out e)
    ⟨rfl, fun _ he => False.elim (List.not_mem_nil he)⟩
    (fun r hr' st h' ⟨he, prior⟩ => by
      subst he
      simp only [HeldM.run_bind, HeldM.run_pure]
      obtain ⟨hs, fresh⟩ := seal_ok hr n { send := [(.conn r.cid, r.payload)] } h'
      rw [hs]
      refine ⟨rfl, fun e hm => ?_⟩
      rcases List.mem_append.1 hm with old | new
      · exact prior e old
      · exact (fresh e new).mono (by
          intro p hp
          have eq : p = (.conn r.cid, r.payload) := List.mem_singleton.mp hp
          rw [eq]
          exact authorized r hr'))
  simp only [HeldM.run_pure]
  exact pR

theorem effectsPurge_goes (ids : List Id) (scrub : Bool) : Goes x.fam (Effects.purge x ids scrub) := by
  unfold Effects.purge
  intro h
  split
  · exact .single (.purge ids scrub h)
  · exact .refl _

/-- Handing out the outbox adds only bare sends. -/
theorem flush_ok (hr : ReadOnly x) (n : Node) (out : Acts) (h : Held F) :
    Moves x.fam h ((n.flush x out).run h).2 ∧ ∀ cid b,
      ((Route.conn cid, b) ∈ ((n.flush x out).run h).1.2.send ∨
        (Route.conn cid, b) ∈ ((n.flush x out).run h).1.2.serve) →
      ((Route.conn cid, b) ∈ out.send ∨ (Route.conn cid, b) ∈ out.serve) := by
  unfold Node.flush
  simp only [HeldM.run_bind, hr.outbox h, hr.stale h]
  split
  · exact ⟨.refl _, fun _ _ hb => hb⟩
  · simp only [HeldM.run_bind, HeldM.run_pure]
    refine ⟨effectsPurge_goes _ _ _, fun cid b hb => ?_⟩
    simp only [Acts.append_def, List.mem_append, List.mem_map, List.append_nil] at hb
    rcases hb with (hb | ⟨_, _, e⟩) | hb
    · exact Or.inl hb
    · simp only [Prod.mk.injEq] at e; exact absurd e.1 (by intro h; cases h)
    · exact Or.inr hb

theorem endSession_goes (hr : ReadOnly x) (cid : Id) : Goes x.fam (Node.endSession x cid) :=
  Goes.bind' (hr.closing cid).goes fun _ => effectsPurge_goes _ _

/-- **What an entry point sends, run from h0 to h1:** each frame is a
bare op to an address, or a bundle of payloads sealed for a session at a
store on the way, each payload the bytes of a fresh step's send on that
session at a store on the way. -/
def FramesBy (x : Sync F (HeldM F)) (P : Held F → Id → Op → Prop) (h0 h1 : Held F) (e : Effects) : Prop :=
  ∀ a p, (a, p) ∈ e.send → (∃ b, p = tagged bareTag b) ∨
    ∃ (cid : Id) (g : List ByteArray) (f : ByteArray) (h : Held F), p = tagged sealedTag f ∧
      Moves x.fam h0 h ∧ Moves x.fam h h1 ∧ ((x.hooks.sealFor cid (Codec.encode g)).run h).1 = some f ∧
      ∀ q ∈ g, ∃ o h', q = o.bytes ∧ Moves x.fam h0 h' ∧ Moves x.fam h' h1 ∧ P h' cid o

/-- Each payload a fresh step's send (`Sent`). -/
abbrev FramesOk (x : Sync F (HeldM F)) : Held F → Held F → Effects → Prop := FramesBy x (Sent x)

/-- What holds of every fresh step's send holds of every payload. -/
theorem FramesBy.mono {P Q : Held F → Id → Op → Prop} {h0 h1 : Held F} {e : Effects}
    (hPQ : ∀ h cid o, P h cid o → Q h cid o) (hp : FramesBy x P h0 h1 e) : FramesBy x Q h0 h1 e := by
  intro a p hap
  rcases hp a p hap with hb | ⟨cid, g, f, h, e1, m0, m1, hf, hq⟩
  · exact Or.inl hb
  · refine Or.inr ⟨cid, g, f, h, e1, m0, m1, hf, fun q hq' => ?_⟩
    obtain ⟨o, h', e2, m2, m3, ho⟩ := hq q hq'
    exact ⟨o, h', e2, m2, m3, hPQ h' cid o ho⟩

/-- Every entry point ends in `finish`: from acts whose session sends
are fresh, it sends only frames `FramesOk` allows. -/
theorem finish_ok (hr : ReadOnly x) (n : Node) (out : Acts) (now : Nat) {h0 h : Held F}
    (m0 : Moves x.fam h0 h) (hok : ActsOk x h0 h out) :
    Moves x.fam h ((n.finish x out now).run h).2 ∧
      FramesOk x h0 ((n.finish x out now).run h).2 ((n.finish x out now).run h).1.2 := by
  unfold Node.finish
  simp only [HeldM.run_bind]
  obtain ⟨f1, f2⟩ := follow_ok hr n now h
  generalize HeldM.run (Node.follow x n now) h = A at f1 f2 ⊢
  obtain ⟨g1, g2⟩ := flush_ok hr A.1.1 out A.2
  generalize HeldM.run (Node.flush x A.1.1 out) A.2 = B at g1 g2 ⊢
  rw [hr.retired B.2]
  generalize (x.hooks.retired.run B.2).1 = ret
  generalize List.foldl Node.drop B.1.1 ret = N
  have mB : Moves x.fam h B.2 := f1.trans g1
  have okO : ActsOk x h0 B.2 (B.1.2 ++ A.1.2) := by
    refine ActsOk.append ?_ ((f2.left m0).right g1)
    intro cid b hb
    obtain ⟨o, h', e, m1, m2, hs⟩ := hok cid b (g2 cid b hb)
    exact ⟨o, h', e, m1, m2.trans mB, hs⟩
  let merged := B.1.2 ++ A.1.2
  let out' := { merged with drop := merged.drop ++ ret }
  let retries := merged.retry.filter fun r => merged.serve.contains (.conn r.cid, r.payload)
  let ordinary := merged.serve.filter fun p => !retries.any fun r => p == (.conn r.cid, r.payload)
  obtain ⟨s1, t1⟩ := seal_ok hr N out' B.2
  rw [s1]
  obtain ⟨s2, t2⟩ := seal_ok hr N { send := ordinary } B.2
  rw [s2]
  have authorized : ∀ r ∈ retries, (Route.conn r.cid, r.payload) ∈ merged.serve := by
    letI : LawfulBEq ByteArray := byteArray_lawfulBEq
    intro r hr'
    exact List.contains_iff_mem.mp (List.mem_filter.1 hr').2
  obtain ⟨s3, t3⟩ := sealRetries_ok hr N retries { send := merged.serve } B.2 authorized
  rw [s3]
  generalize hR : HeldM.run (forIn (m := HeldM F) ((B.1.2 ++ A.1.2).drop ++ ret) (_ : List Id) _) B.2 = R
  have pR := forIn_inv hR (fun h' (_ : List Id) => Moves x.fam B.2 h') (.refl _) (fun cid _ l h' hm => by
    simp only [HeldM.run_bind, HeldM.run_pure]; exact hm.trans (endSession_goes hr cid h'))
  simp only [HeldM.run_pure]
  refine ⟨mB.trans pR, fun a p hp => ?_⟩
  rcases List.mem_append.1 hp with hp | hp
  · rcases List.mem_append.1 hp with hp | hp
    · rcases t1 (a, p) hp with ⟨b, _, e⟩ | ⟨cid, g, f, e, hf, hq⟩
      · exact Or.inl ⟨b, e⟩
      · refine Or.inr ⟨cid, g, f, B.2, e, m0.trans mB, pR, hf, fun q hq' => ?_⟩
        obtain ⟨o, h', e', m1, m2, hs⟩ := okO cid q (Or.inl (hq q hq'))
        exact ⟨o, h', e', m1, m2.trans pR, hs⟩
    · rcases t2 (a, p) hp with ⟨b, _, e⟩ | ⟨cid, g, f, e, hf, hq⟩
      · exact Or.inl ⟨b, e⟩
      · refine Or.inr ⟨cid, g, f, B.2, e, m0.trans mB, pR, hf, fun q hq' => ?_⟩
        obtain ⟨o, h', e', m1, m2, hs⟩ := okO cid q (Or.inr (List.mem_filter.1 (hq q hq')).1)
        exact ⟨o, h', e', m1, m2.trans pR, hs⟩
  · rcases t3 (a, p) hp with ⟨b, _, e⟩ | ⟨cid, g, f, e, hf, hq⟩
    · exact Or.inl ⟨b, e⟩
    · refine Or.inr ⟨cid, g, f, B.2, e, m0.trans mB, pR, hf, fun q hq' => ?_⟩
      obtain ⟨o, h', e', m1, m2, hs⟩ := okO cid q (Or.inr (hq q hq'))
      exact ⟨o, h', e', m1, m2.trans pR, hs⟩

theorem FramesOk.empty (h0 h1 : Held F) : FramesOk x h0 h1 {} :=
  fun _ _ hp => absurd hp List.not_mem_nil

/-! ## The entry points -/

/-- **A local write.** -/
theorem onWrite_fresh (hr : ReadOnly x) (n : Node) (ops : List Op) (now : Nat) (h : Held F) :
    Moves x.fam h ((n.onWrite x ops now).run h).2 ∧
      FramesOk x h ((n.onWrite x ops now).run h).2 ((n.onWrite x ops now).run h).1.2 := by
  unfold Node.onWrite
  simp only [HeldM.run_bind]
  obtain ⟨m1, ok1⟩ := store_ok hr n ops true h
  generalize HeldM.run (Node.store x n ops true) h = A at m1 ok1 ⊢
  obtain ⟨m2, ok2⟩ := finish_ok hr (A.1.1.heat x A.1.1.fresh now) A.1.2 now m1 ok1
  exact ⟨m1.trans m2, ok2⟩

/-- **A socket closing.** -/
theorem onClose_fresh (hr : ReadOnly x) (n : Node) (addr : ByteArray) (now : Nat) (h : Held F) :
    Moves x.fam h ((n.onClose x addr now).run h).2 ∧
      FramesOk x h ((n.onClose x addr now).run h).2 ((n.onClose x addr now).run h).1.2 := by
  unfold Node.onClose
  exact finish_ok hr _ _ now (.refl h)
    (ActsOk.noConn (fun _ _ hb => List.not_mem_nil hb) (fun _ _ hb => List.not_mem_nil hb))

/-- **The clock.** -/
theorem onTickDirect_fresh (hr : ReadOnly x) (n : Node) (now : Nat) (h : Held F) :
    Moves x.fam h ((n.onTickDirect x now).run h).2 ∧
      FramesOk x h ((n.onTickDirect x now).run h).2 ((n.onTickDirect x now).run h).1.2 := by
  unfold Node.onTickDirect
  simp only [HeldM.run_bind, hr.dial now h]
  obtain ⟨m1, ok1⟩ := store_ok hr n ((x.hooks.dial now).run h).1 true h
  generalize HeldM.run (Node.store x n ((x.hooks.dial now).run h).1 true) h = A at m1 ok1 ⊢
  generalize hR : HeldM.run (forIn (m := HeldM F) A.1.1.conns ((A.1.1, A.1.2) : Node × Acts) _) A.2 = R
  have pR := forIn_inv hR (fun h' (st : Node × Acts) => Moves x.fam h h' ∧ ActsOk x h h' st.2)
    ⟨m1, ok1⟩ (fun a _ st h' ⟨hm, hok⟩ => by
      split
      · exact ⟨hm, hok⟩
      · rename_i c _
        simp only [HeldM.run_bind, refresh_carry hr]
        split
        · exact ⟨hm, hok⟩
        · simp only [HeldM.run_bind]
          have e := tickGive_reads x.fam x.cfg st.1.ix (c.carry (((x.hooks.rooms a.1).run h').1)) now h'
          generalize hS : HeldM.run (Conn.tickGive x.fam x.cfg st.1.ix (c.carry (((x.hooks.rooms a.1).run h').1)) now) h' = S at e
          rw [e]
          obtain ⟨g1, g2⟩ := apply_ok hr st.1 a.1 S.1 now h' (fun o ho =>
            Or.inr (Or.inr (Or.inl ⟨c, st.1.ix, now, by rw [hS]; exact ho⟩)))
          generalize HeldM.run (Node.apply x st.1 a.1 S.1 now) h' = B at g1 g2 ⊢
          obtain ⟨g3, g4⟩ := sweep_ok (hr.afterActs B.1.1 (st.2 ++ B.1.2)) B.1.1 a.1 B.2
          change Moves x.fam B.2 _ at g3
          change ActsOk x B.2 _ _ at g4
          generalize HeldM.run (Node.sweep _ B.1.1 a.1) B.2 = C at g3 g4 ⊢
          obtain ⟨g5, g6⟩ := serveOwed_ok (hr.afterActs C.1.1 (st.2 ++ B.1.2 ++ C.1.2)) C.1.1 a.1 now C.2
          change Moves x.fam C.2 _ at g5
          change ActsOk x C.2 _ _ at g6
          simp only [HeldM.run_pure]
          refine ⟨hm.trans (g1.trans (g3.trans g5)), ?_⟩
          exact (((hok.right (g1.trans (g3.trans g5))).append
            ((g2.left hm).right (g3.trans g5))).append
            ((g4.left (hm.trans g1)).right g5)).append
            (g6.left (hm.trans (g1.trans g3))))
  obtain ⟨mR, okR⟩ := pR
  obtain ⟨m2, ok2⟩ := finish_ok hr R.1.1 R.1.2 now mR okR
  exact ⟨mR.trans m2, ok2⟩

/-- The runtime retry admission pass can only retain already-authorized
acts or append an actual freshly authorized sweep. Pure ordering and candidate
refusal introduce no additional emitter. -/
theorem sweepAll_ok (hr : ReadOnly x) (n : Node) (ready : List Id) (out : Acts)
    {h0 h : Held F} (hm : Moves x.fam h0 h) (hok : ActsOk x h0 h out) :
    Moves x.fam h0 ((n.sweepAll x ready out).run h).2 ∧
      ActsOk x h0 ((n.sweepAll x ready out).run h).2 ((n.sweepAll x ready out).run h).1.2 := by
  unfold Node.sweepAll
  simp only [HeldM.run_bind]
  generalize hR : HeldM.run (forIn (m := HeldM F)
    (RetryOrder.reconcile (n.conns.map Prod.fst) n.retryOrder)
    ((n, out, [], out.retry.filterMap (fun r => n.addr? r.cid)) : Node × Acts × List Id × List ByteArray) _) h = R
  have pR := forIn_inv hR (fun h' (st : Node × Acts × List Id × List ByteArray) =>
      Moves x.fam h0 h' ∧ ActsOk x h0 h' st.2.1) ⟨hm, hok⟩
    (fun cid _ st h' ⟨hm, hok⟩ => by
      split
      · exact ⟨hm, hok⟩
      · simp only [HeldM.run_bind]
        cases mode : x.deferredRetries
        · simp only [Bool.false_eq_true, ↓reduceIte]
          obtain ⟨m, ok⟩ := sweep_ok (hr.afterActs st.1 st.2.1) st.1 cid h'
          change Moves x.fam h' _ at m
          change ActsOk x h' _ _ at ok
          simp only [HeldM.run_pure, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
          exact ⟨hm.trans m, (hok.right m).append (ok.left hm)⟩
        · simp only [↓reduceIte]
          obtain ⟨m, ok⟩ := sweep_ok hr st.1 cid h'
          split
          · exact ⟨hm.trans m, hok.right m⟩
          · exact ⟨hm.trans m, (hok.right m).append (ok.left hm)⟩)
  simp only [HeldM.run_pure]
  exact pR

/-- The production clock preserves the same fresh authorization provenance,
including the separately ordered reserved retry pass. -/
theorem onTickReserved_fresh (hr : ReadOnly x) (n : Node) (now : Nat) (h : Held F) :
    Moves x.fam h ((n.onTickReserved x now).run h).2 ∧
      FramesOk x h ((n.onTickReserved x now).run h).2 ((n.onTickReserved x now).run h).1.2 := by
  unfold Node.onTickReserved
  simp only [HeldM.run_bind, hr.dial now h]
  obtain ⟨m1, ok1⟩ := store_ok hr n ((x.hooks.dial now).run h).1 true h
  generalize HeldM.run (Node.store x n ((x.hooks.dial now).run h).1 true) h = A at m1 ok1 ⊢
  generalize hR : HeldM.run (forIn (m := HeldM F) A.1.1.conns
    ((A.1.1, A.1.2, []) : Node × Acts × List Id) _) A.2 = R
  have pR := forIn_inv hR (fun h' (st : Node × Acts × List Id) => Moves x.fam h h' ∧ ActsOk x h h' st.2.1)
    ⟨m1, ok1⟩ (fun a _ st h' ⟨hm, hok⟩ => by
      split
      · exact ⟨hm, hok⟩
      · rename_i c _
        simp only [HeldM.run_bind, refresh_carry hr]
        split
        · exact ⟨hm, hok⟩
        · simp only [HeldM.run_bind]
          have e := tickGive_reads x.fam x.cfg st.1.ix (c.carry (((x.hooks.rooms a.1).run h').1)) now h'
          generalize hS : HeldM.run (Conn.tickGive x.fam x.cfg st.1.ix (c.carry (((x.hooks.rooms a.1).run h').1)) now) h' = S at e
          rw [e]
          obtain ⟨g1, g2⟩ := apply_ok hr st.1 a.1 S.1 now h' (fun o ho =>
            Or.inr (Or.inr (Or.inl ⟨c, st.1.ix, now, by rw [hS]; exact ho⟩)))
          generalize HeldM.run (Node.apply x st.1 a.1 S.1 now) h' = B at g1 g2 ⊢
          obtain ⟨g3, g4⟩ := serveOwed_ok (hr.afterActs B.1.1 (st.2.1 ++ B.1.2)) B.1.1 a.1 now B.2
          change Moves x.fam B.2 _ at g3
          change ActsOk x B.2 _ _ at g4
          simp only [HeldM.run_pure]
          refine ⟨hm.trans (g1.trans g3), ?_⟩
          exact ((hok.right (g1.trans g3)).append ((g2.left hm).right g3)).append
            (g4.left (hm.trans g1)))
  obtain ⟨mR, okR⟩ := pR
  obtain ⟨mS, okS⟩ := sweepAll_ok hr R.1.1 R.1.2.2 R.1.2.1 mR okR
  generalize HeldM.run (Node.sweepAll x R.1.1 R.1.2.2 R.1.2.1) R.2 = S at mS okS ⊢
  obtain ⟨m2, ok2⟩ := finish_ok hr S.1.1 S.1.2 now mS okS
  exact ⟨mS.trans m2, ok2⟩

/-- **The clock**, for both actual dispatcher branches. -/
theorem onTick_fresh (hr : ReadOnly x) (n : Node) (now : Nat) (h : Held F) :
    Moves x.fam h ((n.onTick x now).run h).2 ∧
      FramesOk x h ((n.onTick x now).run h).2 ((n.onTick x now).run h).1.2 := by
  unfold Node.onTick
  split
  · exact onTickReserved_fresh hr n now h
  · exact onTickDirect_fresh hr n now h

/-- **A sealed frame, as `openFrame` gave it.** -/
theorem onSealed_fresh (hr : ReadOnly x) (n : Node) (addr : ByteArray) (opened : Option (Id × ByteArray))
    (now : Nat) (h : Held F) :
    Moves x.fam h ((n.onSealed x addr opened now).run h).2 ∧
      FramesOk x h ((n.onSealed x addr opened now).run h).2 ((n.onSealed x addr opened now).run h).1.2 := by
  unfold Node.onSealed
  split
  · exact ⟨.refl _, FramesOk.empty _ _⟩
  · rename_i cid bundle
    split
    · simp only [HeldM.run_bind]
      generalize hR : HeldM.run (forIn (m := HeldM F) (_ : List ByteArray)
        ((n.setAddr cid addr, {}) : Node × Acts) _) h = R
      have pR := forIn_inv hR (fun h' (st : Node × Acts) => Moves x.fam h h' ∧ ActsOk x h h' st.2)
        ⟨.refl _, ActsOk.empty _ _⟩ (fun b _ st h' ⟨hm, hok⟩ => by
          split
          · rename_i c _
            simp only [HeldM.run_bind, refresh_carry hr]
            have e := recv_reads x.fam x.cfg st.1.ix (c.carry (((x.hooks.rooms cid).run h').1)) b now h'
            generalize hS : HeldM.run (Conn.recv x.fam x.cfg st.1.ix (c.carry (((x.hooks.rooms cid).run h').1)) b now) h' = S at e
            rw [e]
            obtain ⟨g1, g2⟩ := apply_ok hr st.1 cid S.1 now h' (fun o ho =>
              Or.inl ⟨c, st.1.ix, b, now, by rw [hS]; exact ho⟩)
            simp only [HeldM.run_pure]
            exact ⟨hm.trans g1, (hok.right g1).append (g2.left hm)⟩
          · exact ⟨hm, hok⟩)
      obtain ⟨mR, okR⟩ := pR
      obtain ⟨g3, g4⟩ := serveOwed_ok hr R.1.1 cid now R.2
      generalize HeldM.run (Node.serveOwed x R.1.1 cid now) R.2 = B at g3 g4 ⊢
      obtain ⟨m2, ok2⟩ := finish_ok hr B.1.1 (R.1.2 ++ B.1.2) now (mR.trans g3)
        ((okR.right g3).append (g4.left mR))
      exact ⟨(mR.trans g3).trans m2, ok2⟩
    · exact ⟨.refl _, FramesOk.empty _ _⟩

/-- **A payload from an address:** a bare op (the handshake's), or a
sealed frame on a session. -/
theorem onFrame_fresh (hr : ReadOnly x) (n : Node) (addr bytes : ByteArray) (now : Nat) (h : Held F) :
    Moves x.fam h ((n.onFrame x addr bytes now).run h).2 ∧
      FramesOk x h ((n.onFrame x addr bytes now).run h).2 ((n.onFrame x addr bytes now).run h).1.2 := by
  unfold Node.onFrame
  split
  · dsimp only
    split
    · exact ⟨.refl _, FramesOk.empty _ _⟩
    · rename_i o _
      split
      · exact ⟨.refl _, FramesOk.empty _ _⟩
      · simp only [HeldM.run_bind]
        have m1 := write_goes x n (intakeConn x.fam [o]) h
        generalize HeldM.run (Node.write x n (intakeConn x.fam [o])) h = A at m1 ⊢
        rw [hr.recv none addr o now A.2]
        obtain ⟨m2, ok2⟩ := store_ok hr A.1.1 ((x.hooks.recv none addr o now).run A.2).1 true A.2
        generalize HeldM.run (Node.store x A.1.1 _ true) A.2 = B at m2 ok2 ⊢
        obtain ⟨m3, ok3⟩ := finish_ok hr B.1.1 B.1.2 now (m1.trans m2) (ok2.left m1)
        exact ⟨(m1.trans m2).trans m3, ok3⟩
  · simp only [HeldM.run_bind, hr.openFrame _ h]
    exact onSealed_fresh hr n addr _ now h
  · exact ⟨.refl _, FramesOk.empty _ _⟩

/-- The node's entry points, as the runner calls them (engine/wire/Tcp.lean):
a payload from an address, the clock, a local write, a socket closing. -/
inductive Entry (x : Sync F (HeldM F)) : (Node → HeldM F (Node × Effects)) → Prop
  | frame (addr bytes : ByteArray) (now : Nat) : Entry x fun n => n.onFrame x addr bytes now
  | tick (now : Nat) : Entry x fun n => n.onTick x now
  | write (ops : List Op) (now : Nat) : Entry x fun n => n.onWrite x ops now
  | close (addr : ByteArray) (now : Nat) : Entry x fun n => n.onClose x addr now

/-- **Every connection step reads its rooms afresh** (`entry_fresh`).
Whatever entry point the node runs, from any store, it changes the store
only by write turns and purges, and every frame it sends is a bare op or
a bundle sealed for one session, each of whose payloads is an op that a
connection step sent, at a store on the way, on the session's
connection as that store gave its rooms. -/
theorem entry_fresh (hr : ReadOnly x) {E : Node → HeldM F (Node × Effects)} (hE : Entry x E)
    (n : Node) (h : Held F) :
    Moves x.fam h ((E n).run h).2 ∧ FramesOk x h ((E n).run h).2 ((E n).run h).1.2 := by
  cases hE with
  | frame addr bytes now => exact onFrame_fresh hr n addr bytes now h
  | tick now => exact onTick_fresh hr n now h
  | write ops now => exact onWrite_fresh hr n ops now h
  | close addr now => exact onClose_fresh hr n addr now h

end

end Engine.Sync
