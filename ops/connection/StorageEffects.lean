/- Store effects of the actual Node event handlers, including production
hooks with advancing entropy, reactions, courier purges and session closes. -/
import ops.connection.HooksTape
import ops.sync.StoreEvolution
import ops.sync.SimLaws
import engine.wire.Loop

namespace Connection.Execution
open Engine Engine.Sync

/-- Only the store is constrained. In particular, entropy state can advance. -/
def GoesM (fam : Family F) {α} (p : M α) : Prop :=
  ∀ s, Moves fam s.held (p s).2.held

theorem ReadsHeld.goes {fam : Family F} {α} {p : M α} (h : ReadsHeld p) : GoesM fam p :=
  fun s => Moves.of_eq (h s).symm

namespace GoesM
theorem pure' (fam : Family F) {α} (a : α) : GoesM fam (pure a : M α) := fun _ => .refl _
theorem bind' {fam : Family F} {α β} {p : M α} {k : α → M β}
    (hp : GoesM fam p) (hk : ∀ a, GoesM fam (k a)) : GoesM fam (p >>= k) :=
  fun s => (hp s).trans (hk _ _)
theorem forIn' {fam : Family F} {α β} (l : List α) (b : β)
    {f : α → β → M (ForInStep β)} (hf : ∀ a b, GoesM fam (f a b)) :
    GoesM fam (forIn l b f) := by
  induction l generalizing b with
  | nil => exact pure' fam b
  | cons a t ih =>
    rw [List.forIn_cons]
    apply bind' (hf a b)
    intro r
    cases r with
    | done b => exact pure' fam b
    | yield b => exact ih b
theorem getOp' (fam : Family F) (i : Id) : GoesM fam (Store.getOp i : M _) :=
  (ReadsHeld.getOp' i).goes
theorem getStatus' (fam : Family F) (i : Id) : GoesM fam (Store.getStatus i : M _) :=
  (ReadsHeld.getStatus' i).goes
theorem turn' (fam : Family F) (ops : List Op) : GoesM fam (Turn.turn fam ops : M Unit) :=
  fun _ => .single (.turn _ _)
theorem purge' (fam : Family F) (ids : List Id) (scrub : Bool) :
    GoesM fam (Turn.purge fam ids scrub : M Unit) := fun _ => .single (.purge ids scrub _)
end GoesM

syntax "goesTape" "[" term,* "]" : tactic
macro_rules
  | `(tactic| goesTape [$ts,*]) => do
    let mut tac : Lean.TSyntax `tactic ← `(tactic| first | split | intro)
    for t in ts.getElems.reverse do
      tac ← `(tactic| first | with_reducible_and_instances apply $t | $tac:tactic)
    `(tactic| repeat' (first
      | dsimp only | with_reducible_and_instances apply GoesM.bind'
      | with_reducible_and_instances apply GoesM.pure' | with_reducible_and_instances apply GoesM.forIn'
      | with_reducible_and_instances apply GoesM.getOp' | with_reducible_and_instances apply GoesM.getStatus'
      | with_reducible_and_instances apply GoesM.turn' | with_reducible_and_instances apply GoesM.purge'
      | $tac:tactic))

namespace NodeTape

structure ReadOnly (x : Sync F M) : Prop where
  rooms : ∀ cid, ReadsHeld (x.hooks.rooms cid)
  recv : ∀ via a o t, ReadsHeld (x.hooks.recv via a o t)
  outbox : ReadsHeld x.hooks.outbox
  closing : ∀ cid, ReadsHeld (x.hooks.closing cid)
  retired : ReadsHeld x.hooks.retired
  react : ReadsHeld x.hooks.react
  dial : ∀ t, ReadsHeld (x.hooks.dial t)
  established : ReadsHeld x.hooks.established
  sealFor : ∀ cid b, ReadsHeld (x.hooks.sealFor cid b)
  openFrame : ∀ b, ReadsHeld (x.hooks.openFrame b)
  catalog : ∀ cat, x.catalog = some cat → ReadsHeld cat.ceiling ∧ ∀ i, ReadsHeld (cat.read i)
  retryKey : ∀ cid, ReadsHeld (x.hooks.retryKey cid)
  retryStore : ∀ store, x.retryStore = some store →
    (∀ peer, ReadsHeld (store.load peer)) ∧ (∀ peer cursor, ReadsHeld (store.save peer cursor))

/-- Discharges every hook premise for the actual advancing-tape interpreter. -/
theorem production_readOnly (S : Setup) (side : Side) : ReadOnly (S.sync side) := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11⟩ :=
    hooks_reads ReadsHeld.fresh family sodium (S.addr side)
  refine ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10, ?_, h11, ?_⟩
  · intro cat hcat
    cases hcat
    exact ⟨fun _ => rfl, fun _ _ => rfl⟩
  · intro store hstore
    cases hstore
    exact ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem ReadOnly.afterActs {x : Sync F M} (hr : ReadOnly x) (n : Engine.Sync.Node) (out : Acts) :
    ReadOnly (n.afterActs x out) :=
  ⟨hr.rooms, hr.recv, hr.outbox, hr.closing, hr.retired, hr.react, hr.dial,
    hr.established, hr.sealFor, hr.openFrame, hr.catalog, hr.retryKey, hr.retryStore⟩

theorem sweep_reads (cat : Catalog M) (hc : ReadsHeld cat.ceiling)
    (hr : ∀ i, ReadsHeld (cat.read i)) (cursor : Sweep) (shows : Op → Bool) (room : Nat) :
    ReadsHeld (Sweep.run (F := F) cat cursor shows room) := by
  unfold Sweep.run
  readsHeld [hc, hr]

theorem read_program {α} (p : Read α) : ReadsHeld (p.run (Store.getOp (F := F)) : M α) := by
  induction p with
  | done a => exact ReadsHeld.pure' a
  | get i next ih => exact ReadsHeld.bind' (ReadsHeld.getOp' i) ih

variable (fam : Family F) (cfg : Config)

theorem holdsIn_reads (r i : Id) : ReadsHeld (holdsIn fam r i : M Bool) := by
  unfold holdsIn; readsHeld []
theorem onHold_reads (c : Conn) (r : Id) (ids : List Id) :
    ReadsHeld (c.onHold fam cfg r ids : M Step) := by
  unfold Conn.onHold; readsHeld [holdsIn_reads]
theorem filed_reads (c : Conn) (ids : List Id) : ReadsHeld (c.filed fam cfg ids : M Step) := by
  unfold Conn.filed; readsHeld []
theorem closure_reads (r : Id) (fuel : Nat) : ∀ todo seen,
    ReadsHeld (closureOps fam r fuel todo seen : M (List Op)) := by
  induction fuel with
  | zero => intro todo seen; rw [closureOps_zero]; exact ReadsHeld.pure' _
  | succ n ih =>
    intro todo
    induction todo with
    | nil => intro seen; rw [closureOps_nil]; exact ReadsHeld.pure' _
    | cons y rest ihr =>
      intro seen
      rw [closureOps_cons]
      split
      · exact ihr seen
      · refine ReadsHeld.bind' (ReadsHeld.getOp' y) fun oo => ?_
        cases oo with
        | none => exact ih _ _
        | some o =>
          dsimp only
          split
          · exact ReadsHeld.bind' (ih _ _) fun _ => ReadsHeld.pure' _
          · exact ih _ _
theorem give_reads : ∀ (l : List (Id × Id)) (c : Conn), ReadsHeld (c.give fam cfg l : M Step)
  | [], _ => ReadsHeld.pure' _
  | (r,x) :: rest, c => by
    unfold Conn.give
    split
    · exact give_reads rest c
    · exact ReadsHeld.bind' (closure_reads fam r _ _ _) fun _ =>
        ReadsHeld.bind' (give_reads rest _) fun _ => ReadsHeld.pure' _
theorem filedGive_reads (c : Conn) (ids : List Id) : ReadsHeld (c.filedGive fam cfg ids : M Step) := by
  unfold Conn.filedGive Conn.notify; readsHeld [give_reads, filed_reads]
theorem walkN_reads : ∀ budget (c : Conn) offer,
    ReadsHeld (c.walkN fam cfg offer budget : M (Conn × List (Id × Id)))
  | 0, _, _ => ReadsHeld.pure' _
  | budget + 1, c, offer => by
    unfold Conn.walkN
    readsHeld [walkN_reads budget]
theorem tickGive_reads (ix : Index) (c : Conn) (now : Nat) :
    ReadsHeld (c.tickGive fam cfg ix now : M Step) := by
  unfold Conn.tickGive Conn.notify Conn.tick Conn.work Conn.walk
  readsHeld [give_reads, walkN_reads]
theorem recv_reads (ix : Index) (c : Conn) (bytes : ByteArray) (now : Nat) :
    ReadsHeld (Conn.recv fam cfg ix c bytes now : M Step) := by
  unfold Conn.recv; readsHeld [onHold_reads]
theorem serveOwed_reads (c : Conn) (budget : Nat) (first : List Id) :
    ReadsHeld (c.serveOwed fam cfg budget first : M (Conn × List Op × List Op)) := by
  unfold Conn.serveOwed; readsHeld [read_program]

variable {fam cfg}
variable (x : Sync F M) (hr : ReadOnly x)

theorem write_goes (n : Engine.Sync.Node) (ops : List Op) : GoesM x.fam (n.write x ops) := by
  unfold Node.write; goesTape []
theorem put_goes (n : Engine.Sync.Node) (ops : List Op) (mine : Bool) : GoesM x.fam (n.put x ops mine) :=
  write_goes x n _
theorem recordGiven_goes (n : Engine.Sync.Node) (st : List (Id × Id)) : GoesM x.fam (n.recordGiven x st) := by
  unfold Node.recordGiven; goesTape [put_goes]
include hr

theorem refresh_reads (cid : Id) (c : Conn) : ReadsHeld (Node.refresh x cid c) := by
  unfold Node.refresh; readsHeld [hr.rooms]
theorem fanout_goes (n : Engine.Sync.Node) (ids : List Id) : GoesM x.fam (n.fanout x ids) := by
  unfold Node.fanout
  goesTape [fun cid c => (refresh_reads x hr cid c).goes,
    fun c ids => (filedGive_reads x.fam x.cfg c ids).goes, recordGiven_goes]
theorem store_goes (n : Engine.Sync.Node) (ops : List Op) (mine : Bool) : GoesM x.fam (n.store x ops mine) := by
  unfold Node.store
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  goesTape [put_goes, fanout_goes x hr, hr.react.goes]
theorem open_goes (n : Engine.Sync.Node) (cid : Id) (addr : ByteArray) (dialer : Bool) (now : Nat) :
    GoesM x.fam (n.open x cid addr dialer now) := by
  unfold Node.open; goesTape [fun cid => (hr.rooms cid).goes]
theorem follow_goes (n : Engine.Sync.Node) (now : Nat) : GoesM x.fam (n.follow x now) := by
  unfold Node.follow; goesTape [hr.established.goes, open_goes x hr]
omit hr in
theorem effectsPurge_goes (ids : List Id) (scrub : Bool) : GoesM x.fam (Effects.purge x ids scrub) := by
  unfold Effects.purge; goesTape []
theorem flush_goes (n : Engine.Sync.Node) (out : Acts) : GoesM x.fam (n.flush x out) := by
  unfold Node.flush; goesTape [hr.outbox.goes, effectsPurge_goes]
theorem seal_goes (n : Engine.Sync.Node) (out : Acts) : GoesM x.fam (n.seal x out) := by
  unfold Node.seal; goesTape [fun cid b => (hr.sealFor cid b).goes]
theorem sealRetries_goes (n : Engine.Sync.Node) (retries : List RetryOffer) :
    GoesM x.fam (n.sealRetries x retries) := by
  unfold Node.sealRetries; goesTape [seal_goes x hr]
theorem endSession_goes (cid : Id) : GoesM x.fam (Node.endSession x cid) := by
  unfold Node.endSession; goesTape [fun cid => (hr.closing cid).goes, effectsPurge_goes]
theorem finish_goes (n : Engine.Sync.Node) (out : Acts) (now : Nat) : GoesM x.fam (n.finish x out now) := by
  unfold Node.finish
  goesTape [follow_goes x hr, flush_goes x hr, hr.retired.goes, seal_goes x hr,
    sealRetries_goes x hr, endSession_goes x hr]
theorem onClose_goes (n : Engine.Sync.Node) (addr : ByteArray) (now : Nat) : GoesM x.fam (n.onClose x addr now) := by
  unfold Node.onClose; goesTape [finish_goes x hr]
theorem apply_goes (n : Engine.Sync.Node) (cid : Id) (st : Step) (now : Nat) :
    GoesM x.fam (n.apply x cid st now) := by
  unfold Node.apply
  goesTape [recordGiven_goes, store_goes x hr, fun via a o t => (hr.recv via a o t).goes]
theorem serve_goes (n : Engine.Sync.Node) (cid : Id) (now : Nat) : GoesM x.fam (n.serveOwed x cid now) := by
  unfold Node.serveOwed
  goesTape [fun cid c => (refresh_reads x hr cid c).goes,
    fun c budget first => (serveOwed_reads x.fam x.cfg c budget first).goes]
theorem sweep_goes (n : Engine.Sync.Node) (cid : Id) : GoesM x.fam (n.sweep x cid) := by
  cases hcat : x.catalog with
  | none => simp only [Node.sweep, hcat]; exact GoesM.pure' x.fam _
  | some cat =>
    obtain ⟨hc, hrd⟩ := hr.catalog cat hcat
    cases hs : x.retryStore with
    | none =>
      simp only [Node.sweep, hcat, hs]
      goesTape [fun cid c => (refresh_reads x hr cid c).goes,
        fun cid => (hr.retryKey cid).goes,
        fun cursor shows room => (sweep_reads cat hc hrd cursor shows room).goes]
    | some store =>
      obtain ⟨hl, hsave⟩ := hr.retryStore store hs
      simp only [Node.sweep, hcat, hs]
      goesTape [fun cid c => (refresh_reads x hr cid c).goes,
        fun cid => (hr.retryKey cid).goes, fun peer => (hl peer).goes,
        fun peer cursor => (hsave peer cursor).goes,
        fun cursor shows room => (sweep_reads cat hc hrd cursor shows room).goes]

theorem sweep_afterActs_goes (n : Engine.Sync.Node) (out : Acts) (cid : Id) :
    GoesM x.fam (n.sweep (n.afterActs x out) cid) :=
  sweep_goes (n.afterActs x out) (hr.afterActs n out) n cid

theorem serve_afterActs_goes (n : Engine.Sync.Node) (out : Acts) (cid : Id) (now : Nat) :
    GoesM x.fam (n.serveOwed (n.afterActs x out) cid now) :=
  serve_goes (n.afterActs x out) (hr.afterActs n out) n cid now

theorem onSealed_goes (n : Engine.Sync.Node) (addr : ByteArray) (opened : Option (Id × ByteArray)) (now : Nat) :
    GoesM x.fam (n.onSealed x addr opened now) := by
  unfold Node.onSealed
  goesTape [fun cid c => (refresh_reads x hr cid c).goes,
    fun ix c bytes now => (recv_reads x.fam x.cfg ix c bytes now).goes,
    apply_goes x hr, serve_goes x hr, finish_goes x hr]
theorem onFrame_goes (n : Engine.Sync.Node) (addr bytes : ByteArray) (now : Nat) :
    GoesM x.fam (n.onFrame x addr bytes now) := by
  unfold Node.onFrame
  goesTape [write_goes, store_goes x hr, fun via a o t => (hr.recv via a o t).goes,
    finish_goes x hr, fun b => (hr.openFrame b).goes, onSealed_goes x hr]
theorem onTick_goes (n : Engine.Sync.Node) (now : Nat) : GoesM x.fam (n.onTick x now) := by
  unfold Node.onTick
  goesTape [fun t => (hr.dial t).goes, store_goes x hr,
    fun cid c => (refresh_reads x hr cid c).goes,
    fun ix c now => (tickGive_reads x.fam x.cfg ix c now).goes,
    apply_goes x hr,
    sweep_afterActs_goes x hr,
    serve_afterActs_goes x hr,
    finish_goes x hr]
theorem onWrite_goes (n : Engine.Sync.Node) (ops : List Op) (now : Nat) : GoesM x.fam (n.onWrite x ops now) := by
  unfold Node.onWrite; goesTape [store_goes x hr, finish_goes x hr]

/-- Every full event handler uses only actual turn/purge effects, including
the hooks' reactions and the common finish path. -/
theorem step_goes (n : Engine.Sync.Node) (input : Node.Input) (now : Nat) :
    GoesM x.fam (n.step x input now) := by
  cases input with
  | write ops => exact onWrite_goes x hr n ops now
  | frame addr bytes => exact onFrame_goes x hr n addr bytes now
  | tick => exact onTick_goes x hr n now
  | close addr => exact onClose_goes x hr n addr now

end NodeTape

/-- Production hooks, the actual dispatch, every input, arbitrary entropy. -/
theorem production_step_moves (S : Setup) (side : Side) (n : Engine.Sync.Node)
    (input : Node.Input) (now : Nat) (s : Memory) :
    Moves family s.held ((n.step (S.sync side) input now) s).2.held :=
  NodeTape.step_goes (S.sync side) (NodeTape.production_readOnly S side) n input now s

theorem production_step_retains (S : Setup) (side : Side) (n : Engine.Sync.Node)
    (input : Node.Input) (now : Nat) (s : Memory) {i : Id} {o : Op}
    (ho : s.held.db.ops i = some o) (hs : (family.room o).isSome) :
    ((n.step (S.sync side) input now) s).2.held.db.ops i = some o :=
  (production_step_moves S side n input now s).shared_retained ho hs

theorem production_step_reachable (S : Setup) (side : Side) (n : Engine.Sync.Node)
    (input : Node.Input) (now : Nat) (s : Memory) (hr : s.held.Reachable family) :
    (((n.step (S.sync side) input now) s).2.held).Reachable family :=
  (production_step_moves S side n input now s).store_reachable hr

/-- Finite settling of this call's validation queue, not a uniform bound on
work per event: the proven runtime budget depends on stored history size. -/
theorem production_step_settled (S : Setup) (side : Side) (n : Engine.Sync.Node)
    (input : Node.Input) (now : Nat) (s : Memory)
    (hr : s.held.Reachable family) (hq : s.held.db.queue = []) :
    ((n.step (S.sync side) input now) s).2.held.db.queue = [] :=
  (production_step_moves S side n input now s).store_settled hr hq

theorem world_run_moves (S : Setup) (w : World) (side target : Side) (queue : List Packet)
    (f : Engine.Sync.Node → M (Engine.Sync.Node × Effects)) (closed : Bool)
    (hf : ∀ n s, Moves family s.held (f n s).2.held) :
    Moves family (w.peer target).memory.held
      ((w.run S side queue f closed).peer target).memory.held := by
  cases side <;> cases target
  · exact hf _ _
  · exact .refl _
  · exact .refl _
  · exact hf _ _

/-- Every environment action, including delivery, drops and two-sided close,
preserves the exact per-peer primitive-store transition relation. -/
theorem world_step_moves (S : Setup) (w : World) (a : Action) (target : Side) :
    Moves family (w.peer target).memory.held ((step S w a).peer target).memory.held := by
  have hp : ∀ (w : World) (side : Side) (queue : List Packet) (input : Node.Input) (closed : Bool),
      Moves family (w.peer target).memory.held
        ((w.run S side queue (fun n => n.step (S.sync side) input w.now) closed).peer target).memory.held :=
    fun w side queue input closed => world_run_moves S w side target queue _ closed
      (fun n s => production_step_moves S side n input w.now s)
  have time : ∀ w' : World, ({ w' with now := w.now + 1 }.peer target).memory.held =
      (w'.peer target).memory.held := by intro w'; cases target <;> rfl
  unfold step
  rw [time]
  cases a with
  | tick side => exact hp w side w.net .tick false
  | write side ops => exact hp w side w.net (.write ops) false
  | idle => exact .refl _
  | drop => cases target <;> exact .refl _
  | close =>
    have ha := world_run_moves S w .a target []
      (fun n => n.onClose (S.sync .a) (S.addr .b) w.now) true
      (NodeTape.onClose_goes (S.sync .a) (NodeTape.production_readOnly S .a) · (S.addr .b) w.now)
    let wa := w.run S .a [] (fun n => n.onClose (S.sync .a) (S.addr .b) w.now) true
    have hb := world_run_moves S wa .b target wa.net
      (fun n => n.onClose (S.sync .b) (S.addr .a) w.now) true
      (NodeTape.onClose_goes (S.sync .b) (NodeTape.production_readOnly S .b) · (S.addr .a) w.now)
    exact ha.trans hb
  | deliver =>
    cases hnet : w.net with
    | nil => simpa only [World.deliver, hnet] using (Moves.refl (fam := family) (w.peer target).memory.held)
    | cons p rest =>
      by_cases ha : p.dst = S.addr .a
      · simpa only [World.deliver, hnet, ite_eq_left ha, Node.step] using hp w .a rest (.frame p.src p.bytes) false
      · by_cases hb : p.dst = S.addr .b
        · simpa only [World.deliver, hnet, ite_eq_right ha, ite_eq_left hb, Node.step] using hp w .b rest (.frame p.src p.bytes) false
        · simp only [World.deliver, hnet, ite_eq_right ha, ite_eq_right hb]
          cases target <;> exact .refl _

theorem world_trace_moves (S : Setup) (w : World) (actions : List Action) (target : Side) :
    Moves family (w.peer target).memory.held
      ((trace S w actions).peer target).memory.held := by
  induction actions generalizing w with
  | nil => exact .refl _
  | cons a rest ih => exact (world_step_moves S w a target).trans (ih (step S w a))

/-- Arbitrary full production-event prefixes remain reachable and settled.
The schedule need not be fair; entropy can differ at every fresh draw. -/
theorem empty_trace_store (S : Setup) (ea eb : Nat → ByteArray)
    (actions : List Action) (target : Side) :
    let h := ((trace S (empty ea eb) actions).peer target).memory.held
    h.Reachable family ∧ h.db.queue = [] := by
  have hm := world_trace_moves S (empty ea eb) actions target
  have he : ((empty ea eb).peer target).memory.held = ({} : Held F) := by cases target <;> rfl
  rw [he] at hm
  exact ⟨hm.store_reachable (held_empty_reachable family),
    hm.store_settled (held_empty_reachable family) rfl⟩

/-- The byte-retention statement applies to every execution, not only a
chosen fair schedule. It does not claim an invalid op becomes valid. -/
theorem Run.shared_retained {S initial} (r : Run S initial) (target : Side)
    {n k : Nat} (hnk : n ≤ k) {i : Id} {o : Op}
    (ho : ((r.state n).peer target).memory.held.db.ops i = some o)
    (hs : (family.room o).isSome) :
    ((r.state k).peer target).memory.held.db.ops i = some o := by
  induction hnk with
  | refl => exact ho
  | @step k _ ih =>
    rw [r.next k]
    exact (world_step_moves S (r.state k) (r.action k) target).shared_retained ih hs

end Connection.Execution
