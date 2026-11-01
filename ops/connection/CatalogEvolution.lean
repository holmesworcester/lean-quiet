/- Stable catalog positions through the actual runtime handlers. Writes
append new shared bytes; purges remove only local history entries. -/
import ops.connection.WriteProgress

namespace Connection.Execution
open Engine Engine.Sync

/-- Prefix order, not merely set inclusion, is the catalog cursor invariant. -/
def HistoryStep (fam : Family F) (a b : Held F) : Prop :=
  a.Reachable fam → a.LogAgrees →
    b.Reachable fam ∧ b.LogAgrees ∧ ∃ tail, Catalog.shared fam b = Catalog.shared fam a ++ tail

namespace HistoryStep
 theorem refl {fam : Family F} (h : Held F) : HistoryStep fam h h :=
   fun hr ha => ⟨hr, ha, [], by simp⟩
 theorem trans {fam : Family F} {a b c : Held F} (h1 : HistoryStep fam a b) (h2 : HistoryStep fam b c) :
     HistoryStep fam a c := by
   intro hr ha
   obtain ⟨hrb, hab, tail, he⟩ := h1 hr ha
   obtain ⟨hrc, hac, rest, he'⟩ := h2 hrb hab
   exact ⟨hrc, hac, tail ++ rest, by rw [he', he, List.append_assoc]⟩

 /-- Exact point lookups below an already captured high-water mark survive
 every full handler, including local-secret purge and concurrent appends. -/
 theorem catalog_read {fam : Family F} {a b : Held F} (step : HistoryStep fam a b)
     (hr : a.Reachable fam) (ha : a.LogAgrees) {seq : Nat}
     (positive : 0 < seq) (below : seq ≤ (Catalog.shared fam a).length) :
     ((Catalog.held fam).read seq b).1 = ((Catalog.held fam).read seq a).1 := by
   obtain ⟨_, _, tail, he⟩ := step hr ha
   simp only [Catalog.held, he]
   rw [List.getElem?_append_left (by omega)]

 theorem ceiling_mono {fam : Family F} {a b : Held F} (step : HistoryStep fam a b)
     (hr : a.Reachable fam) (ha : a.LogAgrees) :
     ((Catalog.held fam).ceiling a).1 ≤ ((Catalog.held fam).ceiling b).1 := by
   obtain ⟨_, _, tail, he⟩ := step hr ha
   simp only [Catalog.held, he, List.length_append]
   omega
end HistoryStep

def HistoryM (fam : Family F) {α} (p : M α) : Prop :=
  ∀ s, HistoryStep fam s.held (p s).2.held

theorem ReadsHeld.history {fam : Family F} {α} {p : M α} (hp : ReadsHeld p) : HistoryM fam p := by
  intro s hr ha
  rw [hp s]
  exact ⟨hr, ha, [], by simp⟩

namespace HistoryM
 theorem pure' (fam : Family F) {α} (a : α) : HistoryM fam (pure a : M α) :=
   (ReadsHeld.pure' a).history
 theorem bind' {fam : Family F} {α β} {p : M α} {k : α → M β}
     (hp : HistoryM fam p) (hk : ∀ a, HistoryM fam (k a)) : HistoryM fam (p >>= k) := by
   intro s hr ha
   obtain ⟨hr', ha', tail, he⟩ := hp s hr ha
   obtain ⟨hr'', ha'', rest, he'⟩ := hk (p s).1 (p s).2 hr' ha'
   exact ⟨hr'', ha'', tail ++ rest, by rw [M.bind_apply, he', he, List.append_assoc]⟩
 theorem forIn' {fam : Family F} {α β} (l : List α) (b : β)
     {f : α → β → M (ForInStep β)} (hf : ∀ a b, HistoryM fam (f a b)) :
     HistoryM fam (forIn l b f) := by
   induction l generalizing b with
   | nil => exact pure' fam b
   | cons a t ih =>
     rw [List.forIn_cons]
     apply bind' (hf a b)
     intro r
     cases r with
     | done b => exact pure' fam b
     | yield b => exact ih b
 theorem getOp' (fam : Family F) (i : Id) : HistoryM fam (Store.getOp i : M _) :=
   (ReadsHeld.getOp' i).history
 theorem getStatus' (fam : Family F) (i : Id) : HistoryM fam (Store.getStatus i : M _) :=
   (ReadsHeld.getStatus' i).history
 theorem purge' (fam : Family F) (ids : List Id) (scrub : Bool) :
     HistoryM fam (Turn.purge fam ids scrub : M Unit) := by
   intro s hr ha
   exact ⟨purge_reachable fam ids scrub s.held hr, purge_log_agrees fam s.held ids scrub ha,
     [], by
       change Catalog.shared fam ((Turn.purge fam ids scrub : HeldM F Unit) s.held).2 = _
       simpa using shared_log_purge fam s.held ids scrub ha⟩
end HistoryM

syntax "historyTape" "[" term,* "]" : tactic
macro_rules
  | `(tactic| historyTape [$ts,*]) => do
    let mut tac : Lean.TSyntax `tactic ← `(tactic| first | split | intro)
    for t in ts.getElems.reverse do
      tac ← `(tactic| first | with_reducible_and_instances apply $t | $tac:tactic)
    `(tactic| repeat' (first
      | dsimp only | with_reducible_and_instances apply HistoryM.bind'
      | with_reducible_and_instances apply HistoryM.pure' | with_reducible_and_instances apply HistoryM.forIn'
      | with_reducible_and_instances apply HistoryM.getOp' | with_reducible_and_instances apply HistoryM.getStatus'
      | with_reducible_and_instances apply HistoryM.purge'
      | $tac:tactic))

namespace NodeHistory
open NodeTape
variable (x : Sync F M) (hr : ReadOnly x)

theorem write_history (n : Engine.Sync.Node) (ops : List Op) : HistoryM x.fam (n.write x ops) := by
  intro s hr ha
  obtain ⟨history, reach, _⟩ := hr
  have hi := reach_inv reach
  refine ⟨(NodeTape.write_goes x n ops s).store_reachable ⟨history, reach, by assumption⟩,
    write_log_agrees_tape x n s ops hi ha, ?_⟩
  rw [write_store_tape, write_store]
  dsimp only
  split
  · exact ⟨[], by simp⟩
  · exact ⟨_, shared_log_turn _ _ _⟩

theorem put_history (n : Engine.Sync.Node) (ops : List Op) (mine : Bool) : HistoryM x.fam (n.put x ops mine) :=
  write_history x n _
theorem recordGiven_history (n : Engine.Sync.Node) (st : List (Id × Id)) : HistoryM x.fam (n.recordGiven x st) := by
  unfold Node.recordGiven; historyTape [put_history]
include hr

theorem refresh_reads (cid : Id) (c : Conn) : ReadsHeld (Node.refresh x cid c) := by
  unfold Node.refresh; readsHeld [hr.rooms]
theorem fanout_history (n : Engine.Sync.Node) (ids : List Id) : HistoryM x.fam (n.fanout x ids) := by
  unfold Node.fanout
  historyTape [fun cid c => (refresh_reads x hr cid c).history,
    fun c ids => (NodeTape.filedGive_reads x.fam x.cfg c ids).history, recordGiven_history]
theorem store_history (n : Engine.Sync.Node) (ops : List Op) (mine : Bool) : HistoryM x.fam (n.store x ops mine) := by
  unfold Node.store
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  historyTape [put_history, fanout_history x hr, hr.react.history]
theorem open_history (n : Engine.Sync.Node) (cid : Id) (addr : ByteArray) (dialer : Bool) (now : Nat) :
    HistoryM x.fam (n.open x cid addr dialer now) := by
  unfold Node.open; historyTape [fun cid => (hr.rooms cid).history]
theorem follow_history (n : Engine.Sync.Node) (now : Nat) : HistoryM x.fam (n.follow x now) := by
  unfold Node.follow; historyTape [hr.established.history, open_history x hr]
omit hr in
theorem effectsPurge_history (ids : List Id) (scrub : Bool) : HistoryM x.fam (Effects.purge x ids scrub) := by
  unfold Effects.purge; historyTape []
theorem flush_history (n : Engine.Sync.Node) (out : Acts) : HistoryM x.fam (n.flush x out) := by
  unfold Node.flush; historyTape [hr.outbox.history, effectsPurge_history]
theorem seal_history (n : Engine.Sync.Node) (out : Acts) : HistoryM x.fam (n.seal x out) := by
  unfold Node.seal; historyTape [fun cid b => (hr.sealFor cid b).history]
theorem sealRetries_history (n : Engine.Sync.Node) (retries : List RetryOffer) :
    HistoryM x.fam (n.sealRetries x retries) := by
  unfold Node.sealRetries; historyTape [seal_history x hr]
theorem endSession_history (cid : Id) : HistoryM x.fam (Node.endSession x cid) := by
  unfold Node.endSession; historyTape [fun cid => (hr.closing cid).history, effectsPurge_history]
theorem finish_history (n : Engine.Sync.Node) (out : Acts) (now : Nat) : HistoryM x.fam (n.finish x out now) := by
  unfold Node.finish
  historyTape [follow_history x hr, flush_history x hr, hr.retired.history, seal_history x hr,
    sealRetries_history x hr, endSession_history x hr]
theorem onClose_history (n : Engine.Sync.Node) (addr : ByteArray) (now : Nat) : HistoryM x.fam (n.onClose x addr now) := by
  unfold Node.onClose; historyTape [finish_history x hr]
theorem apply_history (n : Engine.Sync.Node) (cid : Id) (st : Step) (now : Nat) :
    HistoryM x.fam (n.apply x cid st now) := by
  unfold Node.apply
  historyTape [recordGiven_history, store_history x hr, fun via a o t => (hr.recv via a o t).history]
theorem serve_history (n : Engine.Sync.Node) (cid : Id) (now : Nat) : HistoryM x.fam (n.serveOwed x cid now) := by
  unfold Node.serveOwed
  historyTape [fun cid c => (refresh_reads x hr cid c).history,
    fun c budget first => (NodeTape.serveOwed_reads x.fam x.cfg c budget first).history]
theorem sweep_history (n : Engine.Sync.Node) (cid : Id) : HistoryM x.fam (n.sweep x cid) := by
  cases hcat : x.catalog with
  | none => simp only [Node.sweep, hcat]; exact HistoryM.pure' x.fam _
  | some cat =>
    obtain ⟨hc, hrd⟩ := hr.catalog cat hcat
    cases hs : x.retryStore with
    | none =>
      simp only [Node.sweep, hcat, hs]
      historyTape [fun cid c => (refresh_reads x hr cid c).history,
        fun cid => (hr.retryKey cid).history,
        fun cursor shows room => (NodeTape.sweep_reads cat hc hrd cursor shows room).history]
    | some store =>
      obtain ⟨hl, hsave⟩ := hr.retryStore store hs
      simp only [Node.sweep, hcat, hs]
      historyTape [fun cid c => (refresh_reads x hr cid c).history,
        fun cid => (hr.retryKey cid).history, fun peer => (hl peer).history,
        fun peer cursor => (hsave peer cursor).history,
        fun cursor shows room => (NodeTape.sweep_reads cat hc hrd cursor shows room).history]

theorem sweep_afterActs_history (n : Engine.Sync.Node) (out : Acts) (cid : Id) :
    HistoryM x.fam (n.sweep (n.afterActs x out) cid) :=
  sweep_history (n.afterActs x out) (hr.afterActs n out) n cid

theorem serve_afterActs_history (n : Engine.Sync.Node) (out : Acts) (cid : Id) (now : Nat) :
    HistoryM x.fam (n.serveOwed (n.afterActs x out) cid now) :=
  serve_history (n.afterActs x out) (hr.afterActs n out) n cid now

theorem onSealed_history (n : Engine.Sync.Node) (addr : ByteArray) (opened : Option (Id × ByteArray)) (now : Nat) :
    HistoryM x.fam (n.onSealed x addr opened now) := by
  unfold Node.onSealed
  historyTape [fun cid c => (refresh_reads x hr cid c).history,
    fun ix c bytes now => (NodeTape.recv_reads x.fam x.cfg ix c bytes now).history,
    apply_history x hr, serve_history x hr, finish_history x hr]
theorem onFrame_history (n : Engine.Sync.Node) (addr bytes : ByteArray) (now : Nat) :
    HistoryM x.fam (n.onFrame x addr bytes now) := by
  unfold Node.onFrame
  historyTape [write_history, store_history x hr, fun via a o t => (hr.recv via a o t).history,
    finish_history x hr, fun b => (hr.openFrame b).history, onSealed_history x hr]
theorem onTick_history (n : Engine.Sync.Node) (now : Nat) : HistoryM x.fam (n.onTick x now) := by
  unfold Node.onTick
  historyTape [fun t => (hr.dial t).history, store_history x hr,
    fun cid c => (refresh_reads x hr cid c).history,
    fun ix c now => (NodeTape.tickGive_reads x.fam x.cfg ix c now).history,
    apply_history x hr,
    sweep_afterActs_history x hr,
    serve_afterActs_history x hr,
    finish_history x hr]
theorem onWrite_history (n : Engine.Sync.Node) (ops : List Op) (now : Nat) : HistoryM x.fam (n.onWrite x ops now) := by
  unfold Node.onWrite; historyTape [store_history x hr, finish_history x hr]

/-- Every full event handler uses only actual turn/purge effects, including
the hooks' reactions and the common finish path. -/
theorem step_history (n : Engine.Sync.Node) (input : Node.Input) (now : Nat) :
    HistoryM x.fam (n.step x input now) := by
  cases input with
  | write ops => exact onWrite_history x hr n ops now
  | frame addr bytes => exact onFrame_history x hr n addr bytes now
  | tick => exact onTick_history x hr n now
  | close addr => exact onClose_history x hr n addr now

end NodeHistory

/-- Every production event preserves shared catalog positions, while allowing
new shared writes and local/session purges in the same event. -/
theorem production_step_history (S : Setup) (side : Side) (n : Engine.Sync.Node)
    (input : Node.Input) (now : Nat) (s : Memory) :
    HistoryStep family s.held ((n.step (S.sync side) input now) s).2.held :=
  NodeHistory.step_history (S.sync side) (NodeTape.production_readOnly S side) n input now s

theorem world_run_history (S : Setup) (w : World) (side target : Side) (queue : List Packet)
    (f : Engine.Sync.Node → M (Engine.Sync.Node × Effects)) (closed : Bool)
    (hf : ∀ n s, HistoryStep family s.held (f n s).2.held) :
    HistoryStep family (w.peer target).memory.held
      ((w.run S side queue f closed).peer target).memory.held := by
  cases side <;> cases target
  · exact hf _ _
  · exact .refl _
  · exact .refl _
  · exact hf _ _

/-- Every environment action, including delivery, drops and two-sided close,
preserves each peer's reachable, agreeing, append-only shared history. -/
theorem world_step_history (S : Setup) (w : World) (a : Action) (target : Side) :
    HistoryStep family (w.peer target).memory.held ((step S w a).peer target).memory.held := by
  have hp : ∀ (w : World) (side : Side) (queue : List Packet) (input : Node.Input) (closed : Bool),
      HistoryStep family (w.peer target).memory.held
        ((w.run S side queue (fun n => n.step (S.sync side) input w.now) closed).peer target).memory.held :=
    fun w side queue input closed => world_run_history S w side target queue _ closed
      (fun n s => production_step_history S side n input w.now s)
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
    have ha := world_run_history S w .a target []
      (fun n => n.onClose (S.sync .a) (S.addr .b) w.now) true
      (NodeHistory.onClose_history (S.sync .a) (NodeTape.production_readOnly S .a) · (S.addr .b) w.now)
    let wa := w.run S .a [] (fun n => n.onClose (S.sync .a) (S.addr .b) w.now) true
    have hb := world_run_history S wa .b target wa.net
      (fun n => n.onClose (S.sync .b) (S.addr .a) w.now) true
      (NodeHistory.onClose_history (S.sync .b) (NodeTape.production_readOnly S .b) · (S.addr .a) w.now)
    exact ha.trans hb
  | deliver =>
    cases hnet : w.net with
    | nil => simpa only [World.deliver, hnet] using (HistoryStep.refl (fam := family) (w.peer target).memory.held)
    | cons p rest =>
      by_cases ha : p.dst = S.addr .a
      · simpa only [World.deliver, hnet, ite_eq_left ha, Node.step] using hp w .a rest (.frame p.src p.bytes) false
      · by_cases hb : p.dst = S.addr .b
        · simpa only [World.deliver, hnet, ite_eq_right ha, ite_eq_left hb, Node.step] using hp w .b rest (.frame p.src p.bytes) false
        · simp only [World.deliver, hnet, ite_eq_right ha, ite_eq_right hb]
          cases target <;> exact .refl _

theorem world_trace_history (S : Setup) (w : World) (actions : List Action) (target : Side) :
    HistoryStep family (w.peer target).memory.held
      ((trace S w actions).peer target).memory.held := by
  induction actions generalizing w with
  | nil => exact .refl _
  | cons a rest ih => exact (world_step_history S w a target).trans (ih (step S w a))


/-- Starting empty, arbitrary actual event prefixes have a collision-safe
shared history. No fairness or quiescence assumption is needed. -/
theorem empty_trace_history (S : Setup) (ea eb : Nat → ByteArray)
    (actions : List Action) (target : Side) :
    let h := ((trace S (empty ea eb) actions).peer target).memory.held
    h.Reachable family ∧ h.LogAgrees := by
  have hm := world_trace_history S (empty ea eb) actions target
  have he : ((empty ea eb).peer target).memory.held = ({} : Held F) := by cases target <;> rfl
  rw [he] at hm
  have h := hm (held_empty_reachable family) empty_log_agrees
  exact ⟨h.1, h.2.1⟩

/-- Catalog positions are stable across every finite interval of the actual
execution relation. This permits unbounded append traffic and reconnects. -/
theorem Run.history {S initial} (r : Run S initial) (target : Side)
    {n k : Nat} (hnk : n ≤ k) :
    HistoryStep family ((r.state n).peer target).memory.held
      ((r.state k).peer target).memory.held := by
  induction hnk with
  | refl => exact .refl _
  | @step k _ ih =>
    rw [r.next k]
    exact ih.trans (world_step_history S (r.state k) (r.action k) target)

end Connection.Execution

