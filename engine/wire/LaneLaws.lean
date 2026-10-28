/-
Laws of the send lanes and the run loop's inbox (Lanes.lean), over the
functions the runner calls:

- `write_first`, `write_within`, `frame_next`: a local write waiting is
  the loop's next event, whatever frames are queued;
- `urgent_ahead`: an urgent frame goes out in its socket's next native
  write, after only the urgent frames before it and ahead of the whole
  serve backlog; `cut_bytes`: a write's serve part is at most `burst`
  bytes, or one frame; `ahead_bytes`: so what reaches the socket between
  an urgent frame's push and the frame is urgent traffic and one burst;
- `apart`: a socket's next write depends on its own lanes and frames
  only, whatever any other socket holds;
- `lane_control`, `hot_ids`, `heat_hot`: what a node sends urgent:
  messages naming few ids, and the ops it wrote, from the write on for
  `hotMs` (`fresh_served`, WorldLaws).
-/
import engine.wire.Node

namespace Engine.Sync

/-! ## The send lanes -/

theorem fill_append (room : Nat) (fs : List ByteArray) : (fill room fs).1 ++ (fill room fs).2 = fs := by
  induction fs generalizing room with
  | nil => rfl
  | cons f fs ih =>
    simp only [fill]
    split
    · simp [ih]
    · rfl

theorem fill_bytes (room : Nat) (fs : List ByteArray) : bytesOf (fill room fs).1 ≤ room := by
  induction fs generalizing room with
  | nil => simp [fill, bytesOf]
  | cons f fs ih =>
    simp only [fill]
    split
    · have := ih (room - f.size)
      simp only [bytesOf, List.map_cons, List.sum_cons] at this ⊢
      omega
    · simp [bytesOf]

/-- A burst and what it leaves are the queue, in order. -/
theorem cut_append (burst : Nat) (fs : List ByteArray) : (cut burst fs).1 ++ (cut burst fs).2 = fs := by
  cases fs with
  | nil => rfl
  | cons f fs => simp [cut, fill_append]

/-- **A write's serve part is at most `burst` bytes, or one frame.** -/
theorem cut_bytes (burst : Nat) (fs : List ByteArray) :
    bytesOf (cut burst fs).1 ≤ max burst (fs.headD .empty).size := by
  cases fs with
  | nil => simp [cut, bytesOf]
  | cons f fs =>
    have := fill_bytes (burst - f.size) fs
    simp only [cut, bytesOf, List.map_cons, List.sum_cons, List.headD_cons] at this ⊢
    omega

/-- A write from a serve lane that is not empty takes its first frame:
the backlog always moves. -/
theorem cut_progress (burst : Nat) (f : ByteArray) (fs : List ByteArray) :
    ∃ rest, (cut burst (f :: fs)).1 = f :: rest := ⟨_, rfl⟩

/-- **Every urgent frame goes before the burst**, in one native write. -/
theorem take_urgent_first (burst : Nat) (q : Lanes) :
    (q.take burst).1 = q.urgent ++ (cut burst q.serve).1 := rfl

/-- What a write takes and what it leaves are the lanes, urgent first:
nothing is dropped or reordered within a lane. -/
theorem take_append (burst : Nat) (q : Lanes) :
    (q.take burst).1 ++ (q.take burst).2.serve = q.urgent ++ q.serve ∧ (q.take burst).2.urgent = [] := by
  simp [Lanes.take, List.append_assoc, cut_append]

def urgents (ps : List (Lane × ByteArray)) : List ByteArray :=
  ps.filterMap fun p => if p.1 = .urgent then some p.2 else none

def serves (ps : List (Lane × ByteArray)) : List ByteArray :=
  ps.filterMap fun p => if p.1 = .serve then some p.2 else none

theorem pushAll_lanes (q : Lanes) (ps : List (Lane × ByteArray)) :
    (q.pushAll ps).urgent = q.urgent ++ urgents ps ∧ (q.pushAll ps).serve = q.serve ++ serves ps := by
  induction ps generalizing q with
  | nil => simp [Lanes.pushAll, urgents, serves]
  | cons p ps ih =>
    obtain ⟨l, f⟩ := p
    have := ih (q.push l f)
    simp only [Lanes.pushAll, List.foldl_cons] at this ⊢
    cases l <;> simp_all [Lanes.push, urgents, serves]

/-- **An urgent frame overtakes the backlog.** Whatever a socket's lanes
hold when urgent frame u is pushed, and whatever the loop pushes after
it, the writer's next native write sends u after only the urgent frames
pushed before it, and ahead of every serve frame queued since the last
write began (the burst boundary). So what the writer hands the socket
between u's push and u is the write already under way, and those urgent
frames: never the serve lane's backlog. -/
theorem urgent_ahead (burst : Nat) (q : Lanes) (u : ByteArray) (ps : List (Lane × ByteArray)) :
    (((q.push .urgent u).pushAll ps).take burst).1 =
      q.urgent ++ u :: (urgents ps ++ (cut burst (q.serve ++ serves ps)).1) := by
  rw [take_urgent_first]
  obtain ⟨hu, hs⟩ := pushAll_lanes (q.push .urgent u) ps
  rw [hu, hs]
  simp [Lanes.push]

theorem bytesOf_append (a b : List ByteArray) : bytesOf (a ++ b) = bytesOf a + bytesOf b := by
  simp [bytesOf]

/-- **What a fresh frame waits for on its socket**, the send-path premise
of `fresh_stmt`. Write w₁ began from lanes q₀; while it was under way the
loop pushed `pre`, then urgent frame u, then `post`. The writer's next
write w₂ sends u after only the urgent frames of `pre`; and w₁ is the
urgent frames queued when it began, and at most `burst` bytes of serve
frames, or one frame. So what reaches the socket from u's push to u is
bounded by the urgent traffic and one burst, whatever backlog the serve
lane holds. -/
theorem ahead_bytes (burst : Nat) (q₀ : Lanes) (pre post : List (Lane × ByteArray)) (u : ByteArray) :
    (∃ rest, (((((q₀.take burst).2.pushAll pre).push .urgent u).pushAll post).take burst).1 =
      urgents pre ++ u :: rest) ∧
    bytesOf (q₀.take burst).1 ≤ bytesOf q₀.urgent + max burst (q₀.serve.headD .empty).size := by
  refine ⟨?_, ?_⟩
  · rw [urgent_ahead]
    obtain ⟨hu, -⟩ := pushAll_lanes (q₀.take burst).2 pre
    rw [hu, (take_append burst q₀).2]
    exact ⟨_, by simp; rfl⟩
  · rw [take_urgent_first, bytesOf_append]
    have := cut_bytes burst q₀.serve
    omega

/-! ## Sockets apart -/

/-- **A slow socket holds up no other.** Socket s's lanes after a step
are its own, with the step's frames to its address pushed in order; so
its next native write is the same whatever any other socket holds
(`o` and `o'` agree at s only), however long another's backlog. -/
theorem apart (o o' : Nat → Lanes) (sockOf : ByteArray → Option Nat) (fs : List (ByteArray × Lane × ByteArray))
    (s burst : Nat) (h : o s = o' s) :
    ((o s).pushAll (framesFor sockOf s fs)).take burst = ((o' s).pushAll (framesFor sockOf s fs)).take burst := by
  rw [h]

/-- And the frames pushed onto socket s are exactly the step's frames to
an address of s, in order. -/
theorem framesFor_mem (sockOf : ByteArray → Option Nat) (s : Nat) (fs : List (ByteArray × Lane × ByteArray))
    (a : ByteArray) (p : Lane × ByteArray) (hp : (a, p) ∈ fs) (ha : sockOf a = some s) :
    p ∈ framesFor sockOf s fs :=
  List.mem_filterMap.2 ⟨(a, p), hp, by simp [ha]⟩

theorem framesFor_only (sockOf : ByteArray → Option Nat) (s : Nat) (fs : List (ByteArray × Lane × ByteArray))
    (p : Lane × ByteArray) (hp : p ∈ framesFor sockOf s fs) : ∃ a, (a, p) ∈ fs ∧ sockOf a = some s := by
  obtain ⟨⟨a, q⟩, hq, he⟩ := List.mem_filterMap.1 hp
  by_cases ha : sockOf a = some s
  · simp [ha] at he; subst he; exact ⟨a, hq, ha⟩
  · simp [ha] at he

/-! ## The run loop's inbox -/

/-- The loop's two channels as queues: local writes, and everything else. -/
abbrev Queues (W E : Type) := StateM (List W × List E)

def popW {W E : Type} : Queues W E (Option W) :=
  modifyGet fun (ws, es) => match ws with
    | [] => (none, ([], es))
    | w :: ws => (some w, (ws, es))

def popE {W E : Type} : Queues W E (Option E) :=
  modifyGet fun (ws, es) => match es with
    | [] => (none, (ws, []))
    | e :: es => (some e, (ws, es))

/-- **A local write is the loop's next event, whatever frames are
queued.** -/
theorem write_first {W E : Type} (w : W) (ws : List W) (es : List E) :
    (Inbox.next popW popE).run (w :: ws, es) = (some (.inl w), (ws, es)) := rfl

/-- With no write waiting, the next event is the next frame: writes hold
frames back only by being taken. -/
theorem frame_next {W E : Type} (e : E) (es : List E) :
    (Inbox.next (popW (W := W)) popE).run ([], e :: es) = (some (.inr e), ([], es)) := rfl

/-- n iterations of the loop's choice. -/
def Inbox.iter {W E : Type} : Nat → Queues W E (List (Option (W ⊕ E)))
  | 0 => pure []
  | n + 1 => do
    let x ← Inbox.next popW popE
    let xs ← Inbox.iter n
    return x :: xs

theorem iter_write {W E : Type} (n : Nat) (w : W) (ws : List W) (es : List E) :
    (Inbox.iter (n + 1)).run (w :: ws, es) =
      (some (.inl w) :: ((Inbox.iter n).run (ws, es)).1, ((Inbox.iter n).run (ws, es)).2) := rfl

/-- **The p-th write waiting enters within p + 1 iterations**, whatever
frames are queued and however many. -/
theorem write_within {W E : Type} (ws : List W) (es : List E) (p : Nat) (hp : p < ws.length) :
    ((Inbox.iter (p + 1)).run (ws, es)).1 = (ws.take (p + 1)).map (some ∘ .inl) := by
  induction p generalizing ws with
  | zero =>
    cases ws with
    | nil => simp at hp
    | cons w ws => rfl
  | succ p ih =>
    cases ws with
    | nil => simp at hp
    | cons w ws =>
      rw [iter_write, ih ws (by simp at hp; omega)]
      simp

/-! ## What a node sends urgent -/

section
variable {F : Type} {m : Type → Type} [Monad m] (x : Sync F m)

/-- **Control goes urgent:** a message naming at most `urgentIds` ids
(at least one) takes the urgent lane; a longer one (a round's
difference, closure offers) the serve lane. -/
theorem lane_control (o : Op) (hl : o.reqs.length ≤ max x.cfg.urgentIds 1) : wireLane x o = .urgent := by
  simp [wireLane, hl]

/-- A message naming one id or none (an offer or a want of one op, a
round's claims, a hello) is urgent whatever `urgentIds` is. -/
theorem lane_one (o : Op) (hl : o.reqs.length ≤ 1) : wireLane x o = .urgent :=
  lane_control x o (by omega)

/-- **A fresh write is hot:** an op this node wrote at t is among the
ids it serves first until t + `hotMs` (`Node.serveOwed`). -/
theorem hot_ids (n : Node) (i : Id) (t now : Nat) (hh : (i, t) ∈ n.hot) (ht : now ≤ t + x.cfg.hotMs) :
    i ∈ n.hotIds x now :=
  List.mem_filterMap.2 ⟨(i, t), hh, by simp [ht]⟩

/-- **A write's ops are hot from the write on**, while they are at most
`hotCap`. -/
theorem heat_hot (n : Node) (ids : List Id) (now : Nat) (hc : ids.length ≤ x.cfg.hotCap) :
    ∀ i ∈ ids, (i, now) ∈ (n.heat x ids now).hot := by
  intro i hi
  simp only [Node.heat, List.take_append]
  apply List.mem_append_left
  rw [List.take_of_length_le (by simpa using hc)]
  exact List.mem_map.2 ⟨i, List.mem_reverse.2 hi, rfl⟩

/-- The stream's single offer and want are urgent. -/
@[simp] theorem lane_want_one (i : Id) : wireLane x (Msg.want [i]).op = .urgent :=
  lane_one x _ (by simp [Msg.op])

@[simp] theorem lane_hold_one (r i : Id) : wireLane x (Msg.hold r [i]).op = .urgent :=
  lane_one x _ (by simp [Msg.op])

@[simp] theorem heat_conns (n : Node) (ids : List Id) (now : Nat) : (n.heat x ids now).conns = n.conns := rfl
@[simp] theorem heat_managed (n : Node) (ids : List Id) (now : Nat) : (n.heat x ids now).managed = n.managed := rfl
@[simp] theorem heat_addrs (n : Node) (ids : List Id) (now : Nat) : (n.heat x ids now).addrs = n.addrs := rfl
@[simp] theorem heat_ix (n : Node) (ids : List Id) (now : Nat) : (n.heat x ids now).ix = n.ix := rfl
@[simp] theorem heat_fresh (n : Node) (ids : List Id) (now : Nat) : (n.heat x ids now).fresh = n.fresh := rfl
@[simp] theorem heat_dropped (n : Node) (ids : List Id) (now : Nat) : (n.heat x ids now).dropped = n.dropped := rfl
@[simp] theorem heat_floor (n : Node) (ids : List Id) (now : Nat) : (n.heat x ids now).floor = n.floor := rfl

end

@[simp] theorem sends_serve (cid : Id) (ops : List Op) : (sends cid ops).serve = [] := rfl

/-- A step whose sends are all urgent is split as it was sent before
lanes. -/
theorem split_urgent (lane : Op → Lane) (cid : Id) (ops : List Op) (h : ∀ o ∈ ops, lane o = .urgent) :
    split lane cid ops = sends cid ops := by
  have hs : ops.filter (fun o => Decidable.decide (lane o = .serve)) = [] :=
    List.filter_eq_nil_iff.2 fun o ho => by simp [h o ho]
  have hu : ops.filter (fun o => Decidable.decide (lane o = .urgent)) = ops :=
    List.filter_eq_self.2 fun o ho => by simp [h o ho]
  simp [split, sends, hs, hu]

/-- One op's send, in its lane. -/
theorem split_one (lane : Op → Lane) (cid : Id) (o : Op) :
    split lane cid [o] = if lane o = .urgent then sends cid [o] else { serve := [(.conn cid, o.bytes)] } := by
  cases h : lane o <;> simp [split, sends, h]

end Engine.Sync
