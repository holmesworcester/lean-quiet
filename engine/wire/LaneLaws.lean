/-
Laws of the send lanes and the run loop's inbox (Lanes.lean), over the
functions the runner calls:

- `write_first`, `write_within`, `frame_next`: a local write waiting is
  the loop's next event, whatever frames are queued;
- `urgent_ahead`: an urgent frame goes out in its socket's next native
  write, after only the urgent frames before it and ahead of the whole
  serve backlog; `cut_bytes`: a write's serve part is at most `burst`
  bytes, or one frame; `ahead_bytes`: so what reaches the socket between
  an urgent frame's push and the frame is the write under way and the
  urgent frames pushed before it, each at most `sockCap` bytes;
- `push_capped`, `lanes_bounded`: a socket's lanes, both of them, never
  hold more than `sockCap` bytes, whatever is pushed (`Lanes.admit`),
  and `room_window`: serving into a socket's room leaves its lanes
  within `window` and one op;
- `stall_closes`: a socket whose writer's write is not done in
  `stallMs` is one the loop's clock closes.

That one socket's backlog holds up no other is tested over TCP
(tests/engine/FreshTcp.lean), not proven: each socket has its own lanes
and writer, but the threads are not modelled.
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

/-! ## The socket cap -/

theorem pushAll_bytes (q : Lanes) (ps : List (Lane × ByteArray)) :
    (q.pushAll ps).bytes = q.bytes + bytesOf (urgents ps) + bytesOf (serves ps) := by
  obtain ⟨hu, hs⟩ := pushAll_lanes q ps
  simp only [Lanes.bytes, hu, hs, bytesOf_append]
  omega

/-- **A push keeps a socket's lanes within its cap**, or is refused (and
the runner closes the socket): what `Sock.push` does with every step's
frames, whatever the peer sent. -/
theorem push_capped (cap : Nat) (q q' : Lanes) (ps : List (Lane × ByteArray)) (h : q.admit cap ps = some q') :
    q' = q.pushAll ps ∧ q'.bytes ≤ cap := by
  simp only [Lanes.admit] at h
  split at h
  · cases h; exact ⟨rfl, by assumption⟩
  · cases h

theorem push_over (cap : Nat) (q : Lanes) (ps : List (Lane × ByteArray)) (h : q.admit cap ps = none) :
    cap < (q.pushAll ps).bytes := by
  simp only [Lanes.admit] at h
  split at h
  · cases h
  · omega

/-- A write only takes from the lanes. -/
theorem take_bytes (burst : Nat) (q : Lanes) :
    bytesOf (q.take burst).1 + (q.take burst).2.bytes = q.bytes := by
  have h := congrArg bytesOf (take_append burst q).1
  simp only [bytesOf_append] at h
  simp only [Lanes.bytes, (take_append burst q).2]
  have : bytesOf ([] : List ByteArray) = 0 := rfl
  omega

/-- The lanes a socket's writer and the loop can leave: from none,
through the loop's pushes (`Sock.push`, by `admit`), the writer's
writes (`take`), and the stop, which drops them (`Sock.stop`). -/
inductive Lanes.Reach (cap burst : Nat) : Lanes → Prop
  | empty : Reach cap burst {}
  | push {q q' : Lanes} (ps : List (Lane × ByteArray)) :
      Reach cap burst q → q.admit cap ps = some q' → Reach cap burst q'
  | take {q : Lanes} : Reach cap burst q → Reach cap burst (q.take burst).2

/-- **A socket never holds more than `sockCap` bytes**, urgent and serve
together, whatever its peer sends or fails to take. -/
theorem lanes_bounded {cap burst : Nat} {q : Lanes} (h : Lanes.Reach cap burst q) : q.bytes ≤ cap := by
  induction h with
  | empty => simp [Lanes.bytes, bytesOf]
  | push ps _ ha _ => exact (push_capped _ _ _ ps ha).2
  | take _ ih => have := take_bytes burst ‹Lanes›; omega

/-- **What a fresh frame waits for on its socket**, the send-path premise
of `fresh_stmt`. Write w₁ began from lanes q₀; while it was under way the
loop pushed `pre`, then urgent frame u, then `post`, admitted within the
cap. The writer's next write w₂ sends u after only the urgent frames of
`pre`. w₁ is the urgent frames queued when it began, and at most
`burst` bytes of serve frames, or one frame, and at most `cap` bytes in
all; the urgent frames of `pre` and u are at most `cap` bytes. So what
reaches the socket from u's push to u is at most twice the cap, whatever
backlog the serve lane holds. -/
theorem ahead_bytes (cap burst : Nat) (q₀ : Lanes) (pre post : List (Lane × ByteArray)) (u : ByteArray)
    (h₀ : Lanes.Reach cap burst q₀)
    (h : ((((q₀.take burst).2.pushAll pre).push .urgent u).pushAll post).bytes ≤ cap) :
    (∃ rest, (((((q₀.take burst).2.pushAll pre).push .urgent u).pushAll post).take burst).1 =
      urgents pre ++ u :: rest) ∧
    bytesOf (q₀.take burst).1 ≤ min cap (bytesOf q₀.urgent + max burst (q₀.serve.headD .empty).size) ∧
    bytesOf (urgents pre) + u.size ≤ cap := by
  refine ⟨?_, ?_, ?_⟩
  · rw [urgent_ahead]
    obtain ⟨hu, -⟩ := pushAll_lanes (q₀.take burst).2 pre
    rw [hu, (take_append burst q₀).2]
    exact ⟨_, by simp; rfl⟩
  · have h1 := lanes_bounded h₀
    have h2 := take_bytes burst q₀
    rw [take_urgent_first, bytesOf_append] at h2 ⊢
    have := cut_bytes burst q₀.serve
    omega
  · rw [pushAll_bytes] at h
    have hp := pushAll_bytes (q₀.take burst).2 pre
    have hu : (((q₀.take burst).2.pushAll pre).push .urgent u).bytes =
        ((q₀.take burst).2.pushAll pre).bytes + u.size := by
      simp [Lanes.push, Lanes.bytes, bytesOf]; omega
    omega

/-! ## Serving into the window -/

/-- A session's room at a socket's address is `window` less what the
socket's lanes hold. -/
theorem roomOf_found (w : Nat) (qs : List (ByteArray × Lanes)) (a a' : ByteArray) (q : Lanes)
    (h : qs.find? (·.1 == a) = some (a', q)) : roomOf w qs a = some (w - q.bytes) := by
  simp [roomOf, h]

/-- **Serving stays within the window and one op.** A step serves a
session at most its room and one op (`serveOwed_budget`); its room is
what its socket's lanes, holding b bytes, have left of `window`. So the
lanes then hold at most `window` and that op, or the b they held. -/
theorem room_window (w : Nat) (qs : List (ByteArray × Lanes)) (a a' : ByteArray) (q : Lanes)
    (h : qs.find? (·.1 == a) = some (a', q)) (served op : Nat)
    (hs : ∀ r, roomOf w qs a = some r → served ≤ r + op) :
    q.bytes + served ≤ max q.bytes w + op := by
  have := hs _ (roomOf_found w qs a a' q h)
  omega

/-! ## Stalls -/

/-- **A writer stalled for `stallMs` is closed.** A socket whose writer's
write under way began at t is one the loop's clock closes (`shut`) at
any time from t + `stallMs` on. -/
theorem stall_closes (idle stallMs now heard t : Nat) (h : t + stallMs ≤ now) :
    shut idle stallMs now heard (some t) = true := by
  simp [shut, h]

/-- And one heard from within `idle`, with no write under way, or one
under way for less than `stallMs`, is not. -/
theorem shut_live (idle stallMs now heard : Nat) (since : Option Nat) (hh : now ≤ heard + idle)
    (hs : ∀ t, since = some t → now < t + stallMs) : shut idle stallMs now heard since = false := by
  cases since with
  | none => simp [shut]; omega
  | some t => have := hs t rfl; simp [shut]; omega

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

/-- n iterations of a loop's choice. -/
def Inbox.iter {W E : Type} (next : Queues W E (Option (W ⊕ E))) : Nat → Queues W E (List (Option (W ⊕ E)))
  | 0 => pure []
  | n + 1 => do
    let x ← next
    let xs ← Inbox.iter next n
    return x :: xs

theorem iter_write {W E : Type} (n : Nat) (w : W) (ws : List W) (es : List E) :
    (Inbox.iter (Inbox.next popW popE) (n + 1)).run (w :: ws, es) =
      (some (.inl w) :: ((Inbox.iter (Inbox.next popW popE) n).run (ws, es)).1,
        ((Inbox.iter (Inbox.next popW popE) n).run (ws, es)).2) := rfl

/-- **The p-th write waiting enters within p + 1 iterations** of the
loop's choice (`Inbox.next`), whatever frames are queued and however
many. -/
theorem write_within {W E : Type} (ws : List W) (es : List E) (p : Nat) (hp : p < ws.length) :
    ((Inbox.iter (Inbox.next popW popE) (p + 1)).run (ws, es)).1 = (ws.take (p + 1)).map (some ∘ .inl) := by
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
