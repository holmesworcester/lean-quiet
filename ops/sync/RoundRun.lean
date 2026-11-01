/- Runtime RBSR round transitions. The handler uses a snapshot until its
claim batch is finished; per-room epochs reject late terminal markers and
replayed claims without resetting another room's work. -/
import engine.wire.WorldLaws
import ops.sync.TreeLaws
import ops.sync.BoundsLaws

namespace Engine.Sync
attribute [local instance] byteArray_lawfulBEq

/-- The successor claims in one batch of actual answers. -/
def nextClaims (outs : List Out) : List Claim :=
  outs.filterMap fun | .claim x => some x | _ => none

def roundHolds (outs : List Out) : List Id :=
  outs.flatMap fun | .hold xs => xs | _ => []

def roundWants (outs : List Out) : List Id :=
  outs.flatMap fun | .want xs => xs | _ => []

/-- Every fingerprint and id claim in a received batch is answered by
`answer`, from the captured snapshot. The wire contains the exact offers
and the admitted requests; capacity deferral remains explicit. -/
theorem conn_answers_claims (cfg : Config) (ix : Index) (c : Conn)
    (r : Id) (k now : Nat) (cs : List Claim)
    (hr : r ∈ c.rooms) (fresh : c.oldRound r k = false) (hne : cs ≠ []) :
    let outs := cs.flatMap (answer Prod.fst Prod.snd sha256 cfg.params (c.snap ix r k))
    (c.onRbsr cfg ix r k cs now).send =
      (Msg.rbsr r k (nextClaims outs)).op ::
        (chunks cfg (roundHolds outs) (.hold r) ++
          chunks cfg (admitAsks cfg.maxKnown c.asked (roundWants outs)) .want) := by
  have hc : cs.isEmpty = false := List.isEmpty_eq_false_iff.mpr hne
  simp only [Conn.onRbsr, has_of_mem hr, Bool.not_true, Bool.false_eq_true,
    ite_false, fresh, hc]
  dsimp only [nextClaims, roundHolds, roundWants]
  split <;> rfl

/-- Rejected epochs leave the entire connection and output unchanged. -/
theorem conn_ignores_old_round (cfg : Config) (ix : Index) (c : Conn)
    (r : Id) (k now : Nat) (cs : List Claim)
    (hr : r ∈ c.rooms) (old : c.oldRound r k = true) :
    c.onRbsr cfg ix r k cs now = { conn := c } := by
  simp [Conn.onRbsr, has_of_mem hr, old]

/-- An old room's still-active reply cannot rewind the connection-wide
counter or clear newer-round closure work. -/
theorem beginRound_not_newer (c : Conn) (k : Nat) (hk : k ≤ c.round) :
    c.beginRound k = c := by
  have h : ¬ c.round < k := by omega
  simp [Conn.beginRound, Nat.max_eq_left hk, h]

/-- New epoch bookkeeping is bounded by the number of authorized rooms. -/
theorem noteEpoch_bounded (limit : Nat) (epochs : List (Id × Nat)) (r : Id) (k : Nat) :
    (noteEpoch limit epochs r k).length ≤ limit := List.length_take_le ..

/-- Every nonterminal response pins this room's snapshot, independently
of later changes to the live index. It also retains the exact active
epoch, so the next response is accepted. -/
theorem conn_round_continues (cfg : Config) (ix : Index) (c : Conn)
    (r : Id) (k now : Nat) (cs : List Claim)
    (hr : r ∈ c.rooms) (fresh : c.oldRound r k = false) (hne : cs ≠ [])
    (more : nextClaims (cs.flatMap (answer Prod.fst Prod.snd sha256 cfg.params (c.snap ix r k))) ≠ []) :
    let d := (c.onRbsr cfg ix r k cs now).conn
    (∀ ix', d.snap ix' r k = c.snap ix r k) ∧ d.oldRound r k = false ∧ d.rooms = c.rooms := by
  have hc : cs.isEmpty = false := List.isEmpty_eq_false_iff.mpr hne
  have hm : (nextClaims (cs.flatMap (answer Prod.fst Prod.snd sha256 cfg.params (c.snap ix r k)))).isEmpty = false :=
    List.isEmpty_eq_false_iff.mpr more
  have hp : 0 < c.rooms.length := List.length_pos_of_mem hr
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  simp only [Conn.onRbsr, has_of_mem hr, Bool.not_true, Bool.false_eq_true,
    ite_false, fresh, hc]
  split
  · rename_i h
    exact False.elim (more (List.isEmpty_iff.mp h))
  · simp [Conn.snap, Conn.oldRound, Conn.beginRound, noteEpoch, hn]

/-- Decode the next claim batch from the actual handler output. -/
def returnedClaims (send : List Op) : List Claim :=
  match send.head?.bind Msg.ofOp with
  | some (.rbsr _ _ cs) => cs
  | _ => []

@[simp] theorem ofOp_rbsr (r : Id) (k : Nat) (cs : List Claim) :
    Msg.ofOp (Msg.rbsr r k cs).op = some (.rbsr r k cs) := by
  simp [Msg.ofOp, Msg.op, kRbsr, Codec.decode_encode]

theorem conn_returns_claims (cfg : Config) (ix : Index) (c : Conn)
    (r : Id) (k now : Nat) (cs : List Claim)
    (hr : r ∈ c.rooms) (fresh : c.oldRound r k = false) (hne : cs ≠ []) :
    returnedClaims (c.onRbsr cfg ix r k cs now).send =
      nextClaims (cs.flatMap (answer Prod.fst Prod.snd sha256 cfg.params (c.snap ix r k))) := by
  rw [conn_answers_claims cfg ix c r k now cs hr fresh hne]
  simp [returnedClaims]

namespace RoundRun

/-- A delivered batch and the two real connection states. The receiver
and waiting peer exchange roles after each handler call. -/
structure State where
  receiving : Conn
  waiting : Conn
  index : Index
  peerIndex : Index
  pending : List Claim

def State.result (cfg : Config) (r : Id) (k now : Nat) (s : State) : Step :=
  s.receiving.onRbsr cfg s.index r k s.pending now

/-- Exact handler execution followed by delivery of its encoded batch.
Other effects (holds/wants) are recorded in `result.send`. A transport
embedding must arrange these deliveries before a connection is replaced. -/
def State.advance (cfg : Config) (r : Id) (k now : Nat) (s : State) : State :=
  let out := s.result cfg r k now
  { receiving := s.waiting, waiting := out.conn,
    index := s.peerIndex, peerIndex := s.index, pending := returnedClaims out.send }

/-- Both participants are still in this round and use these snapshots.
This is preserved by every nonterminal actual handler response. -/
def Ready (r : Id) (k : Nat) (X Y : List Item) (s : State) : Prop :=
  r ∈ s.receiving.rooms ∧ r ∈ s.waiting.rooms ∧
  s.receiving.oldRound r k = false ∧ s.waiting.oldRound r k = false ∧
  s.receiving.snap s.index r k = X ∧ s.waiting.snap s.peerIndex r k = Y

def outputs (cfg : Config) (X : List Item) (cs : List Claim) : List Out :=
  cs.flatMap (answer Prod.fst Prod.snd sha256 cfg.params X)

theorem successor (cfg : Config) (r : Id) (k now : Nat) (X Y : List Item) (s : State)
    (ready : Ready r k X Y s) (hne : s.pending ≠ []) :
    (s.advance cfg r k now).pending = nextClaims (outputs cfg X s.pending) := by
  exact (conn_returns_claims cfg s.index s.receiving r k now s.pending ready.1 ready.2.2.1 hne).trans
    (by rw [ready.2.2.2.2.1]; rfl)

theorem ready_next (cfg : Config) (r : Id) (k now : Nat) (X Y : List Item) (s : State)
    (ready : Ready r k X Y s) (hne : s.pending ≠ [])
    (more : (s.advance cfg r k now).pending ≠ []) :
    Ready r k Y X (s.advance cfg r k now) := by
  have hm : nextClaims (s.pending.flatMap (answer Prod.fst Prod.snd sha256 cfg.params
      (s.receiving.snap s.index r k))) ≠ [] := by
    rwa [← conn_returns_claims cfg s.index s.receiving r k now s.pending ready.1 ready.2.2.1 hne]
  obtain ⟨snap, fresh, rooms⟩ := conn_round_continues cfg s.index s.receiving r k now s.pending
    ready.1 ready.2.2.1 hne hm
  exact ⟨ready.2.1, by simpa [State.advance, State.result, rooms] using ready.1,
    ready.2.2.2.1, fresh, ready.2.2.2.2.2, (snap _).trans ready.2.2.2.2.1⟩

/-- A fingerprint's extra unit accounts for the final conversion to ids;
a split decreases the sum of the two range populations. -/
def rank (X Y : List Item) : Claim → Nat
  | .ids q _ => 2 * ((within Prod.fst q X).length + (within Prod.fst q Y).length)
  | .fp q _ _ => 2 * ((within Prod.fst q X).length + (within Prod.fst q Y).length) + 1

def HonestBatch (Y : List Item) (cs : List Claim) : Prop :=
  ∀ cl ∈ cs, ∃ q, Honest Prod.fst Prod.snd sha256 Y q cl

/-- All actual successor claims are honest for the answering snapshot,
and their rank is strictly smaller. This needs sorted indices, not a
network-progress assumption or an assumed successful reconciliation. -/
theorem answer_rank (cfg : Config) (X Y : List Item) (sx : Sorted Prod.fst X)
    (cl child : Claim) (hc : Out.claim child ∈ answer Prod.fst Prod.snd sha256 cfg.params X cl) :
    (∃ q, Honest Prod.fst Prod.snd sha256 X q child) ∧ rank Y X child < rank X Y cl := by
  cases cl with
  | ids q ids => simp [answer] at hc
  | fp q n l =>
    simp only [answer] at hc
    split at hc
    · simp at hc
    · split at hc
      · simp only [List.mem_singleton, Out.claim.injEq] at hc
        subst child
        exact ⟨⟨q, rfl, rfl⟩, by simp [rank]; omega⟩
      · rename_i hf hl
        obtain ⟨piece, hp, he⟩ := List.mem_map.mp hc
        cases he
        have shrunk := pieces_shrink (P := cfg.params) sx (Nat.lt_of_not_ge hl) piece hp
        have peer := filter_len_le (l := Y) (fun a ha => shrunk.2 (Prod.fst a) ha)
        refine ⟨⟨piece, rfl, rfl⟩, ?_⟩
        simp only [rank]
        change (within Prod.fst piece Y).length ≤ (within Prod.fst q Y).length at peer
        omega

theorem next_mem (cfg : Config) (X : List Item) (cs : List Claim) (child : Claim) :
    child ∈ nextClaims (outputs cfg X cs) ↔
      ∃ cl ∈ cs, Out.claim child ∈ answer Prod.fst Prod.snd sha256 cfg.params X cl := by
  simp only [nextClaims, outputs, List.mem_filterMap, List.mem_flatMap]
  constructor
  · rintro ⟨out, ⟨cl, hc, ho⟩, he⟩
    cases out <;> simp at he
    rename_i c
    subst child
    exact ⟨cl, hc, ho⟩
  · rintro ⟨cl, hc, ho⟩
    exact ⟨.claim child, ⟨cl, hc, ho⟩, rfl⟩

/-- A run is an equality with the actual handler transition. Scheduling
can choose any sample times; this isolated-round theorem assumes delivery
of the returned batch before timeout, disconnect, or a replacement round. -/
def Run (cfg : Config) (r : Id) (k : Nat) (times : Nat → Nat) (states : Nat → State) : Prop :=
  ∀ t, states (t + 1) = (states t).advance cfg r k (times t)

/-- Every batch terminates after at most one more turn than its largest
claim rank. This isolated trace fixes both indices; the pointwise
`conn_round_continues` lemma separately permits a changed live index.
This statement concerns claim reconciliation, before
bounded want admission and data transport. -/
theorem terminates (cfg : Config) (r : Id) (k : Nat) (times : Nat → Nat) (states : Nat → State)
    (run : Run cfg r k times states) :
    ∀ bound t X Y, Ready r k X Y (states t) → Sorted Prod.fst X → Sorted Prod.fst Y →
      (∀ cl ∈ (states t).pending, rank X Y cl ≤ bound) →
      ∃ j, t ≤ j ∧ j ≤ t + bound + 1 ∧ (states j).pending = [] := by
  intro bound
  induction bound with
  | zero =>
    intro t X Y ready sx sy ranks
    by_cases empty : (states t).pending = []
    · exact ⟨t, Nat.le_refl _, by omega, empty⟩
    have next : (states (t + 1)).pending = [] := by
      rw [run t, successor cfg r k (times t) X Y _ ready empty]
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro child hc
      obtain ⟨cl, hcl, hchild⟩ := (next_mem cfg X _ child).mp hc
      have hlt := (answer_rank cfg X Y sx cl child hchild).2
      have hle := ranks cl hcl
      omega
    exact ⟨t + 1, by omega, by omega, next⟩
  | succ bound ih =>
    intro t X Y ready sx sy ranks
    by_cases empty : (states t).pending = []
    · exact ⟨t, Nat.le_refl _, by omega, empty⟩
    by_cases ended : (states (t + 1)).pending = []
    · exact ⟨t + 1, by omega, by omega, ended⟩
    have nextReady : Ready r k Y X (states (t + 1)) := by
      rw [run t]
      exact ready_next cfg r k (times t) X Y _ ready empty (by rwa [← run t])
    have nextRanks : ∀ cl ∈ (states (t + 1)).pending, rank Y X cl ≤ bound := by
      rw [run t, successor cfg r k (times t) X Y _ ready empty]
      intro child hc
      obtain ⟨cl, hcl, hchild⟩ := (next_mem cfg X _ child).mp hc
      have hlt := (answer_rank cfg X Y sx cl child hchild).2
      have hle := ranks cl hcl
      omega
    obtain ⟨j, hj, hb, hdone⟩ := ih (t + 1) Y X nextReady sy sx nextRanks
    exact ⟨j, by omega, by omega, hdone⟩

/-- The actual wire contains an offer or a request mentioning the id. -/
def Announced (r i : Id) (ops : List Op) : Prop :=
  ∃ ids, i ∈ ids ∧ ((Msg.hold r ids).op ∈ ops ∨ (Msg.want ids).op ∈ ops)

/-- Free slots suffice to admit every newly requested id. Existing asks
remain pending and are retried by the actual connection timer. -/
theorem admit_covers (cap : Nat) (asked : Std.HashSet Id) (ids : List Id) (i : Id)
    (room : asked.size + ids.length ≤ cap) (hi : i ∈ ids) :
    i ∈ asked ∨ i ∈ admitAsks cap asked ids := by
  by_cases old : i ∈ asked
  · exact Or.inl old
  right
  unfold admitAsks
  rw [List.take_of_length_le]
  · exact List.mem_eraseDups.mpr (List.mem_filter.mpr ⟨hi, by simpa using old⟩)
  · have h1 := eraseDups_length_le (ids.filter fun j => !asked.contains j)
    have h2 := List.length_filter_le (fun j => !asked.contains j) ids
    omega

/-- The capacity premise is a numeric bound on pending asks and this
batch's raw requests. It neither assumes discovery nor assumes service. -/
def Capacity (cfg : Config) (r : Id) (k : Nat) (s : State) : Prop :=
  s.receiving.asked.size + (roundWants (outputs cfg (s.receiving.snap s.index r k) s.pending)).length ≤ cfg.maxKnown

def SeenAt (cfg : Config) (r : Id) (k now : Nat) (i : Id) (s : State) : Prop :=
  Announced r i (s.result cfg r k now).send ∨ i ∈ s.receiving.asked

theorem holds_announced (cfg : Config) (r : Id) (k now : Nat) (X Y : List Item) (s : State)
    (ready : Ready r k X Y s) (hne : s.pending ≠ []) (hmax : 0 < cfg.maxIds)
    (cl : Claim) (hcl : cl ∈ s.pending) (ids : List Id) (i : Id)
    (ho : Out.hold ids ∈ answer Prod.fst Prod.snd sha256 cfg.params X cl) (hi : i ∈ ids) :
    Announced r i (s.result cfg r k now).send := by
  have mem : i ∈ roundHolds (outputs cfg X s.pending) :=
    List.mem_flatMap.mpr ⟨.hold ids, List.mem_flatMap.mpr ⟨cl, hcl, ho⟩, hi⟩
  obtain ⟨piece, hp, hip⟩ := chunks_cover cfg _ (.hold r) hmax mem
  refine ⟨piece, hip, Or.inl ?_⟩
  rw [State.result, conn_answers_claims cfg s.index s.receiving r k now s.pending ready.1 ready.2.2.1 hne,
    ready.2.2.2.2.1]
  exact List.mem_cons_of_mem _ (List.mem_append_left _ hp)

theorem wants_seen (cfg : Config) (r : Id) (k now : Nat) (X Y : List Item) (s : State)
    (ready : Ready r k X Y s) (hne : s.pending ≠ []) (hmax : 0 < cfg.maxIds)
    (capacity : Capacity cfg r k s)
    (cl : Claim) (hcl : cl ∈ s.pending) (ids : List Id) (i : Id)
    (ho : Out.want ids ∈ answer Prod.fst Prod.snd sha256 cfg.params X cl) (hi : i ∈ ids) :
    SeenAt cfg r k now i s := by
  have mem : i ∈ roundWants (outputs cfg X s.pending) :=
    List.mem_flatMap.mpr ⟨.want ids, List.mem_flatMap.mpr ⟨cl, hcl, ho⟩, hi⟩
  rw [Capacity, ready.2.2.2.2.1] at capacity
  rcases admit_covers cfg.maxKnown s.receiving.asked _ i capacity mem with old | admitted
  · exact Or.inr old
  obtain ⟨piece, hp, hip⟩ := chunks_cover cfg _ .want hmax admitted
  refine Or.inl ⟨piece, hip, Or.inr ?_⟩
  rw [State.result, conn_answers_claims cfg s.index s.receiving r k now s.pending ready.1 ready.2.2.1 hne,
    ready.2.2.2.2.1]
  exact List.mem_cons_of_mem _ (List.mem_append_right _ hp)

/-- Every id in an honest claim's set difference reaches an actual wire
have/want, or an already-pending ask, within the claim's finite rank.
The only scheduling premise is equality with the real handler transition;
free ask slots and nonzero message chunks are stated separately. -/
theorem discovers (cfg : Config) (r : Id) (k : Nat) (times : Nat → Nat) (states : Nat → State)
    (run : Run cfg r k times states) (capacity : ∀ t, Capacity cfg r k (states t))
    (hmax : 0 < cfg.maxIds) :
    ∀ measure t X Y cl q i, rank X Y cl = measure →
      Ready r k X Y (states t) → Sorted Prod.fst X → Sorted Prod.fst Y →
      Named Prod.fst Prod.snd (X ++ Y) → Sound Prod.fst Prod.snd sha256 X Y →
      cl ∈ (states t).pending → Honest Prod.fst Prod.snd sha256 Y q cl →
      Tree.Diff Prod.fst Prod.snd X Y q i →
      ∃ j, t ≤ j ∧ j ≤ t + measure ∧ SeenAt cfg r k (times j) i (states j) := by
  intro measure
  induction measure using Nat.strongRecOn with
  | ind measure ih =>
    intro t X Y cl q i rankEq ready sx sy named sound member honest diff
    have hne : (states t).pending ≠ [] := List.ne_nil_of_mem member
    have next (child : Claim) (childRange : Range)
        (hchild : Out.claim child ∈ answer Prod.fst Prod.snd sha256 cfg.params X cl)
        (hHonest : Honest Prod.fst Prod.snd sha256 X childRange child)
        (hDiff : Tree.Diff Prod.fst Prod.snd Y X childRange i) :
        ∃ j, t ≤ j ∧ j ≤ t + measure ∧ SeenAt cfg r k (times j) i (states j) := by
      have hlt := (answer_rank cfg X Y sx cl child hchild).2
      have childMem : child ∈ (states (t + 1)).pending := by
        rw [run t, successor cfg r k (times t) X Y _ ready hne]
        exact (next_mem cfg X _ child).mpr ⟨cl, member, hchild⟩
      have nextReady : Ready r k Y X (states (t + 1)) := by
        rw [run t]
        apply ready_next cfg r k (times t) X Y _ ready hne
        rw [← run t]
        exact List.ne_nil_of_mem childMem
      obtain ⟨j, hj, hb, seen⟩ := ih (rank Y X child) (by omega) (t + 1) Y X child childRange i rfl
        nextReady sy sx (named_symm named) sound.symm childMem hHonest hDiff
      exact ⟨j, by omega, by omega, seen⟩
    rcases Tree.answer_step (P := cfg.params) X Y q cl sx named sound honest i diff with
      hold | want | ids | fp
    · obtain ⟨ids, ho, hi, _⟩ := hold
      exact ⟨t, Nat.le_refl _, by omega,
        Or.inl (holds_announced cfg r k (times t) X Y _ ready hne hmax cl member ids i ho hi)⟩
    · obtain ⟨ids, ho, hi, _⟩ := want
      exact ⟨t, Nat.le_refl _, by omega,
        wants_seen cfg r k (times t) X Y _ ready hne hmax (capacity t) cl member ids i ho hi⟩
    · exact next (.ids q ((within Prod.fst q X).map Prod.snd)) q ids.2 ⟨rfl, rfl⟩
        (Or.symm diff)
    · obtain ⟨_, piece, hc, _, hd, _⟩ := fp
      exact next _ piece hc ⟨rfl, rfl⟩ (Or.symm hd)

theorem mem_inserts (ids : List Id) (asked : Std.HashSet Id) (i : Id) :
    i ∈ ids.foldl (fun set x => set.insert x) asked ↔ i ∈ asked ∨ i ∈ ids := by
  induction ids generalizing asked with
  | nil => simp
  | cons x ids ih =>
    simp only [List.foldl_cons, ih, Std.HashSet.mem_insert, beq_iff_eq, List.mem_cons]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inr (Or.inl h.symm)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl h.symm)
      · exact Or.inr h

/-- Receiving claims never invents an outstanding ask: it was pending
already, or this exact call emitted a want containing it. -/
theorem asks_have_source (cfg : Config) (ix : Index) (c : Conn) (r : Id) (k now : Nat)
    (cs : List Claim) (hmax : 0 < cfg.maxIds) :
    ∀ i ∈ (c.onRbsr cfg ix r k cs now).conn.asked,
      i ∈ c.asked ∨ Announced r i (c.onRbsr cfg ix r k cs now).send := by
  unfold Conn.onRbsr
  split
  · intro i hi; exact Or.inl hi
  · split
    · intro i hi; exact Or.inl hi
    · dsimp only
      split
      · intro i hi; exact Or.inl hi
      · split <;> intro i hi
        all_goals
          rcases (mem_inserts _ _ i).mp hi with old | sent
          · exact Or.inl old
          · obtain ⟨piece, hp, hip⟩ := chunks_cover cfg _ .want hmax sent
            exact Or.inr ⟨piece, hip, Or.inr (List.mem_cons_of_mem _ (List.mem_append_right _ hp))⟩

/-- Starting with no outstanding asks, every later pending ask has an
actual earlier wire witness. This removes the pending-ask alternative
from discovery without assuming successful delivery or queue service. -/
theorem pending_source (cfg : Config) (r : Id) (k : Nat) (times : Nat → Nat) (states : Nat → State)
    (run : Run cfg r k times states) (hmax : 0 < cfg.maxIds)
    (emptyA : (states 0).receiving.asked = ∅) (emptyB : (states 0).waiting.asked = ∅) :
    ∀ t i, i ∈ (states t).receiving.asked ∨ i ∈ (states t).waiting.asked →
      ∃ j, j < t ∧ Announced r i ((states j).result cfg r k (times j)).send := by
  intro t
  induction t with
  | zero => intro i hi; simp [emptyA, emptyB] at hi
  | succ t ih =>
    intro i hi
    rw [run t] at hi
    rcases hi with hi | hi
    · obtain ⟨j, hj, hs⟩ := ih i (Or.inr hi)
      exact ⟨j, by omega, hs⟩
    · rcases asks_have_source cfg (states t).index (states t).receiving r k (times t)
          (states t).pending hmax i hi with old | sent
      · obtain ⟨j, hj, hs⟩ := ih i (Or.inl old)
        exact ⟨j, by omega, hs⟩
      · exact ⟨t, by omega, sent⟩

/-- The discovered id actually appears on the wire, including when a
prior answer already reserved its ask slot. -/
theorem discovers_wire (cfg : Config) (r : Id) (k : Nat) (times : Nat → Nat) (states : Nat → State)
    (run : Run cfg r k times states) (capacity : ∀ t, Capacity cfg r k (states t))
    (hmax : 0 < cfg.maxIds) (X Y : List Item)
    (ready : Ready r k X Y (states 0)) (sx : Sorted Prod.fst X) (sy : Sorted Prod.fst Y)
    (named : Named Prod.fst Prod.snd (X ++ Y)) (sound : Sound Prod.fst Prod.snd sha256 X Y)
    (emptyA : (states 0).receiving.asked = ∅) (emptyB : (states 0).waiting.asked = ∅)
    (cl : Claim) (q : Range) (i : Id) (member : cl ∈ (states 0).pending)
    (honest : Honest Prod.fst Prod.snd sha256 Y q cl) (diff : Tree.Diff Prod.fst Prod.snd X Y q i) :
    ∃ j, j ≤ rank X Y cl ∧ Announced r i ((states j).result cfg r k (times j)).send := by
  obtain ⟨j, _, hj, seen⟩ := discovers cfg r k times states run capacity hmax
    (rank X Y cl) 0 X Y cl q i rfl ready sx sy named sound member honest diff
  rcases seen with sent | pending
  · exact ⟨j, by omega, sent⟩
  · obtain ⟨earlier, he, sent⟩ := pending_source cfg r k times states run hmax emptyA emptyB j i (Or.inl pending)
    exact ⟨earlier, by omega, sent⟩

/-- Construct a round using the same `start` call as the dialer's tick,
with a full-history window and one shared room. -/
def initial (cfg : Config) (r : Id) (ix iy : Index) (now : Nat) : State :=
  let receiver : Conn := { dialer := false, floor := 0, rooms := [r] }
  let dialer : Conn := { dialer := true, floor := 0, rooms := [r], peerFloor := some 0 }
  let opened := dialer.start cfg iy now
  { receiving := receiver, waiting := opened.conn,
    index := ix, peerIndex := iy, pending := returnedClaims opened.send }

/-- This is an executable run, not an assumed fair-run witness. -/
def execute (cfg : Config) (r : Id) (k : Nat) (times : Nat → Nat) (first : State) : Nat → State
  | 0 => first
  | t + 1 => (execute cfg r k times first t).advance cfg r k (times t)

theorem execute_runs (cfg : Config) (r : Id) (k : Nat) (times : Nat → Nat) (first : State) :
    Run cfg r k times (execute cfg r k times first) := fun _ => rfl

theorem advance_empty (cfg : Config) (r : Id) (k now : Nat) (s : State)
    (empty : s.pending = []) : (s.advance cfg r k now).pending = [] := by
  simp only [State.advance, State.result, empty, Conn.onRbsr]
  split
  · simp [returnedClaims]
  · split <;> simp [returnedClaims]

theorem run_empty (cfg : Config) (r : Id) (k : Nat) (times : Nat → Nat) (states : Nat → State)
    (run : Run cfg r k times states) (t : Nat) (empty : (states t).pending = []) :
    ∀ n, (states (t + n)).pending = [] := by
  intro n
  induction n with
  | zero => simpa using empty
  | succ n ih =>
    rw [show t + (n + 1) = (t + n) + 1 by omega, run (t + n)]
    exact advance_empty cfg r k (times (t + n)) _ ih

theorem run_bounded (cfg : Config) (r : Id) (k : Nat) (times : Nat → Nat) (states : Nat → State)
    (run : Run cfg r k times states)
    (first : (states 0).receiving.Bounded cfg ∧ (states 0).waiting.Bounded cfg) :
    ∀ t, (states t).receiving.Bounded cfg ∧ (states t).waiting.Bounded cfg := by
  intro t
  induction t with
  | zero => exact first
  | succ t ih =>
    rw [run t]
    exact ⟨ih.2, round_bounded cfg _ _ _ _ _ _ ih.1⟩

/-- Every possible filtered snapshot, for a finite premise certificate. -/
def subsets : List Item → List (List Item)
  | [] => [[]]
  | x :: xs => subsets xs ++ (subsets xs).map (x :: ·)

theorem filter_in_subsets (p : Item → Bool) (xs : List Item) : xs.filter p ∈ subsets xs := by
  induction xs with
  | nil => simp [subsets]
  | cons x xs ih =>
    simp only [List.filter_cons, subsets]
    split
    · exact List.mem_append_right _ (List.mem_map.mpr ⟨_, ih, rfl⟩)
    · exact List.mem_append_left _ ih

/-- All messages hashed by all possible range restrictions. -/
def hashInputs (xs : List Item) : List ByteArray :=
  (subsets xs).flatMap (pres Prod.fst Prod.snd sha256)

/-- A finite executable collision check; SHA itself remains the actual
opaque native implementation, not a substituted injective model hash. -/
def collisionCheckWith (hash : ByteArray → ByteArray) (inputs : List ByteArray) : Bool :=
  inputs.all fun a => inputs.all fun b => Decidable.decide (hash a ≠ hash b ∨ a = b)

def collisionCheck (inputs : List ByteArray) : Bool := collisionCheckWith sha256 inputs

theorem collisionCheck_sound (inputs : List ByteArray) (checked : collisionCheck inputs = true) :
    NoCollision sha256 inputs := by
  intro a ha b hb eqHash
  have both := List.all_eq_true.mp (List.all_eq_true.mp checked a ha) b hb
  have either : sha256 a ≠ sha256 b ∨ a = b := of_decide_eq_true both
  exact either.resolve_left (fun h => h eqHash)

/-- Finite enumeration discharges the apparent universal range premise:
every range restriction is one of the enumerated filtered subsets. -/
theorem sound_of_check (X Y : List Item)
    (checked : collisionCheck (hashInputs X ++ hashInputs Y) = true) :
    Sound Prod.fst Prod.snd sha256 X Y := by
  intro q
  apply nocol_sub (collisionCheck_sound _ checked)
  intro a ha
  rcases List.mem_append.mp ha with hx | hy
  · apply List.mem_append_left
    exact List.mem_flatMap.mpr ⟨_, filter_in_subsets _ X, hx⟩
  · apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨_, filter_in_subsets _ Y, hy⟩

def fullRange : Range := ⟨⟨0, 0⟩, none⟩

theorem initial_ready (cfg : Config) (r : Id) (ix iy : Index) (now : Nat) :
    Ready r 1 (ix.items r) (iy.items r) (initial cfg r ix iy now) := by
  simp [Ready, initial, Conn.start, Conn.beginRound, Conn.snap, Conn.oldRound, noteEpoch]

theorem initial_claim (cfg : Config) (r : Id) (ix iy : Index) (now : Nat) :
    (initial cfg r ix iy now).pending =
      [opening Prod.fst Prod.snd sha256 cfg.params (iy.items r) fullRange] := by
  simp [initial, Conn.start, window, returnedClaims, fullRange]

/-- All initialized asks are empty; the causality proof can therefore
trace every later pending ask to a real want on this round's wire. -/
theorem initial_asks (cfg : Config) (r : Id) (ix iy : Index) (now : Nat) :
    (initial cfg r ix iy now).receiving.asked = ∅ ∧
    (initial cfg r ix iy now).waiting.asked = ∅ := ⟨rfl, rfl⟩

end RoundRun

/-- **The actual connection executes the complete claim exchange.**
For any delivered, unreset round starting from the captured snapshots,
all claim batches terminate. Every id `exchange` says either side lacks
appears in an actual emitted have/want. Numeric capacity and the existing
fingerprint assumptions are explicit; data delivery and validation are
separate phases. No successful-discovery premise is assumed. -/
theorem conn_runs_exchange (cfg : Config) (r : Id) (k bound : Nat) (times : Nat → Nat)
    (states : Nat → RoundRun.State) (X Y : List Item)
    (run : RoundRun.Run cfg r k times states)
    (capacity : ∀ t, RoundRun.Capacity cfg r k (states t)) (hmax : 0 < cfg.maxIds)
    (ready : RoundRun.Ready r k X Y (states 0))
    (sx : Sorted Prod.fst X) (sy : Sorted Prod.fst Y)
    (named : Named Prod.fst Prod.snd (X ++ Y)) (sound : Sound Prod.fst Prod.snd sha256 X Y)
    (emptyA : (states 0).receiving.asked = ∅) (emptyB : (states 0).waiting.asked = ∅)
    (ranks : ∀ cl ∈ (states 0).pending, RoundRun.rank X Y cl ≤ bound) :
    (∃ j, j ≤ bound + 1 ∧ (states j).pending = []) ∧
    ∀ cl ∈ (states 0).pending, ∀ q, Honest Prod.fst Prod.snd sha256 Y q cl →
      ∀ fuel, (within Prod.fst q X).length + (within Prod.fst q Y).length < fuel → ∀ i,
      (i ∈ (exchange Prod.fst Prod.snd sha256 cfg.params fuel X Y cl).1 ∨
       i ∈ (exchange Prod.fst Prod.snd sha256 cfg.params fuel X Y cl).2) →
      ∃ j, j ≤ bound ∧ RoundRun.Announced r i ((states j).result cfg r k (times j)).send := by
  obtain ⟨j, _, hj, ended⟩ := RoundRun.terminates cfg r k times states run bound 0 X Y ready sx sy ranks
  refine ⟨⟨j, by omega, ended⟩, ?_⟩
  intro cl member q honest fuel enough i missing
  have exactDiff := exchange_complete (P := cfg.params) fuel X Y q cl sx sy named sound honest enough i
  have diff : Tree.Diff Prod.fst Prod.snd X Y q i := missing.elim
    (fun h => Or.inl (exactDiff.1.mp h)) (fun h => Or.inr (exactDiff.2.mp h))
  obtain ⟨j, hj, announced⟩ := RoundRun.discovers_wire cfg r k times states run capacity hmax X Y
    ready sx sy named sound emptyA emptyB cl q i member honest diff
  exact ⟨j, Nat.le_trans hj (ranks cl member), announced⟩

end Engine.Sync
