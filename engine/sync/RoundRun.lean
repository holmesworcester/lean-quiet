/- Runtime RBSR round transitions, answered from the live index. Each
claim is answered from the room as the receiver's index holds it at that
step (`Index.answer`); no connection pins a copy of a room. A run fixes
only what each step's actual handler returned: the receiving connection
and its index are free at every step, so writes, other payloads and
ticks may run between two of the round's messages. Per-room epochs
reject late terminal markers and replayed claims without resetting
another room's work.

- `RoundRun.terminates`: a round ends within the rank of its claims over
  any list U holding every item either index held in the room during the
  round. Writes during the round only enlarge U.
- `RoundRun.discovers`: an item the holder keeps either reaches the
  other side's index during the round, or is offered or wanted on the
  actual wire (or already asked), within its claim's rank. A matching
  fingerprint means equal sets at that instant (`lbl_inj`); no premise
  says the indices stay still.
- `live_round_complete` puts the two together from the round's opening;
  ops stored after it are offered by the stream (`fanout_offers`).
- `conn_runs_exchange`: with both indices fixed, the run is `exchange`. -/
import engine.wire.WorldLaws
import engine.sync.TreeLaws
import engine.sync.BoundsLaws

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
`answer`, from the room as the live index holds it now. The wire
contains the exact offers and the admitted requests; capacity deferral
remains explicit. -/
theorem conn_answers_claims (cfg : Config) (ix : Index) (c : Conn)
    (r : Id) (k now : Nat) (cs : List Claim)
    (hr : r ∈ c.rooms) (fresh : c.oldRound r k = false) (hne : cs ≠ []) :
    let outs := cs.flatMap (answer Prod.fst Prod.snd sha256 cfg.params
      (ix.over cfg.params.depth r (c.beginRound k).roundFloor))
    (c.onRbsr cfg ix r k cs now).send =
      (Msg.rbsr r k (nextClaims outs)).op ::
        (chunks cfg (roundHolds outs) (.hold r) ++
          chunks cfg (admitAsks cfg.maxKnown c.asked (roundWants outs)) .want) := by
  have hc : cs.isEmpty = false := List.isEmpty_eq_false_iff.mpr hne
  simp only [Conn.onRbsr, has_of_mem hr, Bool.not_true, Bool.false_eq_true,
    ite_false, fresh, hc, Index.answer_fun]
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

/-- Every nonterminal response keeps the round current at the side that
answered: the same rooms, and the round accepted when its next message
arrives. Nothing of the room is kept: the next answer reads the index
as it is then. -/
theorem conn_round_continues (cfg : Config) (ix : Index) (c : Conn)
    (r : Id) (k now : Nat) (cs : List Claim)
    (hr : r ∈ c.rooms) (fresh : c.oldRound r k = false) (hne : cs ≠ [])
    (more : nextClaims (cs.flatMap (answer Prod.fst Prod.snd sha256 cfg.params
      (ix.over cfg.params.depth r (c.beginRound k).roundFloor))) ≠ []) :
    let d := (c.onRbsr cfg ix r k cs now).conn
    d.oldRound r k = false ∧ d.rooms = c.rooms := by
  have hc : cs.isEmpty = false := List.isEmpty_eq_false_iff.mpr hne
  have hp : 0 < c.rooms.length := List.length_pos_of_mem hr
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  simp only [Conn.onRbsr, has_of_mem hr, Bool.not_true, Bool.false_eq_true,
    ite_false, fresh, hc, Index.answer_fun]
  split
  · rename_i h
    exact False.elim (more (List.isEmpty_iff.mp h))
  · simp [Conn.oldRound, Conn.beginRound, noteEpoch, hn]

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
      nextClaims (cs.flatMap (answer Prod.fst Prod.snd sha256 cfg.params
        (ix.over cfg.params.depth r (c.beginRound k).roundFloor))) := by
  rw [conn_answers_claims cfg ix c r k now cs hr fresh hne]
  simp [returnedClaims]

namespace RoundRun

/-- A delivered batch at its receiver: the receiving connection, its
live index at this step, and the claims to answer. `waiting` is the
other end, which `Exec` (both ends alone) uses; `Run` ignores it. -/
structure State where
  receiving : Conn
  waiting : Conn
  index : Index
  pending : List Claim

def State.result (cfg : Config) (r : Id) (k now : Nat) (s : State) : Step :=
  s.receiving.onRbsr cfg s.index r k s.pending now

/-- The receiver's set for round k of room r, as its live index holds it
at this step: the room's items, or for a windowed round its window and
closure (`Index.over`, at the round's floor). -/
def State.items (cfg : Config) (r : Id) (k : Nat) (s : State) : List Item :=
  s.index.over cfg.params.depth r (s.receiving.beginRound k).roundFloor

/-- A step's result is the running handler's, on the step's receiver,
its live index and its claims. -/
theorem result_eq (cfg : Config) (r : Id) (k now : Nat) (s : State) :
    s.result cfg r k now = s.receiving.onRbsr cfg s.index r k s.pending now := rfl

/-- A connection of a full round: its floor, its peer's and its captured
round floor are all at most 1, so its set is its room's items. -/
def Full (c : Conn) : Prop := c.floor ≤ 1 ∧ c.peerFloor.getD 0 ≤ 1 ∧ c.roundFloor ≤ 1

theorem Full.begin {c : Conn} (h : Full c) (k : Nat) : (c.beginRound k).roundFloor ≤ 1 := by
  unfold Conn.beginRound
  dsimp only
  split
  · have : c.peerFloor.getD c.floor ≤ 1 := by
      cases hp : c.peerFloor with
      | none => simpa using h.1
      | some p => have := h.2.1; simp [hp] at this ⊢; exact this
    exact Nat.max_le.2 ⟨h.1, this⟩
  · exact h.2.2

/-- Answering keeps a full round's floors. -/
theorem Full.onRbsr {c : Conn} (h : Full c) (cfg : Config) (ix : Index) (r : Id) (k : Nat) (cs : List Claim)
    (now : Nat) : Full (c.onRbsr cfg ix r k cs now).conn := by
  unfold Conn.onRbsr
  split
  · exact h
  split
  · exact h
  dsimp only
  have hb := h.begin k
  split
  · exact ⟨h.1, h.2.1, hb⟩
  split <;> exact ⟨h.1, h.2.1, hb⟩

/-- **A full round reads its room's items.** -/
theorem items_full (cfg : Config) (r : Id) (k : Nat) (s : State) (h : Full s.receiving) :
    s.items cfg r k = s.index.items r := by
  unfold State.items
  exact Index.over_full _ _ _ _ (h.begin k)

/-- A step's items are its live index's set at the round's floor. -/
theorem items_eq (cfg : Config) (r : Id) (k : Nat) (s : State) :
    s.items cfg r k = s.index.over cfg.params.depth r (s.receiving.beginRound k).roundFloor := rfl

/-- A round run: each step's claims are what the previous step's actual
handler returned. Everything else is free at every step: the receiving
connection and its live index (between two of the round's messages a
node takes other payloads, ticks and writes, from this peer or others). -/
def Run (cfg : Config) (r : Id) (k : Nat) (times : Nat → Nat) (states : Nat → State) : Prop :=
  ∀ t, (states (t + 1)).pending = returnedClaims ((states t).result cfg r k (times t)).send

/-- Round k of room r is current at this step's receiver: it shows the
room and accepts the round. -/
def Ready (r : Id) (k : Nat) (s : State) : Prop :=
  r ∈ s.receiving.rooms ∧ s.receiving.oldRound r k = false

/-- The round stays current at every step with claims pending: no newer
round of the room replaces it, and the room stays shown. -/
def Current (r : Id) (k : Nat) (states : Nat → State) : Prop :=
  ∀ t, (states t).pending ≠ [] → Ready r k (states t)

def outputs (cfg : Config) (X : List Item) (cs : List Claim) : List Out :=
  cs.flatMap (answer Prod.fst Prod.snd sha256 cfg.params X)

theorem successor (cfg : Config) (r : Id) (k now : Nat) (s : State)
    (ready : Ready r k s) (hne : s.pending ≠ []) :
    returnedClaims (s.result cfg r k now).send = nextClaims (outputs cfg (s.items cfg r k) s.pending) :=
  conn_returns_claims cfg s.index s.receiving r k now s.pending ready.1 ready.2 hne

theorem next_pending (cfg : Config) (r : Id) (k : Nat) (times : Nat → Nat) (states : Nat → State)
    (run : Run cfg r k times states) (cur : Current r k states) (t : Nat)
    (hne : (states t).pending ≠ []) :
    (states (t + 1)).pending = nextClaims (outputs cfg ((states t).items cfg r k) (states t).pending) :=
  (run t).trans (successor cfg r k (times t) _ (cur t hne) hne)

/-- A claim's rank over U: twice U's items in its range, plus one for a
fingerprint (its conversion to ids). With U every item either side holds
in the room during the round, every answer's claims rank lower. -/
def rankIn (U : List Item) : Claim → Nat
  | .ids q _ => 2 * (within Prod.fst q U).length
  | .fp q _ _ => 2 * (within Prod.fst q U).length + 1

/-- A piece the cutter's items are cut into misses one of them. -/
theorem piece_misses (P : Params) {X : List Item} {q : Range} (sX : Sorted Prod.fst X)
    (hl : P.leaf < (within Prod.fst q X).length) (piece : Range)
    (hp : piece ∈ pieces q (cutsOf Prod.fst P (within Prod.fst q X))) :
    ∃ e ∈ X, q.has e.1 = true ∧ piece.has e.1 = false := by
  obtain ⟨hlt, hsub⟩ := pieces_shrink (P := P) sX hl piece hp
  apply Classical.byContradiction
  intro hno
  have hall : ∀ e ∈ X, piece.has e.1 = q.has e.1 := by
    intro e he
    cases hq : q.has e.1
    · cases hpc : piece.has e.1
      · rfl
      · have := hsub _ hpc; rw [hq] at this; cases this
    · cases hpc : piece.has e.1
      · exact absurd ⟨e, he, hq, hpc⟩ hno
      · rfl
  have he : within Prod.fst piece X = within Prod.fst q X := List.filter_congr hall
  rw [he] at hlt
  exact Nat.lt_irrefl _ hlt

/-- All actual successor claims are honest for the answering side's
items, and rank lower over any U holding those items. This needs sorted
items, not a calm or still index. -/
theorem answer_rank (cfg : Config) (X U : List Item) (sx : Sorted Prod.fst X) (sub : ∀ a ∈ X, a ∈ U)
    (cl child : Claim) (hc : Out.claim child ∈ answer Prod.fst Prod.snd sha256 cfg.params X cl) :
    (∃ q, Honest Prod.fst Prod.snd sha256 X q child) ∧ rankIn U child < rankIn U cl := by
  cases cl with
  | ids q ids => simp [answer] at hc
  | fp q n l =>
    simp only [answer] at hc
    split at hc
    · simp at hc
    · split at hc
      · simp only [List.mem_singleton, Out.claim.injEq] at hc
        subst child
        exact ⟨⟨q, rfl, rfl⟩, by simp [rankIn]⟩
      · rename_i hf hl
        obtain ⟨piece, hp, he⟩ := List.mem_map.mp hc
        cases he
        have hp : piece ∈ pieces q (cutsOf Prod.fst cfg.params (within Prod.fst q X)) := by simpa using hp
        obtain ⟨e, heX, hq, hpc⟩ := piece_misses cfg.params sx (Nat.lt_of_not_ge hl) piece hp
        have hsub := (pieces_shrink (P := cfg.params) sx (Nat.lt_of_not_ge hl) piece hp).2
        have hlt := filter_len_lt (l := U) (p := fun a : Item => q.has a.1) (q := fun a : Item => piece.has a.1)
          (fun a ha => hsub _ ha) ⟨e, sub e heX, hq, hpc⟩
        change (within Prod.fst piece U).length < (within Prod.fst q U).length at hlt
        refine ⟨⟨piece, rfl, rfl⟩, ?_⟩
        simp only [rankIn]
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

/-- **A round ends, whatever is written meanwhile.** Every batch of a
run that stays current ends after at most one more turn than its
largest claim rank over U, any list holding every item either side's
index holds in the room at any step. No premise keeps the indices
still. This concerns claim reconciliation, before bounded want
admission and data transport. -/
theorem terminates (cfg : Config) (r : Id) (k : Nat) (times : Nat → Nat) (states : Nat → State)
    (run : Run cfg r k times states) (cur : Current r k states) (U : List Item)
    (sub : ∀ t, ∀ a ∈ (states t).items cfg r k, a ∈ U) (sorted : ∀ t, Sorted Prod.fst ((states t).items cfg r k)) :
    ∀ bound t, (∀ cl ∈ (states t).pending, rankIn U cl ≤ bound) →
      ∃ j, t ≤ j ∧ j ≤ t + bound + 1 ∧ (states j).pending = [] := by
  intro bound
  induction bound with
  | zero =>
    intro t ranks
    by_cases empty : (states t).pending = []
    · exact ⟨t, Nat.le_refl _, by omega, empty⟩
    have next : (states (t + 1)).pending = [] := by
      rw [next_pending cfg r k times states run cur t empty]
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro child hc
      obtain ⟨cl, hcl, hchild⟩ := (next_mem cfg _ _ child).mp hc
      have hlt := (answer_rank cfg _ U (sorted t) (sub t) cl child hchild).2
      have hle := ranks cl hcl
      omega
    exact ⟨t + 1, by omega, by omega, next⟩
  | succ bound ih =>
    intro t ranks
    by_cases empty : (states t).pending = []
    · exact ⟨t, Nat.le_refl _, by omega, empty⟩
    have nextRanks : ∀ cl ∈ (states (t + 1)).pending, rankIn U cl ≤ bound := by
      rw [next_pending cfg r k times states run cur t empty]
      intro child hc
      obtain ⟨cl, hcl, hchild⟩ := (next_mem cfg _ _ child).mp hc
      have hlt := (answer_rank cfg _ U (sorted t) (sub t) cl child hchild).2
      have hle := ranks cl hcl
      omega
    obtain ⟨j, hj, hb, hdone⟩ := ih (t + 1) nextRanks
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
  s.receiving.asked.size + (roundWants (outputs cfg (s.items cfg r k) s.pending)).length ≤ cfg.maxKnown

/-- Seen at a step: offered or wanted on its actual wire, or already
asked there (its want is outstanding, and the connection retries it). -/
def SeenAt (cfg : Config) (r : Id) (k now : Nat) (i : Id) (s : State) : Prop :=
  Announced r i (s.result cfg r k now).send ∨ i ∈ s.receiving.asked

theorem holds_announced (cfg : Config) (r : Id) (k now : Nat) (s : State)
    (ready : Ready r k s) (hne : s.pending ≠ []) (hmax : 0 < cfg.maxIds)
    (cl : Claim) (hcl : cl ∈ s.pending) (ids : List Id) (i : Id)
    (ho : Out.hold ids ∈ answer Prod.fst Prod.snd sha256 cfg.params (s.items cfg r k) cl) (hi : i ∈ ids) :
    Announced r i (s.result cfg r k now).send := by
  have mem : i ∈ roundHolds (outputs cfg (s.items cfg r k) s.pending) :=
    List.mem_flatMap.mpr ⟨.hold ids, List.mem_flatMap.mpr ⟨cl, hcl, ho⟩, hi⟩
  obtain ⟨piece, hp, hip⟩ := chunks_cover cfg _ (.hold r) hmax mem
  refine ⟨piece, hip, Or.inl ?_⟩
  rw [State.result, conn_answers_claims cfg s.index s.receiving r k now s.pending ready.1 ready.2 hne]
  exact List.mem_cons_of_mem _ (List.mem_append_left _ hp)

theorem wants_seen (cfg : Config) (r : Id) (k now : Nat) (s : State)
    (ready : Ready r k s) (hne : s.pending ≠ []) (hmax : 0 < cfg.maxIds)
    (capacity : Capacity cfg r k s)
    (cl : Claim) (hcl : cl ∈ s.pending) (ids : List Id) (i : Id)
    (ho : Out.want ids ∈ answer Prod.fst Prod.snd sha256 cfg.params (s.items cfg r k) cl) (hi : i ∈ ids) :
    SeenAt cfg r k now i s := by
  have mem : i ∈ roundWants (outputs cfg (s.items cfg r k) s.pending) :=
    List.mem_flatMap.mpr ⟨.want ids, List.mem_flatMap.mpr ⟨cl, hcl, ho⟩, hi⟩
  rcases admit_covers cfg.maxKnown s.receiving.asked _ i capacity mem with old | admitted
  · exact Or.inr old
  obtain ⟨piece, hp, hip⟩ := chunks_cover cfg _ .want hmax admitted
  refine Or.inl ⟨piece, hip, Or.inr ?_⟩
  rw [State.result, conn_answers_claims cfg s.index s.receiving r k now s.pending ready.1 ready.2 hne]
  exact List.mem_cons_of_mem _ (List.mem_append_right _ hp)

/-- An item named in either side's difference over q lies in q. -/
theorem has_of_diff {X Y : List Item} {q : Range} {a : Item} (nm : Named Prod.fst Prod.snd (X ++ Y))
    (ha : a ∈ X ++ Y) (hd : Tree.Diff Prod.fst Prod.snd X Y q a.2) : q.has a.1 = true := by
  rcases hd with ⟨h1, _⟩ | ⟨h1, _⟩
  · obtain ⟨b, hb, e⟩ := named_iff.1 h1
    have hbq := mem_within.1 hb
    have := (nm b (List.mem_append_left _ hbq.1) a ha).2 e
    subst this; exact hbq.2
  · obtain ⟨b, hb, e⟩ := named_iff.1 h1
    have hbq := mem_within.1 hb
    have := (nm b (List.mem_append_right _ hbq.1) a ha).2 e
    subst this; exact hbq.2

/-- One side holds a in q and the other does not: a difference over q. -/
theorem diff_of (X Y : List Item) {q : Range} {a : Item} (nm : Named Prod.fst Prod.snd (X ++ Y))
    (hq : q.has a.1 = true) :
    (a ∈ X ∧ a ∉ Y → Tree.Diff Prod.fst Prod.snd X Y q a.2) ∧
      (a ∈ Y ∧ a ∉ X → Tree.Diff Prod.fst Prod.snd X Y q a.2) := by
  refine ⟨fun ⟨hx, hy⟩ => Or.inl ⟨named_iff.2 ⟨a, mem_within.2 ⟨hx, hq⟩, rfl⟩, ?_⟩,
    fun ⟨hy, hx⟩ => Or.inr ⟨named_iff.2 ⟨a, mem_within.2 ⟨hy, hq⟩, rfl⟩, ?_⟩⟩
  · apply named_false.2
    intro b hb e
    have hb' := (mem_within.1 hb).1
    have := (nm b (List.mem_append_right _ hb') a (List.mem_append_left _ hx)).2 e
    subst this; exact hy hb'
  · apply named_false.2
    intro b hb e
    have hb' := (mem_within.1 hb).1
    have := (nm b (List.mem_append_left _ hb') a (List.mem_append_right _ hy)).2 e
    subst this; exact hx hb'

/-- **What a round discovers under live answers.** Along a run that
stays current, `Z t` is what the claimant of step t's claims held when
it made them (`Z (t + 1)` is step t's receiver's items). Item a's
holder receives at the steps where `mine` is true (the two ends
alternate) and keeps a. From a claim over a range holding a's key,
honest for its claimant, where the two ends differ on a: within the
claim's rank, the other end's index holds a, or a is offered or wanted
on the actual wire (or already asked). Each step's premises are about
that step's two item lists only: sorted, named, and no fingerprint
collision between them (`lbl_inj`: a matching fingerprint means equal
sets at that instant). No premise keeps either index still. -/
theorem discovers (cfg : Config) (r : Id) (k : Nat) (times : Nat → Nat) (states : Nat → State)
    (run : Run cfg r k times states) (cur : Current r k states)
    (capacity : ∀ t, Capacity cfg r k (states t)) (hmax : 0 < cfg.maxIds)
    (U : List Item) (sub : ∀ t, ∀ a ∈ (states t).items cfg r k, a ∈ U)
    (sorted : ∀ t, Sorted Prod.fst ((states t).items cfg r k))
    (Z : Nat → List Item) (hZ : ∀ t, Z (t + 1) = (states t).items cfg r k)
    (named : ∀ t, Named Prod.fst Prod.snd ((states t).items cfg r k ++ Z t))
    (sound : ∀ t, Sound Prod.fst Prod.snd sha256 ((states t).items cfg r k) (Z t))
    (mine : Nat → Bool) (alt : ∀ t, mine (t + 1) = !mine t) (a : Item)
    (keep : ∀ t, mine t = true → a ∈ (states t).items cfg r k) :
    ∀ m t cl q, rankIn U cl = m → cl ∈ (states t).pending →
      Honest Prod.fst Prod.snd sha256 (Z t) q cl → q.has a.1 = true →
      (mine t = true ∧ a ∉ Z t) ∨ (mine t = false ∧ a ∈ Z t) →
      ∃ j, t ≤ j ∧ j ≤ t + m ∧
        ((mine j = false ∧ a ∈ (states j).items cfg r k) ∨ SeenAt cfg r k (times j) a.2 (states j)) := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro t cl q rankEq member honest hq side
    have hne : (states t).pending ≠ [] := List.ne_nil_of_mem member
    by_cases got : mine t = false ∧ a ∈ (states t).items cfg r k
    · exact ⟨t, Nat.le_refl _, by omega, Or.inl got⟩
    have inX : a ∈ (states t).items cfg r k ∨ a ∈ Z t := by
      rcases side with ⟨hm, _⟩ | ⟨_, hz⟩
      · exact Or.inl (keep t hm)
      · exact Or.inr hz
    have ha : a ∈ (states t).items cfg r k ++ Z t := List.mem_append.2 inX
    have diff : Tree.Diff Prod.fst Prod.snd ((states t).items cfg r k) (Z t) q a.2 := by
      rcases side with ⟨hm, hz⟩ | ⟨hm, hz⟩
      · exact (diff_of _ _ (named t) hq).1 ⟨keep t hm, hz⟩
      · exact (diff_of _ _ (named t) hq).2 ⟨hz, fun h => got ⟨hm, h⟩⟩
    have next (child : Claim) (q' : Range)
        (hchild : Out.claim child ∈ answer Prod.fst Prod.snd sha256 cfg.params ((states t).items cfg r k) cl)
        (hHonest : Honest Prod.fst Prod.snd sha256 ((states t).items cfg r k) q' child)
        (hq' : q'.has a.1 = true) :
        ∃ j, t ≤ j ∧ j ≤ t + m ∧
          ((mine j = false ∧ a ∈ (states j).items cfg r k) ∨ SeenAt cfg r k (times j) a.2 (states j)) := by
      have hlt := (answer_rank cfg _ U (sorted t) (sub t) cl child hchild).2
      have childMem : child ∈ (states (t + 1)).pending := by
        rw [next_pending cfg r k times states run cur t hne]
        exact (next_mem cfg _ _ child).mpr ⟨cl, member, hchild⟩
      have side' : (mine (t + 1) = true ∧ a ∉ Z (t + 1)) ∨ (mine (t + 1) = false ∧ a ∈ Z (t + 1)) := by
        rw [hZ t, alt t]
        rcases side with ⟨hm, _⟩ | ⟨hm, _⟩
        · exact Or.inr ⟨by simp [hm], keep t hm⟩
        · exact Or.inl ⟨by simp [hm], fun h => got ⟨hm, h⟩⟩
      obtain ⟨j, hj, hb, res⟩ := ih (rankIn U child) (by omega) (t + 1) child q' rfl childMem
        (by rw [hZ t]; exact hHonest) hq' side'
      exact ⟨j, by omega, by omega, res⟩
    rcases Tree.answer_step (P := cfg.params) ((states t).items cfg r k) (Z t) q cl (sorted t) (named t)
        (sound t) honest a.2 diff with hold | want | ids | fp
    · obtain ⟨ids, ho, hi, _⟩ := hold
      exact ⟨t, Nat.le_refl _, by omega,
        Or.inr (Or.inl (holds_announced cfg r k (times t) _ (cur t hne) hne hmax cl member ids a.2 ho hi))⟩
    · obtain ⟨ids, ho, hi, _⟩ := want
      exact ⟨t, Nat.le_refl _, by omega,
        Or.inr (wants_seen cfg r k (times t) _ (cur t hne) hne hmax (capacity t) cl member ids a.2 ho hi)⟩
    · exact next _ q ids.2 ⟨rfl, rfl⟩ hq
    · obtain ⟨_, piece, hc, _, hd, _⟩ := fp
      exact next _ piece hc ⟨rfl, rfl⟩ (has_of_diff (named t) ha hd)

/-! ## Both ends alone: the two-party execution -/

/-- The two ends taking turns with nothing else between: the receiver
becomes the waiting side with the handler's connection, the waiting
side receives, with its index `next`. -/
def State.advance (cfg : Config) (r : Id) (k now : Nat) (next : Index) (s : State) : State :=
  let out := s.result cfg r k now
  { receiving := s.waiting, waiting := out.conn, index := next, pending := returnedClaims out.send }

/-- A step of the two ends: the receiver's running handler on its live
index and the pending claims; the sides swap. -/
theorem advance_eq (cfg : Config) (r : Id) (k now : Nat) (next : Index) (s : State) :
    s.advance cfg r k now next =
      { receiving := s.waiting, waiting := (s.receiving.onRbsr cfg s.index r k s.pending now).conn,
        index := next, pending := returnedClaims (s.receiving.onRbsr cfg s.index r k s.pending now).send } := rfl

/-- An execution of the actual handler, the two ends alternating, step
t + 1's receiver reading index `ixs (t + 1)`. -/
def Exec (cfg : Config) (r : Id) (k : Nat) (times : Nat → Nat) (ixs : Nat → Index)
    (states : Nat → State) : Prop :=
  ∀ t, states (t + 1) = (states t).advance cfg r k (times t) (ixs (t + 1))

/-- In an execution of a round between full ends, every step's ends stay full. -/
theorem exec_full (cfg : Config) (r : Id) (k : Nat) (times : Nat → Nat) (ixs : Nat → Index)
    (states : Nat → State) (exec : Exec cfg r k times ixs states)
    (h0 : Full (states 0).receiving ∧ Full (states 0).waiting) :
    ∀ t, Full (states t).receiving ∧ Full (states t).waiting
  | 0 => h0
  | t + 1 => by
    obtain ⟨hr, hw⟩ := exec_full cfg r k times ixs states exec h0 t
    rw [exec t]
    exact ⟨hw, hr.onRbsr cfg _ r k _ _⟩

theorem exec_runs (cfg : Config) (r : Id) (k : Nat) (times : Nat → Nat) (ixs : Nat → Index)
    (states : Nat → State) (exec : Exec cfg r k times ixs states) : Run cfg r k times states :=
  fun t => by rw [exec t]; rfl

/-- The round is current at both ends. -/
def Both (r : Id) (k : Nat) (s : State) : Prop :=
  Ready r k s ∧ r ∈ s.waiting.rooms ∧ s.waiting.oldRound r k = false

theorem advance_empty (cfg : Config) (r : Id) (k now : Nat) (next : Index) (s : State)
    (empty : s.pending = []) : (s.advance cfg r k now next).pending = [] := by
  simp only [State.advance, State.result, empty, Conn.onRbsr]
  split
  · simp [returnedClaims]
  · split <;> simp [returnedClaims]

/-- **Two ends alone keep the round current**: the handler keeps it at
the side that answered (`conn_round_continues`), and nothing else runs. -/
theorem exec_current (cfg : Config) (r : Id) (k : Nat) (times : Nat → Nat) (ixs : Nat → Index)
    (states : Nat → State) (exec : Exec cfg r k times ixs states) (first : Both r k (states 0)) :
    Current r k states := by
  have inv : ∀ t, (states t).pending ≠ [] → Both r k (states t) := by
    intro t
    induction t with
    | zero => intro _; exact first
    | succ t ih =>
      intro hne
      have hprev : (states t).pending ≠ [] := by
        intro h; apply hne; rw [exec t]; exact advance_empty cfg r k _ _ _ h
      obtain ⟨⟨hr, hf⟩, hwr, hwf⟩ := ih hprev
      have more : nextClaims (outputs cfg ((states t).items cfg r k) (states t).pending) ≠ [] := by
        rw [← successor cfg r k (times t) _ ⟨hr, hf⟩ hprev]
        have := hne; rw [exec t] at this; exact this
      obtain ⟨fresh, rooms⟩ := conn_round_continues cfg (states t).index (states t).receiving r k (times t)
        (states t).pending hr hf hprev more
      rw [exec t]
      exact ⟨⟨hwr, hwf⟩, by simpa [State.advance, State.result, rooms] using hr, fresh⟩
  exact fun t hne => (inv t hne).1

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
theorem pending_source (cfg : Config) (r : Id) (k : Nat) (times : Nat → Nat) (ixs : Nat → Index)
    (states : Nat → State) (exec : Exec cfg r k times ixs states) (hmax : 0 < cfg.maxIds)
    (emptyA : (states 0).receiving.asked = ∅) (emptyB : (states 0).waiting.asked = ∅) :
    ∀ t i, i ∈ (states t).receiving.asked ∨ i ∈ (states t).waiting.asked →
      ∃ j, j < t ∧ Announced r i ((states j).result cfg r k (times j)).send := by
  intro t
  induction t with
  | zero => intro i hi; simp [emptyA, emptyB] at hi
  | succ t ih =>
    intro i hi
    rw [exec t] at hi
    rcases hi with hi | hi
    · obtain ⟨j, hj, hs⟩ := ih i (Or.inr hi)
      exact ⟨j, by omega, hs⟩
    · rcases asks_have_source cfg (states t).index (states t).receiving r k (times t)
          (states t).pending hmax i hi with old | sent
      · obtain ⟨j, hj, hs⟩ := ih i (Or.inl old)
        exact ⟨j, by omega, hs⟩
      · exact ⟨t, by omega, sent⟩

/-- This is an executable run, not an assumed fair-run witness. -/
def execute (cfg : Config) (r : Id) (k : Nat) (times : Nat → Nat) (ixs : Nat → Index)
    (first : State) : Nat → State
  | 0 => first
  | t + 1 => (execute cfg r k times ixs first t).advance cfg r k (times t) (ixs (t + 1))

theorem execute_runs (cfg : Config) (r : Id) (k : Nat) (times : Nat → Nat) (ixs : Nat → Index)
    (first : State) : Exec cfg r k times ixs (execute cfg r k times ixs first) := fun _ => rfl

theorem run_empty (cfg : Config) (r : Id) (k : Nat) (times : Nat → Nat) (ixs : Nat → Index)
    (states : Nat → State) (exec : Exec cfg r k times ixs states) (t : Nat)
    (empty : (states t).pending = []) : ∀ n, (states (t + n)).pending = [] := by
  intro n
  induction n with
  | zero => simpa using empty
  | succ n ih =>
    rw [show t + (n + 1) = (t + n) + 1 by omega, exec (t + n)]
    exact advance_empty cfg r k _ _ _ ih

theorem run_bounded (cfg : Config) (r : Id) (k : Nat) (times : Nat → Nat) (ixs : Nat → Index)
    (states : Nat → State) (exec : Exec cfg r k times ixs states)
    (first : (states 0).receiving.Bounded cfg ∧ (states 0).waiting.Bounded cfg) :
    ∀ t, (states t).receiving.Bounded cfg ∧ (states t).waiting.Bounded cfg := by
  intro t
  induction t with
  | zero => exact first
  | succ t ih =>
    rw [exec t]
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

/-- Construct a round using the same `start` call as the dialer's tick,
with a full-history window and one shared room. -/
def initial (cfg : Config) (r : Id) (ix iy : Index) (now : Nat) : State :=
  let receiver : Conn := { dialer := false, floor := 0, rooms := [r] }
  let dialer : Conn := { dialer := true, floor := 0, rooms := [r], peerFloor := some 0 }
  let opened := dialer.start cfg iy now
  { receiving := receiver, waiting := opened.conn, index := ix, pending := returnedClaims opened.send }

theorem initial_ready (cfg : Config) (r : Id) (ix iy : Index) (now : Nat) :
    Both r 1 (initial cfg r ix iy now) := by
  simp [Both, Ready, initial, Conn.start, Conn.due, Conn.roundedAt, Conn.beginRound, Conn.oldRound, noteEpoch]

/-- The structure range and the claimed times: a full window (`window 0`). -/
def structureRange : Range := ⟨⟨0, 0⟩, some ⟨1, 0⟩⟩
def timedRange : Range := ⟨⟨1, 0⟩, none⟩

theorem initial_claim (cfg : Config) (r : Id) (ix iy : Index) (now : Nat) :
    (initial cfg r ix iy now).pending =
      [opening Prod.fst Prod.snd sha256 cfg.params (iy.items r) structureRange,
       opening Prod.fst Prod.snd sha256 cfg.params (iy.items r) timedRange] := by
  simp [initial, Conn.start, Conn.due, Conn.roundedAt, window, returnedClaims, structureRange, timedRange,
    Index.opening_fun]

/-- All initialized asks are empty; the causality proof can therefore
trace every later pending ask to a real want on this round's wire. -/
theorem initial_asks (cfg : Config) (r : Id) (ix iy : Index) (now : Nat) :
    (initial cfg r ix iy now).receiving.asked = ∅ ∧
    (initial cfg r ix iy now).waiting.asked = ∅ := by
  simp [initial, Conn.start, Conn.due, Conn.roundedAt, Conn.beginRound]

/-- Step t's items, when the two ends' indices are fixed at X (even
steps) and Y (odd). -/
theorem items_par {states : Nat → State} {r : Id} {X Y : List Item}
    (hX : ∀ t, (states (2 * t)).items cfg r k = X) (hY : ∀ t, (states (2 * t + 1)).items cfg r k = Y) (t : Nat) :
    (states t).items cfg r k = if t % 2 = 0 then X else Y := by
  by_cases h : t % 2 = 0
  · rw [if_pos h]; have := hX (t / 2); rwa [show 2 * (t / 2) = t by omega] at this
  · rw [if_neg h]; have := hY (t / 2); rwa [show 2 * (t / 2) + 1 = t by omega] at this

theorem par_alt (t : Nat) : ((t + 1) % 2 == 0) = !(t % 2 == 0) := by
  by_cases h : t % 2 = 0
  · have : (t + 1) % 2 = 1 := by omega
    simp [h, this]
  · have : (t + 1) % 2 = 0 := by omega
    simp [h, this]

end RoundRun

/-- **A round completes on the live index, with no calm premise.** Along
any run of the actual handler that stays current (`Current`: no newer
round of the room replaces it and the room stays shown; writes, other
payloads and ticks may run between its messages):
- it ends within one more turn than its opening claims' rank over U,
  any list of every item either side's index holds in the room at any
  step (writes during the round only enlarge U);
- every item a its holder keeps (`mine` marks the steps the holder
  receives; the ends alternate), in the range of an opening claim, was
  held by the other side when the round opened, or within that bound the
  other side's live index holds it, or it is offered or wanted on the
  actual wire (or already asked, its want outstanding).
Each step's premises concern that step's two item lists only: the
receiver's live items and what the claimant held when it made the
claims (`Z`), sorted, named, and with no fingerprint collision. Ops
stored after the round opened are offered by the stream
(`fanout_offers`); together the two say what each side holds at the
end, given what both held at the start. -/
theorem live_round_complete (cfg : Config) (r : Id) (k bound : Nat) (times : Nat → Nat)
    (states : Nat → RoundRun.State)
    (run : RoundRun.Run cfg r k times states) (cur : RoundRun.Current r k states)
    (capacity : ∀ t, RoundRun.Capacity cfg r k (states t)) (hmax : 0 < cfg.maxIds)
    (U : List Item) (sub : ∀ t, ∀ a ∈ (states t).items cfg r k, a ∈ U)
    (sorted : ∀ t, Sorted Prod.fst ((states t).items cfg r k))
    (Z : Nat → List Item) (hZ : ∀ t, Z (t + 1) = (states t).items cfg r k)
    (named : ∀ t, Named Prod.fst Prod.snd ((states t).items cfg r k ++ Z t))
    (sound : ∀ t, Sound Prod.fst Prod.snd sha256 ((states t).items cfg r k) (Z t))
    (ranks : ∀ cl ∈ (states 0).pending, RoundRun.rankIn U cl ≤ bound) :
    (∃ j, j ≤ bound + 1 ∧ (states j).pending = []) ∧
    ∀ (mine : Nat → Bool), (∀ t, mine (t + 1) = !mine t) → ∀ a : Item,
      (∀ t, mine t = true → a ∈ (states t).items cfg r k) → (mine 0 = false → a ∈ Z 0) →
      ∀ cl ∈ (states 0).pending, ∀ q, Honest Prod.fst Prod.snd sha256 (Z 0) q cl → q.has a.1 = true →
      (mine 0 = true ∧ a ∈ Z 0) ∨
      ∃ j, j ≤ bound ∧ ((mine j = false ∧ a ∈ (states j).items cfg r k) ∨
        RoundRun.SeenAt cfg r k (times j) a.2 (states j)) := by
  obtain ⟨j, _, hj, ended⟩ := RoundRun.terminates cfg r k times states run cur U sub sorted bound 0 ranks
  refine ⟨⟨j, by omega, ended⟩, ?_⟩
  intro mine alt a keep start cl hcl q honest hq
  by_cases h0 : mine 0 = true ∧ a ∈ Z 0
  · exact Or.inl h0
  right
  have side : (mine 0 = true ∧ a ∉ Z 0) ∨ (mine 0 = false ∧ a ∈ Z 0) := by
    cases hm : mine 0
    · exact Or.inr ⟨rfl, start hm⟩
    · exact Or.inl ⟨rfl, fun h => h0 ⟨hm, h⟩⟩
  obtain ⟨j, _, hj, res⟩ := RoundRun.discovers cfg r k times states run cur capacity hmax U sub sorted
    Z hZ named sound mine alt a keep (RoundRun.rankIn U cl) 0 cl q rfl hcl honest hq side
  exact ⟨j, Nat.le_trans (by omega) (ranks cl hcl), res⟩

/-- **The actual connection executes the complete claim exchange** when
the two ends alone take turns with fixed indices X and Y (no write during
the round): the round ends, and every id `exchange` says either side
lacks appears in an actual emitted have or want. The fixed-index case of
`live_round_complete`. Numeric capacity and the fingerprint assumptions
are explicit; data delivery and validation are separate phases. -/
theorem conn_runs_exchange (cfg : Config) (r : Id) (k bound : Nat) (times : Nat → Nat)
    (ixs : Nat → Index) (states : Nat → RoundRun.State) (X Y : List Item)
    (exec : RoundRun.Exec cfg r k times ixs states)
    (capacity : ∀ t, RoundRun.Capacity cfg r k (states t)) (hmax : 0 < cfg.maxIds)
    (ready : RoundRun.Both r k (states 0))
    (hX : ∀ t, (states (2 * t)).items cfg r k = X) (hY : ∀ t, (states (2 * t + 1)).items cfg r k = Y)
    (sx : Sorted Prod.fst X) (sy : Sorted Prod.fst Y)
    (named : Named Prod.fst Prod.snd (X ++ Y)) (sound : Sound Prod.fst Prod.snd sha256 X Y)
    (emptyA : (states 0).receiving.asked = ∅) (emptyB : (states 0).waiting.asked = ∅)
    (ranks : ∀ cl ∈ (states 0).pending, RoundRun.rankIn (X ++ Y) cl ≤ bound) :
    (∃ j, j ≤ bound + 1 ∧ (states j).pending = []) ∧
    ∀ cl ∈ (states 0).pending, ∀ q, Honest Prod.fst Prod.snd sha256 Y q cl →
      ∀ fuel, (within Prod.fst q X).length + (within Prod.fst q Y).length < fuel → ∀ i,
      (i ∈ (exchange Prod.fst Prod.snd sha256 cfg.params fuel X Y cl).1 ∨
       i ∈ (exchange Prod.fst Prod.snd sha256 cfg.params fuel X Y cl).2) →
      ∃ j, j ≤ bound ∧ RoundRun.Announced r i ((states j).result cfg r k (times j)).send := by
  have run := RoundRun.exec_runs cfg r k times ixs states exec
  have cur := RoundRun.exec_current cfg r k times ixs states exec ready
  have par := RoundRun.items_par hX hY
  let Z : Nat → List Item := fun t => if t % 2 = 0 then Y else X
  have hZ : ∀ t, Z (t + 1) = (states t).items cfg r k := by
    intro t; rw [par t]; simp only [Z]
    by_cases h : t % 2 = 0
    · rw [if_neg (by omega), if_pos h]
    · rw [if_pos (by omega), if_neg h]
  have sub : ∀ t, ∀ a ∈ (states t).items cfg r k, a ∈ X ++ Y := by
    intro t a ha; rw [par t] at ha
    split at ha
    · exact List.mem_append_left _ ha
    · exact List.mem_append_right _ ha
  have sorted : ∀ t, Sorted Prod.fst ((states t).items cfg r k) := by
    intro t; rw [par t]; split
    · exact sx
    · exact sy
  have named' : ∀ t, Named Prod.fst Prod.snd ((states t).items cfg r k ++ Z t) := by
    intro t; rw [par t]; simp only [Z]; split
    · exact named
    · exact named_symm named
  have sound' : ∀ t, Sound Prod.fst Prod.snd sha256 ((states t).items cfg r k) (Z t) := by
    intro t; rw [par t]; simp only [Z]; split
    · exact sound
    · exact sound.symm
  obtain ⟨⟨j, hj, ended⟩, disc⟩ := live_round_complete cfg r k bound times states run cur capacity hmax
    (X ++ Y) sub sorted Z hZ named' sound' ranks
  refine ⟨⟨j, hj, ended⟩, ?_⟩
  intro cl member q honest fuel enough i missing
  have exactDiff := exchange_complete (P := cfg.params) fuel X Y q cl sx sy named sound honest enough i
  -- the witness: a's holder holds a, the other end never does
  have wire : ∀ (mine : Nat → Bool) (a : Item), a.2 = i → (∀ t, mine (t + 1) = !mine t) →
      (∀ t, (mine t = true → a ∈ (states t).items cfg r k) ∧ (mine t = false → a ∉ (states t).items cfg r k)) →
      (mine 0 = false → a ∈ Z 0) → (mine 0 = true → a ∉ Z 0) → q.has a.1 = true →
      ∃ j, j ≤ bound ∧ RoundRun.Announced r i ((states j).result cfg r k (times j)).send := by
    intro mine a hai alt hold start start' hq
    rcases disc mine alt a (fun t => (hold t).1) start cl member q honest hq with h | ⟨j, hj, res⟩
    · exact absurd h.2 (start' h.1)
    rcases res with ⟨hm, ha⟩ | seen
    · exact absurd ha ((hold j).2 hm)
    rcases seen with sent | pending
    · exact ⟨j, hj, hai ▸ sent⟩
    · obtain ⟨e, he, sent⟩ := RoundRun.pending_source cfg r k times ixs states exec hmax emptyA emptyB j a.2
        (Or.inl pending)
      exact ⟨e, by omega, hai ▸ sent⟩
  rcases missing with h | h
  · obtain ⟨hx, hy⟩ := exactDiff.1.mp h
    obtain ⟨a, ha, hai⟩ := named_iff.1 hx
    obtain ⟨haX, hq⟩ := mem_within.1 ha
    have haY : a ∉ Y := fun hy' => by
      rw [named_false] at hy; exact hy a (mem_within.2 ⟨hy', hq⟩) hai
    refine wire (fun t => t % 2 == 0) a hai RoundRun.par_alt (fun t => ⟨?_, ?_⟩) ?_ ?_ hq
    · intro hm; rw [par t, if_pos (by simpa using hm)]; exact haX
    · intro hm; rw [par t, if_neg (by simpa using hm)]; exact haY
    · intro hm; simp at hm
    · intro _; simp [Z, haY]
  · obtain ⟨hy, hx⟩ := exactDiff.2.mp h
    obtain ⟨a, ha, hai⟩ := named_iff.1 hy
    obtain ⟨haY, hq⟩ := mem_within.1 ha
    have haX : a ∉ X := fun hx' => by
      rw [named_false] at hx; exact hx a (mem_within.2 ⟨hx', hq⟩) hai
    refine wire (fun t => !(t % 2 == 0)) a hai (fun t => by rw [RoundRun.par_alt]) (fun t => ⟨?_, ?_⟩) ?_ ?_ hq
    · intro hm; rw [par t, if_neg (by simpa using hm)]; exact haY
    · intro hm; rw [par t, if_pos (by simpa using hm)]; exact haX
    · intro _; simp [Z, haY]
    · intro hm; simp at hm

end Engine.Sync
