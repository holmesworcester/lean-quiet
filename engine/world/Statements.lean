/-
The many-node laws, stated over the plain world (n real nodes on held
stores, rooms read from each store, frames in the clear;
engine/world/World.lean) and the network we tolerate
(engine/world/Fair.lean), for review before they are proven
(docs/PROOFS.md, "Statements").

Each is a closed `Prop` named `…_stmt`. Names follow the program:
- **L-** laws are about the running code, one entry point at a time,
  lifted over every reachable world (`grows_stmt`, `round_stmt`, …).
- **T-** laws are about what many nodes do together over time
  (`op_stmt`, `converge_stmt`, `join_stmt`, …).
- Topologies, bounds and scale come last.

Proven so far: `grows_stmt` (engine/world/Plain.lean, given the walk's
laws), the epidemic reduction and its corollaries (engine/world/Epidemic.lean),
and the findings' witnesses (engine/world/Findings.lean). Statements
false of today's code say so, with the finding.
-/
import engine.world.Fair
import engine.core.Locality
import engine.core.View

namespace Engine.World
open Engine Engine.Sync

variable {F : Type}

/-! ## Standing assumptions -/

/-- The plain setup's standing assumptions: addresses are distinct, no
data op uses a sync wire kind (a family obligation: a session would read
it as a sync message and never take it), and a want may name an id. -/
structure PlainOk (Q : Plain F) : Prop where
  addr_inj : ∀ i j, Q.addr i = Q.addr j → i = j
  wire : ∀ o, Q.fam.shared o = true → isWire o.kind = false
  maxIds : 0 < Q.cfg.maxIds

/-- No two ops any nodes hold share an id: SHA-256 has no collision on
the ops the execution carries (the crypto assumption behind `Distinct`). -/
def Unclashed {n : Nat} (w : World (Held F) n) : Prop :=
  ∀ i j x o o', (w.box i).db.ops x = some o → (w.box j).db.ops x = some o' → o = o'

/-- No collision in what any two windows' range labels hash (`Sound`,
the claim trees' crypto assumption), at any two steps. -/
def FpSound (Q : Plain F) (E : Q.Run) : Prop :=
  ∀ k k' i j r, Sound Prod.fst Prod.snd sha256 (((E.world k).node i).ix.items r) (((E.world k').node j).ix.items r)

/-- **What every liveness law assumes** of an execution of the plain
world from empty stores, with no attacker: the setup's standing
assumptions, a symmetric knows-graph, an execution the network admits
(`Net.Admits`: nothing at offline nodes; from gst, timely delivery,
ticks and redials), 2Δ shorter than patience, every window within W
items, and the two collision assumptions. Which rooms each session
carries is a separate premise (`Carries`), since rooms change. -/
structure Fair (Q : Plain F) (N : Net Q.n) (E : Q.Run) (W : Nat) : Prop where
  ok : PlainOk Q
  symm : ∀ i j, N.G i j → N.G j i
  net : N.Admits E
  patient : 2 * N.Δ < Q.cfg.patience
  bounded : ∀ r, Bounded E r W
  unclashed : ∀ k, Unclashed (E.world k)
  fp : FpSound Q E

/-- The time an op takes to cross an edge by rounds, with windows of at
most W items. -/
abbrev Plain.epochW (Q : Plain F) (N : Net Q.n) (W : Nat) : Nat := epoch Q.cfg N (depth Q.cfg W)

/-! ## L: the running code, lifted over every reachable world -/

/-- **L-grows: shared stores only grow.** No step of any node, against
any attacker, takes an op of a room out of a store. Proven (Plain.lean,
`grows_proof`, given `walk_stmt`). -/
def grows_stmt : Prop :=
  ∀ (F : Type) (Q : Plain F) adv (w : World (Held F) Q.n) (a : Act Q.n) i r x,
    Q.Reach adv w → Legal Q.setup adv w a → Q.Holds w i r x → Q.Holds (w.step Q.setup a) i r x

/-- **L-offered, its first half: the room index is the store.** At every
world reached, each node's in-memory index of room r names exactly the
ops of room r in its store. So every op a node holds is in every round
it opens or answers, and none written past the node is missed (the
app-write bypass broke this). -/
def index_store_stmt : Prop :=
  ∀ (F : Type) (Q : Plain F) adv (w : World (Held F) Q.n), Q.Reach adv w → ∀ i r x,
    (∃ it ∈ (w.node i).ix.items r, it.2 = x) ↔ Q.Holds w i r x

/-- **L-offered, its second half: the stream.** A step that stores op x
of room r at node i leaves x offered on, or known to, every session of i
that shows r; and on a session that had neither offered nor known x, an
offer naming x is in flight to the session's address. -/
def stream_stmt : Prop :=
  ∀ (F : Type) (Q : Plain F) adv (w : World (Held F) Q.n) (a : Act Q.n) i r x cid c,
    Q.Reach adv w → Legal Q.setup adv w a → PlainOk Q →
    ¬ Q.Holds w i r x → Q.Holds (w.step Q.setup a) i r x →
    ((w.step Q.setup a).node i).conn? cid = some c → r ∈ Shows Q.setup (w.step Q.setup a) i cid →
      x ∈ c.known ∨ (x ∈ c.offered ∧
        ∀ c₀, (w.node i).conn? cid = some c₀ → x ∉ c₀.offered → x ∉ c₀.known →
          ∃ p ∈ (w.step Q.setup a).flight, p.src = some i ∧ some p.dst = ((w.step Q.setup a).node i).addr? cid ∧
            ∃ L ps, x ∈ L ∧ plainPeek p.bytes = some (cid, ps) ∧ (Msg.hold L).op.bytes ∈ ps)

/-- **L-offered: store = offered**, both halves. -/
def offered_stmt : Prop := index_store_stmt ∧ stream_stmt

/-- h' holds every op h holds. -/
def Kept (h h' : Held F) : Prop := ∀ x o, h.db.ops x = some o → h'.db.ops x = some o

/-- **Only members receive.** Every session frame an honest node sends
carries sync messages, and ops of rooms the session showed during the
step that sent it, whatever the attacker does. -/
def members_only_stmt : Prop :=
  ∀ (F : Type) (Q : Plain F) adv (w : World (Held F) Q.n) (a : Act Q.n),
    Q.Reach adv w → Legal Q.setup adv w a →
    ∀ p ∈ (w.step Q.setup a).wire, p ∉ w.wire → ∀ i, p.src = some i → ∀ cid ps, plainPeek p.bytes = some (cid, ps) →
      ∀ b ∈ ps, ∀ o, Op.decode b = some o → isWire o.kind = true ∨
        ∃ h r, Kept (w.box i) h ∧ Kept h ((w.step Q.setup a).box i) ∧ r ∈ Q.rooms i h cid ∧ Q.fam.room o = some r

/-- **L-dup, its first half: frames never close a session.** In the plain
world only a tick (patience) and the harness close a session: no
delivery, duplicate, injection or write does, whatever its bytes. -/
def frames_keep_sessions_stmt : Prop :=
  ∀ (F : Type) (Q : Plain F) adv (w : World (Held F) Q.n) (a : Act Q.n) i cid,
    Q.Reach adv w → Legal Q.setup adv w a → (∀ j t, a ≠ .tick j t) → (∀ j t, a ≠ .restart j t) →
    (∀ j j' d t, a ≠ .connect j j' cid d t) → w.isOpen i cid → (w.step Q.setup a).isOpen i cid

/-- **L-idem: a frame taken twice is taken once.** Delivering the same
bytes to a node again, right after, leaves its store as the first
delivery left it (wire messages may be answered again; nothing is
stored twice). -/
def idem_stmt : Prop :=
  ∀ (F : Type) (Q : Plain F) adv (w : World (Held F) Q.n) (i : Fin Q.n) (a b : ByteArray) (t t' : Nat),
    Q.Reach adv w →
    let w₁ := w.enter Q.setup i t fun nd => nd.onFrame (Q.setup.sync i) a b t
    let w₂ := w₁.enter Q.setup i t' fun nd => nd.onFrame (Q.setup.sync i) a b t'
    w₂.box i = w₁.box i

/-- **L-restart: a restart loses only memory.** After node i crashes and
boots from its store, it holds the same ops, its index names exactly
its store's ops of each room, and it has no sessions. -/
def restart_stmt : Prop :=
  ∀ (F : Type) (Q : Plain F) adv (w : World (Held F) Q.n) (i : Fin Q.n) (t : Nat),
    Q.Reach adv w → Legal Q.setup adv w (.restart i t) →
    (∀ r x, Q.Holds w i r x ↔ Q.Holds (w.step Q.setup (.restart i t)) i r x) ∧
    (∀ r x, (∃ it ∈ ((w.step Q.setup (.restart i t)).node i).ix.items r, it.2 = x) ↔
      Q.Holds (w.step Q.setup (.restart i t)) i r x) ∧
    ((w.step Q.setup (.restart i t)).node i).conns = []

/-- **Waiting ops close.** At every world reached, every node's store is
at rest and its verdicts are the spec's over the ops it holds. So an op
that waited on a missing requirement is judged in the very step that
brings the last of them, as if it had arrived after them. -/
def waiting_closure_stmt : Prop :=
  ∀ (F : Type) (Q : Plain F) adv (w : World (Held F) Q.n), Q.Reach adv w → ∀ i, CollisionFree (w.box i).log →
    (w.box i).db.queue = [] ∧ ∀ x v, (w.box i).db.status x = some v ↔ Spec Q.fam (w.box i).db.ops x v

/-- **Nodes holding a closure judge alike.** If node i judged x as v, and
node j holds every op of x's requirement closure at i, j judged x as v. -/
def closure_agree_stmt : Prop :=
  ∀ (F : Type) (Q : Plain F) adv (w : World (Held F) Q.n), Q.Reach adv w → ∀ i j x v,
    CollisionFree (w.box i).log → CollisionFree (w.box j).log →
    (∀ y o, Engine.Sync.Reach (w.box i).db.ops x y → (w.box i).db.ops y = some o → (w.box j).db.ops y = some o) →
    (w.box i).db.status x = some v → (w.box j).db.status x = some v

/-- **L-local: the same ops, the same facts and views.** Two nodes whose
stores hold the same ops judge every op alike, and every view (a
composition of lists, engine/core/View.lean) reads the same answer at
both. -/
def local_stmt : Prop :=
  ∀ (F : Type) [SortKey F] (Q : Plain F) adv (w : World (Held F) Q.n), Q.Reach adv w → ∀ i j,
    CollisionFree (w.box i).log → CollisionFree (w.box j).log →
    (∀ x, (w.box i).db.ops x = (w.box j).db.ops x) →
    (∀ x, (w.box i).db.status x = (w.box j).db.status x) ∧
    ∀ (α : Type) (v : View F α), ((v.run : HeldM F α).run (w.box i)).1 = ((v.run : HeldM F α).run (w.box j)).1

/-! ## L: one round, under any interleaving -/

/-- Round kr of room r on session cid: its opening, a packet from i to
j carrying i's openings of the window ranges, is in flight at step k. -/
def Opening (Q : Plain F) (E : Q.Run) (i j : Fin Q.n) (cid r : Id) (kr k : Nat) (p : Packet Q.n) : Prop :=
  p ∈ (E.world k).flight ∧ p.src = some i ∧ p.dst = Q.addr j ∧
  ∃ ps X, plainPeek p.bytes = some (cid, ps) ∧
    (Msg.rbsr r kr ((window (max ((E.world k).node i).floor ((E.world k).node j).floor)).map
        (opening Prod.fst Prod.snd sha256 Q.cfg.params X))).op.bytes ∈ ps

/-- From step k on, session cid shows the same rooms at i and j, r among
them. -/
def Agree (Q : Plain F) (E : Q.Run) (i j : Fin Q.n) (cid r : Id) (k : Nat) : Prop :=
  ∀ k', k ≤ k' → Shows Q.setup (E.world k') i cid = Shows Q.setup (E.world k') j cid ∧
    r ∈ Shows Q.setup (E.world k') i cid

/-- **L-round: a round carries both sides' ops, whatever else happens.**
A round of room r opened from i (dialing) to j on a session joined from
step k on, whose ends agree on rooms and show r, with the edge live:
every op of r i held when the round opened, j holds within `roundTime`,
and every op of r j held when the opening reached it, i holds within the
same time. Other rounds on other sessions, other rooms, writes,
duplicates and deliveries in any order may interleave: the hypotheses
say nothing of them. It rests on stores that only grow (so every
snapshot is served from the live store) and on `FpSound`. -/
def round_stmt : Prop :=
  ∀ (F : Type) (Q : Plain F) (N : Net Q.n) (E : Q.Run) (W : Nat) (i j : Fin Q.n) (cid r : Id) (kr k : Nat)
    (p : Packet Q.n),
    Fair Q N E W → N.G i j → Joined E i j cid k → N.gst ≤ p.sent → Agree Q E i j cid r k →
    N.Live i j p.sent (p.sent + roundTime N.Δ (depth Q.cfg W)) → Opening Q E i j cid r kr k p →
    (∀ x, Q.Holds (E.world k) i r x →
      ∃ k', k ≤ k' ∧ (E.world k').now ≤ p.sent + roundTime N.Δ (depth Q.cfg W) ∧ Q.Holds (E.world k') j r x) ∧
    (∀ k₁ idx t, k ≤ k₁ → E.act k₁ = .deliver idx t → (E.world k₁).flight[idx]? = some p →
      ∀ y, Q.Holds (E.world k₁) j r y →
        ∃ k', k₁ ≤ k' ∧ (E.world k').now ≤ p.sent + roundTime N.Δ (depth Q.cfg W) ∧ Q.Holds (E.world k') i r y)

/-- **L-round-terminates.** Such a round ends at both ends (neither keeps
its snapshot) within (D + 1)Δ of its opening, D the claim depth. -/
def round_ends_stmt : Prop :=
  ∀ (F : Type) (Q : Plain F) (N : Net Q.n) (E : Q.Run) (W : Nat) (i j : Fin Q.n) (cid r : Id) (kr k : Nat)
    (p : Packet Q.n),
    Fair Q N E W → N.G i j → Joined E i j cid k → N.gst ≤ p.sent → Agree Q E i j cid r k →
    N.Live i j p.sent (p.sent + (depth Q.cfg W + 1) * N.Δ) → Opening Q E i j cid r kr k p →
    ∃ k', k ≤ k' ∧ (E.world k').now ≤ p.sent + (depth Q.cfg W + 1) * N.Δ ∧
      ∀ c c', ((E.world k').node i).conn? cid = some c → ((E.world k').node j).conn? cid = some c' →
        (∀ e ∈ c.snaps, e.1 ≠ (r, kr)) ∧ (∀ e ∈ c'.snaps, e.1 ≠ (r, kr))

/-- **L-no-false-settle.** When node i reports room r settled on session
cid (the first round has ended and nothing it wanted is outstanding), it
holds every op of r in the round's window that the other end j held
when it took its snapshot of that round. -/
def no_false_settle_stmt : Prop :=
  ∀ (F : Type) (Q : Plain F) (E : Q.Run) (i j : Fin Q.n) (cid r : Id) (k : Nat),
    PlainOk Q → (∀ k, Unclashed (E.world k)) → FpSound Q E →
    (JoinedAt Q.setup (E.world k) i j cid ∨ JoinedAt Q.setup (E.world k) j i cid) →
    (∀ c, ((E.world k).node i).conn? cid = some c → r ∉ c.settled) →
    (∃ c, ((E.world (k + 1)).node i).conn? cid = some c ∧ r ∈ c.settled) →
    ∀ k₁ c' X, k₁ ≤ k → ((E.world k₁).node j).conn? cid = some c' → ((r, 1), X) ∈ c'.snaps →
      ∀ it ∈ X, (∃ rg ∈ window (max ((E.world k₁).node i).floor ((E.world k₁).node j).floor), rg.has it.1 = true) →
        Q.Holds (E.world (k + 1)) i r it.2

/-- **L-dup-concurrent.** Duplicates and concurrency break nothing:
frames never close a session, a frame taken twice is taken once, and a
round delivers whatever runs beside it (`round_stmt` names no other
activity). -/
def dup_concurrent_stmt : Prop := frames_keep_sessions_stmt ∧ idem_stmt ∧ round_stmt

/-- **A session stays up.** Under timely delivery with 2Δ shorter than
patience, a session joined across a live edge of G, whose rooms agree, is
never dropped while neither end restarts and the harness opens nothing
over it. False on today's code (finding 1, `patience_drops_idle`): a
cadence round is dropped whenever its answer takes longer than a tick. -/
def session_stable_stmt : Prop :=
  ∀ (F : Type) (Q : Plain F) (N : Net Q.n) (E : Q.Run) (W : Nat) (i j : Fin Q.n) (cid : Id) (k₀ k : Nat),
    Fair Q N E W → N.G i j → N.gst ≤ (E.world k₀).now →
    N.Live i j (E.world k₀).now ((E.world k).now + N.Δ) →
    (∀ k', k₀ ≤ k' → Shows Q.setup (E.world k') i cid = Shows Q.setup (E.world k') j cid) →
    (∀ k', k₀ ≤ k' → ∀ t, E.act k' ≠ .restart i t ∧ E.act k' ≠ .restart j t) →
    (∀ k', k₀ ≤ k' → ∀ a b d t, E.act k' ≠ .connect a b cid d t) →
    JoinedAt Q.setup (E.world k₀) i j cid → k₀ ≤ k → JoinedAt Q.setup (E.world k) i j cid

/-- **The pilot (leaf regime, one leg):** a round's claim of ids in room
r, in flight from i to j at step k on a session joined from k on, listing
x, which i holds: j holds x within 3Δ of the claim's sending. -/
def claim_delivers_stmt : Prop :=
  ∀ (F : Type) (Q : Plain F) (N : Net Q.n) (E : Q.Run) (W : Nat) (i j : Fin Q.n) (cid r : Id) (k kr : Nat)
    (p : Packet Q.n) (ps : List ByteArray) (rg : Range) (L : List Id) (x : Id),
    Fair Q N E W → N.G i j → Joined E i j cid k → N.gst ≤ p.sent → N.Live i j p.sent (p.sent + 3 * N.Δ) →
    (∀ k', k ≤ k' → r ∈ Shows Q.setup (E.world k') i cid ∧ r ∈ Shows Q.setup (E.world k') j cid) →
    p ∈ (E.world k).flight → p.src = some i → p.dst = Q.addr j → plainPeek p.bytes = some (cid, ps) →
    (Msg.rbsr r kr [.ids rg L]).op.bytes ∈ ps → x ∈ L → Q.Holds (E.world k) i r x →
      ∃ k', k ≤ k' ∧ (E.world k').now ≤ p.sent + 3 * N.Δ ∧ Q.Holds (E.world k') j r x

/-! ## Liveness: per edge -/

/-- **Per-edge progress** in room r, the lemma every liveness law rests
on: across an edge of G live for B ms from gst on, an op one end holds,
the other end holds within B. -/
def Edge {M : Type → Type} {S : Type} [Monad M] [Store F M] [Turn F M] {P : Setup F M S}
    {adv : World S P.n → ByteArray → Prop} {w₀ : World S P.n}
    (E : Exec P adv w₀) (N : Net P.n) (r : Id) (k₀ B : Nat) : Prop :=
  ∀ k i j x, k₀ ≤ k → N.gst ≤ (E.world k).now → N.G i j → N.Live i j (E.world k).now ((E.world k).now + B) →
    Holds P (E.world k) i r x → ∃ k', k ≤ k' ∧ (E.world k').now ≤ (E.world k).now + B ∧ Holds P (E.world k') j r x

/-- **The per-edge statement:** every fair execution has the per-edge
bound `epoch` in every room its sessions carry. -/
def edge_stmt : Prop :=
  ∀ (F : Type) (Q : Plain F) (N : Net Q.n) (E : Q.Run) (r : Id) (k₀ W : Nat),
    Fair Q N E W → Carries E N.G r k₀ → Edge E N r k₀ (Q.epochW N W)

/-! ## T: many nodes over time -/

/-- **T-op: every op travels every path, under continuous writes.** Over
a path of d edges of G, all live: an op the path's first node holds, its
last holds within d · epoch. Nothing is quiescent: other writes, rounds
and deliveries go on throughout. -/
def op_stmt : Prop :=
  ∀ (F : Type) (Q : Plain F) (N : Net Q.n) (E : Q.Run) (r : Id) (k₀ W d : Nat) (i j : Fin Q.n),
    Fair Q N E W → Carries E N.G r k₀ → Path N.G d i j →
    ∀ k x, k₀ ≤ k → N.gst ≤ (E.world k).now → N.Calm (E.world k).now ((E.world k).now + d * Q.epochW N W) →
      Q.Holds (E.world k) i r x →
      ∃ k', k ≤ k' ∧ (E.world k').now ≤ (E.world k).now + d * Q.epochW N W ∧ Q.Holds (E.world k') j r x

/-- **T-converge** ("users always eventually sync the whole community",
when they transitively know each other): over a G of diameter d, an op
of room r any node holds, every node holds from some step on, within
d · epoch. -/
def converge_stmt : Prop :=
  ∀ (F : Type) (Q : Plain F) (N : Net Q.n) (E : Q.Run) (r : Id) (k₀ W d : Nat),
    Fair Q N E W → Carries E N.G r k₀ → Diam N.G d →
    ∀ k i j x, k₀ ≤ k → N.gst ≤ (E.world k).now → N.Calm (E.world k).now ((E.world k).now + d * Q.epochW N W) →
      Q.Holds (E.world k) i r x →
      ∃ k', k ≤ k' ∧ (E.world k').now ≤ (E.world k).now + d * Q.epochW N W ∧
        ∀ k'', k' ≤ k'' → Q.Holds (E.world k'') j r x

/-- **T-converge, everyone knowing everyone:** within one epoch. -/
def converge_all_stmt : Prop :=
  ∀ (F : Type) (Q : Plain F) (N : Net Q.n) (E : Q.Run) (r : Id) (k₀ W : Nat),
    Fair Q N E W → Carries E N.G r k₀ → AllKnow N.G →
    ∀ k i j x, k₀ ≤ k → N.gst ≤ (E.world k).now → N.Calm (E.world k).now ((E.world k).now + Q.epochW N W) →
      Q.Holds (E.world k) i r x →
      ∃ k', k ≤ k' ∧ (E.world k').now ≤ (E.world k).now + Q.epochW N W ∧
        ∀ k'', k' ≤ k'' → Q.Holds (E.world k'') j r x

/-- **T-converge, two peers who know each other.** -/
def converge_two_stmt : Prop :=
  ∀ (F : Type) (Q : Plain F) (N : Net Q.n) (E : Q.Run) (r : Id) (k₀ W : Nat), Q.n = 2 →
    Fair Q N E W → Carries E N.G r k₀ → AllKnow N.G →
    ∀ k i j x, k₀ ≤ k → N.gst ≤ (E.world k).now → N.Calm (E.world k).now ((E.world k).now + Q.epochW N W) →
      Q.Holds (E.world k) i r x →
      ∃ k', k ≤ k' ∧ (E.world k').now ≤ (E.world k).now + Q.epochW N W ∧
        ∀ k'', k' ≤ k'' → Q.Holds (E.world k'') j r x

/-- **T-converge, three peers who know each other only transitively** (a
chain of three): within two epochs. -/
def converge_three_stmt : Prop :=
  ∀ (F : Type) (Q : Plain F) (N : Net Q.n) (E : Q.Run) (r : Id) (k₀ W : Nat), Q.n = 3 →
    Fair Q N E W → Carries E N.G r k₀ → (∀ i j, chain Q.n i j → N.G i j) →
    ∀ k i j x, k₀ ≤ k → N.gst ≤ (E.world k).now → N.Calm (E.world k).now ((E.world k).now + 2 * Q.epochW N W) →
      Q.Holds (E.world k) i r x →
      ∃ k', k ≤ k' ∧ (E.world k').now ≤ (E.world k).now + 2 * Q.epochW N W ∧
        ∀ k'', k' ≤ k'' → Q.Holds (E.world k'') j r x

/-- **The reduction:** the per-edge bound and growth give convergence
over any connected G (engine/world/Epidemic.lean proves this
implication). -/
def converge_of_edge_stmt : Prop := edge_stmt → grows_stmt → converge_stmt

/-- The ids of room r a store holds. -/
def held (fam : Family F) (h : Held F) (r : Id) : List Id :=
  h.db.stored.filter fun x => match h.db.ops x with
    | some o => Decidable.decide (fam.room o = some r)
    | none => false

/-- **The potential:** over every node, the ops of room r some node holds
and it lacks. Zero exactly when every node holds the same ops of r. -/
def potential (fam : Family F) {n : Nat} (w : World (Held F) n) (r : Id) : Nat :=
  let U := (List.finRange n).flatMap fun i => held fam (w.box i) r
  (List.finRange n).foldl (fun acc i => acc + (U.filter fun x => !(held fam (w.box i) r).contains x).eraseDups.length) 0

/-- **T-converge, the whole community:** if nothing is written from step
k₀ on, the potential never rises, and is zero within d · epoch. -/
def quiescent_stmt : Prop :=
  ∀ (F : Type) (Q : Plain F) (N : Net Q.n) (E : Q.Run) (r : Id) (k₀ W d : Nat),
    Fair Q N E W → Carries E N.G r k₀ → Diam N.G d → N.gst ≤ (E.world k₀).now →
    N.Calm (E.world k₀).now ((E.world k₀).now + d * Q.epochW N W) →
    (∀ k, k₀ ≤ k → ∀ i ops t, E.act k ≠ .write i ops t) →
      (∀ k k', k₀ ≤ k → k ≤ k' → potential Q.fam (E.world k') r ≤ potential Q.fam (E.world k) r) ∧
      ∃ k', k₀ ≤ k' ∧ (E.world k').now ≤ (E.world k₀).now + d * Q.epochW N W ∧ potential Q.fam (E.world k') r = 0

/-- **T-offline: catch-up and the outbox.** Node i was offline, cut off,
or crashed and restarted, any number of times, until step k (its user
may have written while online but disconnected). From k, with every
node online and every edge live for d · epoch: every op any node holds
at k, every node holds within d · epoch, all at one step. That covers
i's catch-up (what others hold) and its outbox (what it wrote away). -/
def offline_stmt : Prop :=
  ∀ (F : Type) (Q : Plain F) (N : Net Q.n) (E : Q.Run) (r : Id) (k₀ W d : Nat),
    Fair Q N E W → Carries E N.G r k₀ → Diam N.G d →
    ∀ k, k₀ ≤ k → N.gst ≤ (E.world k).now → N.Calm (E.world k).now ((E.world k).now + d * Q.epochW N W) →
    ∀ j x, Q.Holds (E.world k) j r x →
      ∃ k', k ≤ k' ∧ (E.world k').now ≤ (E.world k).now + d * Q.epochW N W ∧ ∀ l, Q.Holds (E.world k') l r x

/-- **T-closure: every node ends up judging every op alike.** If node i
judged x as v and every op of x's requirement closure at i is in a room
every edge carries: within d · epoch every node judged x as v. -/
def closure_stmt : Prop :=
  ∀ (F : Type) (Q : Plain F) (N : Net Q.n) (E : Q.Run) (k₀ W d : Nat),
    Fair Q N E W → Diam N.G d →
    ∀ k i x v, k₀ ≤ k → N.gst ≤ (E.world k).now → N.Calm (E.world k).now ((E.world k).now + d * Q.epochW N W) →
      ((E.world k).box i).db.status x = some v →
      (∀ y, Engine.Sync.Reach ((E.world k).box i).db.ops x y →
        ∃ o r, ((E.world k).box i).db.ops y = some o ∧ Q.fam.room o = some r ∧ Carries E N.G r k₀) →
      ∃ k', k ≤ k' ∧ (E.world k').now ≤ (E.world k).now + d * Q.epochW N W ∧
        ∀ j, ((E.world k').box j).db.status x = some v

/-- Every node satisfying p is within d edges of every other through
nodes satisfying p. -/
def DiamOn {n : Nat} (p : Fin n → Prop) (G : Fin n → Fin n → Prop) (d : Nat) : Prop :=
  ∀ i j, p i → p j → ∃ e, e ≤ d ∧ Path (fun a b => G a b ∧ p a ∧ p b) e i j

/-- A session between i and j at world w, either dialing. -/
def Between {M : Type → Type} {S : Type} [Monad M] (P : Setup F M S) (w : World S P.n)
    (i j : Fin P.n) (cid : Id) : Prop :=
  JoinedAt P w i j cid ∨ JoinedAt P w j i cid

/-- **T-join: a joiner gets everything, and is heard** (raced and relayed
included). Members `mem` carry room r among themselves, with diameter
dM. Node J, not a member, shows r on every session; every member that
holds J's admission a shows r to J; J knows some member. Once any member
holds a: every op of r a member or J holds, J and every member hold,
within (dM + 1) · epoch. Raced joins are two instances (each joiner
outside the other's `mem`); a relayed join is one where J's neighbour
did not write a. Today's code needs the rooms to agree at both ends
(finding 2), which a join breaks until J holds a. -/
def join_stmt : Prop :=
  ∀ (F : Type) (Q : Plain F) (N : Net Q.n) (E : Q.Run) (r a : Id) (mem : Fin Q.n → Prop) (J : Fin Q.n)
    (k₀ W dM : Nat),
    Fair Q N E W → ¬ mem J → DiamOn mem N.G dM →
    Carries E (fun i j => N.G i j ∧ mem i ∧ mem j) r k₀ →
    (∀ k cid, k₀ ≤ k → r ∈ Shows Q.setup (E.world k) J cid) →
    (∀ k i cid, k₀ ≤ k → mem i → Between Q.setup (E.world k) i J cid →
      (∃ ra, Q.Holds (E.world k) i ra a) → r ∈ Shows Q.setup (E.world k) i cid) →
    (∃ i, mem i ∧ N.G i J) →
    ∀ k m, k₀ ≤ k → mem m → (∃ ra, Q.Holds (E.world k) m ra a) → N.gst ≤ (E.world k).now →
      N.Calm (E.world k).now ((E.world k).now + (dM + 1) * Q.epochW N W) →
      ∀ x, ((∃ i, mem i ∧ Q.Holds (E.world k) i r x) ∨ Q.Holds (E.world k) J r x) →
        ∃ k', k ≤ k' ∧ (E.world k').now ≤ (E.world k).now + (dM + 1) * Q.epochW N W ∧
          Q.Holds (E.world k') J r x ∧ ∀ i, mem i → Q.Holds (E.world k') i r x

/-- **T-remove, the transport bound.** Removal x of member u: a node that
holds x shows u no room containing r. From step k₁, every node with a
session to u holds x. Then no op of room r that u writes from k₁ on, and
no one else writes, is ever held by another node. (That x reaches u's
neighbours within their distance times epoch is `op_stmt`. The
stronger form, about what u wrote before, is open.) -/
def remove_stmt : Prop :=
  ∀ (F : Type) (Q : Plain F) (E : Q.Run) (u : Fin Q.n) (r x : Id) (k₁ : Nat),
    (∀ k i cid, i ≠ u → (∃ rx, Q.Holds (E.world k) i rx x) → (E.world k).isOpen u cid →
      r ∉ Shows Q.setup (E.world k) i cid) →
    (∀ k i cid, k₁ ≤ k → i ≠ u → (E.world k).isOpen u cid → (E.world k).isOpen i cid →
      ∃ rx, Q.Holds (E.world k) i rx x) →
    ∀ k ops t o, k₁ ≤ k → E.act k = .write u ops t → o ∈ ops → Q.fam.room o = some r →
      (∀ i, ((E.world k).box i).db.ops o.id = none) →
      (∀ k' i ops' t', E.act k' = .write i ops' t' → i ≠ u → o ∉ ops') →
      ∀ k' i, i ≠ u → ¬ Q.Holds (E.world k') i r o.id

/-- A view of the store at an op that depends only on the op's
requirement closure. -/
def LocalAt {α : Type} (v : Held F → Id → α) : Prop :=
  ∀ h h' x, (∀ y o, Engine.Sync.Reach h.db.ops x y → h.db.ops y = some o → h'.db.ops y = some o) → v h x = v h' x

/-- **T-keys / T-read: everyone reads what anyone reads.** For a view
local to closures (a message's text, read with the key its closure
requires), if every op of x's closure at node i is in a room every edge
carries, every node reads x as i does within d · epoch. -/
def read_stmt : Prop :=
  ∀ (F : Type) (Q : Plain F) (N : Net Q.n) (E : Q.Run) (k₀ W d : Nat) (α : Type) (v : Held F → Id → α),
    Fair Q N E W → Diam N.G d → LocalAt v →
    ∀ k i x, k₀ ≤ k → N.gst ≤ (E.world k).now → N.Calm (E.world k).now ((E.world k).now + d * Q.epochW N W) →
      (∀ y, Engine.Sync.Reach ((E.world k).box i).db.ops x y →
        ∃ o r, ((E.world k).box i).db.ops y = some o ∧ Q.fam.room o = some r ∧ Carries E N.G r k₀) →
      ∃ k', k ≤ k' ∧ (E.world k').now ≤ (E.world k).now + d * Q.epochW N W ∧
        ∀ j, v ((E.world k').box j) x = v ((E.world k).box i) x

/-- **T-files: a file's every chunk arrives.** A file is its root and its
chunks, ops of room r: all of them a node holds, every node holds within
d · epoch, however many there are (the window bound W counts them). -/
def files_stmt : Prop :=
  ∀ (F : Type) (Q : Plain F) (N : Net Q.n) (E : Q.Run) (r : Id) (k₀ W d : Nat) (file : List Id),
    Fair Q N E W → Carries E N.G r k₀ → Diam N.G d →
    ∀ k i, k₀ ≤ k → N.gst ≤ (E.world k).now → N.Calm (E.world k).now ((E.world k).now + d * Q.epochW N W) →
      (∀ x ∈ file, Q.Holds (E.world k) i r x) →
      ∃ k', k ≤ k' ∧ (E.world k').now ≤ (E.world k).now + d * Q.epochW N W ∧
        ∀ j, ∀ x ∈ file, Q.Holds (E.world k') j r x

/-- From step k₀ on, every session joining two neighbours in G shows r at
both ends (the other rooms may differ). -/
def Shares {M : Type → Type} {S : Type} [Monad M] [Store F M] [Turn F M] {P : Setup F M S}
    {adv : World S P.n → ByteArray → Prop} {w₀ : World S P.n}
    (E : Exec P adv w₀) (G : Fin P.n → Fin P.n → Prop) (r : Id) (k₀ : Nat) : Prop :=
  ∀ k i j cid, k₀ ≤ k → G i j → JoinedAt P (E.world k) i j cid →
    r ∈ Shows P (E.world k) i cid ∧ r ∈ Shows P (E.world k) j cid

/-- **T-rooms: a room both ends show syncs, whatever else they show.**
The per-edge bound holds in room r when every session shows r at both
ends, though their other rooms differ. False on today's code (finding
2): a room one end shows and the other does not is never answered, and
the dialer opens no round in any room while it waits. -/
def rooms_stmt : Prop :=
  ∀ (F : Type) (Q : Plain F) (N : Net Q.n) (E : Q.Run) (r : Id) (k₀ W : Nat),
    Fair Q N E W → Shares E N.G r k₀ → Edge E N r k₀ (Q.epochW N W)

/-- **T-rooms-concurrent: rooms that come and go.** Every room carried
from some step on syncs from then, whatever rooms came, went, or changed
before and on other sessions. -/
def rooms_concurrent_stmt : Prop :=
  ∀ (F : Type) (Q : Plain F) (N : Net Q.n) (E : Q.Run) (W : Nat) (rk : Id → Nat),
    Fair Q N E W → (∀ r, Carries E N.G r (rk r)) → ∀ r, Edge E N r (rk r) (Q.epochW N W)

/-- **T-relay-concurrent: the stream down a path.** Nodes v 0, …, v d,
each joined to the next by a session showing r from step k on, every
edge live: an op v 0 stores at step k, v d holds within d · 3Δ, while
each relay runs rounds and takes other ops on both sides at the same
time. -/
def relay_stmt : Prop :=
  ∀ (F : Type) (Q : Plain F) (N : Net Q.n) (E : Q.Run) (r : Id) (W d : Nat) (v : Nat → Fin Q.n) (k : Nat),
    Fair Q N E W →
    (∀ m, m < d → N.G (v m) (v (m + 1)) ∧ ∃ cid, (Joined E (v m) (v (m + 1)) cid k ∨ Joined E (v (m + 1)) (v m) cid k) ∧
        ∀ k', k ≤ k' → r ∈ Shows Q.setup (E.world k') (v m) cid ∧ r ∈ Shows Q.setup (E.world k') (v (m + 1)) cid) →
    N.gst ≤ (E.world k).now → N.Calm (E.world k).now ((E.world k).now + d * hop N) →
    ∀ x, ¬ Q.Holds (E.world k) (v 0) r x → Q.Holds (E.world (k + 1)) (v 0) r x →
      ∃ k', k ≤ k' ∧ (E.world k').now ≤ (E.world k).now + d * hop N ∧ Q.Holds (E.world k') (v d) r x

/-- **T-safe-churn: safety whatever the churn.** Under every interleaving
of crashes, restarts, offline spells, drops, duplicates, redials and an
attacker's injections, every reached world keeps the safety laws. -/
def churn_stmt : Prop :=
  grows_stmt ∧ offered_stmt ∧ members_only_stmt ∧ frames_keep_sessions_stmt ∧ waiting_closure_stmt ∧ restart_stmt

/-- **T-fresh: a fresh write is not starved by a backlog.** On FIFO links
of bandwidth bw (`Fifo`), there is a bound B, fixed by the settings, Δ
and bw alone, such that an op a node writes reaches a neighbour joined
to it within B, however much else is in flight or being synced. False
on today's code (docs/PROOFS.md, "T-fresh"): the answer to one want is
up to `maxIds` ops sent at once, and a fresh offer queues behind all of
them on the link and at the receiver. -/
def fresh_stmt : Prop :=
  ∃ B : Config → Nat → Nat → Nat,
  ∀ (F : Type) (Q : Plain F) (N : Net Q.n) (E : Q.Run) (W bw : Nat) (i j : Fin Q.n) (cid r : Id) (k : Nat),
    Fair Q N E W → Fifo E N bw → 0 < bw → N.G i j → (Joined E i j cid k ∨ Joined E j i cid k) →
    (∀ k', k ≤ k' → r ∈ Shows Q.setup (E.world k') i cid ∧ r ∈ Shows Q.setup (E.world k') j cid) →
    N.gst ≤ (E.world k).now → N.Live i j (E.world k).now ((E.world k).now + B Q.cfg N.Δ bw) →
    ∀ ops t o, E.act k = .write i ops t → o ∈ ops → Q.fam.room o = some r → ((E.world k).box i).db.ops o.id = none →
      ∃ k', k ≤ k' ∧ (E.world k').now ≤ (E.world k).now + B Q.cfg N.Δ bw ∧ Q.Holds (E.world k') j r o.id

/-! ## Topologies and bounds -/

/-- **A chain:** an op at either end reaches the other within (n - 1)
epochs (d rounds for d edges). -/
def chain_stmt : Prop :=
  ∀ (F : Type) (Q : Plain F) (N : Net Q.n) (E : Q.Run) (r : Id) (k₀ W : Nat),
    Fair Q N E W → Carries E N.G r k₀ → (∀ i j, chain Q.n i j → N.G i j) →
    ∀ k i j x, k₀ ≤ k → N.gst ≤ (E.world k).now → N.Calm (E.world k).now ((E.world k).now + (Q.n - 1) * Q.epochW N W) →
      Q.Holds (E.world k) i r x →
      ∃ k', k ≤ k' ∧ (E.world k').now ≤ (E.world k).now + (Q.n - 1) * Q.epochW N W ∧ Q.Holds (E.world k') j r x

/-- **A star:** an op anywhere reaches everyone within two epochs. -/
def star_stmt : Prop :=
  ∀ (F : Type) (Q : Plain F) (N : Net Q.n) (E : Q.Run) (r : Id) (k₀ W : Nat),
    Fair Q N E W → Carries E N.G r k₀ → (∀ i j, star Q.n i j → N.G i j) →
    ∀ k i j x, k₀ ≤ k → N.gst ≤ (E.world k).now → N.Calm (E.world k).now ((E.world k).now + 2 * Q.epochW N W) →
      Q.Holds (E.world k) i r x →
      ∃ k', k ≤ k' ∧ (E.world k').now ≤ (E.world k).now + 2 * Q.epochW N W ∧ Q.Holds (E.world k') j r x

/-- **A web:** an op at s reaches everyone within s's eccentricity times
epoch. -/
def web_stmt : Prop :=
  ∀ (F : Type) (Q : Plain F) (N : Net Q.n) (E : Q.Run) (r : Id) (k₀ W e : Nat) (s : Fin Q.n),
    Fair Q N E W → Carries E N.G r k₀ → Ecc N.G s e →
    ∀ k j x, k₀ ≤ k → N.gst ≤ (E.world k).now → N.Calm (E.world k).now ((E.world k).now + e * Q.epochW N W) →
      Q.Holds (E.world k) s r x →
      ∃ k', k ≤ k' ∧ (E.world k').now ≤ (E.world k).now + e * Q.epochW N W ∧ Q.Holds (E.world k') j r x

/-- **The matching lower bound, one hop per packet.** If every packet
takes at least δ to arrive, sessions only join neighbours in G, and op x
was first written at s at step k₀, a node d edges from s holds x no
earlier than d · δ later. With δ = Δ the stream's upper bound is three
times it per hop (an offer, a want, the op). -/
def lower_stmt : Prop :=
  ∀ (F : Type) (Q : Plain F) (E : Q.Run) (G : Fin Q.n → Fin Q.n → Prop) (δ : Nat) (s j : Fin Q.n) (d : Nat)
    (x : Id) (k₀ : Nat),
    (∀ k idx t p, E.act k = .deliver idx t → (E.world k).flight[idx]? = some p → p.sent + δ ≤ t) →
    (∀ k a b cid dl t, E.act k = .connect a b cid dl t → G a b) →
    (∀ k i ops t o, E.act k = .write i ops t → o ∈ ops → o.id = x → i = s ∧ k₀ ≤ k) →
    (∀ i, ((E.world k₀).box i).db.ops x = none) → Far G s j d →
    ∀ k r, Q.Holds (E.world k) j r x → (E.world k₀).now + d * δ ≤ (E.world k).now

/-! ## Scale -/

/-- Packets node i put in flight with sending time in [t₁, t₂). -/
def sentBy {n : Nat} {S : Type} (w : World S n) (i : Fin n) (t₁ t₂ : Nat) : Nat :=
  (w.wire.filter fun p => Decidable.decide (p.src = some i) && Decidable.decide (t₁ ≤ p.sent) &&
    Decidable.decide (p.sent < t₂)).length

/-- **Per-node work at rest is O(degree · rooms), whatever n.** There is
a constant c, fixed by the settings alone, such that when nothing is
written, every store already agrees, and sessions join only neighbours
in G: in any window of length T, a node of degree at most D whose
sessions show at most R rooms sends at most c · D · R · (1 + T / every)
packets, independent of the community's size and of how much it holds. -/
def work_stmt : Prop :=
  ∃ c : Config → Nat,
  ∀ (F : Type) (Q : Plain F) (N : Net Q.n) (E : Q.Run) (W D R : Nat) (i : Fin Q.n) (k₀ : Nat),
    Fair Q N E W → Degree N.G i D →
    (∀ k cid, (Shows Q.setup (E.world k) i cid).length ≤ R) →
    (∀ k a b cid dl t, E.act k = .connect a b cid dl t → N.G a b) →
    (∀ k, k₀ ≤ k → ∀ j ops t, E.act k ≠ .write j ops t) →
    (∀ j j' x, ((E.world k₀).box j).db.ops x = ((E.world k₀).box j').db.ops x) →
    ∀ k t T, k₀ ≤ k → (E.world k₀).now ≤ t →
      sentBy (E.world k) i t (t + T) ≤ c Q.cfg * D * R * (1 + T / Q.cfg.every)

end Engine.World
