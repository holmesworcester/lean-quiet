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

Proven so far, given the walk's laws: `grows_stmt` (engine/world/Plain.lean)
and the pilot, `claim_delivers_stmt` (engine/world/Pilot.lean). Proven
outright: the epidemic reduction and its corollaries
(engine/world/Epidemic.lean), and the findings' witnesses
(engine/world/Findings.lean). Statements false of today's code say so,
with the finding.
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

/-- h' holds every op h holds. -/
def Kept (h h' : Held F) : Prop := ∀ x o, h.db.ops x = some o → h'.db.ops x = some o

/-- Payload b names op x: it is x, or a have naming x. -/
def Names (b : ByteArray) (x : Id) : Prop :=
  ∃ o, Op.decode b = some o ∧ (o.id = x ∨ ∃ r L, Msg.ofOp o = some (.hold r L) ∧ x ∈ L)

/-- **L-offered, its second half: the stream offers every op a node
stores**, not only its own writes: an op relayed from a third peer is
offered on too. A step that stores op x of room r at node i, on a
session cid that i held before the step and still holds after it, and
that shows r at every store the step passes through: either i knew
before the step that the peer holds x, or the frame the step hands i on
the session names x (the peer sent x or a have of it), or the step puts
in flight to the session's address a frame of i's naming x.

Since sync-harden, what a session knows its peer holds is a bounded hint
that a later payload may forget (finding 9), so the law names frames,
not what the session knows after the step.

What it does not cover: a session that comes to show r after x was
stored never gets x on the stream; only a round in r carries it (today's
cadence round, or a round when a room opens, docs/PROOFS.md). -/
def stream_offers_stored_stmt : Prop :=
  ∀ (F : Type) (Q : Plain F) adv (w : World (Held F) Q.n) (a : Act Q.n) i r x cid c₀ c,
    Q.Reach adv w → Legal Q.setup adv w a → PlainOk Q →
    ¬ Q.Holds w i r x → Q.Holds (w.step Q.setup a) i r x →
    (∀ h, Kept (w.box i) h → Kept h ((w.step Q.setup a).box i) → r ∈ Q.rooms i h cid) →
    (w.node i).conn? cid = some c₀ → ((w.step Q.setup a).node i).conn? cid = some c →
      x ∈ c₀.known ∨
        (∃ bytes ps, (w.step Q.setup a).delivered = w.delivered ++ [(i, bytes)] ∧
          plainPeek bytes = some (cid, ps) ∧ ∃ b ∈ ps, Names b x) ∨
        ∃ p ∈ (w.step Q.setup a).flight, p ∉ w.flight ∧ p.src = some i ∧
          some p.dst = ((w.step Q.setup a).node i).addr? cid ∧
          ∃ ps, plainPeek p.bytes = some (cid, ps) ∧ ∃ b ∈ ps, Names b x

/-- **L-offered: store = offered**, both halves. -/
def offered_stmt : Prop := index_store_stmt ∧ stream_offers_stored_stmt

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
stored twice), when the node's rooms do not depend on its store. With
rooms read from the store it is false (finding 6): a frame carrying an
op of room r and then an admission that opens r skips the op the first
time and takes it the second. -/
def idem_stmt : Prop :=
  ∀ (F : Type) (Q : Plain F) adv (w : World (Held F) Q.n) (i : Fin Q.n) (a b : ByteArray) (t t' : Nat),
    Q.Reach adv w → (∀ h h' cid, Q.rooms i h cid = Q.rooms i h' cid) →
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

/-- The ids a round message's id claims list: all it can make its
receiver ask (holmes-a3's `Msg.offers` of a round). -/
def claimIds (cs : List Claim) : List Id := cs.flatMap fun | .ids _ xs => xs | .fp .. => []

/-- The ids a payload can make its receiver ask: a have's, and a round's
id claims'. -/
def asksOf (b : ByteArray) : List Id :=
  match Op.decode b with
  | some o => match Msg.ofOp o with
    | some (.hold _ ids) => ids
    | some (.rbsr _ _ cs) => claimIds cs
    | _ => []
  | none => []

/-- The ids a session frame can make its receiver ask. -/
def frameAsks (bytes : ByteArray) : List Id :=
  match plainPeek bytes with
  | some (_, ps) => ps.flatMap asksOf
  | none => []

/-- **Finding 7's first premise.** Every op the store holds has at most B
bytes, and a want's `maxIds` ops of B bytes fit its byte budget, so a want
is served whole. -/
def Small (cfg : Config) (B : Nat) (h : Held F) : Prop :=
  B * cfg.maxIds < cfg.wantBytes ∧ ∀ y o, h.db.ops y = some o → o.bytes.size ≤ B

/-- **Finding 7's second premise.** While packet p is in flight, node j's
session cid has not asked x, and its asks have room for every id p's
frame offers. -/
def Roomy (Q : Plain F) (E : Q.Run) (j : Fin Q.n) (cid : Id) (k : Nat) (p : Packet Q.n) (x : Id) : Prop :=
  ∀ k' c, k ≤ k' → p ∈ (E.world k').flight → ((E.world k').node j).conn? cid = some c →
    x ∉ c.asked ∧ c.asked.size + (frameAsks p.bytes).length ≤ Q.cfg.maxKnown

/-- Round kr of room r on session cid: its opening, a packet from i to
j carrying i's openings of the window's ranges over X, i's index of room
r at the step the round opened, is in flight at step k. -/
def Opening (Q : Plain F) (E : Q.Run) (i j : Fin Q.n) (cid r : Id) (kr k : Nat) (p : Packet Q.n)
    (X : List Item) : Prop :=
  p ∈ (E.world k).flight ∧ p.src = some i ∧ p.dst = Q.addr j ∧
  (∃ k₀, k₀ ≤ k ∧ X = ((E.world k₀).node i).ix.items r) ∧
  ∃ ps, plainPeek p.bytes = some (cid, ps) ∧
    (Msg.rbsr r kr ((window (max ((E.world k).node i).floor ((E.world k).node j).floor)).map
        (opening Prod.fst Prod.snd sha256 Q.cfg.params X))).op.bytes ∈ ps

/-- Item it is in the window round kr of room r runs over, at step k. -/
def InWindow (Q : Plain F) (E : Q.Run) (i j : Fin Q.n) (k : Nat) (it : Item) : Prop :=
  ∃ rg ∈ window (max ((E.world k).node i).floor ((E.world k).node j).floor), rg.has it.1 = true

/-- From step k on, session cid shows the same rooms at i and j, r among
them. -/
def Agree (Q : Plain F) (E : Q.Run) (i j : Fin Q.n) (cid r : Id) (k : Nat) : Prop :=
  ∀ k', k ≤ k' → Shows Q.setup (E.world k') i cid = Shows Q.setup (E.world k') j cid ∧
    r ∈ Shows Q.setup (E.world k') i cid

/-- **L-round: a round carries both sides' ops, whatever else happens.**
A round of room r opened from i (dialing) to j on a session joined from
step k on, whose ends agree on rooms and show r, with the edge live:
every op in the round's window that i's index named when the round
opened, j holds within `roundTime`, and every op of r j held when the
opening reached it, i holds within the same time. Other rounds on other sessions, other rooms, writes,
duplicates and deliveries in any order may interleave: the hypotheses
say nothing of them. It rests on stores that only grow (so every
snapshot is served from the live store) and on `FpSound`. -/
def round_stmt : Prop :=
  ∀ (F : Type) (Q : Plain F) (N : Net Q.n) (E : Q.Run) (W : Nat) (i j : Fin Q.n) (cid r : Id) (kr k : Nat)
    (p : Packet Q.n) (X : List Item),
    Fair Q N E W → N.G i j → Joined E i j cid k → N.gst ≤ p.sent → Agree Q E i j cid r k →
    N.Live i j p.sent (p.sent + roundTime N.Δ (depth Q.cfg W)) → Opening Q E i j cid r kr k p X →
    (∀ it ∈ X, InWindow Q E i j k it →
      ∃ k', k ≤ k' ∧ (E.world k').now ≤ p.sent + roundTime N.Δ (depth Q.cfg W) ∧ Q.Holds (E.world k') j r it.2) ∧
    (∀ k₁ idx t, k ≤ k₁ → E.act k₁ = .deliver idx t → (E.world k₁).flight[idx]? = some p →
      ∀ y, Q.Holds (E.world k₁) j r y →
        ∃ k', k₁ ≤ k' ∧ (E.world k').now ≤ p.sent + roundTime N.Δ (depth Q.cfg W) ∧ Q.Holds (E.world k') i r y)

/-- **L-round-terminates.** Such a round ends at both ends (neither keeps
its snapshot) within (D + 1)Δ of its opening, D the claim depth. -/
def round_ends_stmt : Prop :=
  ∀ (F : Type) (Q : Plain F) (N : Net Q.n) (E : Q.Run) (W : Nat) (i j : Fin Q.n) (cid r : Id) (kr k : Nat)
    (p : Packet Q.n) (X : List Item),
    Fair Q N E W → N.G i j → Joined E i j cid k → N.gst ≤ p.sent → Agree Q E i j cid r k →
    N.Live i j p.sent (p.sent + (depth Q.cfg W + 1) * N.Δ) → Opening Q E i j cid r kr k p X →
    ∃ k', k ≤ k' ∧ (E.world k').now ≤ p.sent + (depth Q.cfg W + 1) * N.Δ ∧
      ∀ c c', ((E.world k').node i).conn? cid = some c → ((E.world k').node j).conn? cid = some c' →
        (∀ e ∈ c.snaps, e.1 ≠ (r, kr)) ∧ (∀ e ∈ c'.snaps, e.1 ≠ (r, kr))

/-- **L-no-false-settle.** When node i reports room r settled on session
cid (the first round has ended and nothing it wanted is outstanding), it
holds every op of r in the round's window that the other end j held
when it took its snapshot of that round. False since sync-harden
(finding 10, `expiry_settles`): an ask that expires empties `asked`, and
the room is reported settled without the op. -/
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
over it. Finding 1 made it false; sync-harden fixed that (patience starts
at the later of the last arrival and the last round). It waits on
holmes-a3's single timer (simplification 2). -/
def session_stable_stmt : Prop :=
  ∀ (F : Type) (Q : Plain F) (N : Net Q.n) (E : Q.Run) (W : Nat) (i j : Fin Q.n) (cid : Id) (k₀ k : Nat),
    Fair Q N E W → N.G i j → N.gst ≤ (E.world k₀).now →
    N.Live i j (E.world k₀).now ((E.world k).now + N.Δ) →
    (∀ k', k₀ ≤ k' → Shows Q.setup (E.world k') i cid = Shows Q.setup (E.world k') j cid) →
    (∀ k', k₀ ≤ k' → ∀ t, E.act k' ≠ .restart i t ∧ E.act k' ≠ .restart j t) →
    (∀ k', k₀ ≤ k' → ∀ a b d t, E.act k' ≠ .connect a b cid d t) →
    JoinedAt Q.setup (E.world k₀) i j cid → k₀ ≤ k → JoinedAt Q.setup (E.world k) i j cid

/-- **The pilot (leaf regime, one leg):** a round's message in room r, in
flight from i to j at step k on a session joined from k on, one of whose
claims lists ids including x, which i holds: j holds x within 3Δ of the
message's sending. Both ends
show r on the session whatever they store (the fixed-rooms case).
Since sync-harden, with finding 7's premises: i's ops are small, and j
has not asked x on the session and has room to. -/
def claim_delivers_stmt : Prop :=
  ∀ (F : Type) (Q : Plain F) (N : Net Q.n) (E : Q.Run) (W B : Nat) (i j : Fin Q.n) (cid r : Id) (k kr : Nat)
    (p : Packet Q.n) (ps : List ByteArray) (cs : List Claim) (rg : Range) (L : List Id) (x : Id),
    Fair Q N E W → N.G i j → Joined E i j cid k → N.gst ≤ p.sent → N.Live i j p.sent (p.sent + 3 * N.Δ) →
    (∀ h, r ∈ Q.rooms i h cid ∧ r ∈ Q.rooms j h cid) →
    p ∈ (E.world k).flight → p.src = some i → p.dst = Q.addr j → plainPeek p.bytes = some (cid, ps) →
    (Msg.rbsr r kr cs).op.bytes ∈ ps → Claim.ids rg L ∈ cs → x ∈ L → Q.Holds (E.world k) i r x →
    (∀ m, Small Q.cfg B ((E.world m).box i)) → Roomy Q E j cid k p x →
      ∃ k', k ≤ k' ∧ (E.world k').now ≤ p.sent + 3 * N.Δ ∧ Q.Holds (E.world k') j r x

/-- **L-round's forward leg, in the leaf regime:** with every window of
at most `leaf` items, a round's opening from i gets every op of its
window that i's index named when the round opened to j within 3Δ (the
opening lists ids, so each is the pilot). Both ends show r on the
session whatever they store. With finding 7's premises. -/
def round_forward_stmt : Prop :=
  ∀ (F : Type) (Q : Plain F) (N : Net Q.n) (E : Q.Run) (W B : Nat) (i j : Fin Q.n) (cid r : Id) (kr k : Nat)
    (p : Packet Q.n) (X : List Item),
    Fair Q N E W → W ≤ Q.cfg.params.leaf → N.G i j → Joined E i j cid k → N.gst ≤ p.sent →
    N.Live i j p.sent (p.sent + 3 * N.Δ) → (∀ h, r ∈ Q.rooms i h cid ∧ r ∈ Q.rooms j h cid) →
    (∀ m, Small Q.cfg B ((E.world m).box i)) →
    Opening Q E i j cid r kr k p X → ∀ it ∈ X, InWindow Q E i j k it → Roomy Q E j cid k p it.2 →
      ∃ k', k ≤ k' ∧ (E.world k').now ≤ p.sent + 3 * N.Δ ∧ Q.Holds (E.world k') j r it.2

/-- **An offer delivers:** the stream, a round's reverse leg and closure
offers all end this way. A have of room r naming y, in flight at step k
from j to i on a session joined from k on, both of whose ends show r
whatever they store, with j holding y: i holds y within 3Δ of the have's
sending, with finding 7's premises: j's ops are small, and while the have
is in flight i's side of the session has not asked y and has room to. -/
def offer_delivers_stmt : Prop :=
  ∀ (F : Type) (Q : Plain F) (N : Net Q.n) (E : Q.Run) (W B : Nat) (i j : Fin Q.n) (cid r : Id) (k : Nat)
    (q : Packet Q.n) (qs : List ByteArray) (H : List Id) (y : Id),
    Fair Q N E W → N.G j i → (Joined E i j cid k ∨ Joined E j i cid k) → N.gst ≤ q.sent →
    N.Live j i q.sent (q.sent + 3 * N.Δ) → (∀ h, r ∈ Q.rooms i h cid ∧ r ∈ Q.rooms j h cid) →
    q ∈ (E.world k).flight → q.src = some j → q.dst = Q.addr i → plainPeek q.bytes = some (cid, qs) →
    (Msg.hold r H).op.bytes ∈ qs → y ∈ H → H.length ≤ Q.cfg.maxIds → Q.Holds (E.world k) j r y →
    (∀ m, Small Q.cfg B ((E.world m).box j)) → Roomy Q E i cid k q y →
    ∃ k', k ≤ k' ∧ (E.world k').now ≤ q.sent + 3 * N.Δ ∧ Q.Holds (E.world k') i r y

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
dM. Node J, not a member, shows r on every session; every member whose
store holds J's admission a shows r on its sessions with J (the trust
rule, read from any store); J knows some member. Once any member
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
    (∀ (h : Held F) cid, r ∈ Q.rooms J h cid) →
    (∀ i (h : Held F) cid, mem i → (∃ k, Between Q.setup (E.world k) i J cid) →
      (∃ o, h.db.ops a = some o) → r ∈ Q.rooms i h cid) →
    (∃ i, mem i ∧ N.G i J) →
    ∀ k m, k₀ ≤ k → mem m → (∃ ra, Q.Holds (E.world k) m ra a) → N.gst ≤ (E.world k).now →
      N.Calm (E.world k).now ((E.world k).now + (dM + 1) * Q.epochW N W) →
      ∀ x, ((∃ i, mem i ∧ Q.Holds (E.world k) i r x) ∨ Q.Holds (E.world k) J r x) →
        ∃ k', k ≤ k' ∧ (E.world k').now ≤ (E.world k).now + (dM + 1) * Q.epochW N W ∧
          Q.Holds (E.world k') J r x ∧ ∀ i, mem i → Q.Holds (E.world k') i r x

/-- **T-remove, the transport bound.** Removal x of member u: a node whose
store holds x shows r on none of u's sessions (the trust rule, read from
any store, mid-step included). From step k₁, every node with a
session to u holds x. Then no op of room r that u writes from k₁ on, and
no one else writes, is ever held by another node. (That x reaches u's
neighbours within their distance times epoch is `op_stmt`. The
stronger form, about what u wrote before, is open.) -/
def remove_stmt : Prop :=
  ∀ (F : Type) (Q : Plain F) (E : Q.Run) (u : Fin Q.n) (r x : Id) (k₁ : Nat),
    (∀ i (h : Held F) cid, i ≠ u → (∃ o, h.db.ops x = some o) → (∃ k, (E.world k).isOpen u cid) →
      r ∉ Q.rooms i h cid) →
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
