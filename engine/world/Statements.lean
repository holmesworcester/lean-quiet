/-
The many-node laws, stated over the world of n real nodes in the plain
setup (fixed rooms per session, frames in the clear; engine/world/World.lean),
for review before they are proven (docs/PROOFS.md, "Statements").

Each is a `Prop` named `…_stmt`. Proven so far: the epidemic reduction
(`converge_of_edge_stmt`, engine/world/Epidemic.lean: the per-edge bound
gives convergence over any connected G, with the 2- and 3-peer cases as
corollaries) and the pilot (engine/world/Pilot.lean).

Standing assumptions of the plain setup (`PlainOk`): addresses are
distinct, no data op has a sync wire kind, and a want may name an id.
-/
import engine.world.Fair
import engine.core.Locality

namespace Engine.World
open Engine Engine.Sync

variable {F : Type}

/-- The plain setup's standing assumptions. -/
structure PlainOk (fam : Family F) (cfg : Config) (n : Nat) (addr : Fin n → ByteArray) : Prop where
  addr_inj : ∀ i j, addr i = addr j → i = j
  /-- Data ops never use sync's wire kinds: a session would read them as
  sync messages and never take them. A family obligation. -/
  wire : ∀ o, fam.shared o = true → isWire o.kind = false
  maxIds : 0 < cfg.maxIds

/-- n nodes booted on empty stores, nothing in flight. -/
def start (fam : Family F) (cfg : Config) (n : Nat) (addr : Fin n → ByteArray)
    (rooms : Fin n → Id → List Id) : World (Held F) n :=
  World.init (plain fam cfg n addr rooms) fun _ => {}

/-- Every world the plain setup reaches from empty stores, against
attacker `adv`. -/
def PlainReach (fam : Family F) (cfg : Config) (n : Nat) (addr : Fin n → ByteArray)
    (rooms : Fin n → Id → List Id) (adv : World (Held F) n → ByteArray → Prop) (w : World (Held F) n) :
    Prop :=
  Reachable (plain fam cfg n addr rooms) adv (start fam cfg n addr rooms) w

/-! ## Safety, lifted to the world by induction on steps -/

/-- **Shared stores only grow.** No step of any node, against any
attacker, takes an op of a room out of a store. -/
def grows_stmt : Prop :=
  ∀ (F : Type) (fam : Family F) cfg n addr rooms adv (w : World (Held F) n) (a : Act n) i r x,
    PlainReach fam cfg n addr rooms adv w → Legal (plain fam cfg n addr rooms) adv w a →
      Holds (plain fam cfg n addr rooms) w i r x → Holds (plain fam cfg n addr rooms) (w.step _ a) i r x

/-- **The room index is the store** ("store = offered", its half that
rounds need): at every world reached, each node's in-memory index of room
r names exactly the ops of room r in its store. So every op a node holds
is in every round it opens or answers, and no op written past the node
is missed (the app-write bypass broke this). -/
def index_store_stmt : Prop :=
  ∀ (F : Type) (fam : Family F) cfg n addr rooms adv (w : World (Held F) n),
    PlainReach fam cfg n addr rooms adv w → ∀ i r x,
      (∃ it ∈ (w.node i).ix.items r, it.2 = x) ↔ Holds (plain fam cfg n addr rooms) w i r x

/-- **The stream** ("store = offered", its latency half): a step that
stores op x of room r at node i leaves x offered on, or known to, every
session of i that shows r; and a session that had neither offered nor
known x before has an offer naming x in flight, from i to the session's
address. -/
def stream_stmt : Prop :=
  ∀ (F : Type) (fam : Family F) cfg n addr rooms adv (w : World (Held F) n) (a : Act n) i r x cid c,
    PlainReach fam cfg n addr rooms adv w → Legal (plain fam cfg n addr rooms) adv w a →
    PlainOk fam cfg n addr →
    ¬ Holds (plain fam cfg n addr rooms) w i r x → Holds (plain fam cfg n addr rooms) (w.step _ a) i r x →
    ((w.step _ a).node i).conn? cid = some c → r ∈ rooms i cid →
      x ∈ c.known ∨ (x ∈ c.offered ∧
        ∀ c₀, (w.node i).conn? cid = some c₀ → x ∉ c₀.offered → x ∉ c₀.known →
          ∃ p ∈ (w.step _ a).flight, p.src = some i ∧ some p.dst = ((w.step _ a).node i).addr? cid ∧
            ∃ L ps, x ∈ L ∧ plainPeek p.bytes = some (cid, ps) ∧ (Msg.hold L).op.bytes ∈ ps)

/-- **"Store = offered"**: both halves. -/
def store_offered_stmt : Prop := index_store_stmt ∧ stream_stmt

/-- **Only members receive.** Every session frame an honest node sends
carries sync messages and ops of the session's rooms only, whatever the
attacker does. -/
def members_only_stmt : Prop :=
  ∀ (F : Type) (fam : Family F) cfg n addr rooms adv (w : World (Held F) n),
    PlainReach fam cfg n addr rooms adv w →
    ∀ p ∈ w.wire, ∀ i, p.src = some i → ∀ cid ps, plainPeek p.bytes = some (cid, ps) →
      ∀ b ∈ ps, ∀ o, Op.decode b = some o → isWire o.kind = true ∨ ∃ r ∈ rooms i cid, fam.room o = some r

/-- **Waiting ops close.** At every world reached, every node's store is
at rest and its verdicts are the spec's over the ops it holds. So an op
that waited on a missing requirement is judged in the very step that
brings the last of them, as if it had arrived after them. -/
def waiting_closure_stmt : Prop :=
  ∀ (F : Type) (fam : Family F) cfg n addr rooms adv (w : World (Held F) n),
    PlainReach fam cfg n addr rooms adv w → ∀ i, CollisionFree (w.box i).log →
      (w.box i).db.queue = [] ∧ ∀ x v, (w.box i).db.status x = some v ↔ Spec fam (w.box i).db.ops x v

/-- **Nodes holding a closure judge alike.** If node i judged x as v, and
node j holds every op of x's requirement closure at i, j judged x as v. -/
def closure_agree_stmt : Prop :=
  ∀ (F : Type) (fam : Family F) cfg n addr rooms adv (w : World (Held F) n),
    PlainReach fam cfg n addr rooms adv w → ∀ i j x v,
      CollisionFree (w.box i).log → CollisionFree (w.box j).log →
      (∀ y o, Engine.Sync.Reach (w.box i).db.ops x y → (w.box i).db.ops y = some o → (w.box j).db.ops y = some o) →
      (w.box i).db.status x = some v → (w.box j).db.status x = some v

/-! ## Liveness: bounded progress under explicit fairness -/

section
variable (fam : Family F) (cfg : Config) (n : Nat) (addr : Fin n → ByteArray) (rooms : Fin n → Id → List Id)

/-- What every liveness statement assumes of an execution of the plain
setup from empty stores, with no attacker: the setup's standing
assumptions, timely delivery on G's links within Δ with 2Δ shorter than
patience, ticks every τ, time passing, and health from step k₀ (every
window of r within N items). -/
structure Fair (E : Exec (plain fam cfg n addr rooms) noAdv (start fam cfg n addr rooms))
    (G : Fin n → Fin n → Prop) (r : Id) (Δ τ k₀ N : Nat) : Prop where
  ok : PlainOk fam cfg n addr
  symm : ∀ i j, G i j → G j i
  timely : Timely E G Δ
  patient : 2 * Δ < cfg.patience
  ticks : Ticks E τ
  unbounded : Unbounded E
  healthy : Healthy E G r k₀ N

end

/-- **Per-edge progress**, the lemma every liveness law rests on: across
an edge of G, in room r, an op one end holds at step k ≥ k₀ the other end
holds by `now k + B`. -/
def Edge {M : Type → Type} {S : Type} [Monad M] [Store F M] [Turn F M] {P : Setup F M S}
    {adv : World S P.n → ByteArray → Prop} {w₀ : World S P.n}
    (E : Exec P adv w₀) (G : Fin P.n → Fin P.n → Prop) (r : Id) (k₀ B : Nat) : Prop :=
  ∀ k i j x, k₀ ≤ k → G i j → Holds P (E.world k) i r x →
    ∃ k', k ≤ k' ∧ (E.world k').now ≤ (E.world k).now + B ∧ Holds P (E.world k') j r x

/-- **The per-edge statement:** every fair execution has the per-edge
bound `epoch`. -/
def edge_stmt : Prop :=
  ∀ (F : Type) (fam : Family F) cfg n addr rooms (E : Exec (plain fam cfg n addr rooms) noAdv (start fam cfg n addr rooms))
    (G : Fin n → Fin n → Prop) (r : Id) (Δ τ k₀ N : Nat),
    Fair fam cfg n addr rooms E G r Δ τ k₀ N → Edge E G r k₀ (epoch cfg Δ τ (depth cfg N))

/-- **Convergence over a connected G** ("users always eventually sync the
whole community", when they transitively know each other): an op of
room r that any node holds at step k ≥ k₀, every node holds from some
step on, within d · epoch ms, where d bounds G's diameter. -/
def converge_stmt : Prop :=
  ∀ (F : Type) (fam : Family F) cfg n addr rooms (E : Exec (plain fam cfg n addr rooms) noAdv (start fam cfg n addr rooms))
    (G : Fin n → Fin n → Prop) (r : Id) (d Δ τ k₀ N : Nat),
    Fair fam cfg n addr rooms E G r Δ τ k₀ N → Diam G d →
    ∀ k i j x, k₀ ≤ k → Holds (plain fam cfg n addr rooms) (E.world k) i r x →
      ∃ k', k ≤ k' ∧ (E.world k').now ≤ (E.world k).now + d * epoch cfg Δ τ (depth cfg N) ∧
        ∀ k'', k' ≤ k'' → Holds (plain fam cfg n addr rooms) (E.world k'') j r x

/-- **When everyone knows everyone:** within one epoch. -/
def converge_all_stmt : Prop :=
  ∀ (F : Type) (fam : Family F) cfg n addr rooms (E : Exec (plain fam cfg n addr rooms) noAdv (start fam cfg n addr rooms))
    (G : Fin n → Fin n → Prop) (r : Id) (Δ τ k₀ N : Nat),
    Fair fam cfg n addr rooms E G r Δ τ k₀ N → AllKnow G →
    ∀ k i j x, k₀ ≤ k → Holds (plain fam cfg n addr rooms) (E.world k) i r x →
      ∃ k', k ≤ k' ∧ (E.world k').now ≤ (E.world k).now + epoch cfg Δ τ (depth cfg N) ∧
        ∀ k'', k' ≤ k'' → Holds (plain fam cfg n addr rooms) (E.world k'') j r x

/-- **Two peers who know each other.** -/
def converge_two_stmt : Prop :=
  ∀ (F : Type) (fam : Family F) cfg addr rooms (E : Exec (plain fam cfg 2 addr rooms) noAdv (start fam cfg 2 addr rooms))
    (r : Id) (Δ τ k₀ N : Nat),
    Fair fam cfg 2 addr rooms E (fun i j => i ≠ j) r Δ τ k₀ N →
    ∀ k i j x, k₀ ≤ k → Holds (plain fam cfg 2 addr rooms) (E.world k) i r x →
      ∃ k', k ≤ k' ∧ (E.world k').now ≤ (E.world k).now + epoch cfg Δ τ (depth cfg N) ∧
        ∀ k'', k' ≤ k'' → Holds (plain fam cfg 2 addr rooms) (E.world k'') j r x

/-- 0 — 1 — 2: node 0 and node 2 know each other only through node 1. -/
def line3 (i j : Fin 3) : Prop := (i.val + 1 = j.val) ∨ (j.val + 1 = i.val)

/-- **Three peers who know each other transitively** (a line): within
two epochs. -/
def converge_three_stmt : Prop :=
  ∀ (F : Type) (fam : Family F) cfg addr rooms (E : Exec (plain fam cfg 3 addr rooms) noAdv (start fam cfg 3 addr rooms))
    (r : Id) (Δ τ k₀ N : Nat),
    Fair fam cfg 3 addr rooms E line3 r Δ τ k₀ N →
    ∀ k i j x, k₀ ≤ k → Holds (plain fam cfg 3 addr rooms) (E.world k) i r x →
      ∃ k', k ≤ k' ∧ (E.world k').now ≤ (E.world k).now + 2 * epoch cfg Δ τ (depth cfg N) ∧
        ∀ k'', k' ≤ k'' → Holds (plain fam cfg 3 addr rooms) (E.world k'') j r x

/-- **The reduction:** the per-edge bound and growth give convergence
over any connected G (engine/world/Epidemic.lean proves this implication). -/
def converge_of_edge_stmt : Prop := edge_stmt → grows_stmt → converge_stmt

/-! ## The pieces of the per-edge bound -/

/-- **A session stays up.** Under timely delivery on G's links with 2Δ
shorter than patience, a session joined at both ends of an edge of G at
step k₀, whose rooms agree, is never dropped while neither end restarts
and the harness opens nothing over it. (False on the code before the
patience fix: engine/world/Findings.lean.) -/
def session_stable_stmt : Prop :=
  ∀ (F : Type) (fam : Family F) cfg n addr rooms (E : Exec (plain fam cfg n addr rooms) noAdv (start fam cfg n addr rooms))
    (G : Fin n → Fin n → Prop) (Δ : Nat) (i j : Fin n) (cid : Id) (k₀ : Nat),
    PlainOk fam cfg n addr → Timely E G Δ → 2 * Δ < cfg.patience → G i j → rooms i cid = rooms j cid →
    (∀ k, k₀ ≤ k → ∀ t, E.act k ≠ .restart i t ∧ E.act k ≠ .restart j t) →
    (∀ k, k₀ ≤ k → ∀ a b c d t, E.act k = .connect a b c d t → c ≠ cid) →
    (E.world k₀).isOpen i cid → (E.world k₀).isOpen j cid →
    ((E.world k₀).node i).addr? cid = some (addr j) → ((E.world k₀).node j).addr? cid = some (addr i) →
    ∀ k, k₀ ≤ k → (E.world k).isOpen i cid ∧ (E.world k).isOpen j cid

/-- **Per-round progress.** A round of room r on a session joined from i
(dialing) to j: if its opening, a packet from i to j carrying `rbsr r k`
with i's openings of every window range, is in flight at step k, then
every op of room r i held at step k, j holds within `roundTime` of the
opening's sending; and every op of room r j held when the opening
reached it, i holds within the same time. -/
def round_progress_stmt : Prop :=
  ∀ (F : Type) (fam : Family F) cfg n addr rooms (E : Exec (plain fam cfg n addr rooms) noAdv (start fam cfg n addr rooms))
    (G : Fin n → Fin n → Prop) (r : Id) (Δ τ k₀ N : Nat) (i j : Fin n) (cid : Id) (k kr : Nat) (p : Packet n) ps,
    Fair fam cfg n addr rooms E G r Δ τ k₀ N → G i j → Joined E i j cid k₀ → k₀ ≤ k →
    p ∈ (E.world k).flight → p.src = some i → p.dst = addr j → plainPeek p.bytes = some (cid, ps) →
    (∃ X, (Msg.rbsr r kr ((window (max ((E.world k).node i).floor ((E.world k).node j).floor)).map
        (opening Prod.fst Prod.snd sha256 cfg.params X))).op.bytes ∈ ps) →
    (∀ x, Holds (plain fam cfg n addr rooms) (E.world k) i r x →
      ∃ k', k ≤ k' ∧ (E.world k').now ≤ p.sent + roundTime Δ (depth cfg N) ∧
        Holds (plain fam cfg n addr rooms) (E.world k') j r x) ∧
    (∀ k₁ idx t, k ≤ k₁ → E.act k₁ = .deliver idx t → (E.world k₁).flight[idx]? = some p →
      ∀ y, Holds (plain fam cfg n addr rooms) (E.world k₁) j r y →
        ∃ k', k₁ ≤ k' ∧ (E.world k').now ≤ p.sent + roundTime Δ (depth cfg N) ∧
          Holds (plain fam cfg n addr rooms) (E.world k') i r y)

/-- **The pilot (leaf regime, one direction):** a round's opening claim
of ids in room r, in flight from i to j at step k on a session joined
from k on, listing x, which i holds: j holds x within 3Δ of the claim's
sending. Proven in engine/world/Pilot.lean. -/
def claim_delivers_stmt : Prop :=
  ∀ (F : Type) (fam : Family F) cfg n addr rooms (E : Exec (plain fam cfg n addr rooms) noAdv (start fam cfg n addr rooms))
    (G : Fin n → Fin n → Prop) (r : Id) (Δ : Nat) (i j : Fin n) (cid : Id) (k kr : Nat) (p : Packet n)
    (ps : List ByteArray) (rg : Range) (L : List Id) (x : Id),
    PlainOk fam cfg n addr → Timely E G Δ → G i j → G j i → Joined E i j cid k →
    r ∈ rooms i cid → r ∈ rooms j cid →
    p ∈ (E.world k).flight → p.src = some i → p.dst = addr j → plainPeek p.bytes = some (cid, ps) →
    (Msg.rbsr r kr [.ids rg L]).op.bytes ∈ ps → x ∈ L →
    Holds (plain fam cfg n addr rooms) (E.world k) i r x →
      ∃ k', k ≤ k' ∧ (E.world k').now ≤ p.sent + 3 * Δ ∧ Holds (plain fam cfg n addr rooms) (E.world k') j r x

/-! ## Quiescence: the potential -/

/-- The ids of room r node i holds. -/
def held (fam : Family F) (h : Held F) (r : Id) : List Id :=
  h.db.stored.filter fun x => match h.db.ops x with
    | some o => Decidable.decide (fam.room o = some r)
    | none => false

/-- **The potential:** over every node, the ops of room r some node holds
and it lacks. Zero exactly when every node holds the same ops of r. -/
def potential (fam : Family F) {n : Nat} (w : World (Held F) n) (r : Id) : Nat :=
  let U := (List.finRange n).flatMap fun i => held fam (w.box i) r
  (List.finRange n).foldl (fun acc i => acc + (U.filter fun x => !(held fam (w.box i) r).contains x).eraseDups.length) 0

/-- **Quiescent convergence:** if nothing is written or injected from step
k₀ on, the potential never rises, and is zero within d · epoch. -/
def quiescent_stmt : Prop :=
  ∀ (F : Type) (fam : Family F) cfg n addr rooms (E : Exec (plain fam cfg n addr rooms) noAdv (start fam cfg n addr rooms))
    (G : Fin n → Fin n → Prop) (r : Id) (d Δ τ k₀ N : Nat),
    Fair fam cfg n addr rooms E G r Δ τ k₀ N → Diam G d →
    (∀ k, k₀ ≤ k → ∀ i ops t, E.act k ≠ .write i ops t) →
      (∀ k k', k₀ ≤ k → k ≤ k' → potential fam (E.world k') r ≤ potential fam (E.world k) r) ∧
      ∃ k', k₀ ≤ k' ∧ (E.world k').now ≤ (E.world k₀).now + d * epoch cfg Δ τ (depth cfg N) ∧
        potential fam (E.world k') r = 0

end Engine.World
