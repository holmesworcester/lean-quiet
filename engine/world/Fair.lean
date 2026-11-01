/-
The network we tolerate, as a record of parameters (`Net`), and what an
execution must satisfy to be one that network may produce (`Net.Admits`).
Every liveness statement names these hypotheses; nothing about
schedulers is built into the world (docs/PROOFS.md, "The network").

- **Before `gst`, anything:** loss, duplication, reordering, any delay,
  partitions, sessions dropping. The world's steps already allow all of
  it, and an attacker's injections when `adv` allows them.
- **After `gst`, partial synchrony** (assumed; the user has not yet
  approved this as the content of H-fair(K)): a packet an honest node
  sends to a neighbour in the knows-graph `G` is delivered within `Δ`,
  if the receiver is online and the link is up throughout. Online nodes
  tick at least every `τ`, and two online neighbours on a live link
  have a session within `ρ` (redial).
- **Online** (`online t i`) is explicit, per node and per time: on a
  phone it means the app is in the foreground. Nothing runs at an
  offline node, and nothing is delivered to it.
- **Links** (`link t i j`) are explicit too: a partition after `gst` is
  a link that is down for a while. A partition that heals is a link
  that comes back up.

Liveness comes with its bound: `Edge` says an op crosses one live edge
within B, and engine/world/Epidemic.lean turns any such B into
convergence over every web (d · B for diameter d). The stream's B is
`3 * Δ` (an offer, a want, the op).
-/
import engine.world.World

namespace Engine.World
open Engine Engine.Sync

variable {F : Type} {M : Type → Type} {S : Type}

/-! ## Knowledge: graphs -/

/-- j is d edges of G from i. -/
inductive Path {α : Type} (G : α → α → Prop) : Nat → α → α → Prop
  | refl (i : α) : Path G 0 i i
  | step {d : Nat} {i j k : α} : G i j → Path G d j k → Path G (d + 1) i k

/-- Every node is within d edges of every other: G is connected, with
diameter at most d ("they transitively know each other"). -/
def Diam {α : Type} (G : α → α → Prop) (d : Nat) : Prop := ∀ i j, ∃ e, e ≤ d ∧ Path G e i j

/-- Every node is within e edges of s: s's eccentricity is at most e. -/
def Ecc {α : Type} (G : α → α → Prop) (s : α) (e : Nat) : Prop := ∀ j, ∃ d, d ≤ e ∧ Path G d s j

/-- j is no closer to s than d edges. -/
def Far {α : Type} (G : α → α → Prop) (s j : α) (d : Nat) : Prop := ∀ e, Path G e s j → d ≤ e

/-- Every node knows every other. -/
def AllKnow {α : Type} (G : α → α → Prop) : Prop := ∀ i j, i ≠ j → G i j

/-- Node i knows at most D others. -/
def Degree {n : Nat} (G : Fin n → Fin n → Prop) (i : Fin n) (D : Nat) : Prop :=
  ∃ L : List (Fin n), L.length ≤ D ∧ ∀ j, G i j → j ∈ L

/-- A chain: 0 — 1 — … — n-1. -/
def chain (n : Nat) (i j : Fin n) : Prop := i.val + 1 = j.val ∨ j.val + 1 = i.val

/-- A star around node 0: every other node knows only node 0. -/
def star (n : Nat) (i j : Fin n) : Prop := i ≠ j ∧ (i.val = 0 ∨ j.val = 0)

/-! ## The network -/

/-- **The network we tolerate.** -/
structure Net (n : Nat) where
  /-- The knows-graph: who knows, and trusts, whom. -/
  G : Fin n → Fin n → Prop
  /-- Node i is online at time t (on a phone: the app is in the foreground). -/
  online : Nat → Fin n → Prop
  /-- The link between i and j is up at time t (a partition is a link down). -/
  link : Nat → Fin n → Fin n → Prop
  /-- When partial synchrony begins. -/
  gst : Nat
  /-- From `gst`, a packet across a live edge arrives within Δ ms. -/
  Δ : Nat
  /-- From `gst`, an online node ticks at least every τ ms. -/
  τ : Nat
  /-- From `gst`, two online neighbours on a live link have a session within ρ ms. -/
  ρ : Nat

section
variable {n : Nat} (N : Net n)

/-- Node i is online from t₁ to t₂. -/
def Net.Up (i : Fin n) (t₁ t₂ : Nat) : Prop := ∀ t, t₁ ≤ t → t ≤ t₂ → N.online t i

/-- The edge i — j is live from t₁ to t₂: both ends online, the link up
both ways. -/
def Net.Live (i j : Fin n) (t₁ t₂ : Nat) : Prop :=
  ∀ t, t₁ ≤ t → t ≤ t₂ → N.online t i ∧ N.online t j ∧ N.link t i j ∧ N.link t j i

/-- Every node online and every edge of G live, from t₁ to t₂. -/
def Net.Calm (t₁ t₂ : Nat) : Prop := (∀ i, N.Up i t₁ t₂) ∧ ∀ i j, N.G i j → N.Live i j t₁ t₂

end

section
variable [Monad M] [Store F M] [Turn F M]
variable {P : Setup F M S} {adv : World S P.n → ByteArray → Prop} {w₀ : World S P.n}

/-- The node an act runs at, and when: a delivery's is the node at its
packet's address; the network's own acts (dup, drop) run nowhere. -/
def World.actAt (P : Setup F M S) (w : World S P.n) : Act P.n → Option (Fin P.n × Nat)
  | .deliver k t => (w.flight[k]?).bind fun p => (P.at? p.dst).map (·, t)
  | .dup _ => none
  | .drop _ => none
  | .tick i t => some (i, t)
  | .write i _ t => some (i, t)
  | .restart i t => some (i, t)
  | .close i _ t => some (i, t)
  | .connect i _ _ _ t => some (i, t)
  | .inject i _ _ t => some (i, t)

/-- Packet p, in flight at step k, is delivered at a step k' ≥ k, at a
time no later than T. -/
def DeliveredBy (E : Exec P adv w₀) (p : Packet P.n) (k T : Nat) : Prop :=
  ∃ k' idx t, k ≤ k' ∧ E.act k' = .deliver idx t ∧ (E.world k').flight[idx]? = some p ∧ t ≤ T

/-- Session cid joins i (which dials) and j at world w: open at both
ends, each end's frames going to the other. -/
def JoinedAt (P : Setup F M S) (w : World S P.n) (i j : Fin P.n) (cid : Id) : Prop :=
  (∃ c, (w.node i).conn? cid = some c ∧ c.dialer = true) ∧
  (∃ c, (w.node j).conn? cid = some c ∧ c.dialer = false) ∧
  (w.node i).addr? cid = some (P.addr j) ∧ (w.node j).addr? cid = some (P.addr i)

/-- Session cid joins i and j at every step from k₀ on. -/
def Joined (E : Exec P adv w₀) (i j : Fin P.n) (cid : Id) (k₀ : Nat) : Prop :=
  ∀ k, k₀ ≤ k → JoinedAt P (E.world k) i j cid

/-- Some session joins i and j, either dialing. -/
def Linked (P : Setup F M S) (w : World S P.n) (i j : Fin P.n) : Prop :=
  ∃ cid, JoinedAt P w i j cid ∨ JoinedAt P w j i cid

/-- **What an execution of the network must satisfy.** -/
structure Net.Admits (N : Net P.n) (E : Exec P adv w₀) : Prop where
  /-- Nothing runs at an offline node, and nothing is delivered to one. -/
  offline : ∀ k i t, (E.world k).actAt P (E.act k) = some (i, t) → N.online t i
  /-- From gst, timely delivery across live edges of G. -/
  timely : ∀ k p i j, p ∈ (E.world k).flight → p.src = some i → P.at? p.dst = some j → N.G i j →
    N.gst ≤ p.sent → N.Live i j p.sent (p.sent + N.Δ) → DeliveredBy E p k (p.sent + N.Δ)
  /-- From gst, an online node ticks at least every τ. -/
  ticks : ∀ i k, N.gst ≤ (E.world k).now → N.Up i (E.world k).now ((E.world k).now + N.τ) →
    ∃ k' t, k ≤ k' ∧ E.act k' = .tick i t ∧ t ≤ (E.world k).now + N.τ
  /-- From gst, a live edge has a session within ρ. -/
  redial : ∀ i j k, N.G i j → N.gst ≤ (E.world k).now →
    N.Live i j (E.world k).now ((E.world k).now + N.ρ) →
    ∃ k', k ≤ k' ∧ (E.world k').now ≤ (E.world k).now + N.ρ ∧ Linked P (E.world k') i j
  /-- Time passes. -/
  unbounded : ∀ T, ∃ k, T ≤ (E.world k).now

/-! ## Rooms on sessions -/

/-- The rooms node i's hooks sync on session cid, read at world w. -/
def Shows (P : Setup F M S) (w : World S P.n) (i : Fin P.n) (cid : Id) : List Id :=
  Room.syncs (P.run ((P.sync i).hooks.rooms cid) (w.box i)).1

/-- From step k₀ on, every session joining two neighbours in G shows r at
both ends; their other rooms may differ. (fd/proofs asked the rooms to
agree, finding 2; main's `room_independent` and `unshown_room_answered`
made r at both ends enough.) -/
def Carries (E : Exec P adv w₀) (G : Fin P.n → Fin P.n → Prop) (r : Id) (k₀ : Nat) : Prop :=
  ∀ k i j cid, k₀ ≤ k → G i j → JoinedAt P (E.world k) i j cid →
    r ∈ Shows P (E.world k) i cid ∧ r ∈ Shows P (E.world k) j cid

/-- Every window of room r holds at most W items. -/
def Bounded (E : Exec P adv w₀) (r : Id) (W : Nat) : Prop :=
  ∀ k i, (((E.world k).node i).ix.items r).length ≤ W

/-! ## Per-edge progress: the boundary

Everything above it (webs, chains, stars, offline catch-up) is proven
once in engine/world/Epidemic.lean for any execution and any bound B;
everything below it is node code and the network. The plain World
discharges it from the running node's hop laws; the Connection hooks'
sessions (holmes-71) discharge `Net.Admits.redial` and `Carries`. -/

/-- **Per-edge progress** in room r: across an edge of G live for B ms
from gst on, an op one end holds, the other end holds within B. -/
def Edge (E : Exec P adv w₀) (N : Net P.n) (r : Id) (k₀ B : Nat) : Prop :=
  ∀ k i j x, k₀ ≤ k → N.gst ≤ (E.world k).now → N.G i j → N.Live i j (E.world k).now ((E.world k).now + B) →
    Holds P (E.world k) i r x → ∃ k', k ≤ k' ∧ (E.world k').now ≤ (E.world k).now + B ∧ Holds P (E.world k') j r x

/-- **Stores keep room r's ops**: what node i holds at a step it holds at
the next, at every step of the execution. -/
def Grows (E : Exec P adv w₀) (r : Id) : Prop :=
  ∀ k i x, Holds P (E.world k) i r x → Holds P (E.world (k + 1)) i r x

/-! ## A link with a bandwidth (for `fresh_stmt`) -/

/-- Bytes in flight on p's link (the same sender and address) put in
flight before p: what a FIFO link such as TCP carries first. -/
def ahead {n : Nat} (w : World S n) (p : Packet n) : Nat :=
  ((w.flight.takeWhile fun q => q.serial ≠ p.serial).filter fun q =>
    Decidable.decide (q.src = p.src) && Decidable.decide (q.dst = p.dst)).foldl (· + ·.bytes.size) 0

/-- **A FIFO link with a bandwidth**, a refinement of `timely`: a packet
across a live edge arrives within Δ plus the time the bytes queued ahead
of it take at `bw` bytes per ms, counted when it was put in flight. -/
def Fifo (E : Exec P adv w₀) (N : Net P.n) (bw : Nat) : Prop :=
  ∀ k p i j, p ∉ (E.world k).flight → p ∈ (E.world (k + 1)).flight → p.src = some i →
    P.at? p.dst = some j → N.G i j → N.gst ≤ p.sent →
    N.Live i j p.sent (p.sent + N.Δ + ahead (E.world (k + 1)) p / bw) →
    DeliveredBy E p (k + 1) (p.sent + N.Δ + ahead (E.world (k + 1)) p / bw)

/-- Bytes of urgent packets in flight on p's link, put in flight before p:
what the urgent lane carries ahead of it. -/
def aheadU {n : Nat} (w : World S n) (urgent : Packet n → Bool) (p : Packet n) : Nat :=
  ((w.flight.takeWhile fun q => q.serial ≠ p.serial).filter fun q =>
    urgent q && Decidable.decide (q.src = p.src) && Decidable.decide (q.dst = p.dst)).foldl (· + ·.bytes.size) 0

/-- **A link with lanes** (fd/fresh-lane's per-socket `Lanes`, written by
a writer task per socket): an urgent packet across a live edge arrives
within Δ plus the time, at `bw` bytes per ms, of what goes on the wire
ahead of it, which is the kernel's buffer `sndbuf`, the one native write
under way (`batch`: every urgent frame queued when it began, then a burst
or one frame of the serve lane), and the urgent packets on its link put
in flight before it; and the receiver takes it within `qr` (its inbound
queue, a constant). The serve lane's backlog is not ahead of it. -/
def LaneLink (E : Exec P adv w₀) (N : Net P.n) (urgent : Packet P.n → Bool) (bw sndbuf batch qr : Nat) : Prop :=
  ∀ k p i j, p ∉ (E.world k).flight → p ∈ (E.world (k + 1)).flight → p.src = some i →
    P.at? p.dst = some j → N.G i j → N.gst ≤ p.sent → urgent p = true →
    N.Live i j p.sent (p.sent + N.Δ + (sndbuf + batch + aheadU (E.world (k + 1)) urgent p) / bw + qr) →
    DeliveredBy E p (k + 1) (p.sent + N.Δ + (sndbuf + batch + aheadU (E.world (k + 1)) urgent p) / bw + qr)

/-- At most U urgent bytes are ever ahead of a packet on its link: a
node's own writes and its short wire ops in a window, bounded. -/
def UrgentLoad (E : Exec P adv w₀) (urgent : Packet P.n → Bool) (U : Nat) : Prop :=
  ∀ k p, p ∈ (E.world k).flight → aheadU (E.world k) urgent p ≤ U

end

/-! ## The bounds

A round's time, and the gap between rounds on an edge, are restated on
the event-driven live rounds (fd/live-rounds): a round opens when a
session starts showing a room, and a safety round every period. -/

/-- **One edge's time by the stream:** an offer, a want and the op. -/
def hop {n : Nat} (N : Net n) : Nat := 3 * N.Δ

end Engine.World
