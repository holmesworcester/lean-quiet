/-
What liveness assumes of an execution, each stated as a hypothesis the
theorems name (docs/PROOFS.md, "Fairness"):

- **Knowledge.** A knows-graph G over the nodes: who knows (and trusts)
  whom. `Path G d i j`: j is d edges from i. `Diam G d`: every node is
  within d edges of every other ("they transitively know each other").
  `AllKnow G`: every node knows every other.
- **Timely delivery** (`Timely E G Δ`): every packet an honest node puts
  in flight across an edge of G is delivered within Δ ms of being sent.
  So no such packet is dropped, and a link is reliable while it lasts.
  Packets that are not on G's edges (duplicates, the attacker's) are
  delivered or not, in any order.
- **Ticks** (`Ticks E τ`): every node's clock ticks at least every τ ms.
- **Time passes** (`Unbounded E`).
- **Health** (`Healthy`): what the first theorems assume and later ones
  prove. Every edge of G has a session joined at both ends, whose rooms
  agree and include r, with one end dialing; and every node's window of
  room r holds at most N items, which bounds a round's depth. Session
  stability (`session_stable_stmt`) and handshake liveness discharge the
  first; the second is a bound the statements carry.

From these, `epoch` is the time an op takes to cross one edge, so
liveness comes with its bound: within `d * epoch` ms of any node holding
an op, every node within d edges holds it.
-/
import engine.world.World

namespace Engine.World
open Engine Engine.Sync

variable {F : Type} {M : Type → Type} {S : Type}

/-! ## Knowledge -/

/-- j is d edges of G from i. -/
inductive Path {α : Type} (G : α → α → Prop) : Nat → α → α → Prop
  | refl (i : α) : Path G 0 i i
  | step {d : Nat} {i j k : α} : G i j → Path G d j k → Path G (d + 1) i k

/-- Every node is within d edges of every other: G is connected, with
diameter at most d. -/
def Diam {α : Type} (G : α → α → Prop) (d : Nat) : Prop := ∀ i j, ∃ e, e ≤ d ∧ Path G e i j

/-- Every node knows every other. -/
def AllKnow {α : Type} (G : α → α → Prop) : Prop := ∀ i j, i ≠ j → G i j

/-! ## The network and the clocks -/

section
variable [Monad M] [Store F M] [Turn F M]
variable {P : Setup F M S} {adv : World S P.n → ByteArray → Prop} {w₀ : World S P.n}

/-- A packet an honest node sent to the node at the other end of an edge
of G: the links fairness covers. -/
def Link (P : Setup F M S) (G : Fin P.n → Fin P.n → Prop) (p : Packet P.n) : Prop :=
  ∃ i j, p.src = some i ∧ P.at? p.dst = some j ∧ G i j

/-- Packet p, in flight at step k, is delivered at a step k' ≥ k, at a
time no later than T. -/
def DeliveredBy (E : Exec P adv w₀) (p : Packet P.n) (k T : Nat) : Prop :=
  ∃ k' idx t, k ≤ k' ∧ E.act k' = .deliver idx t ∧ (E.world k').flight[idx]? = some p ∧ t ≤ T

/-- **Timely delivery on G's links.** -/
def Timely (E : Exec P adv w₀) (G : Fin P.n → Fin P.n → Prop) (Δ : Nat) : Prop :=
  ∀ k p, p ∈ (E.world k).flight → Link P G p → DeliveredBy E p k (p.sent + Δ)

/-- **Every clock ticks** at least every τ ms. -/
def Ticks (E : Exec P adv w₀) (τ : Nat) : Prop :=
  ∀ i k, ∃ k' t, k ≤ k' ∧ E.act k' = .tick i t ∧ t ≤ (E.world k).now + τ

/-- **Time passes.** -/
def Unbounded (E : Exec P adv w₀) : Prop := ∀ T, ∃ k, T ≤ (E.world k).now

/-! ## Health: what later theorems discharge -/

/-- Session cid joins i (which dials) and j from step k₀ on: open at
both ends, each end's frames going to the other. -/
def Joined (E : Exec P adv w₀) (i j : Fin P.n) (cid : Id) (k₀ : Nat) : Prop :=
  ∀ k, k₀ ≤ k →
    (∃ c, ((E.world k).node i).conn? cid = some c ∧ c.dialer = true) ∧
    (∃ c, ((E.world k).node j).conn? cid = some c ∧ c.dialer = false) ∧
    ((E.world k).node i).addr? cid = some (P.addr j) ∧ ((E.world k).node j).addr? cid = some (P.addr i)

/-- The rooms node i's hooks show on session cid, read at world w. -/
def Shows (P : Setup F M S) (w : World S P.n) (i : Fin P.n) (cid : Id) : List Id :=
  (P.run ((P.sync i).hooks.rooms cid) (w.box i)).1

/-- Every window of room r holds at most N items. -/
def Bounded (E : Exec P adv w₀) (r : Id) (N : Nat) : Prop :=
  ∀ k i, (((E.world k).node i).ix.items r).length ≤ N

/-- **Health**, from step k₀ on: every edge of G has a session joined at
both ends whose rooms agree at its two ends and include r; and every
window of r holds at most N items. -/
structure Healthy (E : Exec P adv w₀) (G : Fin P.n → Fin P.n → Prop) (r : Id) (k₀ N : Nat) : Prop where
  joined : ∀ i j, G i j → ∃ cid, Joined E i j cid k₀ ∨ Joined E j i cid k₀
  agree : ∀ i j cid k, G i j → k₀ ≤ k → Shows P (E.world k) i cid = Shows P (E.world k) j cid
  shown : ∀ i j cid k, G i j → k₀ ≤ k → (E.world k).isOpen i cid → r ∈ Shows P (E.world k) i cid
  bounded : Bounded E r N

end

/-! ## The bound -/

/-- Claim hops in a round when every window holds at most N items: one in
the leaf regime (the opening lists ids, `opening`), else at most
`exchange_ends`'s 2N + 1. (Performance laws tighten the second to
2⌈log_fan N⌉ + 2.) -/
def depth (cfg : Config) (N : Nat) : Nat := if N ≤ cfg.params.leaf then 1 else 2 * N + 1

/-- A round's time once opened, with every hop within Δ: D claim hops,
then an offer, a want and the op. -/
def roundTime (Δ D : Nat) : Nat := (D + 3) * Δ

/-- The longest a dialer waits between opening rounds: its cadence, the
current round's end (D hops and the answer), and a tick. -/
def gap (cfg : Config) (Δ τ D : Nat) : Nat := cfg.every + (D + 1) * Δ + τ

/-- **One edge's time:** an op held at one end at time t is held at the
other by t + epoch. The next round opens within `gap` (its snapshots
are taken after t), and carries the op within `roundTime`. -/
def epoch (cfg : Config) (Δ τ D : Nat) : Nat := gap cfg Δ τ D + roundTime Δ D

end Engine.World
