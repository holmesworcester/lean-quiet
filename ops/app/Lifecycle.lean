/-
Lifecycle policy used by the app, not a second app model.

Durable: local checkpoint ops in `app_ops` in the same SQLite database as
community ops. They hold the acceptance, page/back stack, per-acceptance
composer drafts (including photo bytes), field, invite/name, removal flow,
and scroll anchor (message id and distance from the viewport bottom to
the message top). Each changed checkpoint is committed before the event turn returns. Joining,
admissions and removals themselves remain the engine's existing ops.

Ephemeral: mounted queries, generation leases, keyboard composition and
height, camera/decoder frames, paint tasks, sheets, toasts and velocity.
Unmount revokes leases, drops subscriptions and retires unfinished tasks. A new mount
gets a new generation, so even a return to the same page rejects old work.

An anchor keeps its distance from the viewport's bottom, not an absolute
screen coordinate (that coordinate may cease to exist after rotation).
At offset zero the newest message stays pinned. If an anchor is no longer
readable, the app falls back to the newest message.

`unmounted_quiet` and `old_quiet` prove the running effect gate issues no
read, paint or write for a revoked lease. `subscriptions_exact` describes
the query projection used to prune the live cache. `resize_anchor` proves
the offset correction. `restore_checkpoint` proves the journal codec's
round trip; SQLite's atomic commit remains in the tested native seam.
-/
import engine.renderer.LiveLaws
import Std.Data.HashMap.Lemmas

namespace Lifecycle
open Engine Data

attribute [local instance] LiveLaws.byteArray_lawful LiveLaws.listQ_lawful LiveLaws.q_lawful

structure Lease where
  generation : Nat
  deriving BEq, Repr, Inhabited

structure Mount where
  generation : Nat := 0
  mounted : Bool := true
  /-- Component ids: root = empty bytes; rows use their message ids. -/
  tree : List (Id × List Q) := []
  deriving Inhabited

def Mount.lease (m : Mount) : Lease := ⟨m.generation⟩
def Mount.allows (m : Mount) (l : Lease) : Bool :=
  m.mounted && decide (l.generation = m.generation)
def Mount.unmount (m : Mount) : Mount := ⟨m.generation + 1, false, []⟩
def Mount.mount (m : Mount) : Mount := { m with mounted := true }

def Mount.track (m : Mount) (owner : Id) (q : Q) : Mount :=
  let old := ((m.tree.find? (·.1 == owner)).map (·.2)).getD []
  { m with tree := (owner, if old.contains q then old else q :: old) :: m.tree.filter (·.1 != owner) }

def Mount.forget (m : Mount) (owner : Id) : Mount :=
  { m with tree := m.tree.filter (·.1 != owner) }

def Mount.queries (m : Mount) : List Q := m.tree.flatMap (·.2)
def Mount.subscriptions (m : Mount) : List ByteArray := m.queries.map fun q => (q.win default).key

/-- All page effects pass this gate, including queued event callbacks. -/
def owned {m : Type → Type} [Monad m] {α : Type} (s : Mount) (l : Lease) (action : m α) : m (Option α) :=
  if s.allows l then some <$> action else pure none

theorem unmounted_quiet {m : Type → Type} [Monad m] {α : Type}
    (s : Mount) (l : Lease) (action : m α) : owned s.unmount l action = pure none := by
  simp [owned, Mount.allows, Mount.unmount]

theorem old_quiet {m : Type → Type} [Monad m] {α : Type}
    (s : Mount) (action : m α) : owned s.unmount.mount s.lease action = pure none := by
  simp [owned, Mount.allows, Mount.unmount, Mount.mount, Mount.lease]

theorem subscriptions_exact (s : Mount) (k : ByteArray) :
    k ∈ s.subscriptions ↔ ∃ node ∈ s.tree, ∃ q ∈ node.2, (q.win default).key = k := by
  simp only [Mount.subscriptions, Mount.queries, List.mem_map, List.mem_flatMap]
  constructor
  · rintro ⟨q, ⟨node, hn, hq⟩, hk⟩
    exact ⟨node, hn, q, hq, hk⟩
  · rintro ⟨node, hn, q, hq, hk⟩
    exact ⟨q, ⟨node, hn, hq⟩, hk⟩

/-- The actual live-cache pruning called at the end of an app turn. -/
def prune (l : Live) (s : Mount) : Live := l.keep fun q => s.queries.contains q

/-- Every mounted query has an answer after a successful read turn.
Pruning then leaves exactly those queries in the live cache. -/
theorem live_exact (l : Live) (s : Mount)
    (complete : ∀ q ∈ s.queries, l.entries[q]?.isSome = true) (q : Q) :
    (prune l s).entries[q]?.isSome = true ↔ q ∈ s.queries := by
  simp only [prune, Live.keep, Std.HashMap.getElem?_filter']
  cases h : l.entries[q]? with
  | none =>
    simp only [Option.filter_none, Option.isSome_none, Bool.false_eq_true, false_iff]
    intro hq
    have := complete q hq
    simp [h] at this
  | some e => simp

/-- Keep the message's top edge the same distance above the viewport
bottom. At the content boundary the platform clamps the offset to zero. -/
def offset (top above : Nat) : Nat := top - above

theorem resize_anchor (top above : Nat) (fits : above ≤ top) :
    (top : Int) - offset top above = above := by
  unfold offset; omega

/-- The serialized checkpoint: version, page, acceptance, anchor id and
top-edge distance; the rest is an extensible list of canonical byte fields. -/
abbrev Checkpoint := Nat × Nat × Id × Id × Nat × List ByteArray

def restore (bytes : ByteArray) : Option Checkpoint := Codec.decode bytes

theorem restore_checkpoint (s : Checkpoint) : restore (Codec.encode s) = some s :=
  Codec.decode_encode s

/-- The gate admits real mounted work; the denial laws are not vacuous. -/
theorem mounted_runs (n : Nat) :
    owned (m := Id) ({ generation := n } : Mount) ⟨n⟩ (pure 7) = some 7 := by
  simp [owned, Mount.allows]
  rfl

/-- A local journal of app ops, isolated from the sync family's index.
The sequence is the local ordering; op bytes are content-addressed. -/
def init (db : Db) : IO Unit :=
  db.exec "CREATE TABLE IF NOT EXISTS app_ops (seq INTEGER PRIMARY KEY AUTOINCREMENT, id BLOB NOT NULL, bytes BLOB NOT NULL);"

/-- Commit an encoded checkpoint. Only the writer's thread runs it
(`Data.Writer.start`): the frame hands checkpoints over (`Writer.save`). -/
def save (db : Db) (cp : ByteArray) : IO Unit := do
  let o := Op.make 239 [] cp
  let _ ← db.query "INSERT INTO app_ops(id,bytes) VALUES (?,?)" #[o.id, o.bytes]

def load (db : Db) : IO (Option Checkpoint) := do
  let rows ← db.query "SELECT bytes FROM app_ops ORDER BY seq DESC LIMIT 1" #[]
  return do
    let row ← rows[0]?
    let bytes ← row[0]?
    let o ← Op.decode bytes
    if o.kind != 239 then none else restore o.body

end Lifecycle
