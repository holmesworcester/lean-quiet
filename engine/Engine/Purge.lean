/-
Purge: forgetting ops. Forward secrecy needs it. A session's
ephemeral secrets and keys are local ops, and once the session closes
nothing on disk may open its traffic (tiny's "close is a death key, and
forward secrecy is its verdict"). A shipped courier is forgotten the
same way.

`purge ids` deletes the ops named and every stored op that requires one
of them, transitively: their bytes, verdicts, filings and waits. Only
conn and local ops are ever purged; a shared op named, or reached as a
dependent, is kept, and so is everything it requires. Shared ops leave
only by removal semantics, never by purge.

Purge is an engine operation, not an op. A family's hook names what to
purge: the connection family names a closed session's ops, and the node
names a courier once it is handed out. Nothing records the purge,
because what was purged was this node's transient state. A purged
local op never returns from the wire (`intake_local`). A purged conn op
may return: a replayed request is admitted, opened and either answered
afresh (a new ephemeral, a session nobody but the dialer can use) or
left to time out.

The SQLite instance deletes with `secure_delete` on, so freed pages are
zeroed, and checkpoints the WAL after a purge.

Laws (stated):
- `purge_inv`: purging a dependent-closed set keeps the invariant. The
  remaining ops' verdicts are the spec over the remaining ops.
- `purge_gone`: no purged op is stored, or filed under any key.
- `purge_shared`: no shared op is deleted.

SKELETON: signatures are the contract; bodies are unwritten.
-/
import Engine.Proofs

namespace Engine
variable {F : Type} {fam : Family F}

/-- The ops purge deletes: `ids` and their dependents among the stored
ops, conn and local ones only. -/
def purgeSet (fam : Family F) (s : DB F) (ids : List Id) : List Id := sorry

/-- The state with those ops forgotten. -/
def purgeS (fam : Family F) (ids : List Id) (s : DB F) : DB F := sorry

theorem purge_inv {s : DB F} (h : Inv fam s) (hq : s.queue = []) (ids : List Id) :
    Inv fam (purgeS fam ids s) := sorry

theorem purge_gone (s : DB F) (ids : List Id) {x : Id} (hx : x ∈ purgeSet fam s ids) :
    (purgeS fam ids s).ops x = none ∧ ∀ k, x ∉ (purgeS fam ids s).idx k := sorry

theorem purge_shared (s : DB F) (ids : List Id) {x : Id} {o : Op} (ho : s.ops x = some o)
    (hs : (fam.room o).isSome) : (purgeS fam ids s).ops x = some o := sorry

end Engine
