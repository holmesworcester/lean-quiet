/-
Two O(N) paths and a gap, as statements (`_stmt`) of the laws their
fixes are to prove: no code yet, so nothing here is proven. They land
on a branch from fd/removal (its `react` as openAll, deliverAll,
answerAll, establishAll; its device liveness, `Live` and `Cut`), and
are restated over that code there. docs/PERF.md has the designs.

- **react, driven by the turn's new ids** (ops/connection/Intents.lean).
  Today every entry point scans every request to this node, every
  opened session and every request from it: O(sessions) lists a call,
  up to 16 calls an event. The engine cannot file a row out of a key,
  so "unanswered" cannot be one list. Instead `Hooks.react` takes the
  ids the turn stored (Node.store has them) and handles each new
  request, opened and connection once; a sweep on the clock handles at
  most k pending items a tick, for anything missed (a restart, a
  requirement that came later).
- **The people list by window** (ops/community/profile/View.lean,
  Query.lean). `present` reads every admission and, per admission, its
  user's removals: O(members) lists a re-read. Liveness depends on
  later removals, so the present members cannot be one list either.
  Instead the reader reads them by window (the first n from an
  admission position, cut entries skipped), and the header shows a
  capped count ("999+").
- **An invitation's threshold**: an admission cites its threshold's
  approvals and two more, so a threshold over `maxReqs − 2` makes one
  intake refuses; issuing and validating an invitation is to refuse it.
-/
import ops.connection.Intents
import ops.community.profile.View
import engine.core.CostStore
import engine.core.Sync
import engine.core.ListCost

namespace Plans
open Engine

/-! ## react, driven by the turn's new ids -/

section
variable {m : Type → Type} [Monad m]

/-- **Reads O(fresh + sessions named)**: react on a turn's new ids makes
at most c lists and c point reads per new id and per session those ids
name (`named`), whatever the node's sessions number. -/
def react_reads_stmt (reactNew : List Id → CostT m (List Op)) (named : List Id → Nat) (c : Nat) : Prop :=
  ∀ fresh, Within Meter.lists (c * (fresh.length + named fresh)) (reactNew fresh) ∧
    Within Meter.reads (c * (fresh.length + named fresh)) (reactNew fresh)

/-- **Sound**: what react acts on for the new ids is among what the
scanning react acts on at the same store: a request to open, an opened
session to deliver and answer, a connection to establish (`items`), so
fd/removal's per-item laws (`answer_trusted`, `bare_takes_only_join`)
carry over. Items, not ops: the ephemerals are fresh bytes either way. -/
def react_sound_stmt {σ Item : Type} (items : σ → List Item) (itemsNew : σ → List Id → List Item) : Prop :=
  ∀ s fresh, ∀ i ∈ itemsNew s fresh, i ∈ items s

/-- **Live**: with the sweep handling at most k pending items a tick, in
the order the store lists them, every pending item is handled within
⌈pending / k⌉ ticks with no new arrival. -/
def react_live_stmt {σ Item : Type} (items : σ → List Item) (sweep : Nat → σ → σ) (k : Nat) : Prop :=
  0 < k → ∀ s, ∀ i ∈ items s, ∃ t ≤ ((items s).length + k - 1) / k, i ∉ items (Nat.repeat (sweep k) t s)

/-- The mutant: the scanning react reads at least one list per opened
session, on every call. -/
def react_scans_stmt (react : CostT m (List Op)) (opened : Nat) : Prop :=
  ¬ Within Meter.lists (opened - 1) react

end

/-! ## The people list, by window -/

section
open Community

/-- **The window is a slice of the present members**: the first n from
position `after` (in admission order), on every store. -/
def present_window_stmt (presentW : Id → Nat → Option Pos → View Fact (List (Id × List Key)))
    (presentFrom : Id → Option Pos → View Fact (List (Id × List Key))) : Prop :=
  ∀ (s : DB Fact) c n after, (presentW c n after).eval s = ((presentFrom c after).eval s).take n

/-- **A window costs O(n + cut)**: at most c lists per member shown and
per cut entry passed over, never per member of the community. -/
def present_window_cost_stmt (presentW : Id → Nat → Option Pos → View Fact (List (Id × List Key)))
    (cutPassed : Id → Nat → Option Pos → Nat) (c : Nat) : Prop :=
  ∀ cm n after, View.DepthLe (c * (n + cutPassed cm n after)) (presentW cm n after)

/-- **The header's count is capped**: the present members up to `cap`
("999+" beyond), in at most c · cap lists. -/
def present_count_stmt (presentCount : Id → Nat → View Fact Nat)
    (present : Id → View Fact (List (Id × List Key))) (c : Nat) : Prop :=
  ∀ (s : DB Fact) cm cap, (presentCount cm cap).eval s = min cap ((present cm).eval s).length ∧
    View.DepthLe (c * (cap + 1)) (presentCount cm cap)

end

/-! ## An invitation's threshold -/

/-- **An invitation whose admission would exceed the cap is refused**:
every Valid invitation's threshold is at most `maxReqs − 2`, so the
admission completing it cites at most `maxReqs` and passes intake. -/
def invite_threshold_stmt (valid : Community.Fact → Prop) : Prop :=
  ∀ c issuer bearer link t, valid (.invitation c issuer bearer link t) → t + 2 ≤ maxReqs

end Plans
