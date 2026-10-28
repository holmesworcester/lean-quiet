/-
The board: what the app's reader has read for the frame, each value with
a version (docs/PERF.md, the app's frame).

A reader on a thread of its own evaluates the views the frame wants, on
its own connection, and `put`s each value here. A value equal to the one
held keeps its version and changes nothing; a different one takes the
next version of the board's one counter and is marked moved. The frame
`take`s the moved set, in one swap, and works only on those values: the
signal that a value changed comes from the refill that changed it, when
it lands, and not from the commit that caused it, which a frame may take
a frame or more before the refill lands.

engine/renderer/BoardLaws.lean proves what the frame may rely on: a
version is one value (`ver_ident`), no change is lost between two takes
(`seen_put`, `seen_take`), and the screen settles to the store's values
(`settle`), with the notice-gated frame as its mutant
(`gated_stale`).
-/
import Std.Data.HashMap
import Std.Data.HashSet
import engine.core.Cost

namespace Live

/-- A value's version: one counter for the whole board. -/
abbrev Ver := Nat

structure Board (W V : Type) [BEq W] [Hashable W] where
  /-- Each value held, with its version. -/
  vals : Std.HashMap W (V × Ver) := {}
  /-- Wants whose version moved since the frame last took them. -/
  moved : Std.HashSet W := {}
  /-- The next version: above every version held or ever given. -/
  next : Ver := 1

namespace Board
variable {W V : Type} [BEq W] [Hashable W]

instance : Inhabited (Board W V) := ⟨{}⟩

/-- v as w's new value, at the next version, moved. -/
def bump (b : Board W V) (w : W) (v : V) : Board W V :=
  { b with vals := b.vals.insert w (v, b.next), moved := b.moved.insert w, next := b.next + 1 }

/-- **A refill**: an equal value changes nothing; a different or new one
takes the next version and is moved. -/
def put [BEq V] (b : Board W V) (w : W) (v : V) : Board W V :=
  match b.vals[w]? with
  | some (u, _) => if u == v then b else b.bump w v
  | none => b.bump w v

/-- **The frame's take**: the moved set, and the board without it. -/
def take (b : Board W V) : Std.HashSet W × Board W V := (b.moved, { b with moved := {} })

/-- Forget the values nobody wants any more. -/
def keep (b : Board W V) (want : W → Bool) : Board W V :=
  { b with vals := b.vals.filter fun w _ => want w }

/-- w's value and version, if held. -/
def get? (b : Board W V) (w : W) : Option (V × Ver) := b.vals[w]?

end Board

/-! ## A pass's decisions (engine/renderer/ReaderLaws.lean) -/

/-- A want's reads changed: none held, none recorded (read every pass),
or one of them stale. -/
def staleW {W Q : Type} (staleQ : Q → Bool) (deps : W → Option (List Q)) (x : W) : Bool :=
  match deps x with
  | none => true
  | some qs => qs.isEmpty || qs.any staleQ

section
variable {W : Type} [BEq W] [Hashable W] {m : Type → Type} [Monad m] [Engine.Tick m]

/-- **Mark, then read**: every want whose reads changed is marked, before
any is read again; a hash insert per want marked, a step per want. -/
def markM (stale : W → Bool) : Std.HashSet W → List W → m (Std.HashSet W)
  | d, [] => pure d
  | d, w :: ws => do
    Engine.tick { work := 1 }
    markM stale (if stale w then d.insert w else d) ws

/-- What a pass reads: the first `cap` marked wants, in the frame's
order; a hash lookup per want looked at, a step each. -/
def pickM (dirty : Std.HashSet W) : Nat → List W → m (List W)
  | 0, _ => pure []
  | _, [] => pure []
  | k + 1, w :: ws => do
    Engine.tick { work := 1 }
    if dirty.contains w then return w :: (← pickM dirty k ws) else pickM dirty (k + 1) ws

/-- **A mark at rest**: the dirty set, and the wants this pass's notices
hit, found through the reverse index (each read's wants, by its key): a
step per key noticed and per want it names, nothing per want held. -/
def markHitM {K : Type} (rev : K → List W) : Std.HashSet W → List K → m (Std.HashSet W)
  | d, [] => pure d
  | d, k :: ks => do
    Engine.tick { work := 1 + (rev k).length }
    markHitM rev ((rev k).foldl (·.insert ·) d) ks

end

/-- The frame's wants' generation: it moves only when the wants change,
so a reader at rest stays at rest (`nextGen_same`). -/
def nextGen {W : Type} [BEq W] (old new : Array W) (gen : Nat) : Nat :=
  if old != new then gen + 1 else gen

/-- Whether a pass must open the store at all: a commit since the last
pass (the writers' counter moved), a note, the wants moved, a want
dirty, or `late` (the clock's fallback: a second since the store was
last opened, for commits no counter sees). At rest none, and the pass
reads nothing, not even the journal. -/
def mustRead {W : Type} [BEq W] [Hashable W] (commits seen : Nat) (notes moved : Bool)
    (dirty : Std.HashSet W) (late : Bool) : Bool :=
  commits != seen || notes || moved || !dirty.isEmpty || late

/-- Whether a pass has nothing to do: no notice, no dirty want. -/
def idle {W K : Type} [BEq W] [Hashable W] (ks : List K) (dirty : Std.HashSet W) : Bool :=
  ks.isEmpty && dirty.isEmpty

def markHit {W K : Type} [BEq W] [Hashable W] (rev : K → List W) (dirty : Std.HashSet W) (ks : List K) :
    Std.HashSet W :=
  Id.run (markHitM rev dirty ks)

/-- What runs: the same code, at `Id`. -/
def mark {W : Type} [BEq W] [Hashable W] (wants : List W) (stale : W → Bool) (dirty : Std.HashSet W) :
    Std.HashSet W :=
  Id.run (markM stale dirty wants)

def pick {W : Type} [BEq W] [Hashable W] (wants : List W) (dirty : Std.HashSet W) (cap : Nat) : List W :=
  Id.run (pickM dirty cap wants)

end Live
