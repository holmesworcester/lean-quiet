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

end Live
