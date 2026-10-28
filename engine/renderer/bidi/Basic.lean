/-
Paragraph bidi without explicit embeddings, isolates or paired brackets.
W1–W7, N1–N2, I1–I2, L1 and L2 are linear passes. After W5, maximal EN
and AN runs form blocks: their implicit levels are even, so L2 preserves
their internal order. Every other block is one character. Laws in Laws:
permutation and contiguous logical order of every EN/AN block, for any
input and either paragraph direction. See docs/BIDI.md for the scope.
-/
import engine.renderer.bidi.Class

namespace Text.Bidi

/-- Quiet's policy: directional controls have no directional authority. -/
def control (c : UInt32) : Bool :=
  (0x202A ≤ c && c ≤ 0x202E) || (0x2066 ≤ c && c ≤ 0x2069) ||
  c == 0x200E || c == 0x200F || c == 0x061C

def dirOf (c : UInt32) : Class :=
  if control c then .on else
  let d := classOf c
  if d == .bn then .on else d

/-- P2–P3, within the supported single paragraph. -/
def paragraph : List Class → Bool
  | [] => false
  | .l :: _ => false
  | .r :: _ | .al :: _ => true
  | _ :: t => paragraph t

def base (rtl : Bool) : Class := if rtl then .r else .l

/-- W1: NSM inherits the preceding type, or sos. -/
def w1 (prev : Class) : List (α × Class) → List (α × Class)
  | [] => []
  | (x, d) :: t =>
    let d' := if d == .nsm then prev else d
    (x, d') :: w1 d' t

/-- W2 then W3: remember AL before replacing it with R. -/
def w23 (strong : Class) : List (α × Class) → List (α × Class)
  | [] => []
  | (x, d) :: t =>
    let next := if d == .l || d == .r || d == .al then d else strong
    let d' := if d == .en && strong == .al then .an else if d == .al then .r else d
    (x, d') :: w23 next t

/-- W4 uses the *original* neighbours, never a separator it just changed. -/
def w4 (prev : Class) : List (α × Class) → List (α × Class)
  | [] => []
  | (x, d) :: t =>
    let next := (t.head?).map Prod.snd |>.getD .on
    let d' := if (d == .es || d == .cs) && prev == .en && next == .en then .en
      else if d == .cs && prev == .an && next == .an then .an else d
    (x, d') :: w4 d t

/-- One side of W5. Applying it in both directions reaches every ET in
an ET sequence adjacent to EN, without rescanning any suffix. -/
def et (prevEN : Bool) : List (α × Class) → List (α × Class)
  | [] => []
  | (x, d) :: t =>
    let d' := if d == .et && prevEN then .en else d
    (x, d') :: et (d' == .en) t

def weak (rtl : Bool) (xs : List (α × Class)) : List (α × Class) :=
  let ws := w4 (base rtl) (w23 (base rtl) (w1 (base rtl) xs))
  (et false (et false ws).reverse).reverse

structure Block (α : Type) where
  kind : Class
  chars : List α
  original : Class := .on
  deriving Inhabited, Repr, BEq

/-- Is this a resolved number type (after W1–W5, before W7)? -/
def number (d : Class) : Bool := d == .en || d == .an

/-- The single run definition used by the renderer, laws and harness.
Only equal adjacent numeric types merge; every non-number is a singleton. -/
def runs : List (α × Class) → List (Block α)
  | [] => []
  | (x, d) :: t =>
    match runs t with
    | [] => [{ kind := d, chars := [x] }]
    | b :: bs =>
      if number d && d == b.kind then { kind := d, chars := x :: b.chars } :: bs
      else { kind := d, chars := [x] } :: b :: bs

def blocks (rtl : Bool) (xs : List (α × Class)) : List (Block α) :=
  (runs (weak rtl (xs.map fun (x, d) => ((x, d), d)))).map fun b =>
    { kind := b.kind, chars := b.chars.map Prod.fst
      original := ((b.chars.head?).map Prod.snd).getD .on }

def numberRuns (kind : Class) (rtl : Bool) (xs : List (α × Class)) : List (List α) :=
  ((blocks rtl xs).filter (fun b => b.kind == kind)).map (·.chars)

/-- W6 then W7; W7 remembers only L/R, not EN or AN. -/
def w67 (strong : Class) : List Class → List Class
  | [] => []
  | d :: t =>
    let d' := if d == .es || d == .et || d == .cs then .on
      else if d == .en && strong == .l then .l else d
    let next := if d == .l || d == .r then d else strong
    d' :: w67 next t

/-- Numbers act as R in N1, regardless of the paragraph direction. -/
def strongDir (d : Class) : Option Bool :=
  if d == .l then some false
  else if d == .r || number d then some true else none

/-- First strong type at or after each position, eos after the end. -/
def following (rtl : Bool) : List Class → List Bool
  | [] => []
  | d :: t => let rest := following rtl t; (strongDir d).getD (rest.headD rtl) :: rest

/-- I1–I2, with the single embedding level 0 or 1. -/
def implicit (rtl : Bool) (d : Class) : Nat :=
  if number d then 2 else if d == .r then 1 else if rtl then 2 else 0

/-- N1–N2 followed by I1–I2. -/
def neutrals (rtl prev : Bool) : List Class → List Bool → List Nat
  | [], _ => []
  | d :: t, after =>
    let next := after.headD rtl
    let r := if prev == next then prev else rtl
    let v := match strongDir d with
      | some _ => implicit rtl d
      | none => implicit rtl (base r)
    v :: neutrals rtl ((strongDir d).getD prev) t after.tail

/-- Attach levels without indexing a linked list. -/
def attach (fallback : Nat) : List (Block α) → List Nat → List (Block α × Nat)
  | [], _ => []
  | b :: bs, vs => (b, vs.headD fallback) :: attach fallback bs vs.tail

/-- L1: reset B/S, preceding WS and end-of-line WS. The returned Bool
says whether whitespace immediately before this suffix must reset. -/
def reset (p : Nat) : List (Block α × Nat) → List (Block α × Nat) × Bool
  | [] => ([], true)
  | (b, v) :: t =>
    let (rest, trailing) := reset p t
    let yes := b.original == .b || b.original == .s || (b.original == .ws && trailing)
    ((b, if yes then p else v) :: rest, yes)

def leveled (rtl : Bool) (bs : List (Block α)) : List (Block α × Nat) :=
  let ds := w67 (base rtl) (bs.map (·.kind))
  (reset (if rtl then 1 else 0) (attach 0 bs (neutrals rtl rtl ds (following rtl ds)))).1

/-- Reverse maximal runs at or above lv. Each element is visited once. -/
def reverseRuns (lv : Nat) (run : List (α × Nat)) : List (α × Nat) → List (α × Nat)
  | [] => run
  | x :: t => if x.2 ≥ lv then reverseRuns lv (x :: run) t
    else run ++ x :: reverseRuns lv [] t

/-- L2. Only levels 0, 1 and 2 exist in this scope. Number blocks have
level 0 or 2 and retain their internal order after the two reversals. -/
def reorder (xs : List (α × Nat)) : List (α × Nat) :=
  reverseRuns 1 [] (reverseRuns 2 [] xs)

def display (rtl : Bool) (xs : List (α × Class)) : List α :=
  (reorder (leveled rtl (blocks rtl xs))).flatMap (fun b => b.1.chars)

/-- Logical levels, expanded from the same blocks that `display` uses. -/
def levels (rtl : Bool) (xs : List (α × Class)) : List Nat :=
  (leveled rtl (blocks rtl xs)).flatMap (fun (b, v) => b.chars.map (fun _ => v))

end Text.Bidi
