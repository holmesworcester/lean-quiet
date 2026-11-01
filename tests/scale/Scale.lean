/-
The scaling test (docs/BOUNDS.md): what a round's work costs at 1k, 10k
and 100k items in one room, on the code that runs, with each fix's
negative control. Times go to `out/scale/scale.tsv` and are reported,
not asserted.

- **depth:** the canonical treap's height, which bounds the work of a
  label (`lbl`) and, once the room index holds the treap, its hashes.
  Ids are random 32-byte hashes, one item in a hundred at claimed time
  0 (every structure op is). Under the derived priority (`Key.plt`: the
  id number's low 64 bits, then the number), the height stays within
  3·(log₂ n + 1). The negative control is the old priority, the id
  number alone, which is also the order's tie-break: it chains the
  items of one time, so the height is at least their count.
- **cold opening:** `opening` over the whole room (the dialer's first
  claim: a count and a label), timed under the derived priority and
  under the old one (`oldLbl`, the label as main computed it before).
-/
import engine.sync.Treap
import engine.sync.Conn
import tests.engine.Checks

open Engine Engine.Sync Tests

namespace Scale

def P : Params := {}

/-- Every key. -/
def everything : Range := ⟨⟨0, 0⟩, none⟩

/-- n items with random 32-byte ids, one in a hundred at time 0. -/
def itemsOf (n : Nat) : List Item := Id.run do
  let mut out : Array Item := #[]
  for i in [0:n] do
    let id := sha256 (Codec.encode (i, "scale".toUTF8))
    let t := if i % 100 == 0 then 0 else 1000 + i
    out := out.push (⟨t, num id.data.toList⟩, id)
  return out.toList

/-- The treap's height under a priority of our choosing (the old rule
compared id numbers alone). -/
partial def heightBy (prio : Item → Nat) (l : List Item) : Nat :=
  match l with
  | [] => 0
  | a :: t =>
    let m := t.foldl (fun m b => if prio m < prio b then b else m) a
    1 + max (heightBy prio (l.filter fun b => Decidable.decide (b.1 < m.1)))
      (heightBy prio (l.filter fun b => Decidable.decide (m.1 < b.1)))

/-- `top` as main ran it before the derived priority: the item of largest
id number, by the same recursion. -/
def oldTop : List Item → Option Item
  | [] => none
  | a :: t => match oldTop t with
    | none => some a
    | some b => if b.1.n < a.1.n then some a else some b

/-- `lbl` as main ran it before (the negative control's timing): the same
code as `lbl`, with `oldTop` for `top`. -/
partial def oldLbl (l : List Item) : ByteArray :=
  match oldTop l with
  | none => sha256 .empty
  | some m =>
    sha256 (Codec.encode (oldLbl (below Prod.fst l m), m.2, oldLbl (above Prod.fst l m)))

/-- Nanoseconds, the least of three runs. -/
def time (f : Unit → IO Nat) : IO (Nat × Nat) := do
  let mut best := 0
  let mut v := 0
  for i in [0:3] do
    let t0 ← IO.monoNanosNow
    v ← f ()
    let t1 ← IO.monoNanosNow
    if i == 0 || t1 - t0 < best then best := t1 - t0
  return (v, best)

def ms (ns : Nat) : String := s!"{ns / 1000000}.{ns / 100000 % 10}"

@[noinline] def keep {α : Type} (_ : Nat) (x : α) : α := x

def main (args : List String) : IO UInt32 := do
  let dir := args.headD "out/scale"
  let sizes := match args.drop 1 with
    | [] => [1000, 10000, 100000]
    | l => l.filterMap String.toNat?
  IO.FS.createDirAll dir
  let t ← Checks.new
  let mut rows : Array String := #["step\tn\tvariant\tvalue\tms"]
  for n in sizes do
    let items := itemsOf n
    let same := (items.filter (·.1.t == 0)).length
    let lg := Nat.log2 n
    let hNew := height Prod.fst items
    let hOld := heightBy (·.1.n) items
    IO.println s!"depth n={n}: height {hNew} under the derived priority; {hOld} under the old one, with {same} items at time 0; log₂ n = {lg}"
    t.ok s!"n={n}: the treap's height is within 3·(log₂ n + 1) under the derived priority" (hNew ≤ 3 * (lg + 1))
    t.ok s!"n={n}: negative control: the old priority chains the {same} items of time 0" (hOld ≥ same)
    t.ok s!"n={n}: the running priority's height is the derived priority's (heightBy)"
      (heightBy (fun a => a.1.low.toNat * 2 ^ 264 + a.1.n) items == hNew)
    rows := rows.push s!"depth\t{n}\tderived\t{hNew}\t"
    rows := rows.push s!"depth\t{n}\told\t{hOld}\t"
    let (c, tNew) ← time fun _ => do
      let cl := opening Prod.fst Prod.snd sha256 P (keep n items) everything
      return match cl with | .fp _ k _ => k | .ids _ xs => xs.length
    let (_, tOld) ← time fun _ => return (oldLbl (keep n items)).size
    IO.println s!"cold opening n={n}: {ms tNew} ms under the derived priority, {ms tOld} ms under the old one"
    t.ok s!"n={n}: the opening counts the room" (c == n)
    rows := rows.push s!"cold opening\t{n}\tderived\t{c}\t{ms tNew}"
    rows := rows.push s!"cold opening\t{n}\told\t{c}\t{ms tOld}"
  IO.FS.writeFile s!"{dir}/scale.tsv" (String.intercalate "\n" rows.toList ++ "\n")
  t.finish "scale"

end Scale

def main (args : List String) : IO UInt32 := Scale.main args
