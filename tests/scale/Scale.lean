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
- **room treap:** the index's room built by inserts (`RoomTree.ofList`),
  its height, and the running `Index.opening`/`Index.answer` checked
  equal to the list `opening`/`answer` on the window and on a cut claim;
  their hashes, counted by the meter (`openingTM`, `answerTM`), within
  the proven 2·height and 2·(fan + 1)·height, against the list label's
  2n + 1; and the times. The control is the old list index: an insert
  into a sorted list per item, quadratic (up to 10k only).
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

/-- A value and the least of three runs' nanoseconds. -/
def timeV {β : Type} (f : Nat → IO β) : IO (β × Nat) := do
  let mut best := 0
  let mut v ← f 0
  for i in [0:3] do
    let t0 ← IO.monoNanosNow
    v ← f (i + 1)
    let t1 ← IO.monoNanosNow
    if i == 0 || t1 - t0 < best then best := t1 - t0
  return (v, best)

def room : Id := sha256 "scale room".toUTF8

/-- Claims, compared by what they say. -/
def claimEq : Claim → Claim → Bool
  | .fp r n l, .fp r' n' l' => r == r' && n == n' && l == l'
  | .ids r xs, .ids r' ys => r == r' && xs == ys
  | _, _ => false

def outEq : Out → Out → Bool
  | .claim c, .claim c' => claimEq c c'
  | .hold xs, .hold ys => xs == ys
  | .want xs, .want ys => xs == ys
  | _, _ => false

def outsEq (a b : List Out) : Bool := a.length == b.length && (a.zip b).all fun p => outEq p.1 p.2

@[noinline] def keep {α : Type} (_ : Nat) (x : α) : α := x

def main (args : List String) : IO UInt32 := do
  let dir := args.headD "out/scale"
  let sizes : List Nat := match args.drop 1 with
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
    -- the room as the index holds it: a treap built by inserts
    let (rm, tBuild) ← timeV fun i => do
      let rm := RoomTree.ofList (keep i items)
      if rm.items.length == 0 then IO.eprintln "empty"
      return rm
    let ix : Index := { rooms := [(room, rm)] }
    let sorted := ix.items room
    t.ok s!"n={n}: the room treap holds the room's items in key order" (sorted.length == n &&
      sorted == (keep n items).mergeSort fun a b => decide (a.1 < b.1) || a.1 == b.1)
    let ht := (ix.tree room).height
    t.ok s!"n={n}: the room treap's height is the items' (height_canon)" (ht == hNew)
    rows := rows.push s!"room treap build\t{n}\tinserts\t{ht}\t{ms tBuild}"
    if n ≤ 10000 then
      let (_, tList) ← time fun _ => return ((keep n items).foldl (fun acc a => ins a acc) []).length
      IO.println s!"index n={n}: built by treap inserts in {ms tBuild} ms; as a sorted list (the control) in {ms tList} ms"
      rows := rows.push s!"room list build\t{n}\tcontrol\t\t{ms tList}"
    else
      IO.println s!"index n={n}: built by treap inserts in {ms tBuild} ms"
    -- an opening over the window (the last 15 days' worth of times)
    let w : Range := ⟨⟨n / 2 + 1000, 0⟩, none⟩
    let ((ow, owc), tOpen) ← timeV fun i => do
      let x := openingTM (m := Counted) Prod.fst Prod.snd sha256 P (keep i (ix.tree room)) w
      return (Counted.val x, Counted.cost x)
    let lw := opening Prod.fst Prod.snd sha256 P sorted w
    t.ok s!"n={n}: the running opening is the list opening (Index.opening_eq)" (claimEq ow lw && claimEq (ix.opening P room w) lw)
    t.ok s!"n={n}: an opening hashes {owc.hashes}, within 2·height = {2 * ht} (openingTM_hashes)" (owc.hashes ≤ 2 * ht)
    -- a claim the room disagrees with: cut into pieces
    let c : Claim := .fp w 1 .empty
    let ((aw, awc), tAns) ← timeV fun i => do
      let x := answerTM (m := Counted) Prod.fst Prod.snd sha256 P (keep i (ix.tree room)) c
      return (Counted.val x, Counted.cost x)
    let (la, tListAns) ← timeV fun i => do
      return answer Prod.fst Prod.snd sha256 P (keep i sorted) c
    t.ok s!"n={n}: the running answer is the list answer (Index.answer_eq)" (outsEq aw la && outsEq (ix.answer P room c) la)
    t.ok s!"n={n}: an answer hashes {awc.hashes}, within 2·(fan + 1)·height = {2 * (P.fan + 1) * ht} (answerTM_hashes)"
      (awc.hashes ≤ 2 * (P.fan + 1) * ht)
    IO.println s!"room n={n}: height {ht}; opening {owc.hashes} hashes in {ms tOpen} ms; a cut answer {awc.hashes} hashes in {ms tAns} ms, the list answer {ms tListAns} ms"
    rows := rows.push s!"treap opening\t{n}\thashes\t{owc.hashes}\t{ms tOpen}"
    rows := rows.push s!"treap answer\t{n}\thashes\t{awc.hashes}\t{ms tAns}"
    rows := rows.push s!"list answer\t{n}\tcontrol\t\t{ms tListAns}"
  IO.FS.writeFile s!"{dir}/scale.tsv" (String.intercalate "\n" rows.toList ++ "\n")
  t.finish "scale"

end Scale

def main (args : List String) : IO UInt32 := Scale.main args
