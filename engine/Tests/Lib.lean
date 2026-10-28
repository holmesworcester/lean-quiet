/-
Test helpers: checks that count failures, a seeded generator, and
running a list of ops on the model.
-/
import Community

namespace Tests
open Engine Community

def hex (b : ByteArray) : String :=
  String.join (b.toList.take 4 |>.map fun x =>
    let s := (Nat.toDigits 16 x.toNat).asString; if s.length < 2 then "0" ++ s else s)

structure Checks where
  failed : IO.Ref Nat
  passed : IO.Ref Nat

def Checks.new : IO Checks := do return ⟨← IO.mkRef 0, ← IO.mkRef 0⟩

def Checks.ok (c : Checks) (name : String) (b : Bool) : IO Unit := do
  if b then c.passed.modify (· + 1)
  else
    c.failed.modify (· + 1)
    IO.eprintln s!"FAIL: {name}"

def Checks.finish (c : Checks) (suite : String) : IO UInt32 := do
  let f ← c.failed.get
  let p ← c.passed.get
  IO.println s!"{suite}: {p} passed, {f} failed"
  return if f == 0 then 0 else 1

/-- A splitmix-style generator. -/
structure Rng where
  s : UInt64

def Rng.next (g : Rng) : UInt64 × Rng :=
  let s := g.s + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), ⟨s⟩)

def Rng.below (g : Rng) (n : Nat) : Nat × Rng :=
  let (x, g) := g.next
  (if n == 0 then 0 else x.toNat % n, g)

def Rng.shuffle {α} (g : Rng) (l : List α) : List α × Rng := Id.run do
  let mut a := l.toArray
  let mut g := g
  for i in [0:a.size] do
    let (j, g') := g.below (a.size - i)
    g := g'
    a := a.swapIfInBounds i (i + j)
  return (a.toList, g)

/-- The model after ingesting ops in order and judging until the queue
is empty. -/
def modelRun (fam : Family Fact) (ops : List Op) : DB Fact :=
  let s := ops.foldl (fun s o => ingestS o s) DB.empty
  drainS fam (10 * ops.length + 10) s

/-- An op's spec verdict among ops, computed at a depth past any
derivation (each level of a derivation is a distinct op). -/
def specOf (fam : Family Fact) (ops : Id → Option Op) (n : Nat) (x : Id) : Option (Verdict Fact) :=
  specAt fam ops (n + 1) x

def verdictStr : Option (Verdict Fact) → String
  | none => "unresolved"
  | some .invalid => "invalid"
  | some (.valid _) => "valid"

/-- A workload: a community, then random ops. Most cite plausible
earlier ops (an admission, an invitation, an admin proof) and are signed
by the device the cited admission names, so long valid chains form;
the rest cite random or never-arriving ids, or carry the wrong
signature or none. -/
def workload (seed : Nat) (n : Nat) : List Op := Id.run do
  let devs := (List.range 8).map fun i => Device.named s!"dev-{seed}-{i}"
  let r := root devs[0]!
  let c := r.id
  let mut ops : Array Op := #[r]
  let mut ids : Array Id := #[c]
  let mut adms : Array (Id × Device) := #[(c, devs[0]!)]
  let mut invs : Array (Id × Device) := #[]
  let mut reqs : Array (Id × Device) := #[]
  let mut apps : Array (Id × Id) := #[]
  let mut admins : Array Id := #[c]
  let mut g := Rng.mk seed.toUInt64
  for i in [0:n] do
    let (kind, g1) := g.below 10
    let (w1, g2) := g1.below 8
    let (w2, g3) := g2.below 8
    let (k1, g4) := g3.below 1000
    let (k2, g5) := g4.below 1000
    let (k3, g6) := g5.below 1000
    let (di, g7) := g6.below devs.length
    let (flag, g8) := g7.below 2
    g := g8
    let missing := sha256 s!"missing-{seed}-{i}".toUTF8
    let anyId (k : Nat) := if k % 9 == 0 then missing else ids[k % ids.size]!
    let adm (k : Nat) : Id × Device :=
      if w1 == 0 then (anyId k, devs[di]!) else adms[k % adms.size]!
    let d := devs[di]!
    let signer (dv : Device) := if w2 == 0 then d else dv
    let o : Op := match kind with
      | 0 =>
        let (a, dv) := adm k1
        -- Link invitations need one approval; member ones 0, 1 or 2
        -- (sometimes a link asks for another number, and is refused).
        let t := if flag == 1 && w2 != 1 then 1 else k2 % 3
        invite c a (signer dv) (Device.named s!"bearer-{seed}-{i}").pk (flag == 1) t
      | 1 =>
        if invs.isEmpty then post c (adm k1).1 d "k".toUTF8 "early".toUTF8 else
        let (inv, bearer) := invs[k1 % invs.size]!
        request c inv d (if w2 == 0 then d.sk else bearer.sk)
      | 8 =>
        let rq := if reqs.isEmpty || w1 == 1 then anyId k1 else reqs[k1 % reqs.size]!.1
        let (a, dv) := adm k2
        approve c rq a (signer dv)
      | 9 =>
        if reqs.isEmpty then post c (adm k1).1 d "k".toUTF8 "early".toUTF8 else
        let rq := reqs[k1 % reqs.size]!.1
        let mine := (apps.filter (·.1 == rq)).toList.map (·.2)
        -- Mostly the approvals held, cut to 0..2 of them; sometimes a
        -- random id among them.
        let aps := if w1 == 1 then [anyId k3] ++ mine.take 1 else mine.take (k2 % 3)
        admit c rq aps
      | 2 =>
        let (a, dv) := adm k1
        let auth := if w1 == 1 then anyId k2 else admins[k2 % admins.size]!
        grant c a auth (adm k3).1 (signer dv)
      | 3 | 4 =>
        let (a, dv) := adm k1
        let auth := if w1 == 1 then a else admins[k2 % admins.size]!
        remove c a auth (adm k3).1 (signer dv)
      | 5 => let (a, dv) := adm k1; post c a (signer dv) "k".toUTF8 s!"m{i}".toUTF8
      | 6 => wrap c "k".toUTF8 d.enc "box".toUTF8
      | _ =>
        if w2 < 4 then mkOp [c, anyId k1] (.post "k".toUTF8 "unsigned".toUTF8 0 .empty)
        else { id := sha256 s!"junk-{seed}-{i}".toUTF8, kind := 9, reqs := [anyId k1], body := "junk".toUTF8 }
    if !(ids.contains o.id) then
      ops := ops.push o
      ids := ids.push o.id
      match kind with
      | 0 => invs := invs.push (o.id, Device.named s!"bearer-{seed}-{i}")
      | 1 => if !invs.isEmpty then reqs := reqs.push (o.id, d)
      | 8 => if !reqs.isEmpty then apps := apps.push (o.reqs.getD 1 .empty, o.id)
      | 9 =>
        if !reqs.isEmpty then
          let rq := o.reqs.getD 1 .empty
          match reqs.find? (·.1 == rq) with
          | some (_, rd) => adms := adms.push (o.id, rd)
          | none => pure ()
      | 2 => admins := admins.push o.id
      | _ => pure ()
  return ops.toList

def group {α} (rows : List (ByteArray × α)) (k : ByteArray) : List α :=
  rows.filterMap fun (k', a) => if k' == k then some a else none

/-- Every table of the database equals the model's. -/
def sameTables (t : Checks) (tag : String) (db : Db) (m : DB Fact) (ids0 : List Id) : IO Unit := do
  let ops ← (dumpOps (F := Fact)).run db
  let st ← (dumpStatus (F := Fact)).run db
  let waits ← (dumpWaits (F := Fact)).run db
  let queue ← (dumpQueue (F := Fact)).run db
  let idx ← (dumpIdx (F := Fact)).run db
  t.ok s!"{tag}: ops" (ops.all (fun o => m.ops o.id == some o) &&
    ops.length == (ids0.filter fun x => (m.ops x).isSome).length)
  t.ok s!"{tag}: verdicts" (st.all (fun (x, v) => m.status x == some v) &&
    st.length == (ids0.filter fun x => (m.status x).isSome).length)
  t.ok s!"{tag}: waits" (ids0.all fun r => group waits r == m.waits r)
  t.ok s!"{tag}: queue" (queue == m.queue)
  let keysUsed := ids0.foldl (fun acc x => match m.status x with
    | some (.valid f) => acc ++ keys f
    | _ => acc) ([] : List ByteArray)
  t.ok s!"{tag}: index" (keysUsed.all (fun k => group idx k == m.idx k) &&
    idx.all fun (k, _) => keysUsed.contains k)

end Tests
