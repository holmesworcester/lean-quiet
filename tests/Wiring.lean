/-
Which laws are about the code that runs (README, "Not yet about running
code"). ci/proof-links.py writes that README section from this program's
output, and local CI fails when it goes stale.

- **What runs** is every definition an entry point's code reaches:
  `main` (Main.lean: the app, which the Android and iOS shells start as
  their main), the node's runner (`Engine.Sync.Runner.start`, the loop a
  daemon runs), and any `entry` of tests/wiring.txt (an `@[export]` a
  shipping platform calls; qr's own Android harness does not ship). Code is a
  definition's value without its types. A `partial def` runs its
  `_unsafe_rec`, an `implemented_by` definition its implementation, an
  `[init]` its initializer, and a `@[csimp]` definition its replacement
  too. Theorems do not run.
- **A law's subject** is the data definitions its statement names, seen
  through the Prop-valued definitions and inductives it names (an op's
  validity, a reachable state), three deep. Left out: instances,
  projections, matchers, the assumptions (`assume` in tests/wiring.txt),
  and the specifications it states running code against (`spec`), which
  are seen through too, keeping only what runs of what they name.
  tests/wiring.txt may narrow a subject (`subject`), to names it has.
- **Wired:** the subject is not empty and each of its definitions runs,
  or is a mirror a `bridge` law proves equal to running code (`run_step`:
  the engine's `step`, run on the store model, is `stepS`).
- **Model:** proven, and some definition of its subject does not run (a
  model, a harness, or code nothing calls yet), or its subject is empty
  (a general lemma). The missing link is each subject definition that
  does not run, with what calls it instead and tests/wiring.txt's `todo`
  note: which running code would have to call what.
- **Stated only:** a Prop-valued `…_stmt` definition no audited law
  concludes.
- **Assumption:** an `assume` of tests/wiring.txt, with the laws that
  take it as a hypothesis or state running code over it (directly, or
  through a bridge).

It fails (exit 1) if a name tests/wiring.txt gives is missing or stale
(a `spec` or a mirror that runs), a `bridge` law is not audited or does
not name its mirror, a law tests/wiring.txt marks `wired` is not, or an
audited law is missing. Negative control: a model law marked `wired`
must be caught, and the entry points must reach `App.step` and the
node's `onFrame`.

  lake env lean --run tests/Wiring.lean   (needs `lake build` and `lake build +Main`)

`WIRING_NOTES=path` reads other notes (ci/proof-links.py's negative
control adds a false `wired`).

Output, one line each, tab-separated: `law NAME STATUS SUBJECT MISSING
ASSUMES`, `stmt NAME STATUS SUBJECT MISSING`, `missing NAME RANK NOTE
CALLERS` (RANK: the `todo`'s place in tests/wiring.txt), `assume NAME
TEXT LAWS`, and a closing `count` line.
-/
import Lean

open Lean

/-- The module roots of this repository. -/
def roots : List Name := [`engine, `ops, `App, `Quiet, `Main]

def modOf (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!

def ours (env : Environment) (n : Name) : Bool :=
  match modOf env n with
  | some m => roots.contains m.getRoot
  | none => false

/-- The constants code names: a value without its types (binder types,
foralls) and structure names of projections. -/
partial def code (e : Expr) (acc : NameSet) : NameSet :=
  match e with
  | .const c _ => acc.insert c
  | .app f a => code a (code f acc)
  | .lam _ _ b _ => code b acc
  | .letE _ _ v b _ => code b (code v acc)
  | .mdata _ b => code b acc
  | .proj _ _ b => code b acc
  | _ => acc

/-- What a definition runs: its value's code, and what the compiler runs
for it instead or as well. -/
def runs (env : Environment) (n : Name) : NameSet := Id.run do
  let mut out : NameSet := {}
  match env.find? n with
  | some (.defnInfo d) => out := code d.value out
  | some (.opaqueInfo o) => out := code o.value out
  | _ => pure ()
  let csimp := (Compiler.CSimp.ext.getState env).map.find? n
  for x in [Name.str n "_unsafe_rec"] ++ (Compiler.getImplementedBy? env n).toList ++
      (getInitFnNameFor? env n).toList ++ (csimp.map (·.toDeclName)).toList do
    if env.contains x then out := out.insert x
  return out

/-- Every definition the entry points reach. -/
def running (env : Environment) (entry : List Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo : Array Name := entry.toArray
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    for c in runs env n do
      if !seen.contains c then todo := todo.push c
  return seen

/-- The sort a type ends in, past its binders. -/
def endSort : Expr → Option Level
  | .forallE _ _ b _ => endSort b
  | .sort l => some l
  | _ => none

/-- A definition of data: not Prop- or Type-valued, nor an instance, a
projection, a matcher or an auxiliary. -/
def isData (env : Environment) (c : Name) : Bool :=
  !c.isInternal && !Meta.isInstanceCore env c && !env.isProjectionFn c &&
  !Meta.isMatcherCore env c && !isAuxRecursor env c && !isNoConfusion env c &&
  match env.find? c with
  | some (.defnInfo d) => (endSort d.type).isNone
  | some (.opaqueInfo d) => (endSort d.type).isNone
  | _ => false

def isProp (env : Environment) (c : Name) : Bool :=
  match env.find? c with
  | some ci => endSort ci.type == some .zero
  | none => false

/-- The data definitions a statement names, through the Prop-valued
definitions and inductives it names, `depth` deep, stopping at `stop`;
and the constants met on the way. A specification (`spec`) is seen
through too, but of what its value names only what runs (`run`) is a
subject: the rest is more specification. -/
partial def about (env : Environment) (stop spec run : NameSet) (e : Expr) (depth : Nat)
    (inSpec : Bool) (acc : NameSet × NameSet) : NameSet × NameSet := Id.run do
  let mut (subj, props) := acc
  for c in e.getUsedConstants do
    if !ours env c || props.contains c then continue
    if stop.contains c then props := props.insert c; continue
    if isData env c && !spec.contains c then
      if !inSpec || run.contains c then subj := subj.insert c
      continue
    if !isProp env c && !spec.contains c then continue
    props := props.insert c
    if depth == 0 then continue
    let inSpec := inSpec || spec.contains c
    match env.find? c with
    | some (.defnInfo d) => (subj, props) := about env stop spec run d.value (depth - 1) inSpec (subj, props)
    | some (.inductInfo i) =>
      for k in i.ctors do
        if let some ci := env.find? k then
          (subj, props) := about env stop spec run ci.type (depth - 1) inSpec (subj, props)
    | _ => pure ()
  return (subj, props)

/-! ## tests/wiring.txt -/

structure Notes where
  spec : NameMap String := {}
  assume : NameMap String := {}
  /-- mirror ↦ the law that proves it equal to running code -/
  bridge : NameMap Name := {}
  todo : NameMap String := {}
  /-- the `todo` names, in the file's order -/
  order : Array Name := #[]
  subject : NameMap (List Name) := {}
  wired : List Name := []
  entry : List Name := []
  /-- every name given, with its line, for the existence check -/
  names : List (Name × Nat) := []

def Notes.stop (ns : Notes) : NameSet := ns.assume.foldl (fun s n _ => s.insert n) {}
def Notes.through (ns : Notes) : NameSet := ns.spec.foldl (fun s n _ => s.insert n) {}

/-- The first `n` words of a line, and the rest. -/
def fields (l : String) (n : Nat) : List String × String := Id.run do
  let mut rest := l.trimAscii.toString
  let mut ws : List String := []
  for _ in [0:n] do
    let w := rest.takeWhile (!·.isWhitespace) |>.toString
    if w.isEmpty then break
    ws := ws ++ [w]
    rest := (rest.drop w.length).trimAscii.toString
  return (ws, rest)

def readNotes (path : System.FilePath) : IO Notes := do
  let mut ns : Notes := {}
  let mut i := 0
  for l in (← IO.FS.readFile path).splitOn "\n" do
    i := i + 1
    let l := l.trimAscii.toString
    if l.isEmpty || l.startsWith "#" then continue
    match fields l 2 with
    | (["spec", n], t) => ns := { ns with spec := ns.spec.insert n.toName t, names := (n.toName, i) :: ns.names }
    | (["assume", n], t) => ns := { ns with assume := ns.assume.insert n.toName t, names := (n.toName, i) :: ns.names }
    | (["todo", n], t) =>
      ns := { ns with todo := ns.todo.insert n.toName t, order := ns.order.push n.toName,
                      names := (n.toName, i) :: ns.names }
    | (["wired", n], _) => ns := { ns with wired := n.toName :: ns.wired, names := (n.toName, i) :: ns.names }
    | (["entry", n], _) => ns := { ns with entry := n.toName :: ns.entry, names := (n.toName, i) :: ns.names }
    | (["bridge", m], t) =>
      let law := t.toName
      ns := { ns with bridge := ns.bridge.insert m.toName law, names := (m.toName, i) :: (law, i) :: ns.names }
    | (["subject", n], t) =>
      let s := (t.splitOn " ").filter (· ≠ "") |>.map String.toName
      ns := { ns with subject := ns.subject.insert n.toName s, names := (n.toName, i) :: s.map (·, i) ++ ns.names }
    | _ => throw <| IO.userError s!"tests/wiring.txt:{i}: not a note: {l}"
  return ns

/-! ## The classification -/

structure Law where
  name : Name
  subject : List Name
  missing : List Name
  assumes : List Name
  wired : Bool

/-- A law's subject and status. A mirror in its subject brings its
bridge's assumptions (`via`). -/
def classify (env : Environment) (run : NameSet) (ns : Notes) (via : NameMap (List Name))
    (law : Name) (ty : Expr) : Law := Id.run do
  let (subj, props) := about env ns.stop ns.through run ty 3 false ({}, {})
  let named := subj.toList ++ props.toList
  let subject := match ns.subject.find? law with
    | some s => s
    | none => subj.toList.filter fun c => !ns.spec.contains c && !ns.assume.contains c
  let subject := subject.toArray.qsort (·.toString < ·.toString) |>.toList
  let missing := subject.filter fun c => !run.contains c && !ns.bridge.contains c
  let assumes := (named ++ ty.getUsedConstants.toList).filter ns.assume.contains ++
    subject.flatMap (via.getD · [])
  let assumes := assumes.eraseDups.toArray.qsort (·.toString < ·.toString) |>.toList
  return { name := law, subject, missing, assumes, wired := !subject.isEmpty && missing.isEmpty }

/-- The laws marked `wired` that are not. -/
def falseMarks (laws : List Law) (marks : List Name) : List Name :=
  marks.filter fun m => match laws.find? (·.name == m) with
    | some l => !l.wired
    | none => true

def commas (ns : List Name) : String := ", ".intercalate (ns.map toString)

unsafe def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let audit := (← IO.FS.readFile "tests/Axioms.lean").splitOn "\n"
  let laws := audit.filterMap fun l =>
    if l.startsWith "#print axioms " then some (l.drop 14).trimAscii.toString.toName else none
  let ns ← readNotes ((← IO.getEnv "WIRING_NOTES").getD "tests/wiring.txt")
  -- every module of the libraries, the app and its main
  let mut mods : Array Name := #[`App, `Quiet, `Main]
  for dir in ["engine", "ops"] do
    for f in ← System.FilePath.walkDir dir do
      if f.extension == some "lean" then
        mods := mods.push ((f.withExtension "").toString.replace "/" ".").toName
  enableInitializersExecution
  let env ← importModules (mods.map ({ module := · })) {} (loadExts := true)
  let mut problems : Array String := #[]
  let run := running env ([`main, `Engine.Sync.Runner.start] ++ ns.entry)
  for (n, why) in [(`App.step, "the app's frame"), (`Engine.Sync.Node.onFrame, "the node's frames")] do
    if !run.contains n then problems := problems.push s!"control: the entry points do not reach {n} ({why})"
  -- what calls each definition, among this repository's
  let mut callers : NameMap NameSet := {}
  for i in [0:env.header.moduleNames.size] do
    if roots.contains env.header.moduleNames[i]!.getRoot then
      for n in env.header.moduleData[i]!.constNames do
        for c in runs env n do
          callers := callers.insert c ((callers.getD c {}).insert n)
  -- the notes name what exists, and are not stale
  for (n, i) in ns.names do
    if !env.contains n then problems := problems.push s!"tests/wiring.txt:{i}: no {n}"
  for (n, _) in ns.spec do
    if run.contains n then problems := problems.push s!"tests/wiring.txt: spec {n} runs; drop the note"
  for (m, law) in ns.bridge do
    if run.contains m then problems := problems.push s!"tests/wiring.txt: mirror {m} runs; drop the bridge"
    if !laws.contains law then problems := problems.push s!"tests/wiring.txt: bridge {law} is not audited"
    else if let some ci := env.find? law then
      let cs := ci.type.getUsedConstants
      if !cs.contains m || !cs.any run.contains then
        problems := problems.push s!"tests/wiring.txt: bridge {law} does not name {m} and running code"
  -- the laws, the bridges' first
  let mut via : NameMap (List Name) := {}
  for (m, law) in ns.bridge do
    if let some ci := env.find? law then via := via.insert m (classify env run ns {} law ci.type).assumes
  let mut out : Array Law := #[]
  for law in laws do
    match env.find? law with
    | some ci =>
      let l := classify env run ns via law ci.type
      if let some s := ns.subject.find? law then
        let (subj, _) := about env {} ns.through run ci.type 3 false ({}, {})
        for c in s do
          if !subj.contains c then problems := problems.push s!"tests/wiring.txt: {law}'s statement does not name {c}"
      out := out.push l
    | none => problems := problems.push s!"{law} is audited but not in the libraries"
  let lawList := out.toList
  for m in falseMarks lawList ns.wired do
    problems := problems.push s!"tests/wiring.txt marks {m} wired, but it is not"
  -- negative control: a model law marked wired is caught
  match lawList.find? (!·.wired) with
  | some l =>
    if (falseMarks lawList [l.name]).isEmpty then
      problems := problems.push s!"negative control: {l.name}, marked wired, was not caught"
  | none => pure ()
  -- the statements: every `…_stmt`, and the audited law that concludes it
  let mut stmts : Array (Name × Expr) := #[]
  let mut proof : NameMap Name := {}
  for i in [0:env.header.moduleNames.size] do
    if roots.contains env.header.moduleNames[i]!.getRoot then
      for n in env.header.moduleData[i]!.constNames do
        match env.find? n with
        | some (.defnInfo d) =>
          if (match n with | .str _ s => s.endsWith "_stmt" | _ => false) && endSort d.type == some .zero then
            stmts := stmts.push (n, d.value)
        | some (.thmInfo t) =>
          if laws.contains n then
            let rec concl : Expr → Expr
              | .forallE _ _ b _ => concl b
              | e => e
            if let some h := (concl t.type).getAppFn.constName? then proof := proof.insert h n
        | _ => pure ()
  -- the report
  let mut missing : NameSet := {}
  for l in lawList do
    for c in l.missing do missing := missing.insert c
    IO.println s!"law\t{l.name}\t{if l.wired then "wired" else "model"}\t{commas l.subject}\t{commas l.missing}\t{commas l.assumes}"
  let mut stated := 0
  for (n, v) in stmts do
    let l := classify env run ns via n v
    for c in l.missing do missing := missing.insert c
    match proof.find? n with
    | some p => IO.println s!"stmt\t{n}\tproven by {p}\t{commas l.subject}\t{commas l.missing}"
    | none => stated := stated + 1; IO.println s!"stmt\t{n}\tstated\t{commas l.subject}\t{commas l.missing}"
  for c in missing do
    let by_ := (callers.getD c {}).toList.filter (isData env) |>.toArray.qsort (·.toString < ·.toString)
    let rank := (ns.order.idxOf? c).getD ns.order.size
    IO.println s!"missing\t{c}\t{rank}\t{ns.todo.getD c ""}\t{commas (by_.toList.take 4)}"
  let mut assumed := 0
  for (n, t) in ns.assume do
    if !t.startsWith "=" then assumed := assumed + 1
    IO.println s!"assume\t{n}\t{t}\t{(lawList.filter (·.assumes.contains n)).length}"
  let nw := (lawList.filter (·.wired)).length
  IO.println s!"count\twired {nw}\tmodel {lawList.length - nw}\tstated {stated}\tassumption {assumed}"
  for p in problems do IO.eprintln s!"wiring: {p}"
  return if problems.isEmpty then 0 else 1
