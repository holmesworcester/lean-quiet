/-
Which laws are about the code that runs (README, "Not yet about running
code"). ci/proof-links.py writes that README section from this program's
output, and local CI fails when it goes stale.

- **What runs** is every definition an entry point's code reaches:
  `main` (Main.lean: the app, which the Android and iOS shells start as
  their main), the node's runner (`Engine.Sync.Runner.start`, the loop a
  daemon runs), and any `entry` of tests/wiring.txt (an `@[export]` a
  shipping platform calls). Code is a definition's value without its
  types. A `partial def` runs its `_unsafe_rec`, an `[init]` its
  initializer, a `@[csimp]` definition its replacement too, and an
  `implemented_by` definition its implementation instead: it does not
  run itself, since nothing proves the two equal.
- **A law's subject** is the data definitions its statement names, its
  conclusion's and its premises', seen through the Prop-valued
  definitions and inductives it names (an op's validity, a reachable
  state) and the fields of an instance it projects (`Turn.purge` on the
  held store is `purgeS`), three deep. Left out: instances, projections,
  matchers, the assumptions (`assume` in tests/wiring.txt), and the
  specifications the law states running code against (`spec`), which
  are seen through too, keeping only what runs of what they name.
  tests/wiring.txt may narrow a subject (`subject`), to names its
  statement has.
- **Wired:** the subject is not empty, each of its definitions runs or
  is a mirror a `bridge` law proves equal to running code (`run_step`:
  the engine's `step`, run on the store model, is `stepS`), and the law
  does not restate running code instead of naming it (`copy`).
- **Model:** proven, but it names something that does not run (a model,
  a harness, or code nothing calls yet), or its subject is empty (a
  lemma about a specification or an assumption). A model in a premise
  counts as one in the conclusion: `o ∈ offer … → room o ≠ none` is
  about what `offer` returns, and a law over `Reach` states holds of the
  running node only if its purges are `Reach`'s. The missing link is
  each subject definition that does not run, with what calls it instead
  and tests/wiring.txt's `todo` note: which running code would have to
  call what.
- **PREMISES** lists the models only a law's premises name, and those it
  names outside a narrowed subject (`conn_answers_ids` names the round's
  model).
- **Stated only:** a Prop-valued `…_stmt` definition no audited law
  concludes.
- **Assumption:** an `assume` of tests/wiring.txt, with the laws that
  take it as a hypothesis or are stated over it (directly, or through a
  bridge).

It fails (exit 1) if a note is stale or wrong: a name it gives is
missing; a `spec`, `todo` or mirror runs; no law waits on a `todo`; a
`bridge` law is not audited or does not conclude an equation or iff with
its mirror on one side and running code on the other; an `entry` is not
an `@[export]` whose symbol a shipping platform's source names; a `copy`
law names the code it copies, or that code does not run; a `subject`
names what its law's conclusion does not; a law marked `wired` is not.
It fails too if an audited law is missing, or the entry points do not
reach `App.step` and the node's `onFrame` (the walk's positive control;
ci/proof-links.py's negative control marks a model law wired).

  lake env lean --run tests/Wiring.lean   (needs `lake build` and `lake build +Main`)

`WIRING_NOTES=path` reads other notes. Output, one line each,
tab-separated: `law NAME STATUS SUBJECT MISSING ASSUMES MODULE PREMISES`
(PREMISES: as above), `stmt NAME STATUS SUBJECT
MISSING MODULE`, `missing NAME RANK NOTE CALLERS` (RANK: the note's
place in tests/wiring.txt), `assume NAME TEXT LAWS`, and a closing
`count` line.
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
for it as well; an `implemented_by` definition runs its implementation
only. -/
def runs (env : Environment) (n : Name) : NameSet := Id.run do
  if let some impl := Compiler.getImplementedBy? env n then return ({} : NameSet).insert impl
  let mut out : NameSet := {}
  match env.find? n with
  | some (.defnInfo d) => out := code d.value out
  | some (.opaqueInfo o) => out := code o.value out
  | _ => pure ()
  let csimp := (Compiler.CSimp.ext.getState env).map.find? n
  for x in [Name.str n "_unsafe_rec"] ++ (getInitFnNameFor? env n).toList ++
      (csimp.map (·.toDeclName)).toList do
    if env.contains x then out := out.insert x
  return out

/-- Every definition the entry points reach, less those `implemented_by`
replaces. -/
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
  return seen.toList.foldl (fun s n => if (Compiler.getImplementedBy? env n).isSome then s.erase n else s) seen

/-- The sort a type ends in, past its binders. -/
def endSort : Expr → Option Level
  | .forallE _ _ b _ => endSort b
  | .sort l => some l
  | _ => none

/-- A statement's conclusion, past its binders and premises. -/
def concl : Expr → Expr
  | .forallE _ _ b _ => concl b
  | e => e

def stripLams : Expr → Expr
  | .lam _ _ b _ => stripLams b
  | e => e

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

/-- The field a projection takes of an instance constant, as the
instance's value gives it: in `@Turn.purge F (HeldM F) inst …`, `inst`'s
`purge`. -/
def field (env : Environment) (p : Name) (args : Array Expr) : Option Expr := do
  let info ← env.getProjectionFnInfo? p
  let .const i _ := (← args[info.numParams]?).getAppFn | none
  guard (Meta.isInstanceCore env i)
  let .defnInfo d ← env.find? i | none
  let body := stripLams d.value
  let .const k _ := body.getAppFn | none
  let .ctorInfo c ← env.find? k | none
  body.getAppArgs[c.numParams + info.i]?

/-- The instance fields a term projects. -/
partial def fieldsOf (env : Environment) (e : Expr) (acc : Array Expr) : Array Expr :=
  match e with
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    let acc := args.foldl (fun acc a => fieldsOf env a acc) (fieldsOf env fn acc)
    match fn with
    | .const p _ => match field env p args with
      | some f => acc.push f
      | none => acc
    | _ => acc
  | .lam _ t b _ | .forallE _ t b _ => fieldsOf env b (fieldsOf env t acc)
  | .letE _ t v b _ => fieldsOf env b (fieldsOf env v (fieldsOf env t acc))
  | .mdata _ b | .proj _ _ b => fieldsOf env b acc
  | _ => acc

/-- The constants a term names, and those of the instance fields it
projects. -/
def named (env : Environment) (e : Expr) : Array Name :=
  (fieldsOf env e #[]).foldl (fun cs f => cs ++ f.getUsedConstants) e.getUsedConstants

/-- The data definitions a statement names, through the Prop-valued
definitions and inductives it names, `depth` deep, stopping at `stop`;
and the constants met on the way. A specification (`spec`) is seen
through too, but of what its value names only what runs (`run`) is a
subject: the rest is more specification. -/
partial def about (env : Environment) (stop spec run : NameSet) (e : Expr) (depth : Nat)
    (inSpec : Bool) (acc : NameSet × NameSet) : NameSet × NameSet := Id.run do
  let mut (subj, props) := acc
  for c in named env e do
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
  /-- law ↦ the running code it restates, and the note -/
  copy : NameMap (Name × String) := {}
  /-- the `todo` names and the copied code, in the file's order -/
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
    let at_ (ns : Notes) (n : Name) : Notes := { ns with names := (n, i) :: ns.names }
    match fields l 2 with
    | (["spec", n], t) => ns := at_ { ns with spec := ns.spec.insert n.toName t } n.toName
    | (["assume", n], t) => ns := at_ { ns with assume := ns.assume.insert n.toName t } n.toName
    | (["todo", n], t) =>
      ns := at_ { ns with todo := ns.todo.insert n.toName t, order := ns.order.push n.toName } n.toName
    | (["wired", n], _) => ns := at_ { ns with wired := n.toName :: ns.wired } n.toName
    | (["entry", n], _) => ns := at_ { ns with entry := n.toName :: ns.entry } n.toName
    | (["bridge", m], t) => ns := at_ (at_ { ns with bridge := ns.bridge.insert m.toName t.toName } m.toName) t.toName
    | (["copy", n], t) =>
      let (d, t) := match fields t 1 with
        | ([d], t) => (d.toName, t)
        | _ => (.anonymous, t)
      ns := at_ (at_ { ns with copy := ns.copy.insert n.toName (d, t), order := ns.order.push d } n.toName) d
    | (["subject", n], t) =>
      let s := (t.splitOn " ").filter (· ≠ "") |>.map String.toName
      ns := s.foldl at_ (at_ { ns with subject := ns.subject.insert n.toName s } n.toName)
    | _ => throw <| IO.userError s!"tests/wiring.txt:{i}: not a note: {l}"
  return ns

/-! ## The classification -/

structure Law where
  name : Name
  subject : List Name
  missing : List Name
  assumes : List Name
  /-- the models only its premises name -/
  premises : List Name
  wired : Bool

def sortNames (ns : List Name) : List Name :=
  ns.eraseDups.toArray.qsort (·.toString < ·.toString) |>.toList

/-- A law's subject and status, from its conclusion; and the models
anywhere in its statement. A mirror in its subject brings its bridge's
assumptions (`via`). -/
def classify (env : Environment) (run : NameSet) (ns : Notes) (via : NameMap (List Name))
    (law : Name) (ty : Expr) : Law := Id.run do
  let (subj, props) := about env ns.stop ns.through run (concl ty) 3 false ({}, {})
  let (whole, wprops) := about env ns.stop ns.through run ty 3 false ({}, {})
  let notRunning (c : Name) := !run.contains c && !ns.bridge.contains c
  let subject := sortNames <| match ns.subject.find? law with
    | some s => s
    | none => whole.toList.filter fun c => !ns.assume.contains c
  let copied := (ns.copy.find? law).map (·.1) |>.toList
  let missing := subject.filter notRunning ++ copied
  -- the models only its premises name, and those it names outside a
  -- narrowed subject
  let premises := sortNames <| (missing.filter fun c => !subj.contains c && !copied.contains c) ++
    whole.toList.filter fun c => notRunning c && !missing.contains c
  let assumes := (subj.toList ++ props.toList ++ whole.toList ++ wprops.toList ++ ty.getUsedConstants.toList).filter
    ns.assume.contains ++ subject.flatMap (via.getD · [])
  return { name := law, subject, missing, assumes := sortNames assumes, premises,
           wired := !subject.isEmpty && missing.isEmpty }

def commas (ns : List Name) : String := ", ".intercalate (ns.map toString)

/-- The source of the shipping platforms (not qr's harness, nor the
probes and tests). -/
def shipping : IO (Array String) := do
  let mut out := #[]
  for dir in ["platforms/android/twin", "platforms/android/native"] do
    for f in ← System.FilePath.walkDir dir do
      if [some "c", some "h", some "java", some "kt"].contains f.extension then
        out := out.push (← IO.FS.readFile f)
  for e in ← System.FilePath.readDir "platforms/ios" do
    if [some "m", some "c", some "h"].contains e.path.extension then
      out := out.push (← IO.FS.readFile e.path)
  return out

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
  for (n, _) in ns.todo do
    if run.contains n then problems := problems.push s!"tests/wiring.txt: todo {n} runs; drop the note"
  let src ← shipping
  for n in ns.entry do
    match getExportNameFor? env n with
    | some sym =>
      if !src.any (fun s => (s.splitOn sym.toString).length > 1) then
        problems := problems.push s!"tests/wiring.txt: entry {n}: no shipping platform calls {sym}"
    | none => problems := problems.push s!"tests/wiring.txt: entry {n} is not an @[export]"
  for (m, law) in ns.bridge do
    if run.contains m then problems := problems.push s!"tests/wiring.txt: mirror {m} runs; drop the bridge"
    if !laws.contains law then problems := problems.push s!"tests/wiring.txt: bridge {law} is not audited"
    else if let some ci := env.find? law then
      let c := concl ci.type
      let sides := match c.eq?, c.iff? with
        | some (_, l, r), _ => some (l, r)
        | none, some (l, r) => some (l, r)
        | none, none => none
      let runsIn (e : Expr) := (named env e).any fun x => x != m && isData env x && run.contains x
      let ok := match sides with
        | some (l, r) => ((named env r).contains m && runsIn l) || ((named env l).contains m && runsIn r)
        | none => false
      if !ok then
        problems := problems.push s!"tests/wiring.txt: bridge {law} does not equate running code with {m}"
  for (law, (d, _)) in ns.copy do
    if !run.contains d then problems := problems.push s!"tests/wiring.txt: copy {law}: {d} does not run"
    if let some ci := env.find? law then
      if (named env ci.type).contains d then
        problems := problems.push s!"tests/wiring.txt: copy {law} names {d}; drop the note"
  -- the laws, the bridges' first
  let mut via : NameMap (List Name) := {}
  for (m, law) in ns.bridge do
    if let some ci := env.find? law then via := via.insert m (classify env run ns {} law ci.type).assumes
  let mut out : Array Law := #[]
  for law in laws do
    match env.find? law with
    | some ci =>
      if let some s := ns.subject.find? law then
        let (subj, _) := about env {} ns.through run ci.type 3 false ({}, {})
        for c in s do
          if !subj.contains c then problems := problems.push s!"tests/wiring.txt: {law}'s statement does not name {c}"
      out := out.push (classify env run ns via law ci.type)
    | none => problems := problems.push s!"{law} is audited but not in the libraries"
  let lawList := out.toList
  for m in ns.wired do
    if !(lawList.find? (·.name == m)).any (·.wired) then
      problems := problems.push s!"tests/wiring.txt marks {m} wired, but it is not"
  -- the statements: every `…_stmt`, and the audited law that concludes it
  let mut stmts : Array (Name × Expr) := #[]
  let mut proof : NameMap Name := {}
  for i in [0:env.header.moduleNames.size] do
    if roots.contains env.header.moduleNames[i]!.getRoot then
      for n in env.header.moduleData[i]!.constNames do
        match env.find? n with
        | some (.defnInfo d) =>
          if (match n with | .str _ s => s.endsWith "_stmt" | _ => false) && endSort d.type == some .zero then
            stmts := stmts.push (n, stripLams d.value)
        | some (.thmInfo t) =>
          if laws.contains n then
            if let some h := (concl t.type).getAppFn.constName? then proof := proof.insert h n
        | _ => pure ()
  -- the report
  let mut waited : NameSet := {}
  let modName (n : Name) := ((modOf env n).getD .anonymous).toString
  for l in lawList do
    for c in l.missing ++ l.premises do waited := waited.insert c
    IO.println s!"law\t{l.name}\t{if l.wired then "wired" else "model"}\t{commas l.subject}\t{commas l.missing}\t{commas l.assumes}\t{modName l.name}\t{commas l.premises}"
  let mut stated := 0
  for (n, v) in stmts do
    let l := classify env run ns via n v
    for c in l.missing do waited := waited.insert c
    match proof.find? n with
    | some p => IO.println s!"stmt\t{n}\tproven by {p}\t{commas l.subject}\t{commas l.missing}\t{modName n}"
    | none => stated := stated + 1; IO.println s!"stmt\t{n}\tstated\t{commas l.subject}\t{commas l.missing}\t{modName n}"
  for (n, _) in ns.todo do
    if !waited.contains n then problems := problems.push s!"tests/wiring.txt: no law waits on todo {n}; drop the note"
  let copyNote : NameMap String := ns.copy.foldl (fun m _ (d, t) => m.insert d t) {}
  for c in waited do
    let by_ := (callers.getD c {}).toList.filter (isData env) |>.toArray.qsort (·.toString < ·.toString)
    let rank := (ns.order.idxOf? c).getD ns.order.size
    let note := (ns.todo.find? c).getD (copyNote.getD c "")
    IO.println s!"missing\t{c}\t{rank}\t{note}\t{commas (by_.toList.take 4)}"
  let mut assumed := 0
  for (n, t) in ns.assume do
    if !t.startsWith "=" then assumed := assumed + 1
    IO.println s!"assume\t{n}\t{t}\t{(lawList.filter (·.assumes.contains n)).length}"
  let nw := (lawList.filter (·.wired)).length
  IO.println s!"count\twired {nw}\tmodel {lawList.length - nw}\tstated {stated}\tassumption {assumed}"
  for p in problems do IO.eprintln s!"wiring: {p}"
  return if problems.isEmpty then 0 else 1
