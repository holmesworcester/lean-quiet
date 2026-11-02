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
  state), with their compiled auxiliaries (a structural recursion's
  body, `X._f`) and the fields of the instances it names: those it projects
  (`Turn.purge` on the held store is `purgeS`), and those the code it
  names can reach (`onFrame` on the held store runs its purge), three
  deep, and through the pattern synonyms it names (`Fact.admission` is
  `Fact.ofAdmission` of an admission). Left out: instances, projections,
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
- **World:** not wired, but every definition it misses is a World's
  network, transport or harness (`world` in tests/wiring.txt: its steps,
  its plain frames, its directly opened sessions), and the code it is
  about, or the World runs, is the running node's (`Engine.Sync.Node`).
  Counted apart: never wired, and not a model. A law about the harness
  alone, with no node code, stays a model.
- **Control:** a law that names a mutant (`control` in tests/wiring.txt:
  a definition meant never to run) is a negative control, proving the
  mutant breaks its law. Counted apart: never wired, never a todo, and
  out of the lead's count.
- **Weak:** a `weak` definition (a seed from the clock) must not be
  reached from any entry point; the check names the path that does. A
  `door` definition (the OS's randomness) may be run, among what the
  entry points reach, only by its doors (`App.newBytes`, and the
  handshake's entropy). These are reachability, not dataflow: a secret
  derived inline from the clock, without freshSeed, would not be seen;
  the single door is what makes every secret's source one place to read.
- **Block:** what the frame must never wait on (a blocking send to the
  node's bounded channel): walked from `App.step`, but not into a
  `thread` it starts (the node's runner, the reader, which wait on
  their own), or an action passed to a saturated SDK task constructor.
  Direct worker calls remain visible. No `block` definition is reached.
  The sole `bounded`
  exception is `App.suspend`: its separate walk permits `App.waitFor`
  but still rejects other blocking calls outside those threads.
  Each `waits` mutant (a
  send as it was, waiting) must be caught by the same walk, and must not
  run: the rule's negative control.
- **Step:** a law that would be a model, but that a wired law's proof
  uses (through the theorems it uses, as their proof bodies show; a law
  stated over an instrument uses every instrument's erasing law, the
  meter's erasure algebra as a whole): a proof
  step of a law about running code, not a claim of its own. Computed,
  never noted: drop the wired use and it is a model again. Counted apart,
  with the wired laws that use it; a README row that cites a step must
  cite one of them (ci/proof-links.py). Control: the first step, walked
  from every wired law but those that use it, is not reached.
- **Instruments:** what the code under test runs in to be measured (the
  cost meter, `CostT`), each erased by an audited equation (`erase_bind`:
  a counted run, its costs dropped, is the plain run). Like an
  assumption, left out of a subject: a cost law over running code is
  about running code; one over a mirror is not.
- **Audited statements** (a `…_stmt` the audit lists) are not laws; they
  are counted with the statements.
- **PREMISES** lists the models only a law's premises name, and those it
  names outside a narrowed subject (`conn_answers_ids` names the round's
  model).
- **Stated only:** a Prop-valued `…_stmt` definition no audited law
  concludes.
- **Assumption:** an `assume` of tests/wiring.txt, with the laws that
  take it as a hypothesis or are stated over it (directly, or through a
  bridge); and a `holds`, a premise laws take that the running node
  keeps only as its note says.
- **Copies:** a `copy` restates running code instead of naming it: a
  law (a model until it names the code), or a definition (a model,
  until the code calls it). The README lists them.
- **The ratchet** (AGENTS.md: no proofs over models): tests/wiring-models.txt
  lists the model laws there were when the rule was made. A model law
  it does not list fails the check, and so does a name it lists that is
  no longer a model law, until its line is deleted: the list only
  shrinks. (ci/proof-links.py --check also fails on a line the merge
  base did not have, and runs the negative control: a model law left
  out of the list must be caught.)

It fails (exit 1) if a note is stale or wrong: a name it gives is
missing; a `spec`, `todo` or mirror runs; no law waits on a `todo`; a
`bridge` law is not audited or does not conclude an equation or iff with
its mirror on one side and running code on the other; an `entry` is not
an `@[export]` whose symbol a shipping platform's source names; a
`control` (a mutant) runs, or no law names it; an `instrument` runs, or
its law is not an audited equation naming it; a `copy`
law names the code it copies, a copied definition runs, or the code
does not run; a `subject` names what its law's conclusion does not; an
`assume` or `holds` no law takes; a law marked `wired` is not. And
every extern must have a contract: each C symbol an `@[extern]`
attribute names, in any Lean file of the repository (the app, the node,
the platforms and the tests), needs an `extern` note of tests/wiring.txt
saying what the proofs take of it; a note no file needs is stale; a
`test` contract is for a test's probe only (tests/, platforms/headless/);
a `prop:` contract names a Prop. A source with an extern no note covers
must be caught (the check's negative control). It fails
too if an audited law is missing, if a model law is not in
tests/wiring-models.txt, or if that list names a law that is not a model
law. Controls: the entry points must reach
`App.step` and the node's `onFrame`, and not the harnesses (`harnesses`);
the laws `models` names must be models, and `worlds` World laws; no law
is both wired and World; and with `Engine.Sync.Node` taken out of what
runs (node code that is a mirror), no World law stays one
(ci/proof-links.py's negative controls mark a model law, and a World
law, wired).

  lake env lean --run tests/Wiring.lean   (needs `lake build` and `lake build +Main`)

`WIRING_NOTES=path` reads other notes, `WIRING_MODELS=path` another
list of model laws. Output, one line each,
tab-separated: `law NAME STATUS SUBJECT MISSING ASSUMES MODULE PREMISES USERS`
(STATUS: wired, world, control, step or model)
(PREMISES: as above; USERS: a step's wired laws), `stmt NAME STATUS SUBJECT
MISSING MODULE`, `missing NAME RANK NOTE CALLERS WORLD` (RANK: the note's
place in tests/wiring.txt), `assume NAME TEXT LAWS` (the `holds` too),
`copy NAME CODE TEXT`, and a closing `count` line.
-/
import Lean

open Lean

/-- The module roots of this repository. -/
def roots : List Name := [`engine, `app, `Quiet, `Main]

/-- The negative controls: harnesses the entry points must not reach
(the Worlds' steps among them), laws that must be classified models (one
over a premise's model and a cost law, in the meter, over a door nothing
runs as it is), laws that must be negative controls (a mutant over its
budget), and laws that must be World laws (the two-node World's stream). Update them if one becomes real. -/
def harnesses : List Name := [`Engine.Sync.World.peer, `Pic.render]
def models : List Name :=
  [`Engine.Sync.RoundRun.collisionCheck_sound, `Engine.list_costs]
/-- Laws that must be negative controls: a mutant over its budget. -/
def controlLaws : List Name := [`Merkle.slow_over_budget, `Engine.Codec.slow_digits_over_budget]
/-- Laws that must be World laws: the node's code over a World. -/
def worlds : List Name := [`Engine.Sync.stream_delivers]

def modOf (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!

def ours (env : Environment) (n : Name) : Bool :=
  match modOf env n with
  | some m => roots.contains m.getRoot
  | none => false

/-- The action argument of a saturated task constructor. The other
arguments (and a partial application) remain on the calling thread. -/
def taskAction (e : Expr) : Option Nat :=
  match e.getAppFn with
  | .const n _ =>
    if (n == `IO.asTask || n == `BaseIO.asTask) && e.getAppNumArgs >= 3 then some 1
    else if n == `EIO.asTask && e.getAppNumArgs >= 4 then some 2
    else none
  | _ => none

/-- The constants code names: a value without its types (binder types,
foralls) and structure names of projections. For blocking checks only,
exclude an action passed to an actual task constructor. This is an edge
boundary, not a whitelist of worker names: calling that action directly
still traverses its body. The full wiring graph includes both threads. -/
partial def code (e : Expr) (acc : NameSet) (sameThread : Bool := false) : NameSet := Id.run do
  if sameThread then
    if let some action := taskAction e then
      let mut out := code e.getAppFn acc sameThread
      for i in [:e.getAppNumArgs] do
        if i != action then out := code e.getAppArgs[i]! out sameThread
      return out
  return match e with
  | .const c _ => acc.insert c
  | .app f a => code a (code f acc sameThread) sameThread
  | .lam _ _ b _ => code b acc sameThread
  | .letE _ _ v b _ => code b (code v acc sameThread) sameThread
  | .mdata _ b => code b acc sameThread
  | .proj _ _ b => code b acc sameThread
  | _ => acc

/-- What a definition runs: its value's code, and what the compiler runs
for it as well; an `implemented_by` definition runs its implementation
only. -/
def runs (env : Environment) (n : Name) (sameThread : Bool := false) : NameSet := Id.run do
  if let some impl := Compiler.getImplementedBy? env n then return ({} : NameSet).insert impl
  let mut out : NameSet := {}
  match env.find? n with
  | some (.defnInfo d) => out := code d.value out sameThread
  | some (.opaqueInfo o) => out := code o.value out sameThread
  | _ => pure ()
  let csimp := (Compiler.CSimp.ext.getState env).map.find? n
  for x in [Name.str n "_unsafe_rec"] ++ (getInitFnNameFor? env n).toList ++
      (csimp.map (·.toDeclName)).toList do
    if env.contains x then out := out.insert x
  return out

/-- A path the walk takes from an entry point to `target`, if it reaches
it: each definition, then one it runs. -/
def pathTo (env : Environment) (entry : List Name) (target : Name) (stop : NameSet := {})
    (sameThread : Bool := false) : Option (List Name) := Id.run do
  let mut parent : NameMap Name := {}
  let mut seen : NameSet := entry.foldl (·.insert ·) {}
  let mut todo : Array Name := entry.toArray
  let mut i := 0
  while h : i < todo.size do
    let n := todo[i]
    i := i + 1
    if n == target then
      let mut path := [n]
      let mut c := n
      while let some p := parent.find? c do
        path := p :: path
        c := p
      return some path
    if stop.contains n then continue
    for c in runs env n sameThread do
      if !seen.contains c then
        seen := seen.insert c
        parent := parent.insert c n
        todo := todo.push c
  return none

/-- Every definition the entry points reach, less those `implemented_by`
replaces; a `stop` is reached but not entered. -/
def running (env : Environment) (entry : List Name) (stop : NameSet := {})
    (sameThread : Bool := false) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo : Array Name := entry.toArray
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if stop.contains n then continue
    for c in runs env n sameThread do
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

/-- The fields of the instances a statement names that the code it names
can reach: an instance passed to running code is used as that code uses
it (`Node.write` runs the held store's `turn`; whatever reaches
`Turn.purge` runs its `purge`, `purgeS`). -/
def fieldsUsed (env : Environment) (ty : Expr) : Array Expr := Id.run do
  let cs := ty.getUsedConstants
  let reach := running env (cs.filter (isData env)).toList
  let mut out := #[]
  for i in cs do
    if !ours env i || !Meta.isInstanceCore env i then continue
    let some (.defnInfo d) := env.find? i | continue
    let body := stripLams d.value
    let .const k _ := body.getAppFn | continue
    let some (.ctorInfo c) := env.find? k | continue
    let fs := getStructureFields env c.induct
    for j in [0:fs.size] do
      let p := c.induct ++ fs[j]!
      if reach.contains p || cs.contains p then
        if let some f := body.getAppArgs[c.numParams + j]? then out := out.push f
  return out

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
    -- a definition's compiled auxiliaries are more of it: a structural
    -- recursion's body is `X._f`, which X's value names (a spec or a
    -- Prop seen through would otherwise hide what its body calls)
    if c.isInternal && !Meta.isMatcherCore env c then
      if let some (.defnInfo d) := env.find? c then
        props := props.insert c
        (subj, props) := about env stop spec run d.value depth inSpec (subj, props)
        continue
    -- a pattern synonym is notation for what it unfolds to:
    -- `Fact.admission c u d e` is `Fact.ofAdmission ⟨c, u, d, e⟩`
    if hasMatchPatternAttribute env c then
      if let some (.defnInfo d) := env.find? c then
        props := props.insert c
        (subj, props) := about env stop spec run d.value depth inSpec (subj, props)
        continue
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
  /-- a law or definition ↦ the running code it restates, and the note -/
  copy : NameMap (Name × String) := {}
  /-- premises laws take, which the running node keeps only as the text
  says -/
  holds : NameMap String := {}
  /-- the World's network, transport and harness: what a World law may
  miss and still run the node's code -/
  world : NameMap String := {}
  /-- mutants: definitions meant never to run, which negative-control laws
  break -/
  control : NameMap String := {}
  /-- an instrument the code under test runs in (the cost meter), ↦ the law
  that erases it -/
  instrument : NameMap Name := {}
  /-- what no shipping path may reach (a secret from the clock) -/
  weak : NameMap String := {}
  /-- a definition ↦ the only definitions, among what the entry points
  reach, that may run it (the OS's randomness, through its doors) -/
  door : NameMap (List Name) := {}
  /-- what the frame must never wait on (a blocking send to sync) -/
  block : NameMap String := {}
  /-- The sole bounded lifecycle barrier, with its deadline contract. -/
  bounded : NameMap String := {}
  /-- a thread the frame starts, which the `block` walk does not enter
  (it waits on its own) -/
  thread : List Name := []
  /-- mutants that wait, which the `block` walk must catch (its negative
  controls) -/
  waits : NameMap String := {}
  /-- the `todo` names and the copied code, in the file's order -/
  order : Array Name := #[]
  subject : NameMap (List Name) := {}
  /-- each extern's C symbol ↦ its contract's kind and text -/
  extern : List (String × String × String) := []
  wired : List Name := []
  entry : List Name := []
  /-- every name given, with its line, for the existence check -/
  names : List (Name × Nat) := []

def Notes.stop (ns : Notes) : NameSet :=
  ns.instrument.foldl (fun s n _ => s.insert n) (ns.assume.foldl (fun s n _ => s.insert n) {})
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
    | (["holds", n], t) => ns := at_ { ns with holds := ns.holds.insert n.toName t } n.toName
    | (["world", n], t) => ns := at_ { ns with world := ns.world.insert n.toName t } n.toName
    | (["control", n], t) => ns := at_ { ns with control := ns.control.insert n.toName t } n.toName
    | (["weak", n], t) => ns := at_ { ns with weak := ns.weak.insert n.toName t } n.toName
    | (["block", n], t) => ns := at_ { ns with block := ns.block.insert n.toName t } n.toName
    | (["bounded", n], t) => ns := at_ { ns with bounded := ns.bounded.insert n.toName t } n.toName
    | (["thread", n], _) => ns := at_ { ns with thread := n.toName :: ns.thread } n.toName
    | (["waits", n], t) => ns := at_ { ns with waits := ns.waits.insert n.toName t } n.toName
    | (["door", n], t) =>
      let d := ((fields t 1).1.headD "").toName
      ns := at_ (at_ { ns with door := ns.door.insert n.toName (d :: ns.door.getD n.toName []) } n.toName) d
    | (["instrument", n], t) =>
      let law := ((fields t 1).1.headD "").toName
      ns := at_ (at_ { ns with instrument := ns.instrument.insert n.toName law } n.toName) law
    | (["todo", n], t) =>
      ns := at_ { ns with todo := ns.todo.insert n.toName t, order := ns.order.push n.toName } n.toName
    | (["wired", n], _) => ns := at_ { ns with wired := n.toName :: ns.wired } n.toName
    | (["entry", n], _) => ns := at_ { ns with entry := n.toName :: ns.entry } n.toName
    | (["bridge", m], t) => ns := at_ (at_ { ns with bridge := ns.bridge.insert m.toName t.toName } m.toName) t.toName
    | (["copy", n], t) =>
      let (d, t) := match fields t 1 with
        | ([d], t) => (d.toName, t)
        | _ => (.anonymous, t)
      let ns' := { ns with copy := ns.copy.insert n.toName (d, t), order := (ns.order.push n.toName).push d }
      ns := at_ (at_ ns' n.toName) d
    | (["extern", sym], t) =>
      let (k, txt) := match fields t 1 with
        | ([k], txt) => (k, txt)
        | _ => ("", t)
      let ns' := { ns with extern := (sym, k, txt) :: ns.extern }
      ns := if k.startsWith "prop:" then at_ ns' (k.drop 5).toString.toName else ns'
    | (["subject", n], t) =>
      let s := (t.splitOn " ").filter (· ≠ "") |>.map String.toName
      ns := s.foldl at_ (at_ { ns with subject := ns.subject.insert n.toName s } n.toName)
    | _ => throw <| IO.userError s!"tests/wiring.txt:{i}: not a note: {l}"
  return ns

/-- tests/wiring-models.txt: the laws over models today, with their lines.
A line's first word is a law; `#` starts a comment. -/
def readModels (path : System.FilePath) : IO (List (Name × Nat)) := do
  let mut out := #[]
  let mut i := 0
  for l in (← IO.FS.readFile path).splitOn "\n" do
    i := i + 1
    let l := ((l.splitOn "#").headD "").trimAscii.toString
    if l.isEmpty then continue
    match fields l 1 with
    | ([n], "") => out := out.push (n.toName, i)
    | _ => throw <| IO.userError s!"{path}:{i}: not a law name: {l}"
  return out.toList

/-- The theorems each reached theorem's proof uses, walked from `roots`:
for each, the theorems that use it directly (the reverse edges), and
every theorem reached. `extra` adds uses the check itself makes (a law
over an instrument uses the instrument's erasing law). A use the walk
cannot see (no proof body loaded) is not made: its lemma stays a model. -/
def proofUses (env : Environment) (roots : List Name) (extra : Name → List Name) :
    NameMap (Array Name) × NameSet := Id.run do
  let mut parents : NameMap (Array Name) := {}
  let mut seen : NameSet := roots.foldl (·.insert ·) {}
  let mut todo := roots.toArray
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    let step (c : Name) : Bool := match env.find? c with
      | some (.thmInfo _) => true
      | some (.defnInfo _) => c.isInternal
      | _ => false
    let uses := match env.find? n with
      | some (.thmInfo t) => t.value.getUsedConstants.toList.filter step
      -- a proof's compiled auxiliaries (a recursion's body) are more of it
      | some (.defnInfo d) => if n.isInternal then d.value.getUsedConstants.toList.filter step else []
      | _ => []
    for c in uses ++ extra n do
      parents := parents.insert c ((parents.getD c #[]).push n)
      if !seen.contains c then
        seen := seen.insert c
        todo := todo.push c
  return (parents, seen)

/-- The roots among `n`'s users, up the reverse edges. -/
def usersOf (parents : NameMap (Array Name)) (roots : NameSet) (n : Name) : List Name := Id.run do
  let mut seen : NameSet := {}
  let mut out : Array Name := #[]
  let mut todo := #[n]
  while h : todo.size > 0 do
    let x := todo.back
    todo := todo.pop
    for p in parents.getD x #[] do
      if !seen.contains p then
        seen := seen.insert p
        if roots.contains p then out := out.push p
        todo := todo.push p
  return out.toList

/-! ## The classification -/

structure Law where
  name : Name
  subject : List Name
  missing : List Name
  assumes : List Name
  /-- the models only its premises name -/
  premises : List Name
  wired : Bool
  /-- not wired, but about the running node code in a World: every
  definition it misses is the World's network, transport or harness
  (`world`), and the node code it runs is `Engine.Sync.Node`'s -/
  world : Bool := false
  /-- a negative control: it names a mutant (`control`), meant never to
  run, and proves the mutant breaks its law -/
  control : Bool := false
  /-- a proof step: a model-class law that a wired law's proof uses
  (through theorems), with those wired laws -/
  step : Bool := false
  users : List Name := []

/-- The class the report prints. -/
def Law.status (l : Law) : String :=
  if l.wired then "wired" else if l.control then "control" else if l.world then "world"
  else if l.step then "step" else "model"

def sortNames (ns : List Name) : List Name :=
  ns.eraseDups.toArray.qsort (·.toString < ·.toString) |>.toList

/-- Node code that runs: `Engine.Sync.Node`'s. -/
def nodeCode (run : NameSet) (c : Name) : Bool := (`Engine.Sync.Node).isPrefixOf c && run.contains c

/-- A law's subject and status, from its conclusion; and the models
anywhere in its statement. A mirror in its subject brings its bridge's
assumptions and what its bridge misses (`via`). -/
def classify (env : Environment) (run : NameSet) (ns : Notes) (via : NameMap (List Name × List Name))
    (law : Name) (ty : Expr) : Law := Id.run do
  let (subj, props) := about env ns.stop ns.through run (concl ty) 3 false ({}, {})
  let (whole, wprops) := (fieldsUsed env ty).foldl
    (fun acc f => about env ns.stop ns.through run f 3 false acc)
    (about env ns.stop ns.through run ty 3 false ({}, {}))
  let notRunning (c : Name) := !run.contains c && !ns.bridge.contains c
  let subject := sortNames <| match ns.subject.find? law with
    | some s => s
    | none => whole.toList.filter fun c => !ns.assume.contains c
  let copied := (ns.copy.find? law).map (·.1) |>.toList
  let bridged := subject.flatMap fun c => ((via.find? c).map (·.2)).getD []
  let missing := sortNames (subject.filter notRunning ++ bridged) ++ copied
  -- the models only its premises name, and those it names outside a
  -- narrowed subject
  let premises := sortNames <| (missing.filter fun c => !subj.contains c && !copied.contains c) ++
    whole.toList.filter fun c => notRunning c && !missing.contains c
  let assumes := (subj.toList ++ props.toList ++ whole.toList ++ wprops.toList ++ ty.getUsedConstants.toList).filter
    (fun c => ns.assume.contains c || ns.holds.contains c) ++ subject.flatMap fun c => ((via.find? c).map (·.1)).getD []
  let wired := !subject.isEmpty && missing.isEmpty
  -- a negative control: it names a mutant
  let control := missing.any ns.control.contains
  -- a World: it misses only the World's network, transport and harness,
  -- and the code it is about, or the World runs, is the running node's
  let world := !wired && !control && !missing.isEmpty && copied.isEmpty && missing.all ns.world.contains &&
    (subject ++ (running env missing).toList).any (nodeCode run)
  return { name := law, subject, missing, assumes := sortNames assumes, premises, wired, world, control }

def commas (ns : List Name) : String := ", ".intercalate (ns.map toString)

/-! ## Externs: each has a stated contract -/

/-- The C symbols of the extern attributes in a file's text. -/
def externSyms (src : String) : List String :=
  ((src.splitOn "@[extern \"").drop 1).filterMap fun rest =>
    match rest.splitOn "\"" with
    | sym :: _ => if sym.isEmpty then none else some sym
    | [] => none

/-- Where a test's probe may be declared: never in shipped code. -/
def testOnly (path : String) : Bool :=
  path.startsWith "tests/" || path.startsWith "platforms/headless/"

/-- What is wrong with the extern notes for these files (path, text): an
extern with no contract, a test contract in shipped code, a stale note,
an unknown kind, a `prop:` naming no Prop, a contract with no text. -/
def externProblems (env : Environment) (srcs : Array (String × String))
    (notes : List (String × String × String)) : Array String := Id.run do
  let mut out := #[]
  let mut seen : List String := []
  for (path, src) in srcs do
    for sym in externSyms src do
      seen := sym :: seen
      match notes.find? (·.1 == sym) with
      | none => out := out.push s!"extern {sym} ({path}) has no contract: give it an `extern {sym} none|effect|test|prop:NAME TEXT` note"
      | some (_, k, _) =>
        if k == "test" && !testOnly path then
          out := out.push s!"extern {sym} ({path}) is shipped code, so its contract cannot be `test`"
  for (sym, k, txt) in notes do
    if !seen.contains sym then out := out.push s!"tests/wiring.txt: extern {sym}: no Lean file declares it; drop the note"
    if txt.isEmpty then out := out.push s!"tests/wiring.txt: extern {sym}: the contract has no text"
    if k.startsWith "prop:" then
      let n := (k.drop 5).toString.toName
      match env.find? n with
      | some ci => if endSort ci.type != some .zero then
          out := out.push s!"tests/wiring.txt: extern {sym}: {n} is not a Prop"
      | none => pure ()
    else if !["none", "effect", "test"].contains k then
      out := out.push s!"tests/wiring.txt: extern {sym}: unknown contract kind {k}"
  return out

/-- Every Lean file of the repository, with its text, but the build's. -/
def leanSources : IO (Array (String × String)) := do
  let mut out := #[]
  for e in ← System.FilePath.readDir "." do
    if e.path.extension == some "lean" then
      out := out.push (e.fileName, ← IO.FS.readFile e.path)
  for dir in ["engine", "app", "ops", "ui", "platforms", "tests"] do
    if ← System.FilePath.isDir dir then
      for f in ← System.FilePath.walkDir dir do
        if f.extension == some "lean" then
          out := out.push (f.toString, ← IO.FS.readFile f)
  return out

/-- The source of the shipping platforms (not qr's harness, nor the
probes and tests). -/
def shipping : IO (Array String) := do
  let mut out := #[]
  for dir in ["platforms/android/twin", "platforms/native"] do
    for f in ← System.FilePath.walkDir dir do
      if [some "c", some "h", some "java", some "kt"].contains f.extension then
        out := out.push (← IO.FS.readFile f)
  -- the glue every platform compiles (glue_android.c is gone: Android and
  -- iOS build engine/native's)
  for f in ["engine/native/glue.c", "engine/native/crypto.c"] do
    out := out.push (← IO.FS.readFile f)
  for e in ← System.FilePath.readDir "platforms/ios" do
    if [some "m", some "c", some "h"].contains e.path.extension then
      out := out.push (← IO.FS.readFile e.path)
  return out

/-! ## The proof graph

`WIRING_GRAPH=path` writes how the laws compose, as JSON, for
ci/proof-tree.py (docs/PROOF-TREE.md): each theorem written by hand in
the modules tests/Axioms.lean imports, with its class (an audited law's,
as classified above; `lemma` for the rest), module and line, and the
laws its proof uses. -/

/-- A theorem or definition Lean made, not one written by hand: an
equation, an auxiliary proof or recursion, a matcher, an instance, a
projection, a structure's or an inductive's lemma. -/
def made (env : Environment) (n : Name) : Bool :=
  let u := privateToUserName n
  u.isInternalDetail || env.isProjectionFn n || Meta.isInstanceCore env n ||
  Meta.isMatcherCore env n || isAuxRecursor env n || isNoConfusion env n ||
  match u with
  | .str _ s => ["eq_def", "eq_unfold", "induct", "mutual_induct", "induct_unfolding", "fun_cases",
      "sizeOf_spec", "injEq", "inj", "ext", "ext_iff", "ofNat_ctorIdx", "brecOn", "congr_simp"].contains s
  | _ => false

/-- The laws `n`'s value names, seen through what Lean made of ours
(`foo.proof_1`, `foo.match_1`, `foo._unary`, an instance). Each constant
is looked at once: `seen` keeps what it adds (nothing, but for a law and
what Lean made). -/
partial def lawUses (env : Environment) (mine : Name → Bool) (law : Std.HashSet Name) (n : Name) :
    StateM (Std.HashMap Name (Array Name)) (Array Name) := do
  modify (·.insert n #[])  -- a cycle among what Lean made ends here
  let some v := (env.find? n).bind (·.value? (allowOpaque := true)) | return #[]
  let mut out : NameSet := {}
  for c in v.getUsedConstants do
    if c == n then continue
    if law.contains c then out := out.insert c; continue
    let ds ← match (← get)[c]? with
      | some ds => pure ds
      | none => if mine c && made env c then lawUses env mine law c else
          modify (·.insert c #[]) *> pure #[]
    for d in ds do
      if d != n then out := out.insert d
  let ds := (sortNames out.toList).toArray
  modify (·.insert n ds)
  return ds

/-- The modules of ours a list of imports reaches. -/
def reached (env : Environment) (imports : List Name) : Array Name := Id.run do
  let mut seen : NameSet := {}
  let mut todo := imports.toArray
  while h : todo.size > 0 do
    let m := todo.back
    todo := todo.pop
    if seen.contains m || !roots.contains m.getRoot then continue
    seen := seen.insert m
    if let some i := env.getModuleIdx? m then
      for imp in env.header.moduleData[i.toNat]!.imports do todo := todo.push imp.module
  return seen.toList.toArray

def writeGraph (env : Environment) (audit : List String) (laws : List Law) (path : String) : IO Unit := do
  let classes : NameMap Law := laws.foldl (fun m l => m.insert l.name l) {}
  let mods := reached env <| audit.filterMap fun l =>
    if l.startsWith "import " then some (l.drop 7).trimAscii.toString.toName else none
  let ourMods : Array Bool := env.header.moduleNames.map (roots.contains ·.getRoot)
  let mine (c : Name) : Bool := match env.getModuleIdxFor? c with
    | some i => ourMods[i.toNat]!
    | none => false
  let line (n : Name) : Nat :=
    ((declRangeExt.find? (level := .server) env n).map (·.selectionRange.pos.line)).getD 0
  let mut names : Array Name := #[]
  for m in mods do
    let some i := env.getModuleIdx? m | continue
    for n in env.header.moduleData[i.toNat]!.constNames do
      if let some (.thmInfo _) := env.find? n then
        if classes.contains n || (!made env n && line n != 0) then names := names.push n
  let law : Std.HashSet Name := names.foldl (·.insert ·) {}
  let (uses, _) := (names.mapM (lawUses env mine law)).run {}
  let mut nodes : Array (String × Json) := #[]
  for n in names, us in uses do
    let cls := ((classes.find? n).map (·.status)).getD "lemma"
    nodes := nodes.push (n.toString, Json.mkObj [("name", Json.str n.toString), ("class", Json.str cls),
      ("module", Json.str ((modOf env n).getD .anonymous).toString), ("line", toJson (line n)),
      ("uses", Json.arr (us.map (Json.str ·.toString))),
      ("users", Json.arr ((((classes.find? n).map (·.users)).getD []).toArray.map (Json.str ·.toString)))])
  let sorted := nodes.qsort (·.1 < ·.1) |>.map (·.2)
  IO.FS.writeFile path (Json.compress (Json.mkObj [("laws", Json.arr sorted)]) ++ "\n")

unsafe def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let audit := (← IO.FS.readFile "tests/Axioms.lean").splitOn "\n"
  let laws := audit.filterMap fun l =>
    if l.startsWith "#print axioms " then some (l.drop 14).trimAscii.toString.toName else none
  let ns ← readNotes ((← IO.getEnv "WIRING_NOTES").getD "tests/wiring.txt")
  -- every module of the libraries, the app and its main
  let mut mods : Array Name := #[`Quiet, `Main]
  for dir in ["engine", "app"] do
    for f in ← System.FilePath.walkDir dir do
      if f.extension == some "lean" then
        mods := mods.push ((f.withExtension "").toString.replace "/" ".").toName
  enableInitializersExecution
  let env ← importModules (mods.map ({ module := · })) {} (loadExts := true)
  let mut problems : Array String := #[]
  let run := running env ([`main, `Engine.Sync.Runner.start] ++ ns.entry)
  for (n, why) in [(`App.step, "the app's frame"), (`Engine.Sync.Node.onFrame, "the node's frames")] do
    if !run.contains n then problems := problems.push s!"control: the entry points do not reach {n} ({why})"
  for n in harnesses do
    if run.contains n then problems := problems.push s!"control: the entry points reach {n}, a harness"
  -- what no shipping path may reach, with the path that does
  let entries := [`main, `Engine.Sync.Runner.start] ++ ns.entry
  for (n, why) in ns.weak do
    if run.contains n then
      let path := (pathTo env entries n).getD [n]
      problems := problems.push s!"weak: the shipping app reaches {n} ({why}): {" → ".intercalate (path.map toString)}"
  -- what only its doors may run, among what the entry points reach
  for (n, doors) in ns.door do
    if !run.contains n then problems := problems.push s!"door: nothing shipping runs {n}; drop the note"
    for d in doors do
      if !run.contains d then problems := problems.push s!"door: {d}, a door of {n}, does not run; drop it"
    for c in run do
      if (runs env c).contains n && !doors.contains c && !c.isPrefixOf n then
        let path := (pathTo env entries c).getD [c]
        problems := problems.push s!"door: {c} runs {n} outside its doors ({commas doors}): {" → ".intercalate (path.map toString)}"
  -- what the frame must never wait on: walked from App.step, not into the
  -- threads it starts (the node's runner, the reader: each waits on its
  -- own, and the frame only offers to them); each mutant that waits must
  -- be caught, and must not run
  let threads : NameSet := ns.thread.foldl (·.insert ·) {}
  let barriers := ns.bounded.foldl (fun acc n _ => acc.insert n) threads
  for (n, why) in ns.bounded do
    if n != `App.suspend || why.isEmpty || !(running env [`App.step] threads true).contains n then
      problems := problems.push s!"bounded: only the reached App.suspend may be exempted, with its deadline contract ({n})"
    let inside := running env [n] threads true
    for (b, _) in ns.block do
      if b != `App.waitFor && inside.contains b then
        problems := problems.push s!"bounded: {n} reaches unbounded {b}; every wait must use waitFor"
  let frame := running env [`App.step] barriers true
  for (n, why) in ns.block do
    if frame.contains n then
      let path := (pathTo env [`App.step] n barriers true).getD [n]
      problems := problems.push s!"block: the frame waits on {n} ({why}): {" → ".intercalate (path.map toString)}"
  for n in ns.thread do
    if !run.contains n then problems := problems.push s!"tests/wiring.txt: thread {n} does not run; drop it"
  for (m, _) in ns.waits do
    if run.contains m then problems := problems.push s!"tests/wiring.txt: waits {m}, a mutant, runs"
    let reach := running env [m] threads true
    if !ns.block.toList.any (fun (n, _) => reach.contains n) then
      problems := problems.push s!"negative control: {m}, which waits, was not caught by a block note"
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
  -- every extern has a stated contract; a source with an extern no note
  -- covers, and a test probe in shipped code, must be caught
  problems := problems ++ externProblems env (← leanSources) ns.extern
  let fake := "@[extern \"lq_uncontracted\"] opaque f : IO Unit"
  if !(externProblems env #[("tests/Fake.lean", fake)] ns.extern).any (·.startsWith "extern lq_uncontracted") then
    problems := problems.push "negative control: an extern with no contract was not caught"
  if let some (sym, _, _) := ns.extern.find? (·.2.1 == "test") then
    let shipped := s!"@[extern \"{sym}\"] opaque g : IO Unit"
    if !(externProblems env #[("engine/Fake.lean", shipped)] ns.extern).any (·.startsWith s!"extern {sym} (engine/Fake.lean)") then
      problems := problems.push s!"negative control: the test probe {sym} in shipped code was not caught"
  for (n, _) in ns.spec do
    if run.contains n then problems := problems.push s!"tests/wiring.txt: spec {n} runs; drop the note"
  for (n, _) in ns.todo do
    if run.contains n then problems := problems.push s!"tests/wiring.txt: todo {n} runs; drop the note"
  for (n, _) in ns.world do
    if run.contains n then problems := problems.push s!"tests/wiring.txt: world {n} runs; drop the note"
  for (n, _) in ns.control do
    if run.contains n then problems := problems.push s!"tests/wiring.txt: control {n}, a mutant, runs"
  -- an instrument does not run, and its law is an audited equation that
  -- names it: what it erases to
  for (n, law) in ns.instrument do
    if run.contains n then problems := problems.push s!"tests/wiring.txt: instrument {n} runs"
    if !laws.contains law then problems := problems.push s!"tests/wiring.txt: instrument law {law} is not audited"
    else if let some ci := env.find? law then
      if (concl ci.type).eq?.isNone || !(named env ci.type).contains n then
        problems := problems.push s!"tests/wiring.txt: {law} is not an equation that erases {n}"
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
  for (n, (d, _)) in ns.copy do
    if !run.contains d then problems := problems.push s!"tests/wiring.txt: copy {n}: {d} does not run"
    if laws.contains n then
      if let some ci := env.find? n then
        if (named env ci.type).contains d then
          problems := problems.push s!"tests/wiring.txt: copy {n} names {d}; drop the note"
    else if run.contains n then
      problems := problems.push s!"tests/wiring.txt: copy {n} runs; drop the note"
  -- the laws, the bridges' first
  let mut via : NameMap (List Name × List Name) := {}
  for (m, law) in ns.bridge do
    if let some ci := env.find? law then
      let b := classify env run ns {} law ci.type
      via := via.insert m (b.assumes, b.missing.filter (!ns.bridge.contains ·))
  let mut out : Array Law := #[]
  for law in laws do
    match env.find? law with
    | some (.defnInfo _) => pure ()  -- an audited statement (`…_stmt`), not a law
    | some ci =>
      if let some s := ns.subject.find? law then
        let (subj, _) := about env {} ns.through run (concl ci.type) 3 false ({}, {})
        for c in s do
          if !subj.contains c then problems := problems.push s!"tests/wiring.txt: {law}'s conclusion does not name {c}"
      out := out.push (classify env run ns via law ci.type)
    | none => problems := problems.push s!"{law} is audited but not in the libraries"
  -- proof steps: model-class laws a wired law's proof uses (through
  -- theorems; a law over an instrument uses its erasing law), with the
  -- wired laws that use each
  let wiredNames := (out.filter (·.wired)).toList.map (·.name)
  let wiredSet : NameSet := wiredNames.foldl (·.insert ·) {}
  -- a wired law over the meter rests on its whole erasure algebra (erase
  -- commutes with pure, bind and each door): naming any instrument, it
  -- uses every instrument's law
  let instrumentLaws := ns.instrument.toList.map (·.2)
  let instrumentUse (n : Name) : List Name :=
    if !wiredSet.contains n then [] else match env.find? n with
      | some ci =>
        let cs := named env ci.type
        if ns.instrument.toList.any (fun (i, _) => cs.contains i) then instrumentLaws else []
      | none => []
  let (parents, usedByWired) := proofUses env wiredNames instrumentUse
  out := out.map fun l =>
    if !l.wired && !l.world && !l.control && usedByWired.contains l.name then
      { l with step := true, users := sortNames (usersOf parents wiredSet l.name) }
    else l
  let lawList := out.toList
  -- the step rule's control: without the wired laws that use it, the
  -- first step is reached by no other wired law, so it would be a model
  if let some st := lawList.find? (·.step) then
    if st.users.isEmpty then problems := problems.push s!"control: {st.name}, a step, has no wired user"
    let rest := wiredNames.filter (!st.users.contains ·)
    let restSet : NameSet := rest.foldl (·.insert ·) {}
    let (_, reached) := proofUses env rest fun n => if restSet.contains n then instrumentUse n else []
    if reached.contains st.name then
      problems := problems.push s!"control: {st.name} stays a step without the wired laws that use it ({commas st.users})"
  for m in ns.wired do
    if !(lawList.find? (·.name == m)).any (·.wired) then
      problems := problems.push s!"tests/wiring.txt marks {m} wired, but it is not"
  -- a World law is never wired; and its node code must be the running
  -- node's: with `Engine.Sync.Node` taken out of what runs (node code
  -- that is a mirror), no World law stays a World law
  let noNode := run.toList.foldl (fun s c => if (`Engine.Sync.Node).isPrefixOf c then s.erase c else s) run
  for l in lawList do
    if l.wired && l.world then problems := problems.push s!"{l.name} is counted wired and World"
    if l.world then
      if let some ci := env.find? l.name then
        if (classify env noNode ns via l.name ci.type).world then
          problems := problems.push s!"control: {l.name} stays a World law with mirrored node code"
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
    IO.println s!"law\t{l.name}\t{l.status}\t{commas l.subject}\t{commas l.missing}\t{commas l.assumes}\t{modName l.name}\t{commas l.premises}\t{commas l.users}"
  let mut stated := 0
  for (n, v) in stmts do
    let l := classify env run ns via n v
    for c in l.missing do waited := waited.insert c
    match proof.find? n with
    | some p => IO.println s!"stmt\t{n}\tproven by {p}\t{commas l.subject}\t{commas l.missing}\t{modName n}"
    | none => stated := stated + 1; IO.println s!"stmt\t{n}\tstated\t{commas l.subject}\t{commas l.missing}\t{modName n}"
  for (n, _) in ns.todo.toList ++ ns.world.toList do
    if !waited.contains n then problems := problems.push s!"tests/wiring.txt: no law waits on {n}; drop the note"
  for (n, _) in ns.control do
    if !waited.contains n then problems := problems.push s!"tests/wiring.txt: no law names control {n}; drop the note"
  -- a law's copy is filed under the code it copies; a definition's, under itself
  let copyNote : NameMap String := ns.copy.foldl
    (fun m n (d, t) => if laws.contains n then m.insert d t else m.insert n t) {}
  for c in waited do
    let by_ := (callers.getD c {}).toList.filter (isData env) |>.toArray.qsort (·.toString < ·.toString)
    let rank := (ns.order.idxOf? c).getD ns.order.size
    let note := (ns.todo.find? c).getD ((ns.world.find? c).getD (copyNote.getD c ""))
    IO.println s!"missing\t{c}\t{rank}\t{note}\t{commas (by_.toList.take 4)}\t{ns.world.contains c}"
  let mut assumed := 0
  for (n, t) in ns.assume.toList ++ ns.holds.toList do
    if !t.startsWith "=" then assumed := assumed + 1
    let k := (lawList.filter (·.assumes.contains n)).length
    if k == 0 then problems := problems.push s!"tests/wiring.txt: no law takes or is stated over {n}; drop the note"
    IO.println s!"assume\t{n}\t{t}\t{k}"
  for (n, (d, t)) in ns.copy do
    IO.println s!"copy\t{n}\t{d}\t{t}"
  -- negative controls: laws known to be about models, and to be World
  -- laws, must be found so
  for m in models do
    if (lawList.find? (·.name == m)).any (fun l => l.wired || l.world || l.step) then
      problems := problems.push s!"control: {m}, a model law, is classified wired, World or a step"
  for m in worlds do
    if !(lawList.find? (·.name == m)).any (·.world) then
      problems := problems.push s!"control: {m}, a World law, is not classified World"
  for m in controlLaws do
    if !(lawList.find? (·.name == m)).any (·.control) then
      problems := problems.push s!"control: {m}, a mutant's law, is not classified a negative control"
  -- the ratchet (AGENTS.md): no new law over a model, and the list of
  -- today's only shrinks
  let base ← readModels ((← IO.getEnv "WIRING_MODELS").getD "tests/wiring-models.txt")
  let mut listed : NameSet := {}
  for (n, i) in base do
    if listed.contains n then problems := problems.push s!"tests/wiring-models.txt:{i}: {n} is listed twice"
    listed := listed.insert n
    match lawList.find? (·.name == n) with
    | some l =>
      if l.wired || l.world || l.control || l.step then
        problems := problems.push s!"tests/wiring-models.txt:{i}: {n} is no longer a model law ({if l.wired then "wired" else if l.world then "World" else if l.control then "control" else "a step of a wired law"}): delete the line (ci/proof-links.py --prune)"
    | none => problems := problems.push s!"tests/wiring-models.txt:{i}: {n} is not an audited law: delete the line (ci/proof-links.py --prune)"
  for l in lawList do
    if !l.wired && !l.world && !l.control && !l.step && !listed.contains l.name then
      problems := problems.push s!"model: {l.name} is a new law over a model (it misses {if l.missing.isEmpty then "every running definition: its subject is empty" else commas l.missing}): state it over the code that runs, or prove its model equal to running code (a bridge); AGENTS.md"
  let nw := (lawList.filter (·.wired)).length
  let nW := (lawList.filter (·.world)).length
  let nc := (lawList.filter (·.control)).length
  let ns_ := (lawList.filter (·.step)).length
  IO.println s!"count\twired {nw}\tworld {nW}\tcontrol {nc}\tstep {ns_}\tmodel {lawList.length - nw - nW - nc - ns_}\tstated {stated}\tassumption {assumed}"
  if let some path ← IO.getEnv "WIRING_GRAPH" then writeGraph env audit lawList path
  for p in problems do IO.eprintln s!"wiring: {p}"
  return if problems.isEmpty then 0 else 1
