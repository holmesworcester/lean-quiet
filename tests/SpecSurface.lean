/-
What a reader must trust to believe a law: its spec surface and its
axioms (CLAUDE.md, section 4 and the appendix).

- `#spec_surface thm` lists this repository's definitions that the
  statement of `thm` depends on, followed through their bodies. The proof
  is not followed.
- `#audit_axioms thm` prints the axioms that `thm`'s proof uses.
- `#headline thm` prints both for docs/HEADLINE.md, with the law's file
  and line, and splits the surface into the app's part and the
  spec-only part. It fails (an error) if the proof uses an axiom other than
  Lean's standard three, so a `sorry` fails the file.

**The surface.** Start from the constants the statement names. For a
definition, add the constants of its type and its body. For an inductive
type, add its type and its constructors' types: the constructors are
what an inductive predicate means. For a theorem, add nothing: a proof
does not change what a statement means. For anything else (an `opaque`,
an axiom), add its type only. An `opaque`'s body is invisible to proofs
(a `partial def` is one), so a law can say little about it.

**What is listed.** Only this repository's own definitions (module roots
`engine`, `app`, `platforms`, `Quiet`, `Main`), and not what Lean makes
for them: constructors, structure fields, recursors, matchers,
`noConfusion`, auxiliary definitions, theorems. Private definitions are
listed by their user-facing names.

**Of the app, or spec-only.** A definition runs if the app's `main`, the
node's runner (`Engine.Sync.Runner.start`) or an `entry` of
tests/wiring.txt reaches it. This is tests/Wiring.lean's walk, copied:
that file is the authority on which laws are about running code, and this
one only shows a reader which parts of a surface are the app's. A
definition is of the app if it runs, a type is if the app's code names it,
and a predicate never is. Of the rest, a mirror that a `bridge` note's law
proves equal to running code is *bridged* (so is the cost meter, an
`instrument` that an audited equation erases), and an `assume` note's name (the
store model, a crypto contract) is *assumed*. What is left is spec-only:
it exists to state laws (predicates, specifications). The spec-only and
assumed parts are what a reviewer must read; the app's part is what the
law is about.

Usage, from the repository's top, after `lake build`, `lake build +Main`
and `lake build SpecTools`:

  lake env lean tests/Headline.lean
-/
import Lean

open Lean Elab Command

namespace SpecSurface

/-- This repository's module roots. -/
def roots : List Name := [`engine, `app, `platforms, `Quiet, `Main]

/-- The module that defines `c`, if it is imported (none: this file). -/
def moduleOf? (env : Environment) (c : Name) : Option Name :=
  (env.getModuleIdxFor? c).map fun i => env.header.moduleNames[i.toNat]!

/-- `c` is this repository's: from one of its modules, or from this file. -/
def ours (env : Environment) (c : Name) : Bool :=
  match moduleOf? env c with
  | some m => roots.contains m.getRoot
  | none => true

/-- The sort a type ends in, past its binders. -/
def endSort : Expr → Option Level
  | .forallE _ _ b _ => endSort b
  | .sort l => some l
  | _ => none

/-- What Lean makes for a definition, which a reader never reads apart
from the definition itself. -/
def generated (env : Environment) (c : Name) : Bool :=
  let user := (privateToUserName? c).getD c
  user.isInternal || Meta.isMatcherCore env c || isAuxRecursor env c || isNoConfusion env c ||
  env.isProjectionFn c ||
  (match user with
   | .str _ s => ["ctorIdx", "toCtorIdx", "ctorElim", "ctorElimType", "noConfusionType",
       "sizeOf_spec", "injEq", "inj"].contains s
   | _ => false) ||
  user.components.any (fun p => ["brecOn", "binductionOn", "below", "ibelow"].contains p.toString) ||
  -- `deriving DecidableEq`'s helper
  (match user with
   | .str p "decEq" => Meta.isInstanceCore env p
   | _ => false) ||
  match env.find? c with
  | some (.ctorInfo _) | some (.recInfo _) | some (.thmInfo _) | some (.quotInfo _) => true
  | _ => false

/-- How a reader meets a definition. -/
inductive Kind where
  /-- a Prop-valued definition or inductive: a claim -/
  | pred
  /-- an inductive type, a structure or a class, or a definition of a type -/
  | type
  /-- an instance -/
  | inst
  /-- a definition of data: code, or a value a law names -/
  | data
  /-- an `opaque` (a `partial def` among them): proofs cannot see its body -/
  | opaque
  /-- an axiom -/
  | ax
  deriving BEq, Inhabited

def Kind.label : Kind → String
  | .pred => "predicates"
  | .type => "types"
  | .inst => "instances"
  | .data => "definitions"
  | .opaque => "opaque"
  | .ax => "axioms"

def kindOf (env : Environment) (c : Name) : Kind :=
  if Meta.isInstanceCore env c then .inst else
  match env.find? c with
  | some (.inductInfo i) => if endSort i.type == some .zero then .pred else .type
  | some (.defnInfo d) =>
    match endSort d.type with
    | some .zero => .pred
    | some _ => .type
    | none => .data
  | some (.opaqueInfo _) => .opaque
  | some (.axiomInfo _) => .ax
  | _ => .data

/-- Every constant the statement of `thm` depends on (see the header),
    `thm` itself left out. A `stop` is listed but not entered. -/
partial def surface (env : Environment) (thm : Name) (stop : NameSet := {}) : NameSet :=
  let rec go (todo : List Name) (seen : NameSet) : NameSet :=
    match todo with
    | [] => seen
    | c :: rest =>
      if seen.contains c then go rest seen else
      if stop.contains c then go rest (seen.insert c) else
      let next := match env.find? c with
        | some (.defnInfo d) => d.type.getUsedConstants.toList ++ d.value.getUsedConstants.toList
        | some (.inductInfo i) => i.type.getUsedConstants.toList ++ i.ctors
        | some (.thmInfo _) => []
        | some ci => ci.type.getUsedConstants.toList
        | none => []
      go (next ++ rest) (seen.insert c)
  match env.find? thm with
  | some ci => go ci.type.getUsedConstants.toList {}
  | none => {}

/-- This repository's definitions in `thm`'s surface, as listed (see the header). -/
def ownSurface (env : Environment) (thm : Name) (stop : NameSet := {}) : Array Name :=
  ((surface env thm stop).toList.filter fun c => ours env c && !generated env c).toArray.qsort
    (·.toString < ·.toString)

/-! ## What runs: tests/Wiring.lean's walk, copied -/

/-- The constants code names: a value without its types. -/
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

/-- tests/wiring.txt's notes of one kind: each note's name and the rest of its line. -/
def notes (kind : String) : IO (List (Name × String)) := do
  let text ← IO.FS.readFile "tests/wiring.txt"
  return text.splitOn "\n" |>.filterMap fun l =>
    if l.startsWith (kind ++ " ") then
      match ((l.drop (kind.length + 1)).trimAscii.toString.splitOn " ") with
      | n :: rest => some (n.toName, " ".intercalate rest)
      | [] => none
    else none

/-- The entry points: `main`, the node's runner, and tests/wiring.txt's `entry` notes. -/
def entries : IO (List Name) := do
  return [`main, `Engine.Sync.Runner.start] ++ (← notes "entry").map (·.1)

/-- The types the app's code is made of: every constant named by the
type or the body of a definition that runs. -/
def appNames (env : Environment) (run : NameSet) : NameSet :=
  run.foldl (init := run) fun acc n =>
    match env.find? n with
    | some ci =>
      let cs := ci.type.getUsedConstants ++ ((ci.value?.map (·.getUsedConstants)).getD #[])
      cs.foldl (·.insert ·) acc
    | none => acc

/-- `c` is part of the app: a definition that runs (or whose
`implemented_by` implementation runs), or a type the app's code uses. A
predicate never runs: it is always for a reviewer to read. -/
def ofApp (env : Environment) (run app : NameSet) (c : Name) : Bool :=
  match kindOf env c with
  | .pred => false
  | .type => app.contains c
  | _ => run.contains c || (Compiler.getImplementedBy? env c).any run.contains

/-! ## The commands -/

/-- A name as a reader writes it. -/
def nameStr (c : Name) : String := toString ((privateToUserName? c).getD c)

def showAll (cs : Array Name) : String := ", ".intercalate (cs.map nameStr).toList

/-- The names listed under each kind, in a fixed order. -/
def byKind (env : Environment) (cs : Array Name) : List (Kind × Array Name) :=
  [Kind.pred, .type, .data, .inst, .opaque, .ax].filterMap fun k =>
    let xs := cs.filter (kindOf env · == k)
    if xs.isEmpty then none else some (k, xs)

def describe (env : Environment) (cs : Array Name) : String :=
  "; ".intercalate <| (byKind env cs).map fun (k, xs) => s!"{k.label} ({xs.size}): {showAll xs}"

/-- Lean's standard axioms, which every law may use. -/
def standard : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- `#spec_surface thm`: this repository's definitions that the statement of
`thm` depends on, by kind. -/
elab "#spec_surface " id:ident : command => do
  let env ← getEnv
  let thm ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let own := ownSurface env thm
  logInfo m!"{thm}: {own.size} definitions; {describe env own}"

/-- `#audit_axioms thm`: the axioms `thm` depends on. -/
elab "#audit_axioms " id:ident : command => do
  let thm ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axs ← liftCoreM <| collectAxioms thm
  logInfo m!"{thm}: {axs.toList}"

/-- The definitions of this repository the statement names directly. -/
def named (env : Environment) (thm : Name) : Array Name :=
  match env.find? thm with
  | some ci => (ci.type.getUsedConstants.filter fun c => ours env c && !generated env c).qsort
      (·.toString < ·.toString)
  | none => #[]

/-- `#headline thm₁ thm₂ …`: for each law, its place, its axioms (an error
unless standard), and its surface. The surface's size is
`#spec_surface`'s. What to review is walked again, stopping at bridged
mirrors (their bodies equal running code, by a law) and at assumptions
(each is read once, in the README's "What is Assumed"); of it, the app's
part is listed apart from the spec-only part. The cost meter (tests/wiring.txt's
`instrument`s, which audited equations erase to the plain run) counts as
bridged. -/
elab "#headline " ids:ident+ : command => do
  let env ← getEnv
  let ents ← entries
  for e in ents do
    if !env.contains e then logWarning m!"entry {e} is not imported: import Main"
  let run := running env ents
  let app := appNames env run
  -- a mirror a bridge law proves equal to running code; an assumption
  -- and the cost meter (an `instrument`, erased to the plain run by its
  -- law), with its types (`Engine.CostT`) and their instances
  let instruments := (← notes "instrument").map fun (m, l) => (m, l.toName)
  let meterTypes : NameSet := instruments.foldl (fun s (m, _) =>
    if env.contains m.getPrefix then s.insert m.getPrefix else s) {}
  let isMeter := fun (c : Name) => meterTypes.contains c ||
    (Meta.isInstanceCore env c && match env.find? c with
      | some ci => ci.type.getUsedConstants.any meterTypes.contains
      | none => false)
  let bridges := (← notes "bridge").map (fun (m, l) => (m, l.toName)) ++ instruments
  let bridgedNames : NameSet := bridges.foldl (fun s (m, _) => s.insert m) {}
  let assumed : NameSet := (← notes "assume").foldl (fun s (n, _) => s.insert n) {}
  -- an instance of an assumed type (the store model's monad) is assumed too
  let isAssumed := fun (c : Name) => assumed.contains c ||
    (Meta.isInstanceCore env c && match env.find? c with
      | some ci => ci.type.getUsedConstants.any assumed.contains
      | none => false)
  let isBridged := fun (c : Name) => bridgedNames.contains c || isMeter c
  let stop := meterTypes.foldl (·.insert ·) (bridgedNames.foldl (·.insert ·) assumed)
  let mut allOff : NameSet := {}
  let mut allAssumed : NameSet := {}
  for id in ids do
    let thm ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let axs ← liftCoreM <| collectAxioms thm
    let bad := axs.filter (!standard.contains ·)
    let file := match moduleOf? env thm with
      | some m => (m.toString.replace "." "/") ++ ".lean"
      | none => "(this file)"
    let line := match ← findDeclarationRanges? thm with
      | some r => toString r.selectionRange.pos.line
      | none => "?"
    let full := ownSurface env thm
    let walk := ownSurface env thm stop
    let mine := walk.filter (ofApp env run app ·)
    let rest := walk.filter (!ofApp env run app ·)
    let bridged := rest.filter isBridged
    let assumes := rest.filter fun c => isAssumed c && !isBridged c
    let off := rest.filter fun c => !isBridged c && !isAssumed c
    let via := bridged.map fun c =>
      let laws := (bridges.filter (·.1 == c)).map (nameStr ·.2)
      s!"{nameStr c} ({if laws.isEmpty then "the meter" else ", ".intercalate laws})"
    let msg := s!"headline {thm}\n  at {file}:{line}\n" ++
      s!"  axioms: {showAll axs}{if bad.isEmpty then " (standard)" else ""}\n" ++
      s!"  surface: {full.size} definitions\n" ++
      s!"  review: {mine.size} of the app, {off.size} spec-only, {assumes.size} assumed, " ++
        s!"{bridged.size} bridged\n" ++
      s!"  named: {showAll (named env thm)}\n" ++
      s!"  spec-only: {describe env off}\n" ++
      s!"  assumed: {showAll assumes}\n" ++
      s!"  bridged: {", ".intercalate via.toList}\n" ++
      s!"  of the app: {showAll mine}"
    if bad.isEmpty then logInfo msg
    else logError m!"{msg}\n  non-standard axioms: {showAll bad}"
    allOff := off.foldl (·.insert ·) allOff
    allAssumed := assumes.foldl (·.insert ·) allAssumed
  if ids.size > 1 then
    let sorted := fun (ns : NameSet) => ns.toArray.qsort (·.toString < ·.toString)
    logInfo (s!"headline all {ids.size} laws\n" ++
      s!"  spec-only, together: {allOff.size}: {describe env (sorted allOff)}\n" ++
      s!"  assumed, together: {allAssumed.size}: {showAll (sorted allAssumed)}")

/-- `e` with every constant named under `a` (the auxiliaries Lean makes
for theorem `a`: a `match`'s matcher and what it calls) renamed under `b`. -/
def renameUnder (a b : Name) (e : Expr) : Expr :=
  e.replace fun x => match x with
    | .const n ls => if a.isPrefixOf n && n != a then some (.const (n.replacePrefix a b) ls) else none
    | _ => none

/-- The auxiliaries named under `a` that `e` reaches, through their own
types and bodies. -/
partial def auxUnder (env : Environment) (a : Name) (e : Expr) : NameSet :=
  let rec go (todo : List Name) (seen : NameSet) : NameSet :=
    match todo with
    | [] => seen
    | c :: rest =>
      if seen.contains c then go rest seen else
      let next := match env.find? c with
        | some ci => (ci.type.getUsedConstants ++ ((ci.value?.map fun (v : Expr) => v.getUsedConstants).getD #[])).toList
        | none => []
      go ((next.filter fun n => a.isPrefixOf n && n != a) ++ rest) (seen.insert c)
  go (e.getUsedConstants.toList.filter fun n => a.isPrefixOf n && n != a) {}

/-- `#same_statement new old`: `new`'s statement is `old`'s, up to the
names of bound variables. For restating a law elsewhere (a challenge
file) without weakening it. A `match` in a statement makes auxiliary
definitions named after its theorem (a matcher, and what the matcher
calls), so two copies of a statement differ in those names: each
auxiliary of `new` must have a partner of `old`'s, named alike, with the
same type and body. -/
elab "#same_statement " a:ident b:ident : command => do
  let env ← getEnv
  let na ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo a
  let nb ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo b
  let (some ca, some cb) := (env.find? na, env.find? nb) | throwError "not found"
  if ca.levelParams.length != cb.levelParams.length then
    throwError "{na} and {nb} have different universe parameters"
  let rn := renameUnder na nb
  let aux := (auxUnder env na ca.type).toList
  let paired := aux.all fun x => match env.find? x, env.find? (x.replacePrefix na nb) with
    | some cx, some cy => (rn cx.type).eqv cy.type &&
        match cx.value?, cy.value? with
        | some vx, some vy => (rn vx).eqv vy
        | none, none => true
        | _, _ => false
    | _, _ => false
  if (rn ca.type).eqv cb.type && paired then
    logInfo m!"{na} states {nb}{if aux.isEmpty then "" else s!" ({aux.length} auxiliaries paired)"}"
  else throwError "{na} does not state {nb}:\n{ca.type}\nvs\n{cb.type}"

/-! ## Can a challenge state a law under its own name?

Comparator judges a theorem by name: the challenge states it with
`sorry`, the solution proves it, and the two must agree. Stated under
the law's own name, the challenge must import the definitions its
statement names without importing the law: no module it imports may be
the law's module, or import it. -/

/-- Each module's direct imports. -/
def importsOf (env : Environment) : NameMap (Array Name) := Id.run do
  let mut m : NameMap (Array Name) := {}
  for i in [0:env.header.moduleNames.size] do
    m := m.insert env.header.moduleNames[i]! (env.header.moduleData[i]!.imports.map (·.module))
  return m

/-- Whether module `a` is `b` or imports it, transitively. -/
partial def reaches (imps : NameMap (Array Name)) (a b : Name) : Bool :=
  let rec go (todo : List Name) (seen : NameSet) : Bool :=
    match todo with
    | [] => false
    | m :: rest =>
      if m == b then true else if seen.contains m then go rest seen else
      go (((imps.find? m).getD #[]).toList ++ rest) (seen.insert m)
  go [a] {}

/-- `#challenge_imports thm₁ thm₂ …`: for each law, the modules a
challenge must import to state it under its own name (those of the
constants its statement names), or the constants that block that: each
lives in the law's module, or in a module that imports it. Then, for the
laws not blocked, the imports of one challenge for all of them, any law
those imports reach, and the fewest groups first fit finds whose imports
reach none of their own laws (one challenge each). Auxiliaries named
after the law (a `match`'s matcher) are left out: the challenge makes
its own. -/
elab "#challenge_imports " ids:ident+ : command => do
  let env ← getEnv
  let imps := importsOf env
  let mut free : Array (Name × Name × Array Name) := #[]
  for id in ids do
    let thm ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let some lawMod := moduleOf? env thm | throwError "{thm} is not imported"
    let some ci := env.find? thm | throwError "{thm} not found"
    let cs := ci.type.getUsedConstants.filter fun c => !(thm.isPrefixOf c && c != thm)
    let ownMods := (cs.filterMap fun c =>
      match moduleOf? env c with
      | some m => if roots.contains m.getRoot then some m else none
      | none => none).toList.eraseDups.toArray.qsort (·.toString < ·.toString)
    let blockers := cs.filterMap fun c => match moduleOf? env c with
      | some m => if roots.contains m.getRoot && reaches imps m lawMod then some (c, m) else none
      | none => none
    if blockers.isEmpty then
      free := free.push (thm, lawMod, ownMods)
      logInfo m!"challenge {thm}: free\n  law in {lawMod}\n  imports {ownMods.toList}"
    else
      let why := blockers.toList.map fun (c, m) =>
        s!"{nameStr c} ({m}{if m == lawMod then ", the law's own module" else ", which imports the law's module"})"
      logInfo m!"challenge {thm}: blocked\n  law in {lawMod}\n  by {", ".intercalate why}"
  let allImports := (free.foldl (fun acc (_, _, ms) => acc ++ ms.toList) []).eraseDups
  let clashes := free.filterMap fun (thm, lawMod, _) =>
    let by_ := free.filterMap fun (other, _, ms) =>
      let hit := ms.filter (reaches imps · lawMod)
      if hit.isEmpty then none else some s!"{nameStr other}'s {hit.toList}"
    if by_.isEmpty then none else some s!"{nameStr thm} (its module is imported by {", ".intercalate by_.toList})"
  logInfo m!"challenge all: {free.size} of {ids.size} free\n  imports {allImports}\n  clashes:\n    {"\n    ".intercalate clashes.toList}"
  -- Group the free laws, first fit, so that no group's imports reach one
  -- of its own laws: one challenge per group.
  let mut groups : Array (Array (Name × Name) × List Name) := #[]
  for (thm, lawMod, ms) in free do
    let fits := fun (g : Array (Name × Name) × List Name) =>
      let imports := (g.2 ++ ms.toList).eraseDups
      let mods := g.1.map (·.2) |>.push lawMod
      !mods.any fun m => imports.any (reaches imps · m)
    match groups.findIdx? fits with
    | some i => groups := groups.modify i fun g => (g.1.push (thm, lawMod), (g.2 ++ ms.toList).eraseDups)
    | none => groups := groups.push (#[(thm, lawMod)], ms.toList)
  let lines := groups.toList.map fun g =>
    s!"{g.1.toList.map (nameStr ·.1)}\n      imports {g.2.mergeSort (·.toString < ·.toString)}"
  logInfo m!"challenge groups: {groups.size}\n    {"\n    ".intercalate lines}"

end SpecSurface
