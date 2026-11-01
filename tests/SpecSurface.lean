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
proves equal to running code is *bridged*, and an `assume` note's name (the
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
part is listed apart from the spec-only part. -/
elab "#headline " ids:ident+ : command => do
  let env ← getEnv
  let ents ← entries
  for e in ents do
    if !env.contains e then logWarning m!"entry {e} is not imported: import Main"
  let run := running env ents
  let app := appNames env run
  -- a mirror a bridge law proves equal to running code; an assumption
  let bridges := (← notes "bridge").map fun (m, l) => (m, l.toName)
  let bridgedNames : NameSet := bridges.foldl (fun s (m, _) => s.insert m) {}
  let assumed : NameSet := (← notes "assume").foldl (fun s (n, _) => s.insert n) {}
  -- an instance of an assumed type (the store model's monad) is assumed too
  let isAssumed := fun (c : Name) => assumed.contains c ||
    (Meta.isInstanceCore env c && match env.find? c with
      | some ci => ci.type.getUsedConstants.any assumed.contains
      | none => false)
  let stop := bridgedNames.foldl (·.insert ·) assumed
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
    let bridged := rest.filter bridgedNames.contains
    let assumes := rest.filter fun c => isAssumed c && !bridgedNames.contains c
    let off := rest.filter fun c => !bridgedNames.contains c && !isAssumed c
    let via := bridged.map fun c =>
      s!"{nameStr c} ({", ".intercalate ((bridges.filter (·.1 == c)).map (nameStr ·.2))})"
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

/-- `#same_statement new old`: `new`'s statement is `old`'s, up to the
names of bound variables. For restating a law elsewhere (a challenge
file) without weakening it. -/
elab "#same_statement " a:ident b:ident : command => do
  let env ← getEnv
  let na ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo a
  let nb ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo b
  let (some ca, some cb) := (env.find? na, env.find? nb) | throwError "not found"
  if ca.levelParams.length == cb.levelParams.length && ca.type.eqv cb.type then
    logInfo m!"{na} states {nb}"
  else throwError "{na} does not state {nb}:\n{ca.type}\nvs\n{cb.type}"

end SpecSurface
