/-
Every audited law's premises (the standing rules' premise tables).

For each law of tests/Axioms.lean, every hypothesis whose type is a
proposition, as the law states it (pretty-printed), with the constants it
names. ci/premises.py tags each one ([discharged], [env], [crypto],
[trusted] or [model]) from tests/wiring.txt's `assume` notes,
tests/Wiring.lean's classification and the vacuity evidence, writes
docs/PREMISES.md, and checks the README's ✅/🟡 against them.

  lake env lean --run tests/Premises.lean    one line per premise:
    premise <TAB> law <TAB> binder <TAB> statement <TAB> constants
-/
import Lean
open Lean Meta

def premisesOf (n : Name) : MetaM (Array (String × String × Array Name)) := do
  let info ← getConstInfo n
  forallTelescope info.type fun xs _ => do
    let mut out := #[]
    for x in xs do
      let d ← x.fvarId!.getDecl
      if ← isProp d.type then
        let s := toString (← ppExpr d.type)
        let flat := " ".intercalate ((s.splitOn "\n").map (·.trimAscii.toString))
        out := out.push (d.userName.eraseMacroScopes.toString, flat, d.type.getUsedConstants)
    return out

unsafe def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let audit := (← IO.FS.readFile "tests/Axioms.lean").splitOn "\n"
  let laws := audit.filterMap fun l =>
    if l.startsWith "#print axioms " then some (l.drop 14).trimAscii.toString.toName else none
  let mut mods : Array Name := #[`Quiet, `Main]
  for dir in ["engine", "app"] do
    for f in ← System.FilePath.walkDir dir do
      if f.extension == some "lean" then
        mods := mods.push ((f.withExtension "").toString.replace "/" ".").toName
  enableInitializersExecution
  let env ← importModules (mods.map ({ module := · })) {} (loadExts := true)
  let ctx : Core.Context := { fileName := "Premises", fileMap := default, maxHeartbeats := 0 }
  let mut missing := 0
  for law in laws do
    if (env.find? law).isNone then
      missing := missing + 1
      IO.println s!"missing\t{law}"
      continue
    let r ← ((premisesOf law).run' {} |>.toIO ctx { env }).toBaseIO
    match r with
    | .ok (ps, _) =>
      IO.println s!"law\t{law}\t{ps.size}"
      for (b, s, cs) in ps do
        IO.println s!"premise\t{law}\t{b}\t{s}\t{",".intercalate (cs.toList.map toString)}"
    | .error e => IO.println s!"error\t{law}\t{e}"
  return if missing = 0 then 0 else 1
