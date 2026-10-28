/-
No back doors (docs/PERF.md): a budget law counts what code does through
its doors, so the code it is about must reach costly work through them
only. This walks every definition the counted code reaches, in Lean's
own environment, and fails if one names a back door:
- a task made by a pure function (`Task.spawn`, `Task.map`, `Task.bind`)
  or by IO's (`BaseIO.asTask` and the rest): in Lean's logic a pure
  spawn is a value and costs nothing, which is how the old `decoded`
  spawned a decode every frame unseen;
- IO run from pure code (`unsafeBaseIO` and the rest);
- the hash itself (`Engine.sha256`), for the Merkle code, which must
  hash through `hashM`.

Theorems are not walked (they do not run). The negative control,
`startPreOld`, the preview's start as it shipped (a pure `Task.spawn` in
a `pure`), must be caught; the run says so.

Run by tests/check.sh: `lake env lean tests/Doors.lean`.
-/
import Lean
import ops.app.Pics
import ops.community.MerkleCost
import engine.core.CodecCost

open Lean

/-- What no counted code may name: tasks and IO outside a door. -/
def backDoors : List Name :=
  [``Task.spawn, ``Task.map, ``Task.bind, ``BaseIO.asTask, ``BaseIO.mapTask, ``BaseIO.bindTask,
   ``BaseIO.mapTasks, ``EIO.asTask, ``EIO.mapTask, ``EIO.bindTask, ``EIO.mapTasks, ``IO.asTask,
   ``IO.mapTask, ``IO.bindTask, ``IO.mapTasks, ``unsafeBaseIO, ``unsafeEIO, ``unsafeIO]

/-- The code each law counts, and what else it may not name: the Merkle
code hashes only through `hashM`. (The decode a picture's task runs
hashes op bytes and opens the file; that is the task's work, off the
frame.) -/
def counted : List (Name × List Name) :=
  [(``Pics.image, []), (``Pics.decoded, []), (``Community.Merkle.rootAndProofsM, [``Engine.sha256]),
   (``Engine.Codec.decNatFromM, []), (``Engine.Codec.decBytesFromM, [])]

/-- The preview's start as it shipped: a task made in a `pure`, so made
when the action is built, and invisible to the meter. -/
def startPreOld {m : Type → Type} [Monad m] (p : Row.Pic) (w h : Nat) : m (Option (Task Paint.Bitmap)) :=
  pure (if p.preview.isEmpty then none
    else some (Task.spawn fun _ => Pics.decodePic p.preview w h false))

/-- The back doors a definition reaches, with the definition that names
each: every definition reached is walked, and theorems are not. -/
def reachDoors (env : Environment) (root : Name) (extra : List Name := []) : List (Name × Name) := Id.run do
  let bad := backDoors ++ extra
  let mut seen : NameSet := {}
  let mut todo : Array Name := #[root]
  let mut found : List (Name × Name) := []
  let mut steps := 0
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    steps := steps + 1
    if steps > 200000 then break
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    let v? := match ci with
      | .defnInfo d => some d.value
      | .opaqueInfo o => some o.value
      | _ => none
    let some v := v? | continue
    for c in v.getUsedConstants do
      if bad.contains c then
        found := (c, n) :: found
      else if !seen.contains c then
        todo := todo.push c
  return found

#eval show CoreM Unit from do
  let env ← getEnv
  for (r, extra) in counted do
    match reachDoors env r extra with
    | [] => IO.println s!"{r}: no back doors"
    | ds => throwError s!"{r} reaches back doors: {ds.map fun (c, n) => s!"{c} (named in {n})"}"
  match reachDoors env ``startPreOld with
  | [] => throwError "negative control: startPreOld's Task.spawn was not caught"
  | ds => IO.println s!"negative control: startPreOld reaches {ds.map (·.1)}, caught"
