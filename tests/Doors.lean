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

The board and the rows' heights (engine/renderer/Board.lean,
Heights.lean) are counted code too: they reach no task and no IO.

The frame (`App.step`) is to read no store (`frame_reads`, docs/PERF.md),
and today it does: the run lists each way it reaches SQLite, as a
report, until the reader and the board land; then `App.step` joins
`counted` with SQLite's doors among what it may not name.

Run by tests/check.sh: `lake env lean tests/Doors.lean`.
-/
import Lean
import ops.app.Pics
import ops.community.MerkleCost
import engine.core.CodecCost
import engine.renderer.Heights
import engine.renderer.Board
import App

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
   (``Engine.Codec.decNatFromM, []), (``Engine.Codec.decBytesFromM, []),
   (``Live.Board.put, []), (``Live.Board.take, []), (``Live.Board.keep, []),
   (``Heights.T.findM, []), (``Heights.T.startM, []), (``Heights.T.setM, []), (``Heights.Rows.push, [])]

/-- SQLite's doors: what the frame is to reach none of. -/
def sqlDoors : List Name := [``Engine.Db.query, ``Engine.Db.exec]

/-- Each way root reaches one of `bad`: the chain of definitions from
root to the one that names it, the first found per door and caller. -/
def reachPaths (env : Environment) (root : Name) (bad : List Name) (most : Nat := 8) :
    List (List Name) := Id.run do
  let mut parent : NameMap Name := {}
  let mut seen : NameSet := ({} : NameSet).insert root
  let mut queue : Array Name := #[root]
  let mut i := 0
  let mut found : List (List Name) := []
  let mut callers : NameSet := {}
  while h : i < queue.size do
    let n := queue[i]
    i := i + 1
    if i > 200000 || found.length ≥ most then break
    let some ci := env.find? n | continue
    let v? := match ci with
      | .defnInfo d => some d.value
      | .opaqueInfo o => some o.value
      | _ => none
    let some v := v? | continue
    for c in v.getUsedConstants do
      if bad.contains c then
        -- the chain back to root; one report per definition of App's
        let mut chain := [n, c]
        let mut k := n
        for _ in [0:64] do
          match parent.find? k with
          | some p => chain := p :: chain; k := p
          | none => break
        let caller := (chain.drop 1).headD n
        if !callers.contains caller then
          callers := callers.insert caller
          found := found ++ [chain]
      else if !seen.contains c then
        seen := seen.insert c
        parent := parent.insert c n
        queue := queue.push c
  return found

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
  -- The shipping component boundary is enforced even while one-shot
  -- command validation and lifecycle bookkeeping still use transactions.
  for r in [``App.query, ``App.mountChildren, ``App.paintRow,
      ``App.refreshHomeCount, ``App.refreshMembers, ``App.refreshAsking,
      ``Component.author, ``Component.attachment, ``Component.reaction] do
    match reachPaths env r sqlDoors with
    | [] => IO.println s!"component query boundary: {r} reaches no SQLite"
    | paths => throwError s!"component bypasses query API: {r}: {paths}"
  for (r, extra) in counted do
    match reachDoors env r extra with
    | [] => IO.println s!"{r}: no back doors"
    | ds => throwError s!"{r} reaches back doors: {ds.map fun (c, n) => s!"{c} (named in {n})"}"
  match reachPaths env ``App.step sqlDoors with
  | [] => IO.println "frame_reads: App.step reaches no SQLite (move it into `counted`)"
  | ps =>
    IO.println s!"frame_reads (❌, a report until the reader lands): App.step reaches SQLite {ps.length} ways, among them:"
    for p in ps do IO.println s!"  {" → ".intercalate (p.map toString)}"
  match reachDoors env ``startPreOld with
  | [] => throwError "negative control: startPreOld's Task.spawn was not caught"
  | ds => IO.println s!"negative control: startPreOld reaches {ds.map (·.1)}, caught"
