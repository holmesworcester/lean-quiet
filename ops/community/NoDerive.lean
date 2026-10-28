/-
**Intents derive no keys.** A device is derived from its seed once, by
the caller, when its secret op is written (`Device.ofSeed`, then
`found`, `joinOps`, `join`); the store holds it whole and readers take
it from there (`device`, `device_derives`). This is checked on the code
that runs, at build time: for every intent and view (a Community
definition that writes ops, `Write`, or reads lists, `View`, and every
definition of the app's kinds, `Kinds`), the definitions it uses, walked
to the end, never reach a derivation: an Ed25519 key pair
(`edKeypair`), an X25519 conversion (`Crypto.staticOf`,
`Crypto.staticPubOf`) or a device from its seed (`Device.ofSeed`).
Proofs are not walked (they do not run). The build fails on the first
intent that does, naming the way it gets there.

The handshake's own derivation (`Connection.Keys.xSec`, once per
handshake) is the connection's, not an intent's.
-/
import Lean
import ops.community.Community
import ops.community.membership.AcceptedView
import ops.community.membership.RequestView
import ops.community.message.View
import ops.community.link.View

namespace Community.NoDerive
open Lean Elab Command

/-- What derives a key. -/
def derivers : List Name :=
  [``Community.edKeypair, ``Engine.Crypto.staticOf, ``Engine.Crypto.staticPubOf, ``Community.Device.ofSeed]

/-- An intent or a view: a Community definition writing ops (`Write`) or
reading lists (`View`), or a definition of the app's kinds. -/
def isIntent (n : Name) (ci : ConstantInfo) : Bool :=
  match ci with
  | .defnInfo _ =>
    !n.isInternal &&
      ((n.getRoot == `Community &&
        match ci.type.getForallBody.getAppFn.constName? with
        | some h => h == ``Community.Write || h == ``Engine.View
        | none => false) ||
       n.getRoot == `Kinds)
  | _ => false

/-- What a constant runs: its definition's value (none for a proof). -/
def runs (ci : ConstantInfo) : Option Expr :=
  match ci with
  | .thmInfo _ => none
  | _ => ci.value? (allowOpaque := true)

/-- The way from n to the first deriver its definitions reach, if any
(or, should the walk run out of steps, a way that says so: an unfinished
walk never passes). -/
def reaches (env : Environment) (n : Name) : Option (List Name) := Id.run do
  let mut seen : NameSet := {}
  let mut parent : NameMap Name := {}
  let mut stack : List Name := [n]
  let path := fun (parent : NameMap Name) (x : Name) => Id.run do
    let mut out := [x]
    let mut cur := x
    for _ in [0:10000] do
      match parent.find? cur with
      | some p => out := p :: out; cur := p
      | none => break
    return out
  for _ in [0:2000000] do
    match stack with
    | [] => return none
    | x :: rest =>
      stack := rest
      if seen.contains x then continue
      seen := seen.insert x
      if derivers.contains x then return some (path parent x)
      if let some v := (env.find? x).bind runs then
        for y in v.getUsedConstants do
          if !seen.contains y then
            parent := if parent.contains y then parent else parent.insert y x
            stack := y :: stack
  return some [n, `walk_ran_out_of_steps]

/-- Fails the build if an intent or view derives a key. -/
elab "#intents_derive_no_keys" : command => do
  let env ← getEnv
  let roots := env.constants.fold (init := #[]) fun acc n ci => if isIntent n ci then acc.push n else acc
  let bad := roots.filterMap fun n => (reaches env n).map (n, ·)
  if bad.isEmpty then
    logInfo m!"{roots.size} intents and views derive no keys"
  else
    throwError m!"intents that derive a key:\n{String.intercalate "\n" (bad.toList.map fun (n, p) =>
      s!"{n}: {" → ".intercalate (p.map toString)}")}"

#intents_derive_no_keys

end Community.NoDerive
