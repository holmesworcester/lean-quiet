import app.community.Family

/-!
`community.name`: intents and composers: the ops an action writes, in this folder and below.
-/
namespace Community
open Engine Codec

/-- Name community c: an admin's register entry, superseding `prev` (the
names it saw), its counter one past theirs. `auth` shows the admin. -/
def setName (c adm auth : Id) (prev : List Id) (n : Nat) (by_ : Device) (name : ByteArray) : Op :=
  let reqs := [c, adm, auth] ++ prev
  mkOp reqs (.name n name (sig by_.sk reqs (.name n name .empty)))
end Community
namespace Community
open Engine

/-- Rename c as device d of an admin (admitted as `myAdm`, shown admin by
`auth`): a name superseding the current one, its counter one past it. -/
def rename (c myAdm auth : Id) (d : Device) (name : ByteArray) : View Fact Write := do
  let cur ← named.current.read [c] (limit := some 1)
  let (prev, n) := match cur.rows.head? with
    | some ((_, x), .named _ _ _ k) => ([x], k + 1)
    | _ => ([], 1)
  pure ⟨[setName c myAdm auth prev n d name]⟩

end Community
