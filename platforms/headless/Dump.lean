/-
A store's ops, one line each, for comparing two devices' stores:
id, type, the ids it requires, and what its body is (Community's bodies
by name; anything else by its type byte).

    dump <quiet.db>
-/
import Quiet

open Engine Community

def h4 (b : ByteArray) : String :=
  String.join (b.toList.take 4 |>.map fun x =>
    let t := String.ofList (Nat.toDigits 16 x.toNat); if t.length < 2 then "0" ++ t else t)

def what (o : Op) : String :=
  match (Codec.decode o.body : Option Body) with
  | some (.root ..) => "root" | some (.invite ..) => "invite" | some (.request ..) => "request"
  | some (.grant ..) => "grant" | some (.remove ..) => "remove"
  | some (.post _ _ t _) => s!"post t={t}" | some (.wrap ..) => "wrap"
  | some (.profile _ t _) => s!"profile t={t}" | some (.attach _ n ..) => s!"attach len={n}"
  | some (.react _ t _) => s!"react t={t}" | some (.approve ..) => "approve" | some .admit => "admit"
  | some (.accept ..) => "accept(local)" | some (.joining ..) => "joining(local)"
  | some (.secret ..) => "secret(local)" | some (.name ..) => "name" | some .abandon => "abandon(local)"
  | some (.key ..) => "key(local)" | some (.chunk _ _ i _ _) => s!"chunk i={i}"
  | none => s!"other type {o.kind}"

def main (args : List String) : IO UInt32 := do
  let some path := args[0]? | IO.eprintln "usage: dump <quiet.db>"; return 2
  let db ← Db.openAt path
  for row in ← db.query "SELECT o.bytes, s.verdict FROM ops o LEFT JOIN status s ON s.id = o.id" #[] do
    let some b := row[0]? | continue
    let v := match row[1]? with
      | some w => if w.size > 0 && w[0]! == 1 then "valid" else "refused"
      | none => "undecided"
    match Op.decode b with
    | some o => IO.println s!"{h4 o.id} {v} {what o} reqs={o.reqs.map h4}"
    | none => IO.println s!"{h4 (Engine.sha256 b)} undecodable"
  return 0
