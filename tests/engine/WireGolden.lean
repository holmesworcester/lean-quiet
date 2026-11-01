/-
The community family's wire format and judgements, as values: every op
type's body and fact as bytes (and read back), its tag, whether it is
local, where its fact sorts and the keys it is filed under, and the
validator's verdict on sample requirements. tests/engine/wire-golden.txt
holds this program's output from main before the families were split into
op folders (e727b5e), with one deliberate wire change since: one-approval
dropped the invitation's and request's threshold, so their bytes, the
invite ops' ids and their verdicts lost that field. Anything else that
moves is a regression. Signatures are a parameter: a scheme that accepts every
signature, and one that accepts none.
-/
import app.community.Proofs
import app.connection.Family

open Engine Codec Community

def hex (b : ByteArray) : String :=
  String.join (b.data.toList.map fun x =>
    let s := (Nat.toDigits 16 x.toNat); String.ofList (if s.length < 2 then '0' :: s else s))

def bs (s : String) : ByteArray := s.toUTF8

def bodies : List (String × Body) :=
  [("root", .root (bs "dev") (bs "enc") (bs "kid") (bs "sig")),
   ("invite", .invite (bs "bearer") true (bs "sig")),
   ("invite2", .invite (bs "bearer") false (bs "sig")),
   ("request", .request (bs "dev") (bs "enc") (bs "consent") (bs "bsig")),
   ("grant", .grant (bs "sig")),
   ("remove", .remove (bs "sig")),
   ("post", .post (bs "kid") (bs "sealed text") 7 1700000 (bs "sig")),
   ("post-cap", .post (bs "kid") (bs "x") (2 ^ 63) 5 (bs "sig")),
   ("wrap", .wrap (bs "box") (bs "sig")),
   ("profile", .profile (bs "Maya") 42 (bs "sig")),
   ("attach", .attach (bs "root-32-bytes-root-32-bytes-root") 1000 (bs "kid") (bs "sealed") (bs "sig")),
   ("react", .react (bs "🌱") 99 (bs "sig")),
   ("approve", .approve (bs "sig")),
   ("admit", .admit),
   ("accept", .accept (bs "c") (bs "dev")),
   ("joining", .joining (bs "c") (bs "inviter") [bs "hint1", bs "hint2"] (bs "req") (bs "Rowan") (bs "dev") 3),
   ("secret", .secret (bs "pk") (bs "seed")),
   ("name", .name 2 (bs "Quiet") (bs "sig")),
   ("abandon", .abandon),
   ("key", .key (bs "c") (bs "k")),
   ("chunk", .chunk (bs "root") 70000 1 (bs "slice") [bs "s1", bs "s2"]),
   ("endpoint", .endpoint (bs "sk")),
   ("receive", .receive 12)]

def facts : List (String × Fact) :=
  [("admission", .admission (bs "c") (bs "u") (bs "dev") (bs "enc") (bs "kid")),
   ("invitation", .invitation (bs "c") (bs "i") (bs "bearer") true),
   ("admin", .admin (bs "c") (bs "u")),
   ("removal", .removal (bs "c") (bs "u") (bs "by")),
   ("message", .message (bs "c") (bs "u") (bs "dev") (bs "kid") (bs "text") 7 1700000),
   ("message-child", .message (bs "c") (bs "u") (bs "dev") (bs "kid") (bs "text") 8 1700001 (some (bs "root"))),
   ("message-cap", .message (bs "c") (bs "u") (bs "dev") (bs "kid") (bs "text") (2 ^ 63) 5),
   ("wrap", .wrap (bs "c") (bs "kid") (bs "recipient") (bs "box")),
   ("profile", .profile (bs "c") (bs "u") (bs "Ma​ya") 42),
   ("attachment", .attachment (bs "c") (bs "m") (bs "u") (bs "root") 1000 (bs "kid") (bs "sealed")),
   ("react", .react (bs "c") (bs "u") (bs "m") (bs "🌱") 99),
   ("request", .request (bs "c") (bs "u") (bs "dev") (bs "enc") false),
   ("approval", .approval (bs "c") (bs "r") (bs "u")),
   ("secret", .secret (bs "pk") (bs "seed")),
   ("accepted", .accepted (bs "c") (bs "dev")),
   ("joining", .joining (bs "c") (bs "inviter") [bs "h"] (bs "req") (bs "Rowan") (bs "dev") 3),
   ("named", .named (bs "c") (bs "u") (bs "Quiet") 2),
   ("abandoned", .abandoned (bs "c") (bs "r") (bs "j")),
   ("key", .key (bs "c") (bs "kid") (bs "k")),
   ("chunk", .chunk (bs "c") (bs "a") (bs "root") 70000 1),
   ("endpoint", .endpoint (bs "pk") (bs "sk")),
   ("received", .received (bs "c") (bs "kid") (bs "m") 12),
   ("received-child", .received (bs "c") (bs "kid") (bs "m") 13 (some (bs "root")))]

def showV (o : Option Fact) : String := match o with
  | some f => hex (encode f)
  | none => "none"

def yes : Crypto := { verify := fun _ _ _ => true, pub := fun s => s }
def no : Crypto := { verify := fun _ _ _ => false, pub := fun _ => ByteArray.empty }

/-- Sample requirement lists: each op type's own shape, and some wrong ones. -/
def reqs : List (List Fact) :=
  let c := bs "c"
  let root := Fact.admission c c (bs "dev0") (bs "enc0") (bs "kid")
  let author := Fact.admission c (bs "u") (bs "dev") (bs "enc") (bs "kid")
  let other := Fact.admission c (bs "v") (bs "dev2") (bs "enc2") (bs "kid")
  let msg := Fact.message c (bs "u") (bs "dev") (bs "kid") (bs "t") 1 2
  let child := Fact.message c (bs "u") (bs "dev") (bs "kid") (bs "t") 1 2 (some (bs "r"))
  let inv := Fact.invitation c (bs "u") (bs "bearer") false
  let req := Fact.request c (bs "u") (bs "dev") (bs "enc") false
  let appr := Fact.approval c (bs "") (bs "v")
  let att := Fact.attachment c (bs "m") (bs "u") (bs "root") 70000 (bs "kid") (bs "x")
  let grant := Fact.admin c (bs "u")
  [[], [root], [root, author], [root, author, msg], [root, author, child], [root, inv],
   [root, req, other], [root, req, appr], [root, author, root, other], [root, author, grant, other],
   [root, author, author, author], [root, att], [msg], [Fact.joining c (bs "i") [] (bs "r") (bs "n") (bs "d") 0],
   [root, author, root], [root, author, grant, Fact.named c (bs "u") (bs "Q") 1], [other, author]]

def op (b : Body) (rs : List Id) : Op := Op.make b.tag rs (encode b)


def cbodies : List (String × Connection.Body) :=
  [("eph", .eph (bs "sk")), ("request", .request (bs "to") (bs "frm") (bs "m1")), ("opened", .opened),
   ("connection", .connection (bs "m2")), ("established", .established), ("send", .send (bs "addr")),
   ("recv", .recv true (bs "via") (bs "addr") 77), ("given", .given (bs "x"))]

def cfacts : List (String × Connection.Fact) :=
  [("eph", .eph (bs "of") (bs "pk") (bs "sk")), ("request", .request (bs "to") (bs "frm") (bs "m1")),
   ("opened", .opened (bs "req") (bs "c") (bs "frm") (bs "addr") [bs "op1"]),
   ("connection", .connection (bs "req") (bs "m2")),
   ("established", .established (bs "cid") (bs "c") (bs "peer") (bs "h") (bs "s") (bs "r") true),
   ("send", .send (bs "op") (bs "addr")), ("recv", .recv (bs "op") false (bs "via") (bs "addr") 78),
   ("given", .given (bs "conn") (bs "x"))]

def creqs : List (List Connection.F) :=
  let pk := ByteArray.mk (Array.replicate 32 7)
  let pk2 := ByteArray.mk (Array.replicate 32 9)
  let req := Connection.Fact.request pk pk2 (ByteArray.mk (Array.replicate 48 1))
  let conn := Connection.Fact.connection (bs "r") (bs "m2")
  [[], [.inr req], [.inr req, .inl (Community.Fact.endpoint pk (bs "sk"))], [.inr conn],
   [.inr conn, .inr req, .inr (Connection.Fact.eph (bs "o") pk (bs "e")), .inl (Community.Fact.endpoint pk (bs "sk"))],
   [.inl (Community.Fact.secret (bs "pk") (bs "seed"))]]

def connection : IO Unit := do
  for (n, b) in cbodies do
    let e := encode b
    IO.println s!"conn body {n} kind={b.kind} bytes={hex e} back={((decode e : Option Connection.Body).map fun x => hex (encode x)) == some (hex e)}"
    let o := Connection.mkOp [bs "x", bs "r"] b
    IO.println s!"  op id={hex o.id} scope={match Connection.scopeOf o with | .local => "local" | .shared c => "shared:" ++ hex c | .conn => "conn"} owns={Connection.owns o.kind}"
    let sk := ByteArray.mk (Array.replicate 32 3)
    for (fs, i) in creqs.zipIdx do
      let b' := match b with | .eph _ => Connection.Body.eph sk | .send _ => .send (bs "addr") | b => b
      let o' := Connection.mkOp [bs "x", bs "r"] b'
      match Connection.check Connection.sodium o' b' fs with
      | some f => IO.println s!"  check reqs{i} = {hex (encode f)}"
      | none => pure ()
  for (n, f) in cfacts do
    let e := encode f
    IO.println s!"conn fact {n} bytes={hex e} back={decode e == some f} sort={hex (Connection.sortOf f)} keys={(Connection.keys f).map hex}"

def main : IO Unit := do
  for (n, b) in bodies do
    let e := encode b
    IO.println s!"body {n} tag={b.tag} local={b.isLocal} bytes={hex e} back={decode e == some b}"
    let o := op b [bs "c", bs "r", bs "m"]
    IO.println s!"  op id={hex o.id} scope={match scopeOf o with | .local => "local" | .shared c => "shared:" ++ hex c | .conn => "conn"} order={orderOf o} signed={hex (signed o b)}"
    for (fs, i) in reqs.zipIdx do
      for (cn, C) in [("yes", yes), ("no", no)] do
        let v := check C o b fs
        if v.isSome then IO.println s!"  check {cn} reqs{i} = {showV v}"
  for (n, f) in facts do
    let e := encode f
    IO.println s!"fact {n} local={f.isLocal} bytes={hex e} back={decode e == some f} sort={hex (sortOf f)}"
    IO.println s!"  keys={(keys f).map hex}"
    IO.println s!"  isAdmin={isAdmin (bs "c") (bs "u") f} prevMax={prevMax (bs "c") [f]}"
  connection
