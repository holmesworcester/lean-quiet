/-
Ops as wire bytes, against a peer that lies. A SQLite node with real
Ed25519 founds a community and posts; then it takes bytes the way a
network delivers them, through `Op.decode`:

- each op's bytes decode to that op, named by their hash, and its
  SQLite row holds exactly those bytes;
- the old row format (the id ahead of the bytes) never yields an op
  named by the id it carries, so a peer cannot pick a name, and the op
  it tried to replace is untouched;
- an op whose bytes are padded (a non-minimal length) is refused;
- a signed post whose body is re-encoded with padding has the same body
  and a still-valid signature but a new id: a lenient decoder takes it
  as a second copy of the message. Strict decoding refuses its body, so
  it is Invalid and the original stays the only one.
-/
import Tests.Lib

open Engine Community Tests

def C := ed25519
def fam := family C

/-- l with byte i, if it ends a number (< 128), spelled in two bytes
with the same value: a non-minimal LEB128 digit. -/
def pad (l : List UInt8) (i : Nat) : Option (List UInt8) :=
  match l[i]? with
  | some b => if b < 128 then some (l.take i ++ [b + 128, 0] ++ l.drop (i + 1)) else none
  | none => none

/-- Every padding of l that the lenient decoder `Codec.dec` still reads
as a, with nothing left over. -/
def paddings {α} [Codec α] [DecidableEq α] (l : List UInt8) (a : α) : List (List UInt8) :=
  (List.range l.length).filterMap fun i =>
    match pad l i with
    | some l' => if (Codec.dec l' : Option (α × List UInt8)) = some (a, []) then some l' else none
    | none => none

def status (x : Id) : SqlM Fact (Option (Verdict Fact)) := Store.getStatus x

def main (args : List String) : IO UInt32 := do
  let dir := args.headD "out/wire"
  IO.FS.createDirAll dir
  for f in ["w.db", "w.db-wal", "w.db-shm"] do
    if ← System.FilePath.pathExists (dir ++ "/" ++ f) then IO.FS.removeFile (dir ++ "/" ++ f)
  let t ← Checks.new
  let db ← Db.openAt (dir ++ "/w.db")
  let run {α} (m : SqlM Fact α) : IO α := m.run db
  let valid (x : Id) : IO Bool := do
    return match ← run (status x) with | some (.valid _) => true | _ => false
  let invalid (x : Id) : IO Bool := do
    return match ← run (status x) with | some .invalid => true | _ => false

  let f1 := Device.named "founder-1"
  let r := root f1
  let c := r.id
  let hello := post c c f1 "k1".toUTF8 "hello".toUTF8
  let other := post c c f1 "k1".toUTF8 "something else".toUTF8
  run (receive fam [r, hello])
  t.ok "the founder's post is Valid" (← valid hello.id)

  -- Bytes in, op out, named by the bytes.
  for o in [r, hello, other] do
    t.ok "an op's bytes decode to it" (Op.decode o.bytes == some o)
    t.ok "an op's id is its bytes' hash" (o.id == sha256 o.bytes)
  for o in [r, hello] do
    let rows ← db.query "SELECT bytes FROM ops WHERE id = ?" #[o.id]
    t.ok "the SQLite row is the wire bytes" (rows.map (·.toList) == #[[o.bytes]])

  -- A peer naming its own op: the old row format put the id ahead of
  -- the bytes. Whatever it decodes to is named by its own hash, never
  -- by the id it carries, and the op that id names is unchanged.
  for (named, carried) in [(hello, hello), (hello, other)] do
    let forged : ByteArray := ⟨(Codec.enc named.id ++ Codec.enc carried).toArray⟩
    match Op.decode forged with
    | some p =>
      t.ok "a forged name is not taken" (p.id != named.id && p.id == sha256 forged)
      run (receive fam [p])
    | none => t.ok "a forged name is not taken" true
  let kept ← run (Store.getOp (F := Fact) hello.id)
  t.ok "the named op is untouched" (kept == some hello)

  -- Padding the op's own bytes: the lenient decoder reads the same op;
  -- the strict one refuses every such spelling.
  let pads := paddings hello.bytes.data.toList hello
  t.ok "the op's bytes can be padded (the attack is real)" (!pads.isEmpty)
  t.ok "padded op bytes are refused" (pads.all fun l => (Op.decode ⟨l.toArray⟩).isNone)

  -- Padding inside the body: same body, so the signature still covers
  -- it, but new bytes and so a new id. Strict decoding refuses the body.
  let body : Body := match (Codec.decode hello.body : Option Body) with
    | some b => b
    | none => default
  t.ok "the post's body decodes" ((Codec.decode hello.body : Option Body).isSome)
  let bodyPads := paddings hello.body.data.toList body
  t.ok "the post's body can be padded (the attack is real)" (!bodyPads.isEmpty)
  let mut n := 0
  for l in bodyPads do
    let twin := Op.make hello.kind hello.reqs ⟨l.toArray⟩
    t.ok "a padded body names a new op" (twin.id != hello.id)
    t.ok "a padded body is not a body" ((Codec.decode twin.body : Option Body).isNone)
    run (receive fam [twin])
    t.ok "a re-padded copy of a signed post is Invalid" (← invalid twin.id)
    n := n + 1
  t.ok "the original post is still Valid" (← valid hello.id)
  IO.println s!"wire: tried {pads.length} op paddings and {n} body paddings"
  t.finish "wire"
