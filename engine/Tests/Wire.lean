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
  it is Invalid and the original stays the only one;
- each op decoded is exactly its bytes (`Op.decode_exact`), and a
  bundle's payloads together are smaller than it (`decode_sum`);
- frames off a TCP stream, taken as the runner's reader takes them
  (`frames`): however the stream is cut into reads, the payloads come
  out exactly, and what is kept between reads stays under one maximal
  frame and its length (`buffer_bounded`); a length over 1 MiB ends the
  connection in the read that completes it (`frames_tooBig`).
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

  -- No amplification: a decoded op is its bytes; a bundle's payloads
  -- are no larger than it.
  for o in [r, hello, other] do
    t.ok "a decoded op is exactly its bytes" ((Op.decode o.bytes).map (·.bytes) == some o.bytes)
  let bundle := Codec.encode ([r, hello, other].map (·.bytes))
  let inner : Option (List ByteArray) := Codec.decode bundle
  t.ok "a bundle's payloads are smaller than it" (match inner with
    | some l => (l.map (·.size)).foldl (· + ·) 0 < bundle.size
    | none => false)

  -- Frames off a TCP stream, as the reader takes them.
  let payloads : List ByteArray := [.empty, "a".toUTF8, ⟨Array.replicate 70000 7⟩,
    ⟨Array.replicate Engine.Sync.maxFrame 9⟩, "end".toUTF8]
  let stream := payloads.foldl (fun s p => s ++ Engine.Sync.frame p) ByteArray.empty
  -- Read the stream in pieces of these sizes, as `reader` does:
  -- payloads out, the largest buffer kept, and whether it ended.
  let readAll (bs : ByteArray) (sizes : Nat → Nat) : List ByteArray × Nat × Bool × Nat := Id.run do
    let mut buf := ByteArray.empty
    let mut got : List ByteArray := []
    let mut most := 0
    let mut at_ := 0
    let mut i := 0
    while at_ < bs.size do
      let chunk := bs.extract at_ (at_ + max 1 (sizes i))
      at_ := at_ + chunk.size
      i := i + 1
      let (ps, kept) := Engine.Sync.frames (buf ++ chunk)
      got := got ++ ps
      match kept with
      | some k =>
        buf := k
        most := max most k.size
      | none => return (got, most, true, at_)
    return (got, most, false, at_)
  let mut g := Rng.mk 7
  let mut cuts : List (Nat → Nat) := [fun _ => 65536, fun _ => 4096, fun i => if i % 2 == 0 then 3 else 100003]
  for _ in [0:4] do
    let (a, g') := g.below 200000
    g := g'
    let (b, g') := g.below 50
    g := g'
    cuts := (fun i => (a + 1) * (i % 7 + 1) % 200000 + b) :: cuts
  for sizes in cuts do
    let (got, most, ended, _) := readAll stream sizes
    t.ok "any cut of the stream gives back exactly its payloads" (got == payloads && !ended)
    t.ok "what is kept between reads is under one maximal frame and its length"
      (most < 4 + Engine.Sync.maxFrame)
  let small := (["x".toUTF8, "yz".toUTF8, .empty].foldl (fun s p => s ++ Engine.Sync.frame p) ByteArray.empty)
  t.ok "byte by byte too" ((readAll small fun _ => 1).1 == ["x".toUTF8, "yz".toUTF8, .empty])
  -- A peer whose length fields lie: past 1 MiB, the connection ends in
  -- the read that completes the length, after the frames before it.
  for len in [Engine.Sync.maxFrame + 1, 4294967295] do
    let lie := Engine.Sync.frame "hi".toUTF8 ++ Engine.Sync.be32 len ++ ⟨Array.replicate 300000 0⟩
    for step in [1, 3, 5, 65536] do
      let (got, most, ended, at_) := readAll lie fun _ => step
      t.ok s!"a length of {len} ends the connection" ended
      t.ok "after the frames before it" (got == ["hi".toUTF8])
      t.ok "in the read that completes the length" (at_ < 6 + 4 + step)
      t.ok "having kept less than a length" (most < 6 + 4)
  t.finish "wire"
