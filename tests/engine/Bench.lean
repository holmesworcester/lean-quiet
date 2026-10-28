/-
Wall times of the byte codec on the paths a photo takes, on SQLite with
real Ed25519: build a 100-chunk attachment (its Merkle root, every
chunk's proof, the chunk ops), encode and decode one 64 KiB chunk op, validate one chunk
against its cited facts, ingest 100 chunk ops in one `receive`, and
decode a 48 KiB frame bundle (the bundle's list, then `Op.decode` of
each op in it). Then an adversarial input: numbers thousands of bytes
long. Each line is the mean over its repetitions. A checksum of every
result is printed, so no measured call is dead code.
-/
import tests.engine.Lib

open Engine Community Tests

def C := ed25519
def fam := family C

def fresh (dir name : String) : IO Db := do
  for suffix in ["", "-wal", "-shm"] do
    let p := dir ++ "/" ++ name ++ suffix
    if ← System.FilePath.pathExists p then IO.FS.removeFile p
  Db.openAt (dir ++ "/" ++ name)

/-- Nanoseconds as microseconds, to a tenth. -/
def usStr (ns : Nat) : String := s!"{ns / 1000}.{ns / 100 % 10} µs"

/-- Run f at least `minRuns` times and until 300 ms have passed (at
most `cap` times), after one run to warm up unless `minRuns` is 1;
print the mean per run, and fold each result into `sum`. -/
def bench (sum : IO.Ref Nat) (label : String) (f : Nat → IO Nat) (cap : Nat := 1000)
    (minRuns : Nat := 3) : IO Unit := do
  if minRuns > 1 then let _ ← f 0
  let t0 ← IO.monoNanosNow
  let mut n := 0
  let mut el := 0
  while n < minRuns || (el < 300000000 && n < cap) do
    let r ← f n
    sum.modify (· + r)
    n := n + 1
    el := (← IO.monoNanosNow) - t0
  IO.println s!"{label}: {usStr (el / n)}  ({n} runs)"

/-! The measured calls, each behind `noinline` with a run counter it
ignores, so the compiler can neither share one result across runs nor
with the setup's. -/

@[noinline] def encodeOp (o : Op) (_ : Nat) : Nat := o.bytes.size
@[noinline] def makeOp (o : Op) (_ : Nat) : Nat := (Op.make o.kind o.reqs o.body).id.size
@[noinline] def decodeOp (b : ByteArray) (_ : Nat) : Nat :=
  match Op.decode b with | some o => o.body.size | none => 0
@[noinline] def validateOp (o : Op) (fs : List Fact) (_ : Nat) : Nat :=
  match fam.validate o fs with | some _ => 1 | none => 0
@[noinline] def decodeBundle (b : ByteArray) (_ : Nat) : Nat :=
  match (Codec.decode b : Option (List ByteArray)) with
  | some bs => bs.foldl (fun n b => match Op.decode b with | some _ => n + 1 | none => n) 0
  | none => 0

/-- Attach file f: its root, every chunk's proof, and the chunk ops. -/
@[noinline] def attachFile (c : Id) (d : Device) (k : ByteArray) (f : NewFile) (_ : Nat) : Nat :=
  let (a, cs) := attach c c c d k f
  cs.foldl (fun n o => n + o.id.size) a.id.size

/-- n rows newest first, as each list of a union reads them. -/
def rowsDesc (n : Nat) : List (Pos × Fact) :=
  (List.range n).reverse.map fun i => ((Merkle.be64 i, sha256 (toString i).toUTF8), Fact.admin .empty .empty)

@[noinline] def sortRows (l : List (Pos × Fact)) (_ : Nat) : Nat := (sortPos l).length

/-- Read the union of c's messages under the keys this device holds,
all of them (`readable`, no limit), newest first. -/
@[noinline] def readAllMessages (db : Db) (c : Id) (_ : Nat) : IO Nat := do
  let a ← ((readable c (limit := none)).run : SqlM Fact (Answer Fact)).run db
  return a.rows.length

/-- One step's views for one community: the first profile, and the keys
wrapped to this device (both write nothing here). -/
@[noinline] def stepViews (db : Db) (c seed : ByteArray) (i : Nat) : IO Nat := do
  let w1 ← ((introduce c seed (i + 100)).run : SqlM Fact Write).run db
  let w2 ← ((unwrap c seed).run : SqlM Fact Write).run db
  return w1.ops.length + w2.ops.length

@[noinline] def deviceOf (seed : ByteArray) (_ : Nat) : Nat := (Device.ofSeed seed).enc.size

@[noinline] def decodeNat (b : ByteArray) (_ : Nat) : Nat :=
  match (Codec.decode b : Option Nat) with | some n => n % 7 | none => 0

/-- A number n bytes long: 0xFF n - 1 times, then 0x01. -/
def longNumber (n : Nat) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity n
  for _ in [0:n - 1] do b := b.push 0xFF
  return b.push 0x01

def main (args : List String) : IO UInt32 := do
  let dir := args.headD "out/bench"
  IO.FS.createDirAll dir
  let sum ← IO.mkRef 0
  let seedA := sha256 "device A".toUTF8
  let dA := Device.ofSeed seedA
  let kA := sha256 "Acme's content key".toUTF8
  let w := found seedA "Acme".toUTF8 "Ann".toUTF8 1 kA (sha256 "esk 1".toUTF8)
  let c := (root dA).id
  -- A file whose ciphertext (the plaintext and a 16-byte tag) is exactly
  -- 100 slices.
  let plain := ByteArray.mk ((Array.range (100 * Merkle.sliceSize - 16)).map
    fun i => (i * 7 + i / 300).toUInt8)
  let nf : NewFile := ⟨⟨"photo.qoi".toUTF8, "image/qoi".toUTF8, 640, 480, "tiny preview".toUTF8⟩, plain,
    sha256 "file key".toUTF8, (sha256 "file nonce".toUTF8).extract 0 24,
    (sha256 "info nonce".toUTF8).extract 0 24⟩
  let wf := send c c seedA kA ((sha256 "nonce 2".toUTF8).extract 0 24) "a photo".toUTF8 7 [nf]
  let chunks := wf.ops.drop 2
  bench sum s!"build a {chunks.length}-chunk attachment (attach: root, proofs, chunk ops)" (cap := 3)
    fun i => pure (attachFile c dA kA nf i)
  let o := chunks.headD default
  let bytes := o.bytes
  IO.println s!"one chunk op: {bytes.size} bytes"

  bench sum "encode one 64 KiB chunk op (Op.bytes)" fun i => pure (encodeOp o i)
  bench sum "make one 64 KiB chunk op (Op.make: encode, then SHA-256)" fun i => pure (makeOp o i)
  bench sum "decode one 64 KiB chunk op (Op.decode)" fun i => pure (decodeOp bytes i)

  -- The community, the post and the attachment on a fresh node: what a
  -- chunk cites.
  let db ← fresh dir "bench.db"
  let mine (ops : List Op) : IO Unit := (receive fam (intake fam true ops)).run db
  mine w.ops
  mine (wf.ops.take 2)
  let mut facts : List Fact := []
  for r in o.reqs do
    if let some (.valid f) ← ((Store.getStatus r : SqlM Fact _).run db) then facts := facts ++ [f]
  IO.println s!"a chunk cites {o.reqs.length} ops, {facts.length} of them Valid here"
  bench sum "validate one chunk (Family.validate)" fun i => pure (validateOp o facts i)

  let mut k := 0
  let mut el := 0
  let reps := 3
  for _ in [0:reps] do
    let db ← fresh dir s!"ingest{k}.db"
    (receive fam (intake fam true w.ops)).run db
    (receive fam (intake fam true (wf.ops.take 2))).run db
    let t ← IO.monoNanosNow
    (receive fam (intake fam false chunks)).run db
    el := el + ((← IO.monoNanosNow) - t)
    let mut valid := 0
    for x in chunks do
      if let some (.valid _) ← ((Store.getStatus x.id : SqlM Fact _).run db) then valid := valid + 1
    sum.modify (· + valid)
    if valid != chunks.length then
      IO.eprintln s!"FAIL: only {valid} of {chunks.length} chunks Valid"
      return 1
    k := k + 1
  IO.println s!"ingest {chunks.length} chunk ops into SQLite (receive): {usStr (el / reps)}  ({reps} runs, every chunk Valid)"

  -- A 48 KiB frame bundle: posts' bytes, as a session seals them.
  let mut payloads : Array ByteArray := #[]
  let mut size := 0
  let mut t := 100
  while size < 49152 do
    let p := (send c c seedA kA ((sha256 s!"nonce {t}".toUTF8).extract 0 24)
      s!"message {t}: {String.ofList (List.replicate 160 'x')}".toUTF8 t).ops.headD default
    if size + p.bytes.size > 49152 then break
    payloads := payloads.push p.bytes
    size := size + p.bytes.size
    t := t + 1
  let bundle := Codec.encode payloads.toList
  IO.println s!"one frame bundle: {payloads.size} ops, {bundle.size} bytes"
  bench sum "decode a 48 KiB frame bundle (the list, then Op.decode of each op)" fun i =>
    pure (decodeBundle bundle i)
  -- Adversarial: a body's number field can be as long as the op, and a
  -- bare frame's op is decoded (`scope`) before anything refuses it; a
  -- frame is at most 1 MiB (`Sync.maxFrame`).
  for n in [4096, 16384, 65536] do
    let b := longNumber n
    bench sum s!"decode a {n}-byte number (adversarial)" (cap := 3) fun i => pure (decodeNat b i)
  let b := longNumber Sync.maxFrame
  bench sum s!"decode a {Sync.maxFrame}-byte number (adversarial, one frame)" (cap := 1) (minRuns := 1)
    fun i => pure (decodeNat b i)
  -- Reads: a union merges its lists' rows by position (`sortPos`).
  bench sum "sortPos of 1,000 rows, newest first" fun i => pure (sortRows (rowsDesc 1000) i)
  let rdb ← fresh dir "reads.db"
  let mine (ops : List Op) : IO Unit := (receive fam (intake fam true ops)).run rdb
  mine w.ops
  let keys := [kA] ++ (List.range 3).map fun j => sha256 s!"key {j}".toUTF8
  mine (keys.drop 1 |>.map (contentKey c))
  let posts := (List.range 1000).map fun t =>
    (send c c seedA keys[t % 4]! ((sha256 s!"n {t}".toUTF8).extract 0 24) s!"message {t}".toUTF8 (t + 10)).ops.headD default
  mine posts
  let got ← readAllMessages rdb c 0
  IO.println s!"a union of {keys.length} keys' lists holds {got} messages"
  bench sum "read 1,000 messages: the union of 4 keys' lists on SQLite (readable, no limit)" (cap := 50)
    fun i => readAllMessages rdb c i
  -- A device from its seed: what the intents derived on every step.
  bench sum "Device.ofSeed (Ed25519 key pair, X25519 conversion)" fun i => pure (deviceOf seedA i)
  bench sum "one step's introduce and unwrap for one community, on SQLite" fun i => stepViews rdb c seedA i
  IO.println s!"checksum {← sum.get}"
  return 0
