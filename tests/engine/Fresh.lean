/-
T-fresh in simulated time: how long a fresh post takes to reach the
peer while a backlog of N attachment chunks syncs, as N grows, under
the runner's lanes and under the old order.

Two real nodes (SQLite in memory, the Community family, real 64 KiB
chunk ops of real attachments) share one session (plain sealing). Each
is run by a simulated runner that calls the runner's own pure parts:
- **lanes** (Tcp.lean today): local writes first (`Inbox.next`); a
  step's frames pushed onto the socket's `Lanes` (`laned`,
  `framesFor`, `Lanes.pushAll`) and drained by its writer one
  `Lanes.take` at a time, whenever the kernel has room; a frame's wants
  answered within `credit`;
- **old** (before this branch): one FIFO channel for writes and frames,
  and the loop waiting until each step's frames are all in the kernel.
The link carries `bw` bytes per µs after `delay`, from a kernel send
buffer of `sndbuf` bytes, into the receiver's event queue of `queue`
frames; while that is full, nothing more arrives and at most `rcvbuf`
bytes wait (TCP's flow control). A step costs `perEvent`, plus
`perOp` per op it stores, plus `perKiB` per KiB it sends.

Two scenarios: the node sending the backlog writes the post (send), and
the node receiving it does (recv), once the receiver holds half the
backlog's chunks. Latency is from the write to the peer storing the
post. Under lanes it must stay within `bound` (`fresh_stmt`'s
3(Δ + (sndbuf + burst + frame)/bw), plus each side's processing) and
flat in N; in the old order it grows with N.
-/
import tests.engine.Lib

open Engine Engine.Sync Community Tests

def C := ed25519
def fam := family C

/-- The link, the costs and the runner's settings (µs and bytes). -/
structure Sim where
  bw : Nat := 2
  delay : Nat := 10000
  sndbuf : Nat := 262144
  rcvbuf : Nat := 262144
  queue : Nat := 64
  perEvent : Nat := 100
  perOp : Nat := 500
  perKiB : Nat := 10
  tick : Nat := 200000
  burst : Nat := 131072
  window : Nat := 4194304
  /-- The step of simulated time. -/
  dt : Nat := 1000

inductive Order where
  | lanes
  | old
  deriving BEq

inductive Ev where
  | write (ops : List Op)
  | frame (b : ByteArray)

/-- One direction of the link: frames in the sender's kernel (the first
`head` bytes of the first already sent), then on the wire with their
arrival times. -/
structure Link where
  kernel : List ByteArray := []
  head : Nat := 0
  wire : List (Nat × ByteArray) := []

def Link.queued (l : Link) : Nat := bytesOf l.kernel - l.head
def Link.onWire (l : Link) : Nat := bytesOf (l.wire.map (·.2))

/-- A node and its runner's queues. -/
structure Box where
  side : Side
  writes : List (List Op) := []
  /-- Frames read from the socket (and, in the old order, writes), in order. -/
  inbox : List Ev := []
  /-- Frames waiting for the writer; in the old order, the frames the
  loop is still waiting to hand the kernel. -/
  lanes : Lanes := {}
  free : Nat := 0
  lastTick : Nat := 0

def Box.frames (b : Box) : Nat := (b.inbox.filter fun | .frame _ => true | _ => false).length

structure Run where
  a : Box
  b : Box
  ab : Link := {}
  ba : Link := {}
  now : Nat := 0
  /-- When the post was written, and when the peer stored it. -/
  wrote : Option Nat := none
  got : Option Nat := none
  /-- Most serve bytes queued at a socket, and chunk ops stored by b. -/
  peakServe : Nat := 0
  chunksAtB : Nat := 0

section
variable (sim : Sim) (order : Order) (x : Sync Fact (SqlM Fact))

/-- Move the link on by one step: bytes leave the kernel at `bw` while
the receiver's buffer has room; frames arrive after `delay`, into the
receiver's queue while it has room. -/
def Link.step (l : Link) (to : Box) (now : Nat) : Link × Box := Id.run do
  let mut l := l
  let mut to := to
  -- arrivals
  while true do
    match l.wire with
    | (t, f) :: rest =>
      if t ≤ now && to.frames < sim.queue then
        to := { to with inbox := to.inbox ++ [.frame f] }
        l := { l with wire := rest }
      else break
    | [] => break
  -- transmission
  let mut budget := sim.bw * sim.dt
  while budget > 0 && l.onWire < sim.rcvbuf do
    match l.kernel with
    | f :: rest =>
      let left := f.size + 4 - l.head
      if left ≤ budget then
        budget := budget - left
        l := { l with kernel := rest, head := 0, wire := l.wire ++ [(now + sim.delay, f)] }
      else
        l := { l with head := l.head + budget }
        budget := 0
    | [] => break
  return (l, to)

/-- What the box's writer hands its kernel: under lanes, a native write
(`Lanes.take`) whenever the kernel has room; in the old order, the
loop's frames as the kernel takes them. -/
def Box.write (b : Box) (l : Link) : Box × Link := Id.run do
  let mut b := b
  let mut l := l
  for _ in [0:10000] do
    if l.queued ≥ sim.sndbuf || b.lanes.isEmpty then break
    match order with
    | .lanes =>
      let (fs, q) := b.lanes.take sim.burst
      b := { b with lanes := q }
      l := { l with kernel := l.kernel ++ fs }
    | .old =>
      match b.lanes.serve with
      | f :: rest =>
        b := { b with lanes := { b.lanes with serve := rest } }
        l := { l with kernel := l.kernel ++ [f] }
      | [] => break
  return (b, l)

/-- A step's frames onto the box's queue (one socket: the peer's). -/
def Box.out (b : Box) (e : Effects) : Box :=
  match order with
  | .lanes =>
    { b with lanes := b.lanes.pushAll (framesFor (fun _ => some 0) 0 (laned e.send e.serve)) }
  | .old => { b with lanes := { b.lanes with serve := b.lanes.serve ++ e.send.map (·.2) } }

def cost (e : Effects) : Nat :=
  sim.perEvent + sim.perOp * e.stored.length + sim.perKiB * bytesOf (e.send.map (·.2)) / 1024

/-- The box's loop, if free: its next event, then the clock. -/
def Box.loop (b : Box) (peer : ByteArray) (now : Nat) : IO (Box × List Id) := do
  -- In the old order the loop waits until its last step's frames are in the kernel.
  if now < b.free || (order == .old && !b.lanes.isEmpty) then return (b, [])
  let ms := now / 1000
  let mut b := b
  let mut stored : List Id := []
  let next : Option Ev ← match order with
    | .lanes =>
      let r := (Inbox.next popW popE).run (b.writes, b.inbox.filterMap fun | .frame f => some f | _ => none)
      b := { b with writes := r.2.1, inbox := r.2.2.map .frame }
      pure (r.1.map fun | .inl w => .write w | .inr f => .frame f)
    | .old =>
      match b.inbox with
      | e :: rest => b := { b with inbox := rest }; pure (some e)
      | [] => pure none
  let mut spent := 0
  match next with
  | some (.write ops) =>
    let (s, e) ← b.side.run fun n => n.onWrite x ops ms
    b := { b.out order e with side := s }
    stored := stored ++ e.stored
    spent := spent + cost sim e
  | some (.frame f) =>
    let x' := match order with
      | .lanes => { x with cfg := { x.cfg with wantBytes := credit sim.window x.cfg.wantBytes b.lanes.queued } }
      | .old => x
    let (s, e) ← b.side.run fun n => n.onFrame x' peer f ms
    b := { b.out order e with side := s }
    stored := stored ++ e.stored
    spent := spent + cost sim e
  | none => pure ()
  if now ≥ b.lastTick + sim.tick then
    let (s, e) ← b.side.run fun n => n.onTick x ms
    b := { b.out order e with side := s, lastTick := now }
    stored := stored ++ e.stored
    spent := spent + cost sim e
  return ({ b with free := now + spent }, stored)

end

/-- A file whose ciphertext is `slices` slices (at most 1024). -/
def fileOf (i slices : Nat) : NewFile :=
  let n := slices * Merkle.sliceSize - 16
  let plain := Id.run do
    let mut b := ByteArray.emptyWithCapacity n
    for j in [0:n] do b := b.push ((j * 7 + i * 13 + j / 300) % 256).toUInt8
    return b
  ⟨⟨s!"f{i}".toUTF8, "application/octet-stream".toUTF8, 0, 0, .empty⟩, plain,
    sha256 s!"file key {i}".toUTF8, (sha256 s!"file nonce {i}".toUTF8).extract 0 24,
    (sha256 s!"meta nonce {i}".toUTF8).extract 0 24⟩

structure Fixture where
  c : Id
  base : List Op
  /-- Each file's post and attachment, and its chunks. -/
  files : List (List Op × List Op)
  post : Op

/-- A community, files of 1000 chunks (the last shorter) making `n`
chunks in all, and a fresh post. -/
def fixture (n : Nat) : Fixture := Id.run do
  let seed := sha256 "fresh founder".toUTF8
  let d := Device.ofSeed seed
  let k := sha256 "fresh content key".toUTF8
  let w := found seed "Fresh".toUTF8 "Ann".toUTF8 1 k (sha256 "fresh esk".toUTF8)
  let c := (root d).id
  let mut files := []
  for i in [0:(n + 999) / 1000] do
    let p := sealedPost c c d k ((sha256 s!"post nonce {i}".toUTF8).extract 0 24) s!"file {i}".toUTF8 (i + 1) (10 + i)
    let (a, cs) := attach c c p.id d k (fileOf i (min 1000 (n - 1000 * i)))
    files := files ++ [([p, a], cs)]
  let post := sealedPost c c d k ((sha256 "fresh post nonce".toUTF8).extract 0 24) "fresh".toUTF8 1000 100000
  return { c, base := w.ops, files, post }

/-- The first n chunks, with their files' posts and attachments. -/
def Fixture.backlog (fx : Fixture) (n : Nat) : List Op := Id.run do
  let mut out := []
  let mut left := n
  for (head, cs) in fx.files do
    if left == 0 then break
    out := out ++ head ++ cs.take left
    left := left - min left cs.length
  return out

def side (x : Sync Fact (SqlM Fact)) (ops : List Op) (addr : String) : IO Side := do
  let db ← Db.openAt ":memory:"
  (receive fam (intake fam true ops)).run db
  return { db, node := Node.boot x.fam (← (dumpOps (F := Fact)).run db) 0, addr := addr.toUTF8 }

def sync (rooms : List Id) : Sync Fact (SqlM Fact) :=
  { fam, cfg := { every := 30000, patience := 20000 },
    hooks := { rooms := fun _ => pure rooms, sealFor := plainSeal, openFrame := plainOpen } }

/-- Which node writes the post: the one sending the backlog (a), or the
one receiving it (b). -/
inductive Writer where
  | send
  | recv

/-- One run: a holds n chunks b lacks; a dials b; the post is written
once b holds n / 2 of them. Until the peer stores it, or `limit` µs. -/
def runOnce (sim : Sim) (order : Order) (fx : Fixture) (n : Nat) (writer : Writer) (limit : Nat) :
    IO Run := do
  let x := sync [fx.c]
  let chunks : Std.HashSet Id := Std.HashSet.ofList ((fx.backlog n).map (·.id))
  let a ← side x (fx.base ++ fx.backlog n) "a"
  let b ← side x fx.base "b"
  let cid := sha256 "fresh session".toUTF8
  let (sa, ea) ← a.run fun nd => nd.connect x cid "b".toUTF8 true 0
  let (sb, eb) ← b.run fun nd => nd.connect x cid "a".toUTF8 false 0
  let mut r : Run := { a := Box.out order { side := sa } ea, b := Box.out order { side := sb } eb }
  let mut t := 0
  while t ≤ limit && r.got.isNone do
    if 2 * r.chunksAtB ≥ n && r.wrote.isNone then
      let w := [fx.post]
      let put (bx : Box) : Box := match order with
        | .lanes => { bx with writes := bx.writes ++ [w] }
        | .old => { bx with inbox := bx.inbox ++ [.write w] }
      r := match writer with
        | .send => { r with a := put r.a, wrote := some t }
        | .recv => { r with b := put r.b, wrote := some t }
    let (ab, rb) := r.ab.step sim r.b t
    let (ba, ra) := r.ba.step sim r.a t
    let (ra, ab) := ra.write sim order ab
    let (rb, ba) := rb.write sim order ba
    let (ra, gotA) ← ra.loop sim order x "b".toUTF8 t
    let (rb, gotB) ← rb.loop sim order x "a".toUTF8 t
    let got := match writer with
      | .send => gotB.contains fx.post.id
      | .recv => gotA.contains fx.post.id
    r := { r with
      a := ra, b := rb, ab := ab, ba := ba, now := t
      got := if got then some t else r.got
      peakServe := max r.peakServe (max ra.lanes.queued rb.lanes.queued)
      chunksAtB := r.chunksAtB + (gotB.filter chunks.contains).length }
    t := t + sim.dt
  return r

def ms (us : Nat) : String := s!"{us / 1000}.{us / 100 % 10} ms"

def main (args : List String) : IO UInt32 := do
  let t ← Checks.new
  let sizes := match args.head? >>= String.toNat? with
    | some n => [100, n]
    | none => [100, 500, 1000, 2000, 5000]
  let sim : Sim := {}
  let fx := fixture (sizes.foldl max 0)
  -- What may queue ahead of each of the three hops' frames: the kernel's
  -- buffer and one native write (a burst, or one chunk's frame).
  let frame := 70000
  let bound := 3 * (sim.delay + (sim.sndbuf + max sim.burst frame) / sim.bw) + 100000
  IO.println s!"fixture: {fx.files.length} files, {(fx.files.map (·.2.length)).sum} chunks"
  let mut table : List (String × Nat × Nat) := []
  let mut peaks : List (String × Nat × Nat) := []
  for writer in [Writer.send, .recv] do
    let wname := match writer with | .send => "send" | .recv => "recv"
    for order in [Order.lanes, .old] do
      let oname := if order == .lanes then "lanes" else "old"
      for n in sizes do
        let r ← runOnce sim order fx n writer 600000000
        let lat := match r.wrote, r.got with
          | some w, some g => g - w
          | _, _ => 600000000
        IO.println s!"{wname} {oname} N={n}: latency {ms lat}; peak serve queue {r.peakServe} B; b stored {r.chunksAtB} ops"
        table := table ++ [(s!"{wname} {oname}", n, lat)]
        peaks := peaks ++ [(s!"{wname} {oname}", n, r.peakServe)]
  let lat (k : String) (n : Nat) : Nat := ((table.find? fun (k', n', _) => k' == k && n' == n).map (·.2.2)).getD 0
  let peak (k : String) (n : Nat) : Nat := ((peaks.find? fun (k', n', _) => k' == k && n' == n).map (·.2.2)).getD 0
  let lo := sizes.headD 100
  let hi := sizes.foldl max 0
  for w in ["send", "recv"] do
    for n in sizes do
      t.ok s!"{w}: under lanes the post arrives within {ms bound} at N={n} ({ms (lat s!"{w} lanes" n)})"
        (lat s!"{w} lanes" n ≤ bound)
    t.ok s!"{w}: under lanes the latency stays flat ({ms (lat s!"{w} lanes" lo)} at N={lo}, {ms (lat s!"{w} lanes" hi)} at N={hi})"
      (2 * lat s!"{w} lanes" hi ≤ 3 * lat s!"{w} lanes" lo + 200000)
    -- The old order's wait is the 4 MiB want answers queued ahead of the
    -- post (the round's, then the receiver's retries), so it grows with
    -- the backlog, though not smoothly.
    for n in sizes.filter (· != lo) do
      t.ok s!"{w}: in the old order it grows with N ({ms (lat s!"{w} old" lo)} at N={lo}, {ms (lat s!"{w} old" n)} at N={n})"
        (lat s!"{w} old" n ≥ 2 * lat s!"{w} old" lo)
    for n in sizes do
      t.ok s!"{w}: a socket's serve lane stays within its window and one op at N={n}"
        (peak s!"{w} lanes" n ≤ sim.window + frame)
    for n in sizes do
      t.ok s!"{w}: the old order waits at least 10 times longer than lanes at N={n}"
        (lat s!"{w} old" n ≥ 10 * lat s!"{w} lanes" n)
  let code ← t.finish "fresh"
  (← IO.getStdout).flush
  IO.Process.exit code.toUInt8
