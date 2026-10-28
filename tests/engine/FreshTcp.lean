/-
T-fresh over real TCP, through the runner (`Runner`): a peer that never
reads holds up no one else.

Node R holds 64 ops of 512 KiB in one room. A raw client S opens a
session with R (plain sealing), asks for all of them in eight wants of
4 MiB, one frame each, and never reads: its socket's buffers fill, and
R's writer for it waits forever. Meanwhile node P syncs the room from
R, and R's app writes a small op.
- P gets all 64 ops: R's loop never waits on S's socket;
- P gets R's write within 2 s of it, with the backlog still flowing
  to P.
Before lanes (`sendOn` in the loop) R's loop stops at S's first full
buffer, and P gets nothing (tests/engine/fresh_negative.py).
-/
import tests.engine.HardenLib

open Engine Engine.Sync Tests Std.Async Std.Net

namespace FreshTcp

def room : ByteArray := "room".toUTF8

/-- A data op of the room, 512 KiB. -/
def blob (i : Nat) : Op :=
  Op.make 1 [room] (ByteArray.mk (Array.replicate 524288 (i % 251).toUInt8) ++ s!"blob {i}".toUTF8)

/-- A session: a local op, named by tag. -/
def sess (tag : String) : Op := Op.make 200 [] tag.toUTF8

def setup (est : IO.Ref (List (Id × ByteArray × Bool))) : Sync Nat (SqlM Nat) :=
  { fam := Harden.fam, cfg := { every := 1000 }, hooks := {
      rooms := fun _ => pure [room]
      established := est.get
      sealFor := plainSeal, openFrame := plainOpen } }

/-- A session's frame under the plain seal, framed for the socket. -/
def frameOf (cid : Id) (payloads : List ByteArray) : ByteArray :=
  frame (tagged sealedTag (Codec.encode (cid, Codec.encode payloads)))

end FreshTcp

open FreshTcp in
def main : IO UInt32 := do
  let t ← Checks.new
  let blobs := (List.range 64).map blob
  let sS := sess "stuck"
  let sP := sess "peer"
  let dr ← Db.openAt ":memory:"
  let dp ← Db.openAt ":memory:"
  (Turn.turn Harden.fam ([sS, sP] ++ blobs) : SqlM Nat Unit).run dr
  (Turn.turn Harden.fam [sP] : SqlM Nat Unit).run dp
  let estR ← IO.mkRef ([] : List (Id × ByteArray × Bool))
  let estP ← IO.mkRef ([] : List (Id × ByteArray × Bool))
  let got ← IO.mkRef ([] : List (Id × Nat))
  let rr ← Runner.start (setup estR) dr 0 0
  let rp ← Runner.start (setup estP) dp 0 0
    (notify := fun ids => do
      let now ← IO.monoMsNow
      got.modify (· ++ ids.map (·, now)))
  -- S: connects to R and never reads.
  let s ← TCP.Socket.Client.mk
  match ← awaitUv (s.native.connect (.v4 ⟨IPv4Addr.ofParts 127 0 0 1, rr.port⟩)) with
  | .error e => throw e
  | .ok _ => pure ()
  let sAddr := addrText (← s.getSockName)
  estR.set [(sS.id, sAddr.toUTF8, false)]
  IO.sleep 600
  let wants := (List.range 8).map fun k => (Msg.want ((blobs.drop (8 * k)).take 8 |>.map (·.id))).op.bytes
  let hello := (Msg.hello 0).op.bytes
  let bytes := frameOf sS.id [hello] :: wants.map fun w => frameOf sS.id [w]
  match ← awaitUv (s.native.send bytes.toArray) with
  | .error e => throw e
  | .ok _ => pure ()
  IO.sleep 1000
  -- P syncs from R while R's writer for S waits forever.
  estR.set [(sS.id, sAddr.toUTF8, false), (sP.id, s!"127.0.0.1:{rp.port}".toUTF8, false)]
  estP.set [(sP.id, s!"127.0.0.1:{rr.port}".toUTF8, true)]
  let ids := blobs.map (·.id)
  let count : IO Nat := do return ((← got.get).filter fun p => ids.contains p.1).length
  for _ in [0:300] do
    if (← count) ≥ 8 then break
    IO.sleep 20
  -- R's app writes while the backlog flows to P.
  let fresh := Op.make 1 [room] "fresh".toUTF8
  let before ← count
  let wrote ← IO.monoMsNow
  rr.write [fresh]
  let mut arrived : Option Nat := none
  for _ in [0:600] do
    if let some (_, at_) := (← got.get).find? (·.1 == fresh.id) then
      arrived := some at_
      break
    IO.sleep 10
  let backlogLeft := 64 - before
  IO.println s!"fresh_tcp: P held {before} of 64 when R wrote; the write arrived in {arrived.map (· - wrote)} ms"
  t.ok "P syncs while S never reads: some of the backlog arrives" (before ≥ 8)
  t.ok "R's write reaches P within 2 s, the backlog still flowing" (arrived.any (· ≤ wrote + 2000) && backlogLeft > 0)
  for _ in [0:3000] do
    if (← count) ≥ 64 then break
    IO.sleep 20
  t.ok "P gets all 64 ops while S never reads" ((← count) == 64)
  closeSocket s
  rp.stop
  rr.stop
  let code ← t.finish "fresh_tcp"
  (← IO.getStdout).flush
  IO.Process.exit code.toUInt8
