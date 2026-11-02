/- Run the RBSR answer/exchange code used by Conn.onRbsr on non-leaf
histories at the proved logarithmic depth. This is a one-round check,
not a claim of delivery or many-node liveness. -/
import engine.sync.Conn
import tests.engine.Checks

open Engine Engine.Sync Tests

namespace ClaimTree

def key (n : Nat) : Key := ⟨n, n⟩
def ident (n : Nat) : ByteArray := (toString n).toUTF8

def check (ck : Checks) (P : Params) (n depth : Nat) : IO Unit := do
  let xs := (List.range n).map (· * 2)
  let ys := (List.range n).map (· * 3)
  let r : Range := ⟨⟨0, 0⟩, none⟩
  let claim := opening key ident sha256 P ys r
  let (give, want) := exchange key ident sha256 P depth xs ys claim
  let missingY := (xs.filter fun x => !ys.contains x).map ident
  let missingX := (ys.filter fun y => !xs.contains y).map ident
  let same := fun (a b : List ByteArray) => a.length == b.length && a.all b.contains && b.all a.contains
  ck.ok s!"non-leaf {n}: logarithmic depth gives exactly the missing ids" (same give missingY && same want missingX)
  let deeper := exchange key ident sha256 P (depth + 3) xs ys claim
  ck.ok s!"non-leaf {n}: deeper exchange is stable" (deeper == (give, want))
  ck.ok s!"non-leaf {n}: opening really is a fingerprint" (match claim with | .fp .. => true | _ => false)

/-- Relay the actual handler's encoded wire ops, including its terminal
marker. Both indices change after the first hop: an op written at both
ends mid-round, which the live answers then read. An op both ends hold
is never offered or wanted; the start's differences are covered exactly. -/
def handlers (ck : Checks) (n : Nat) : IO Unit := do
  let room := "claim-tree-room".toUTF8
  let xs := (List.range n).map (· * 2)
  let ys := (List.range n).map (· * 3)
  let items := fun ns => ns.map fun j => (key j, ident j)
  let ixA : Index := { rooms := [(room, RoomTree.ofList (items xs))] }
  let ixB : Index := { rooms := [(room, RoomTree.ofList (items ys))] }
  let cfg : Config := { params := { leaf := 4, fan := 4 }, maxIds := 7 }
  let mut a : Conn := { dialer := false, floor := 0, rooms := [room] }
  let b : Conn := { dialer := true, floor := 0, rooms := [room], peerFloor := some 0 }
  let opened := b.start cfg ixB 0
  let mut b := opened.conn
  let mut pending := opened.send
  let mut toA := true
  let mut sentA : List Op := []
  let mut sentB : List Op := []
  let mut hops := 0
  let mut ended := false
  let late := (key (n * 100 + 1), "written at both ends mid-round".toUTF8)
  for now in [1:2 * n + 10] do
    let some wire := pending.head? | break
    let some op := Op.decode wire.bytes | ck.ok "handler wire decodes" false; break
    let some (.rbsr r k cs) := Msg.ofOp op | ck.ok "handler successor is a round batch" false; break
    let ixA' := if hops == 0 then ixA else { rooms := [(room, RoomTree.ofList (items xs ++ [late]))] }
    let ixB' : Index := { rooms := [(room, RoomTree.ofList (items ys ++ [late]))] }
    let step := if toA then a.onRbsr cfg ixA' r k cs now else b.onRbsr cfg ixB' r k cs now
    if toA then a := step.conn; sentA := sentA ++ step.send
    else b := step.conn; sentB := sentB ++ step.send
    pending := step.send.take 1
    hops := hops + 1
    toA := !toA
    if cs.isEmpty then ended := true; break
  let holds := fun ops => ops.flatMap fun o => match Msg.ofOp o with | some (.hold _ ids) => ids | _ => []
  let wants := fun ops => ops.flatMap fun o => match Msg.ofOp o with | some (.want ids) => ids | _ => []
  let same := fun (as_ bs : List Id) => as_.all bs.contains && bs.all as_.contains
  ck.ok s!"actual handlers {n}: terminal delivered and no round left in flight"
    (ended && a.active.isEmpty && b.active.isEmpty && hops > 2)
  ck.ok s!"actual handlers {n}: A's wire offers and B's requests cover exactly A's difference"
    (same (holds sentA ++ wants sentB) ((xs.filter fun x => !ys.contains x).map ident))
  ck.ok s!"actual handlers {n}: B's wire offers and A's requests cover exactly B's difference"
    (same (holds sentB ++ wants sentA) ((ys.filter fun y => !xs.contains y).map ident))
  ck.ok s!"actual handlers {n}: an op both ends hold mid-round is neither offered nor wanted"
    (!(holds sentA ++ wants sentA ++ holds sentB ++ wants sentB).contains late.2)

end ClaimTree

def main : IO UInt32 := do
  let ck ← Checks.new
  ClaimTree.check ck { leaf := 4, fan := 4 } 64 6
  ClaimTree.check ck { leaf := 4, fan := 4 } 256 8
  ClaimTree.check ck {} 512 4
  ClaimTree.handlers ck 64
  ClaimTree.handlers ck 256
  ck.finish "claim-tree"
