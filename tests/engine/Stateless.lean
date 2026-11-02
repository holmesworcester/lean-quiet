/-
Full and windowed syncs through real Nodes, SQLite and memory frames.
A windowed round reconciles its window and the window's requirements
within `params.depth` steps (S): depth 1 brings every reaction's post in
the round; depth 0, the window alone, leaves the reactions Missing.
Every decided verdict must still agree with the peer.
-/
import tests.engine.BigSync
import tests.engine.StatelessBook
import tests.engine.Lib
import engine.wire.Pair

open Engine Engine.Sync Tests Community

namespace Stateless

def fam := Community.family ed25519

def history (count : Nat) : List Op × Id := Id.run do
  let d := Device.named "closure-founder"
  let r := root d (Tests.keyOf d) "k".toUTF8
  let old := (List.range count).map fun i => post r.id r.id d "k".toUTF8 s!"old-{i}".toUTF8 i (100 + i)
  let recent := old.zipIdx |>.map fun (o, i) => react r.id r.id o.id d "+1".toUTF8 (172800000 + i)
  return (r :: old ++ recent, r.id)

def side (ops : List Op) (floor : Nat) (addr : String) : IO Side := do
  let db ← Db.openAt ":memory:"
  (receive fam (intake fam true ops)).run db
  return { db, node := Node.boot fam (← (dumpOps (F := Fact)).run db) floor, addr := addr.toUTF8 }

def windowChecks (t : Checks) (count depth : Nat) (cut : Bool) : IO Unit := do
  let (ops, room) := history count
  let cfg : Config := { params := { depth }, maxKnown := 128, maxIds := 16 }
  let x : Sync Fact (SqlM Fact) := { fam, cfg, hooks := { rooms := fun _ => pure [.sync room], sealFor := plainSeal, openFrame := plainOpen } }
  let p : Pair := { a := ← side ops 0 "a", b := ← side [] 86400000 "b", cid := sha256 "stateless-window".toUTF8 }
  let mut p ← p.connect x x
  let mut peaks : Harden.Peaks := {}
  for _ in [0:10000] do
    peaks := (peaks.node p.a.node).node p.b.node
    if p.now ≥ 20000 then break
    p ← p.step x x 100
  peaks := (peaks.node p.a.node).node p.b.node
  let stored ← (dumpOps (F := Fact)).run p.b.db
  let ids := stored.map (·.id)
  let window := ops.filter fun o => fam.order o == 0 || fam.order o ≥ 86400000
  t.ok s!"window depth {depth}: whole window delivered" (window.all fun o => ids.contains o.id)
  t.ok s!"window depth {depth}: hints and rounds stay bounded" (peaks.offered ≤ cfg.maxKnown && peaks.active ≤ 1)
  let mut missing := 0
  let mut decided := 0
  let mut agree := true
  for o in stored do
    let a ← (Store.getStatus o.id : SqlM Fact _).run p.a.db
    let b ← (Store.getStatus o.id : SqlM Fact _).run p.b.db
    match b with
    | none =>
      missing := missing + 1
      -- Missing is caused by an absent required old post, never a wrong verdict.
      agree := agree && o.reqs.any (fun i => !ids.contains i) && a.isSome
    | some _ => decided := decided + 1; agree := agree && a == b
  t.ok s!"window depth {depth}: every decided verdict agrees; incomplete ops are Missing" agree
  if cut then
    t.ok "depth 0: the window alone, its reactions Missing" (stored.length == window.length && missing > 0)
  else
    t.ok "depth 1: the window and its whole closure, every verdict decided"
      (stored.length == ops.length && ops.all (fun o => ids.contains o.id) && missing == 0)
  IO.println s!"window count={count} depth={depth}: held={stored.length}/{ops.length}, decided={decided}, missing={missing}, frames={p.frames}, peaks={repr peaks}"

end Stateless

def main (args : List String) : IO UInt32 := do
  let t ← Checks.new
  let count := (args[0]?.bind String.toNat?).getD 5000
  Harden.bookChecks t
  Harden.bigSyncChecks t count 256
  Stateless.windowChecks t 40 1 false
  Stateless.windowChecks t 40 0 true
  t.finish "stateless"
