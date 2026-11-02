/- Per-transition peaks for the real-node memory transport tests. -/
import tests.engine.HardenLib

open Engine Engine.Sync
namespace Harden

structure Peaks where
  known : Nat := 0
  asked : Nat := 0
  offered : Nat := 0
  active : Nat := 0
  askTime : Nat := 0
  deriving Repr

def Peaks.see (p : Peaks) (c : Conn) : Peaks :=
  { known := max p.known c.known.size, asked := max p.asked c.asked.size,
    offered := max p.offered c.offered.size,
    active := max p.active c.active.length, askTime := max p.askTime c.askTime.size }

def Peaks.node (p : Peaks) (n : Node) : Peaks := n.conns.foldl (fun p (_, c) => p.see c) p

end Harden
