/- Per-transition peaks for the real-node memory transport tests. -/
import tests.engine.HardenLib

open Engine Engine.Sync
namespace Harden

structure Peaks where
  known : Nat := 0
  asked : Nat := 0
  offered : Nat := 0
  closed : Nat := 0
  frontier : Nat := 0
  closure : Nat := 0
  snaps : Nat := 0
  askTime : Nat := 0
  cut : Bool := false
  deriving Repr

def Peaks.see (p : Peaks) (c : Conn) : Peaks :=
  { known := max p.known c.known.size, asked := max p.asked c.asked.size,
    offered := max p.offered c.offered.size, closed := max p.closed c.closed.size,
    frontier := max p.frontier c.frontier.length,
    closure := max p.closure (c.closed.size + c.frontier.length),
    snaps := max p.snaps c.snaps.length, askTime := max p.askTime c.askTime.size,
    cut := p.cut || c.closureCut }

def Peaks.node (p : Peaks) (n : Node) : Peaks := n.conns.foldl (fun p (_, c) => p.see c) p

end Harden
