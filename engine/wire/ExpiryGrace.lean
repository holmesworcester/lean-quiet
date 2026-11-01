/- A single bounded selection opportunity for input admitted before silence
expiry. Pending bytes do not renew an episode; only the handled-input token
can start a different episode. Native authenticated sessions use Conn.heard. -/
namespace Engine.Sync.ExpiryGrace

structure State where
  heard : Nat
  left : Nat
  deriving DecidableEq, BEq, Repr

/-- Every subsequent primary selection consumes one unit, never underflows. -/
def consume (s : State) : State := { s with left := s.left - 1 }

/-- The same heard generation reuses its remaining budget, even at zero.
A no-longer-overdue connection needs no grace. An empty mailbox never delays
expiry. The returned state remembers exhausted episodes until real progress
or closure, so incoming junk cannot rearm one. -/
def check (budget heard : Nat) (overdue pending : Bool) (old : Option State) :
    Bool × Option State :=
  if !overdue then (false, none) else
    let state := match old with
      | some s => if s.heard == heard then s else ⟨heard, budget⟩
      | none => ⟨heard, budget⟩
    (pending && state.left != 0, some state)

/-- The exact prioritized source-service bound used by native ingress. -/
def budget (maxSocks : Nat) : Nat := 4 * (maxSocks + 1)

end Engine.Sync.ExpiryGrace
