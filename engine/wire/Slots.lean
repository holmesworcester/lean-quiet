/-
Socket reservations shared by the listener, dialers and runner. A slot
is acquired before queueing an accepted socket or starting a dial, and
released exactly once when that socket leaves the runner.
-/
import Std.Sync.Mutex

namespace Engine.Sync

structure RunConfig where
  tickMs : Nat := 200
  idle : Nat := 600000
  queue : Nat := 64
  perAddr : Nat := 4
  maxSocks : Nat := 64

/-- The port is not part of a peer's quota. IPv6's current textual
placeholder groups IPv6 peers conservatively in one quota. -/
def peerHost (addr : ByteArray) : String :=
  ((String.fromUTF8! addr).splitOn ":").headD "?"

def admit (cfg : RunConfig) (peers : List String) (peer : String) : Bool :=
  peers.length < cfg.maxSocks && (peers.filter (· == peer)).length < cfg.perAddr

abbrev Slots := Std.Mutex (List String)

def Slots.take (slots : Slots) (cfg : RunConfig) (addr : ByteArray) : IO Bool :=
  slots.atomically do
    let peers ← get
    let peer := peerHost addr
    if admit cfg peers peer then
      set (peer :: peers)
      return true
    return false

def Slots.release (slots : Slots) (addr : ByteArray) : IO Unit :=
  slots.atomically do modify (·.erase (peerHost addr))

end Engine.Sync

namespace Engine.Sync
/-- Successful admission leaves room for exactly this socket, both in
all sockets and in the address's quota. Reservations use this predicate. -/
theorem admit_bounded (cfg : RunConfig) (peers : List String) (peer : String)
    (h : admit cfg peers peer = true) :
    (peer :: peers).length ≤ cfg.maxSocks ∧
      ((peer :: peers).filter (· == peer)).length ≤ cfg.perAddr := by
  simp only [admit, Bool.and_eq_true, decide_eq_true_eq] at h
  simp
  omega
end Engine.Sync
