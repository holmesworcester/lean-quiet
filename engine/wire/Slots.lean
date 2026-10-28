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
  /-- Serve bytes in one native write, after the urgent frames (uiprio's
  `idleBatchBytes` on the send side). -/
  burst : Nat := 131072
  /-- Serve bytes a socket may hold queued: a session's queue of wants is
  served only while its socket's serve lane holds less (`Sync.room`). -/
  window : Nat := 4194304

/-- A peer's quota is its host, the port dropped from the address text
(Tcp.addrText): `a.b.c.d` of `a.b.c.d:port`, `[v6]` of `[v6]:port`, and
any other text whole. Bytes that are not UTF-8 share the quota "?". -/
def peerHost (addr : ByteArray) : String :=
  match String.fromUTF8? addr with
  | none => "?"
  | some s =>
    if s.startsWith "[" then (s.splitOn "]").headD s ++ "]"
    else match s.splitOn ":" with
      | [host, _] => host
      | _ => s

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
