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
  /-- Bytes a socket's lanes may hold before a session at its address
  is served more: a session's queue of wants is served only into what
  is left of this (`Sync.room`, `roomOf`). -/
  window : Nat := 4194304
  /-- Bytes a socket's lanes may hold, both of them: a push past this
  closes the socket (`Lanes.admit`). Serving stays under `window` and
  one op, so only a peer that takes nothing while asking for more, or
  for many of this node's fresh ops, reaches it. -/
  sockCap : Nat := 16777216
  /-- A writer's write not done in this many ms closes its socket: the
  peer took less than one write (urgent frames and `burst`) in that
  time. The writer stays on that write until the peer takes it or the
  connection dies, holding its slot, so `maxSocks` caps such writers. -/
  stallMs : Nat := 30000
  /-- How long `Runner.stop` waits for writers to end their write under
  way. -/
  stopMs : Nat := 1000

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
