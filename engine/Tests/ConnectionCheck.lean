/-
The connection family end to end, on two (or three) SQLite nodes driven
through holmes-a3's Node over a lossy in-memory wire. Real Ed25519,
X25519 and ChaCha20-Poly1305.

SKELETON: each test is named and skipped. Each one becomes a real check
as its part lands, and none may stay skipped when the family is called
done.
-/
import Tests.Lib


open Tests

def skipped : List String := [
  "members: A dials B; both hold one established session with the same id and hash, crossed keys",
  "members: sealed frames carry sync both ways; tampered frames are dropped",
  "join: B pastes A's link and dials; A opens the request and delivers B's join request, and writes no connection and no courier back",
  "join: A's user approves; A answers B's next dial, both establish, and sync admits B",
  "join: the request survives every loss pattern of the lossy wire, and bootstrap still completes",
  "wire: a tampered request is never opened, and a tampered connection is never established",
  "wire: a request to another device's key is stored, but never opened",
  "wire: local ops (eph, opened, established, send, recv) sent bare or on a session are never taken",
  "close: after a close, no eph, opened, established or settled op of the session is stored",
  "close: the closed session's ephemeral secrets and keys appear nowhere in the database file's bytes",
  "close: a replayed request after a close gets a fresh connection id, and the initiator cannot establish it",
  "outbox: every courier is handed out once and then purged; the outbox drains to empty",
  "recv: every op taken has its arrival recorded (via, address, time)",
  "dial: an unanswered dial is resent every tick; once established it stops"
]

def main : IO UInt32 := do
  for s in skipped do IO.println s!"SKIP {s}"
  IO.println s!"connection_check: {skipped.length} skipped (skeleton)"
  return 0
