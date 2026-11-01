/-
Session phases and their only transitions. A connection says hello once,
becomes live on the peer's hello, and closes permanently. SessionLaws
checks every connection handler against Allows and proves Closed terminal.
-/
namespace Engine.Sync
inductive Session where
  | dialing | hello | live | closed
  deriving BEq, DecidableEq, Inhabited

def Session.sayHello : Session → Session
  | .dialing => .hello
  | s => s

def Session.hearHello : Session → Session
  | .hello => .live
  | s => s

def Session.close (_ : Session) : Session := .closed

/-- Staying put, the next handshake phase, or closing. -/
def Session.Allows (a b : Session) : Prop :=
  a = b ∨ (a = .dialing ∧ b = .hello) ∨ (a = .hello ∧ b = .live) ∨ b = .closed

theorem Session.hello_allowed (s : Session) : s.Allows s.hearHello := by
  cases s <;> simp [Allows, hearHello]

theorem Session.closed_terminal (s : Session) (h : Session.closed.Allows s) : s = .closed := by
  simpa [Allows, eq_comm] using h
end Engine.Sync
