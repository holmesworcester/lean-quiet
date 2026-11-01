/-
Hooks written for a store of A, run on a store of A and B: a family on
top (`Family.sum`), such as the app's own ops on the node's
(app/Family.lean). Each hook reads the store as A's (`LeftM`,
engine/core/Left.lean, whose laws say those reads are the A part's), and
none reads or writes anything else.
-/
import engine.wire.Node
import engine.core.Left

namespace Engine.Sync

def Hooks.left {A B : Type} {m : Type → Type} [Monad m] (h : Hooks A (LeftM B m)) : Hooks (A ⊕ B) m where
  rooms := h.rooms
  onGiven := h.onGiven
  recv := h.recv
  outbox := h.outbox
  closing := h.closing
  retired := h.retired
  react := h.react
  dial := h.dial
  established := h.established
  sealFor := h.sealFor
  openFrame := h.openFrame
  retryKey := h.retryKey

end Engine.Sync
