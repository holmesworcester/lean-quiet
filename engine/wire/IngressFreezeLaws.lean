import engine.wire.IngressIO

namespace Engine.Sync.Ingress.Registry
variable {α : Type} {n : Nat}

theorem freeze_input (r : Registry α n) (source : Fin (n+1)) :
    (r.freeze source).1 = r.state.slots[source] := rfl

theorem freeze_preserves_state (r : Registry α n) (source : Fin (n+1)) :
    (r.freeze source).2.state = r.state := rfl

theorem freeze_preserves_owner (r : Registry α n) (source : Fin (n+1)) :
    (r.freeze source).2.live = r.live := rfl

theorem frozen_refuses (r : Registry α n) (source : Fin (n+1)) (value : α) :
    ((r.freeze source).2.offer source value) = (.closed, (r.freeze source).2) := by
  simp [Registry.freeze, Registry.offer]

theorem freeze_preserves_poll (r : Registry α n) (source : Fin (n+1)) :
    (r.freeze source).2.state.poll = r.state.poll := rfl

theorem freeze_idempotent (r : Registry α n) (source : Fin (n+1)) :
    (r.freeze source).2.freeze source = r.freeze source := by
  simp [Registry.freeze]

end Engine.Sync.Ingress.Registry
