import engine.wire.IngressFreezeLaws

namespace Vacuity.IngressFreeze
open Engine.Sync.Ingress

def source : Fin 2 := ⟨1, by decide⟩
def waiting : Registry Nat 1 := {
  live := Vector.replicate 2 true
  accepting := Vector.replicate 2 true
  state := { slots := (Vector.replicate 2 none).set 1 (some 42) } }

theorem captured : (waiting.freeze source).1 = some 42 := by
  rw [Registry.freeze_input]
  decide +kernel

theorem ownership : (waiting.freeze source).2.live = waiting.live :=
  Registry.freeze_preserves_owner waiting source

theorem repeated : (waiting.freeze source).2.freeze source = waiting.freeze source :=
  Registry.freeze_idempotent waiting source

theorem retained : (waiting.freeze source).2.state = waiting.state :=
  Registry.freeze_preserves_state waiting source

theorem no_refill : (waiting.freeze source).2.offer source 99 =
    (.closed, (waiting.freeze source).2) := Registry.frozen_refuses waiting source 99

theorem still_selected : ((waiting.freeze source).2.state.poll).1 = some (source, 42) := by
  rw [Registry.freeze_preserves_poll]
  decide +kernel

theorem no_second_slot : ((waiting.freeze source).2.state.poll).2.slots[source] = none := by decide +kernel

end Vacuity.IngressFreeze
