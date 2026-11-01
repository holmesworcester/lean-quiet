/- Nonempty witnesses for the exact placeholder cache called by App.present.
These establish functional pixel/key/reuse equalities, not allocation or time. -/
import engine.renderer.HoldCacheLaws

namespace Vacuity.HoldCache
open Hold

def sample : St := ⟨Paint.solid 0xF8F8F8 1080, ⟨420, 39, .light, none⟩, 1080⟩
def first : MessageTile := MessageTile.make (MessageKey.ofState sample)
def other : St := { sample with dim := { sample.dim with dpi := 160 } }
def stale : MessageTile := MessageTile.make (MessageKey.ofState other)

theorem nonempty_rows : 0 < first.rows.size := by
  simp [first, MessageTile.make, MessageKey.rows, MessageKey.ofState,
    MessageKey.state, period, Row.Dim.px, sample]

theorem different_density : stale.key ≠ MessageKey.ofState sample := by
  intro h
  have dpi := congrArg MessageKey.dpi h
  simp [stale, MessageTile.make, MessageKey.ofState, other, sample] at dpi

/-- Actual interior text-line row, with nonzero width and density. -/
theorem line : messageLine (MessageKey.ofState sample).state (sample.dim.px 34) =
    messageLine sample (sample.dim.px 34) := messageLine_key ..

/-- The stale 160-dpi cache cannot be selected for the 420-dpi frame. -/
theorem key : (MessageCache.prepare (some stale) sample).key = MessageKey.ofState sample :=
  prepare_key ..

theorem reuse : MessageCache.prepare (some first) sample = first :=
  prepare_reuses first sample rfl

theorem rows : (MessageCache.prepare (some stale) sample).rows = (MessageKey.ofState sample).rows :=
  prepare_rows ..

theorem plane : (cachedMessagePlane (some stale) sample 2209).1 = messagePlane sample 2209 :=
  cachedMessagePlane_exact ..

theorem changed_height :
    (cachedMessagePlane (cachedMessagePlane (some first) sample 2209).2 sample 1100).2 =
      (cachedMessagePlane (some first) sample 2209).2 := cachedMessagePlane_reuses ..

end Vacuity.HoldCache
