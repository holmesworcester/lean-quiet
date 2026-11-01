/- A first committed own-body paint keeps its admitted snapshot while
compatible cosmetic updates accumulate. Work's lifetime gate stays intact. -/
import ops.app.Raster

namespace Raster.RowPaint
open Engine Paint Row

/-- Data whose change must revoke an in-flight body snapshot. Names and
reaction tallies, including their layout, may lag for one paint; identity, body, pending state,
attachments, selection and every other field must agree. -/
def bodyInputs (d : RowData) : RowData :=
  { d with name := "", namesake := false, tallies := [] }

structure Stamp where
  generation : Nat
  message : Id
  width : Nat
  dim : Dim
  background : ByteArray
  body : RowData
  ready : List Bool
  deriving BEq

def stamp (generation : Nat) (message : Id) (width : Nat) (dim : Dim)
    (background : ByteArray) (data : RowData) (ready : List Bool) : Stamp :=
  ⟨generation, message, width, dim, background, bodyInputs data, ready⟩

structure Flight where
  stamp : Stamp
  version : Nat
  requestId : Nat
  data : RowData
  lay : Layout
  images : Array (Option Bitmap)
  handle : Work.Handle Raster.Key Bitmap

/-- The caller declares the returned key for this frame. Retaining that
key keeps the original queue position and publication ticket; replacing it
still uses Work's ordinary revocation. Failed or revoked work is not reused. -/
def request (pool : Work.Pool Raster.Key Bitmap) (owner : Demand.Owner) (visible first : Bool)
    (previous : Option Flight) (stamp : Stamp) (version : Nat)
    (data : RowData) (lay : Layout) (images : Array (Option Bitmap))
    (action : Work.Action Bitmap) : IO (Flight × Option Bitmap) := do
  if let some old := previous then
    if old.stamp == stamp && (first || old.version == version) then
      let current ← pool.state.atomically do return (← get).plan.current old.handle.ticket
      if current then
        let value ← old.handle.value
        if value.isSome || !(← IO.hasFinished old.handle.result) then return (old, value)
  -- A replacement gets a distinct key even if its data version is unchanged
  -- (for example an attachment becomes ready, or a failed action is retried).
  let requestId := max version (previous.map (·.requestId + 1) |>.getD 0)
  let key := Raster.Key.row stamp.generation stamp.message requestId stamp.ready stamp.dim.theme
  let handle ← pool.request ⟨owner, key, visible⟩ action
  return (⟨stamp, version, requestId, data, lay, images, handle⟩, ← handle.value)

end Raster.RowPaint
