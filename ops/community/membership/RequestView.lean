/-
A request to join: the device asking, the approvals it has (decided ones
count toward its threshold; an admission may cite only decided facts),
and whether an admission answers it.

Reads: `approval.byRequest [c, r]` and `admission.byDevice [c, d]` (a
count). The Join requests page lists `request.all [c]` and makes one of
these per row.
-/
import ops.app.Pages
import engine.renderer.Data

namespace Kinds.Request
open Engine Community Data

structure Data where
  id : Id
  device : Key
  threshold : Nat
  /-- Decided approvals' ids (what an admission may cite). -/
  approvals : List Id
  pending : Nat
  admitted : Bool
  deriving Inhabited

variable {m : Type → Type} [Monad m] [Reads m]

def read (c r : Id) (f : Fact) (deps : Array Q) : m (Option Data × Array Q) := do
  let .request _ _ d _ _ t := f | return (none, deps)
  let (aps, pend, deps) ← readList (approval.byRequest.query [c, r]) deps
  let ids := aps.rows.map (·.1.2)
  let (adm, _, deps) ← readList (admission.byDevice.query [c, d] (limit := some 0)) deps
  return (some ⟨r, d, t, ids.filter (!pend.contains ·), (ids.filter pend.contains).length, adm.total > 0⟩, deps)

/-- The requests to c no admission answers yet. -/
def waiting (c : Id) : m (Array Data × Array Q) := do
  let (rq, _, deps) ← readList (request.all.query [c]) #[]
  let mut out := #[]
  let mut deps := deps
  for (pos, f) in rq.rows do
    let (r, d) ← read c pos.2 f deps
    deps := d
    if let some r := r then
      if !r.admitted then out := out.push r
  return (out, deps)

/-- Whether its decided approvals complete its threshold. -/
def Data.ready (r : Data) : Bool := r.threshold > 0 && r.approvals.length ≥ r.threshold

def hexShort (b : ByteArray) : String :=
  String.join (b.toList.take 4 |>.map fun x =>
    let t := String.ofList (Nat.toDigits 16 x.toNat); if t.length < 2 then "0" ++ t else t)

/-- Its row on the Join requests page. -/
def Data.row (r : Data) : Pages.Asking :=
  { device := s!"Device {hexShort r.device}", when := s!"{r.approvals.length} of {r.threshold} approvals",
    going := r.pending > 0 || r.ready }

end Kinds.Request
