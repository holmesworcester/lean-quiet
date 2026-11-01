import ops.app.WriteAdmission

namespace Vacuity.WriteAdmission
open Engine App.WriteAdmission

def op : Op := Op.make 42 [] "nonempty payload".toUTF8
def pending : List ByteArray := ["already queued".toUTF8]
def limit : Limits := ⟨2, 100⟩

theorem accepted : refusal limit pending [op] = none := by decide +kernel

theorem frameFits : (Codec.encode [op.bytes]).size + 74 ≤ Engine.Sync.maxFrame :=
  admitted_frames accepted op (by simp)

theorem countFits : pending.length + [op].length ≤ limit.ops :=
  admitted_count accepted

theorem bytesFit : bytes pending + bytes ([op].map Op.bytes) ≤ limit.bytes :=
  admitted_bytes accepted

example : refusal ⟨1, 100⟩ pending [op] ≠ none := by decide +kernel
example : refusal ⟨2, 1⟩ pending [op] ≠ none := by decide +kernel

end Vacuity.WriteAdmission
