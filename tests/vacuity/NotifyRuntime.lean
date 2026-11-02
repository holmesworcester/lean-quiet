import tests.vacuity.IdentityTrust
import app.community.notice.Proofs
import platforms.headless.Sim
import app.Proofs
import tests.engine.Checks

/-! Runtime premise certificates for notifications: a notice Bob signs
and seals, Valid in the synthetic signed community (real crypto), and a
real headless app state, holding SQLite/ref/task resources, with Sync in
the background on and off. Each certificate is produced only by an
executable check; the data is synthetic. -/
set_option linter.defProp false
namespace Vacuity.NotifyRuntime
open Engine Community Codec Tests Vacuity.Identity Vacuity.IdentityTrust

/-- Bob's notice: a 32-byte recipient (his node key) and a sealed box,
signed by his admitted device. -/
def recipient := keyOf bob
def box := "sealed reads and level".toUTF8
def bobNotice := notice c admission.id bob recipient box 1

def noticeSigned := applyLaw
  (certifyDB (before ++ [bobNotice]) bobNotice (.notice c requestB.id recipient box 1)) notice_signed

/-- Sync in the background, on: sync keeps running out of the front. -/
def kept (s : App.St) :=
  if h : s.keepSync = true then some (PLift.up (App.syncs_kept s h)) else none

/-- And off: only in front with a surface, as before. -/
def stopped (s : App.St) :=
  if h : s.keepSync = false then some (PLift.up (App.syncs_off s h)) else none

def main : IO UInt32 := do
  let t ← Checks.new
  t.ok "notice_signed: Bob's signed, sealed notice is Valid" noticeSigned.isSome
  let forged := notice c admission.id mallory recipient box 2
  t.ok "a notice signed by another device, citing Bob, is refused"
    ((run (before ++ [forged])).status forged.id == some .invalid)
  let dir := "out/vacuity/notify-runtime"
  IO.FS.createDirAll dir
  let sm ← Sim.new
  let s ← App.start sm.io #[390, 844, 0, 0, 160] (dir ++ "/quiet.db")
  t.ok "the twin has the service" s.canKeep
  let on := App.keepSyncSt s true
  t.ok "syncs_kept: a real app with Sync in the background on" (kept { on with active := false }).isSome
  t.ok "and it syncs out of the front" { on with active := false }.syncs
  let off := App.keepSyncSt s false
  t.ok "syncs_off: a real app with it off" (stopped off).isSome
  t.ok "and out of the front it does not sync" (!{ off with active := false }.syncs)
  t.finish "notifications vacuity (runtime premises)"

end Vacuity.NotifyRuntime
