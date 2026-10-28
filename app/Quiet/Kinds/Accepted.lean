/-
The communities this device is in, each as this device sees it: its
device there (from its secret, read by intents to sign), its admission
(none while waiting to be approved), and its name.

Reads: `accepted.all []` and `joining.all []` (this device's own local
facts), then for each community `secret.byKey [pk]`, `admission.byDevice
[c, pk]` and `named.current [c]` (newest, one row), and for a join not
yet answered `abandoned.byRequest [req]`: a join this device stopped
waiting on is not listed (unless an approval let it in after all). Nothing else: which community is
current is the app's memory, not state.
-/
import Quiet.Data

namespace Kinds.Accepted
open Engine Community Data

structure Me where
  dev : Device
  seed : ByteArray
  c : Id
  /-- This device's admission (the root for a founder); empty while waiting. -/
  adm : Id
  /-- My user there (the community id for its founder); empty while waiting. -/
  user : Id := .empty
  name : String
  /-- While waiting: the joining op (what Stop waiting supersedes), and
  the address its request is sent to (the link's first hint). -/
  joiningOp : Id := .empty
  dialing : String := ""
  deriving Inhabited

def Me.waiting (m : Me) : Bool := m.adm.isEmpty

variable {m : Type → Type} [Monad m] [Reads m]

def read : m (Array Me × Array Q) := do
  let (acc, _, deps) ← readList (accepted.all.query []) #[]
  let (jn, _, deps) ← readList (joining.all.query []) deps
  let mut out := #[]
  let mut deps := deps
  for (_, f) in acc.rows do
    let .accepted c pk := f | continue
    let (sec, _, d1) ← readList (secret.byKey.query [pk] (limit := some 1)) deps
    let (adm, _, d2) ← readList (admission.byDevice.query [c, pk] (limit := some 1)) d1
    let (nm, _, d3) ← readList (named.current.query [c] (limit := some 1)) d2
    deps := d3
    let some (_, .secret _ seed) := sec.rows.head? | continue
    let name := match nm.rows.head? with
      | some (_, .named _ _ n _) => (String.fromUTF8? n).getD "?"
      | _ => "Waiting to join"
    let admId := (adm.rows.head?.map (·.1.2)).getD .empty
    let user := match adm.rows.head? with | some (_, .admission _ u _ _) => u | _ => .empty
    -- a join not answered: its joining op, and whether I stopped waiting
    let jop := (jn.rows.find? fun (_, f) => match f with | .joining c' .. => c' == c | _ => false)
    let mut joiningOp := ByteArray.empty
    let mut dialing := ""
    if admId.isEmpty then
      if let some ((_, jid), .joining _ _ hs req _) := jop then
        dialing := (hs.head?.bind String.fromUTF8?).getD ""
        let (ab, _, d4) ← readList (abandoned.byRequest.query [req] (limit := some 0)) deps
        deps := d4
        if ab.total > 0 then continue
        joiningOp := jid
    out := out.push ⟨Device.ofSeed seed, seed, c, admId, user, name, joiningOp, dialing⟩
  -- a stable order: by name, then id
  let sorted := out.qsort fun a b => a.name < b.name || (a.name == b.name && Engine.bcmp a.c b.c == .lt)
  return (sorted, deps)

end Kinds.Accepted
