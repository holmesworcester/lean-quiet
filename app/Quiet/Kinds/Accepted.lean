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

Each entry is one acceptance, keyed by its op id (`acc`), never by the
community id or a name, and there is one per community: joining a held
community is refused (App.takeInvite), and two acceptances that raced
fold to the least (`dedupe`). A join is this entry's own: the joining
fact whose request is this device's.
-/
import Quiet.Data

namespace Kinds.Accepted
open Engine Community Data

structure Me where
  /-- This acceptance's op id: what the switcher and the app key it by. -/
  acc : Id := .empty
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

/-- What a page shows of an entry, and its key. -/
structure Key where
  acc : Id
  c : Id
  name : String
  waiting : Bool
  dialing : String
  deriving BEq, Inhabited

def Me.key (m : Me) : Key := ⟨m.acc, m.c, m.name, m.waiting, m.dialing⟩

/-- The first entry of each key, in order. -/
def dedupeBy (key : Me → Id) : List Me → List Id → List Me
  | [], _ => []
  | m :: t, seen =>
    if seen.any (fun x => decide (x = key m)) then dedupeBy key t seen else m :: dedupeBy key t (key m :: seen)

/-- The entries the app holds, from the store's acceptances sorted by
(name, admitted first, acceptance): one per community, and then one per
acceptance (a list read never repeats an op, but the switcher's laws
should not rest on that). A device holds a community at most once, so a
second acceptance of one (two joins that raced) is folded away: its entry
is the admitted one, else the least acceptance id, a tiebreak every reader
of the same ops makes alike (entries of one community share its name). -/
def dedupe (ms : Array Me) : Array Me :=
  (dedupeBy (·.acc) (dedupeBy (·.c) ms.toList []) []).toArray

/-- The entry for acceptance `a`. -/
def select (ms : Array Me) (a : Id) : Option Me := ms.find? fun m => decide (m.acc = a)

variable {m : Type → Type} [Monad m] [Reads m]

def read : m (Array Me × Array Q) := do
  let (acc, _, deps) ← readList (accepted.all.query []) #[]
  let (jn, _, deps) ← readList (joining.all.query []) deps
  let mut out := #[]
  let mut deps := deps
  for ((_, accId), f) in acc.rows do
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
    -- a join not answered: this device's joining op (its request is this
    -- device's), and whether I stopped waiting
    let mut jop := none
    for ((p, jid), g) in jn.rows do
      let .joining c' _ _ req _ := g | continue
      if c' != c then continue
      -- the request op as stored (it waits, undecided, for the
      -- community's ops): its body names the device that asked
      let a ← Reads.read (.op req)
      deps := deps.push (.op req)
      if let .bytes (some b) := a then
        if let some o := Engine.Op.decode b then
          if let some (.request d _ _ _) := (Codec.decode o.body : Option Community.Body) then
            if d == pk then jop := some ((p, jid), g)
    let mut joiningOp := ByteArray.empty
    let mut dialing := ""
    if admId.isEmpty then
      if let some ((_, jid), .joining _ _ hs req _) := jop then
        dialing := (hs.head?.bind String.fromUTF8?).getD ""
        let (ab, _, d4) ← readList (abandoned.byRequest.query [req] (limit := some 0)) deps
        deps := d4
        if ab.total > 0 then continue
        joiningOp := jid
    out := out.push { acc := accId, dev := Device.ofSeed seed, seed, c, adm := admId, user, name, joiningOp, dialing }
  -- a total order: by name, then admitted before waiting, then acceptance
  -- (op ids are distinct): `dedupe` keeps the first of each community
  let sorted := out.qsort fun a b => a.name < b.name || (a.name == b.name &&
    (!a.waiting && b.waiting || (a.waiting == b.waiting && Engine.bcmp a.acc b.acc == .lt)))
  return (dedupe sorted, deps)

end Kinds.Accepted
