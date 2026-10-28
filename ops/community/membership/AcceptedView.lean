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
community id or a name, and there is one per community: the engine's
`Community.mine c` picks it (the admitted acceptance, else the least
id; stopped joins are not held), the same entry the node answers and
dials as. Joining a held community writes nothing (Community.join). A
join is this entry's own: its device's joining fact, not stopped.
-/
import engine.renderer.Data

namespace Kinds.Accepted
open Engine Community Data

structure Me where
  /-- This acceptance's op id: what the switcher and the app key it by. -/
  acc : Id := .empty
  dev : Device
  seed : ByteArray
  /-- The device is the seed's, so whoever holds an entry signs with the
  device without deriving it again (a curve25519 key pair). -/
  dev_ok : dev = Device.ofSeed seed
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
  /-- Whether this entry's user has been removed from the community (a
  Valid removal of it is in the store). -/
  removed : Bool := false

instance : Inhabited Me :=
  ⟨{ dev := Device.ofSeed .empty, seed := .empty, dev_ok := rfl, c := .empty, adm := .empty, name := "" }⟩

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

/-- The entries listed: those whose user is not removed (a removed one
is hidden, its data kept). -/
def listed (ms : Array Me) : Array Me := ms.filter (!·.removed)

/-- The entries removed since `seen` (acceptance ids already told). -/
def newlyGone (seen : List Id) (ms : Array Me) : List Me :=
  ms.toList.filter fun m => m.removed && !seen.any (fun x => decide (x = m.acc))

/-- The entry for acceptance `a`. -/
def select (ms : Array Me) (a : Id) : Option Me := ms.find? fun m => decide (m.acc = a)

/-- Where the app lands: the current entry if still listed, else the
first listed one, else none (Get started). -/
def landing (cs : Array Me) (cur : Id) : Option Me := select cs cur <|> cs[0]?


/-- The device of a seed: an entry's of `known` for the same seed (it was
derived when that entry was read), else derived now. -/
def deviceOf (known : Array Me) (seed : ByteArray) : { d : Device // d = Device.ofSeed seed } :=
  match h : known.find? (fun m => decide (m.seed = seed)) with
  | some m => ⟨m.dev, by
      have hp := Array.find?_some (p := fun (x : Me) => decide (x.seed = seed)) h
      rw [m.dev_ok, of_decide_eq_true hp]⟩
  | none => ⟨Device.ofSeed seed, rfl⟩

variable {m : Type → Type} [Monad m] [Reads m]

/-- The entries, as described above. Each entry's device is taken from
an entry of `known` with the same seed if there is one (the entries the
caller read last time), so a step derives no device it already holds. -/
def read (known : Array Me := #[]) : m (Array Me × Array Q) := do
  let (acc, _, deps) ← readList (accepted.all.query []) #[]
  let (jn, _, deps) ← readList (joining.all.query []) deps
  let mut deps := deps
  let mut out := #[]
  let mut seen : List Id := []
  for (_, f) in acc.rows do
    let .accepted c _ := f | continue
    if seen.contains c then continue
    seen := c :: seen
    -- this device's entry in c: the engine's choice (Community.mine), the
    -- one the node answers and dials as, so the two cannot disagree
    let (pick, d0) ← readView (Community.mine c) deps
    deps := d0
    let some (pk, accId) := pick | continue
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
    -- waiting: this device's live join of c (the one Stop waiting stops)
    let mut joiningOp := ByteArray.empty
    let mut dialing := ""
    if admId.isEmpty then
      for ((_, jid), g) in jn.rows do
        let .joining c' _ hs _ _ d _ := g | continue
        if c' != c || d != pk then continue
        let (ab, _, d4) ← readList (abandoned.byJoining.query [jid] (limit := some 0)) deps
        deps := d4
        if ab.total == 0 then
          joiningOp := jid
          dialing := (hs.head?.bind String.fromUTF8?).getD ""
    let (rm, _, d6) ← readList (removal.byUser.query [c, user] (limit := some 0)) deps
    deps := d6
    let removed := !user.isEmpty && rm.total > 0
    let dv := deviceOf known seed
    out := out.push { acc := accId, dev := dv.1, seed, dev_ok := dv.2, c, adm := admId, user, name, joiningOp,
                      dialing, removed }
  let sorted := out.qsort fun a b => a.name < b.name || (a.name == b.name && Engine.bcmp a.acc b.acc == .lt)
  return (dedupe sorted, deps)

/-- Whatever devices are known, each seed's is the same: the seed's. -/
theorem deviceOf_eq (known known' : Array Me) (seed : ByteArray) :
    deviceOf known seed = deviceOf known' seed :=
  Subtype.ext ((deviceOf known seed).2.trans (deviceOf known' seed).2.symm)

/-- **Reading with the devices already held is reading**: `read known`
is `read` for every `known`, so its entries are the same; it only
derives no device it is given. -/
theorem read_known (known : Array Me) : (read known : m (Array Me × Array Q)) = read := by
  unfold read
  simp only [deviceOf_eq known #[]]

end Kinds.Accepted
