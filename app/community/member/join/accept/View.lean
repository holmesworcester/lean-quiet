import app.Commands
import app.community.Family

/-!
`community.member.join.accept`: its component, which reads its own facts, and the component's laws.
-/
namespace Kinds.Accepted
open _root_.Engine _root_.Community _root_.Data

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
  /-- Whether this entry's device has been cut: admitted, and a user of
  it removed (a Valid removal of it is in the store). `Community.mine`
  no longer holds such an entry; it is read (`Community.cutEntry`) only to
  be hidden and told. -/
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

/-- Whatever devices are known, each seed's is the same: the seed's. -/
theorem deviceOf_eq (known known' : Array Me) (seed : ByteArray) :
    deviceOf known seed = deviceOf known' seed :=
  Subtype.ext ((deviceOf known seed).2.trans (deviceOf known' seed).2.symm)

end Kinds.Accepted
