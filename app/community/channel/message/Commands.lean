import app.community.Family
import app.community.channel.message.attachment.chunk.Commands
import app.community.channel.message.receipt.Commands

namespace Community
open Engine

/-- The highest counter, capped, of c's messages this device holds (0
for none): the first of `message.all [c]`, newest first. -/
def topCount (c : Id) : View Fact Nat := do
  let a ← message.all.read [c] (limit := some 1)
  pure (match a.rows.head? with
    | some (_, .message _ _ _ _ _ n _ _) => min n countCap
    | _ => 0)
open Engine Codec

/-- A post claiming counter n, at `time` (minutes since the Unix epoch). -/
def post (c adm : Id) (by_ : Device) (ckey text : ByteArray) (n time : Nat) (clump : Option Id := none) : Op :=
  let reqs := [c, adm] ++ clump.toList
  mkOp reqs (.post ckey text n time (sig by_.sk reqs (.post ckey text n time .empty)))

/-- A post whose text is sealed under content key k with a fresh
24-byte nonce: its sealed bytes are the nonce, then the ciphertext. -/
def sealedPost (c adm : Id) (by_ : Device) (k : Key32) (nonce : Nonce24) (text : ByteArray) (n time : Nat)
    (clump : Option Id := none) : Op :=
  let kid := kidOf cryptoSeal k
  post c adm by_ kid (nonce.1 ++ sealBody cryptoSeal k nonce c kid text) n time clump
end Community
namespace Community.Clump
open Engine

/-- Quiet's time unit is wall-clock minutes. The total span from the
root is strictly below five minutes; a backwards clock starts a root. -/
def within (rootTime now : Nat) : Bool := decide (rootTime ≤ now ∧ now < rootTime + 5)

/-- An id lookup is the singleton list every valid op is filed in. -/
def fact (id : Id) : View Fact (Option Fact) := do
  let a ← View.read { key := opKey id, limit := some 1 }
  return a.rows.head?.map (·.2)

/-- Only the latest known author's own root can continue. Linked devices
of the same user can continue a clump. An intervening author starts a new
root even when an older clump of ours is still within the time window. -/
def choose (c myAdm : Id) (now : Nat) : View Fact (Option Id) := do
  let some (.admission ac me _ _) ← fact myAdm | return none
  if ac != c then return none
  let last ← message.all.read [c] (limit := some 1)
  let some ((_, id), .message lc author _ _ _ _ time parent) := last.rows.head? | return none
  if lc != c || author != me then return none
  match parent with
  | none => return if within time now then some id else none
  | some root =>
    let some (.message rc ru _ _ _ _ rootTime none) ← fact root | return none
    return if rc == c && ru == me && within rootTime now then some root else none
end Community.Clump
namespace Community
open Engine

/-- Send a message to c as device d at `now` (wall-clock minutes since
the Unix epoch, the caller's clock), its text sealed under content key k with
nonce `nonce`, and attach files to it: the post, its receipt if it is
saturated (`receiptFor`), then each file's attachment (a child of the post)
and its chunks, which claim the post's time. The post claims one more than the highest counter this
device holds in c, up to the cap, so it sorts after every message here
(`send_after`); its time is `now` as given. Everything is ops; no bytes
live beside the store. -/
def send (c myAdm : Id) (d : Device) (k : Key32) (nonce : Nonce24) (text : ByteArray) (now : Nat)
    (files : List NewFile := []) : View Fact Write := do
  let clump ← Clump.choose c myAdm now
  let p := sealedPost c myAdm d k nonce text (min ((← topCount c) + 1) countCap) now clump
  let r ← receiptFor p
  pure ⟨p :: r ++ files.flatMap (fun f => let (a, cs) := attach c myAdm p.id now d k f; a :: cs)⟩

end Community
