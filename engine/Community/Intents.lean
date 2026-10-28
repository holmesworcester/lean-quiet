/-
Intents: a user's action, as the ops one writer job commits together
(this node's own). An intent may read lists first (a View); it changes
nothing but the ops it returns. Founding, inviting, joining, approving,
naming, sending and reacting are all just ops: local ones (this
device's secret, the communities it is in, its pending joins) and
shared ones. What a node shows about them (its communities, who is
waiting, a community's name) is lists of those ops' facts.
-/
import Community.Link
import Community.Connect

namespace Community
open Engine

/-- What an intent writes: ops, and the bytes of the blobs they name. -/
structure Write where
  ops : List Op
  blobs : List ByteArray := []

/-- Found a community named `name` from this device's seed, the founder
known as `myName`: the device's secret (local), the root, the device's
acceptance (local), the first name, and the founder's first profile (the
root is the founder's admission). -/
def found (seed name myName : ByteArray) (time : Nat) : Write :=
  let d := Device.ofSeed seed
  let r := root d
  ⟨[secret seed, r, accept r.id d.pk, setName r.id r.id r.id [] 1 d name,
    profile r.id r.id d myName time []], []⟩

/-- Invite to c from this device (admitted as `myAdm`): the invitation,
and its link, with the bearer seed and dial hints given. -/
def inviteTo (c myAdm : Id) (seed bearerSeed : ByteArray) (hints : List ByteArray)
    (threshold : Nat := 1) : Write × Invite :=
  let p := issue c myAdm (Device.ofSeed seed) bearerSeed hints threshold
  (⟨[p.1], []⟩, p.2)

/-- Join from a link, to be known as `name`: the device's secret, its
request (the one op that travels), its acceptance of the community, and
the pending join (which keeps the name until admission). -/
def join (i : Invite) (seed name : ByteArray) : Write :=
  let d := Device.ofSeed seed
  let req := i.request d
  ⟨[secret seed, req, accept i.community d.pk, joining i req.id name], []⟩

/-- Once admitted into c with no profile yet: the first profile, named as
the join asked. Reads my admission, my profile and my join; writes
nothing otherwise. -/
def introduce (c : Id) (seed : ByteArray) (time : Nat) : View Fact Write := do
  let d := Device.ofSeed seed
  let adms ← admission.byDevice.read [c, d.pk]
  match adms.rows.head? with
  | some ((_, adm), .admission _ u _ _) =>
    let prof ← profile.byUser.read [c, u] (limit := some 0)
    let joins ← joining.all.read []
    let name := joins.rows.findSome? fun (_, f) => match f with
      | .joining c' _ _ _ nm => if c' = c then some nm else none
      | _ => none
    match name with
    | some nm => pure (if prof.total = 0 then ⟨[profile c adm d nm time []], []⟩ else ⟨[], []⟩)
    | none => pure ⟨[], []⟩
  | _ => pure ⟨[], []⟩

/-- Stop waiting on a join: the local record of it is closed. -/
def stopWaiting (joiningOp : Id) : Write := ⟨[abandon joiningOp], []⟩

/-- The first approval of each user, in order. -/
def firstPerUser (l : List (Id × Id)) : List (Id × Id) :=
  l.foldl (fun acc p => if acc.any (fun q => decide (q.2 = p.2)) then acc else acc ++ [p]) []

/-- Approve request req of c as this device (admitted as `myAdm`): my
approval, and the admission too when mine completes the tally. Reads the
request, my admission and the approvals so far. -/
def approveReq (c req myAdm : Id) (seed : ByteArray) : View Fact Write := do
  let d := Device.ofSeed seed
  let ok := approve c req myAdm d
  let rq ← View.read { key := opKey req, limit := some 1 }
  let me ← View.read { key := opKey myAdm, limit := some 1 }
  let aps ← approval.byRequest.read [c, req]
  match rq.rows.head?, me.rows.head? with
  | some (_, .request _ _ _ _ _ t), some (_, .admission _ u _ _) =>
    let others := firstPerUser (aps.rows.filterMap fun (p, f) => match f with
      | .approval _ _ v => if v = u then none else some (p.2, v)
      | _ => none)
    let chosen := ok.id :: others.map (·.1)
    pure (if t ≤ chosen.length then ⟨[ok, admit c req (chosen.take t)], []⟩ else ⟨[ok], []⟩)
  | _, _ => pure ⟨[ok], []⟩

/-- Rename c as this admin (admitted as `myAdm`, shown admin by `auth`):
a name superseding the current one, its counter one past it. -/
def rename (c myAdm auth : Id) (seed name : ByteArray) : View Fact Write := do
  let cur ← named.current.read [c] (limit := some 1)
  let (prev, n) := match cur.rows.head? with
    | some ((_, x), .named _ _ _ k) => ([x], k + 1)
    | _ => ([], 1)
  pure ⟨[setName c myAdm auth prev n (Device.ofSeed seed) name], []⟩

/-- Send a message to c with pictures (bytes, width, height): a blob op
per picture, then the post citing them; the bytes go in the blob store. -/
def send (c myAdm : Id) (seed ckey text : ByteArray) (time : Nat)
    (pictures : List (ByteArray × Nat × Nat)) : Write :=
  let d := Device.ofSeed seed
  let bs := pictures.map fun (b, w, h) => blob c b w h
  ⟨bs ++ [post c myAdm d ckey text time (bs.map (·.id))], pictures.map (·.1)⟩

/-- React to a message. -/
def reactTo (c myAdm target : Id) (seed emoji : ByteArray) (time : Nat) : Write :=
  ⟨[react c myAdm target (Device.ofSeed seed) emoji time], []⟩

/-! ## Laws -/

theorem body_mkOp (reqs : List Id) (b : Body) : (Codec.decode (mkOp reqs b).body : Option Body) = some b :=
  Codec.decode_encode b

theorem shared_mkOp (C : Crypto) (reqs : List Id) (b : Body) :
    (family C).shared (mkOp reqs b) = !b.isLocal := by
  cases hs : b.isLocal <;> simp [Family.shared, Family.room, family, scopeOf, body_mkOp, hs]

/-- **Joining is just ops, and only the request leaves the device.** The
join intent writes the device's secret, the request, the acceptance and
the pending join; of these, sync may offer only the request. -/
theorem join_travels (C : Crypto) (i : Invite) (seed name : ByteArray) :
    (join i seed name).ops.filter (family C).shared = [i.request (Device.ofSeed seed)] := by
  simp [join, Invite.request, Community.request, secret, accept, joining, shared_mkOp, Body.isLocal]

/-- **Stopping waiting is local.** -/
theorem stopWaiting_local (C : Crypto) (j : Id) : (stopWaiting j).ops.filter (family C).shared = [] := by
  simp [stopWaiting, abandon, shared_mkOp, Body.isLocal]

/-- **Founding is just ops**; the secret and the acceptance stay. -/
theorem found_travels (C : Crypto) (seed name myName : ByteArray) (time : Nat) :
    (found seed name myName time).ops.filter (family C).shared =
      let d := Device.ofSeed seed; let r := root d
      [r, setName r.id r.id r.id [] 1 d name, profile r.id r.id d myName time []] := by
  simp [found, root, secret, accept, setName, profile, shared_mkOp, Body.isLocal]

end Community
