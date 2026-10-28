/-
Intents: a user's action, as the ops one writer job commits together
(this node's own). An intent may read lists first (a View); it changes
nothing but the ops it returns. Founding, inviting, joining, approving,
naming, sending and reacting are all just ops: local ones (this
device's secret, the communities it is in, its pending joins) and
shared ones. What a node shows about them (its communities, who is
waiting, a community's name) is lists of those ops' facts.

An intent that signs as this device takes the device itself
(`Device`), derived from its seed once by the caller: a derivation is a
curve25519 key pair, and some of these views are built on every step.
Only those that write the seed (`found`, `joinOps`, `join`) take it.
-/
import ops.community.Link
import ops.community.Connect

namespace Community
open Engine

/-- What an intent writes: ops. Everything is ops, file bytes included
(an attachment's chunks). -/
structure Write where
  ops : List Op

/-- Found a community named `name` from this device's seed, the founder
known as `myName`: the device's secret (local), the root, the device's
acceptance (local), the first name, the founder's first profile (the
root is the founder's admission), and the community's first content
key `k` (local), wrapped to the founder's device with ephemeral secret
`esk` (both fresh random bytes from the caller). -/
def found (seed name myName : ByteArray) (time : Nat) (k esk : ByteArray) : Write :=
  let d := Device.ofSeed seed
  let r := root d
  ⟨[secret seed, r, accept r.id d.pk, setName r.id r.id r.id [] 1 d name,
    profile r.id r.id d myName time, contentKey r.id k, wrapKey r.id k esk d.enc]⟩

/-- Invite to c from device d (admitted as `myAdm`): the invitation,
and its link, with the bearer seed and dial hints given. -/
def inviteTo (c myAdm : Id) (d : Device) (bearerSeed : ByteArray) (hints : List ByteArray)
    (threshold : Nat := 1) : Write × Invite :=
  let p := issue c myAdm d bearerSeed hints threshold
  (⟨[p.1]⟩, p.2)

/-- Join from a link, to be known as `name`: the device's secret, its
request (the one op that travels), its acceptance of the community, and
the pending join (which keeps the name until admission). -/
def joinOps (i : Invite) (seed name : ByteArray) : Write :=
  let d := Device.ofSeed seed
  let req := i.request d
  ⟨[secret seed, req, accept i.community d.pk, joining i req.id name d.pk]⟩

/-- Byte order on ids. -/
def idLt (a b : Id) : Bool := decide (a.toList < b.toList)

/-- The device this store is in community c as, with its acceptance:
among its acceptances of c whose device's secret it holds, and that are
not a join it stopped waiting on, the admitted one first, else the least
acceptance id. A node holds a community at most once (libquiet #580,
#940); this is which one, and every reader of the same ops picks the
same (the app's switcher, and the network node). -/
def mine (c : Id) : View Fact (Option (Key × Id)) := do
  let acc ← accepted.all.read []
  let joins ← joining.all.read []
  let mut best : Option (Key × Id × Bool) := none
  for ((_, aid), f) in acc.rows do
    let .accepted c' d := f | continue
    if c' ≠ c then continue
    let sec ← secret.byKey.read [d] (limit := some 0)
    if sec.total = 0 then continue
    let adm ← admission.byDevice.read [c, d] (limit := some 0)
    let admitted := adm.total ≠ 0
    if !admitted then
      -- waiting: held only while one of its joins is not stopped
      let mut live := false
      for ((_, jid), g) in joins.rows do
        let .joining c'' _ _ _ _ d' _ := g | continue
        if c'' ≠ c || d' ≠ d then continue
        let ab ← abandoned.byJoining.read [jid] (limit := some 0)
        if ab.total = 0 then live := true
      if !live then continue
    best := match best with
      | none => some (d, aid, admitted)
      | some (bd, ba, badm) =>
        if (admitted && !badm) || (admitted == badm && idLt aid ba) then some (d, aid, admitted)
        else some (bd, ba, badm)
  pure (best.map fun (d, a, _) => (d, a))

/-- Join from a link, to be known as `name`, unless this store already
holds the community (`mine`): then nothing. A join of c stopped waiting
on is resumed rather than made again: a new joining op (one epoch on)
for the same request, so the inviter sees the same request (libquiet's
dormant join). Otherwise a fresh join (`joinOps`). -/
def join (i : Invite) (seed name : ByteArray) : View Fact Write := do
  let c := i.community
  if (← mine c).isSome then return ⟨[]⟩
  let joins ← joining.all.read []
  let dormant := joins.rows.foldl (fun acc (_, f) => match f with
    | .joining c' k hs r nm d n =>
      if c' = c then match acc with
        | some (_, _, _, _, _, m) => if n ≥ m then some (k, hs, r, nm, d, n) else acc
        | none => some (k, hs, r, nm, d, n)
      else acc
    | _ => acc) none
  match dormant with
  | some (k, hs, r, nm, d, n) => return ⟨[mkOp [] (.joining c k hs r nm d (n + 1))]⟩
  | none => return joinOps i seed name

/-- Once device d is admitted into c with no profile yet: the first
profile, named as the join asked. Reads my admission, my profile and my
join; writes nothing otherwise. -/
def introduce (c : Id) (d : Device) (time : Nat) : View Fact Write := do
  let adms ← admission.byDevice.read [c, d.pk]
  match adms.rows.head? with
  | some ((_, adm), .admission _ u _ _) =>
    let prof ← profile.byUser.read [c, u] (limit := some 0)
    let joins ← joining.all.read []
    let name := joins.rows.findSome? fun (_, f) => match f with
      | .joining c' _ _ _ nm _ _ => if c' = c then some nm else none
      | _ => none
    match name with
    | some nm => pure (if prof.total = 0 then ⟨[profile c adm d nm time]⟩ else ⟨[]⟩)
    | none => pure ⟨[]⟩
  | _ => pure ⟨[]⟩

/-- Stop waiting on a join: the local record of it is closed. -/
def stopWaiting (joiningOp : Id) : Write := ⟨[abandon joiningOp]⟩

/-- The first approval of each user, in order. -/
def firstPerUser (l : List (Id × Id)) : List (Id × Id) :=
  l.foldl (fun acc p => if acc.any (fun q => decide (q.2 = p.2)) then acc else acc ++ [p]) []

/-- Approve request req of c as device d (admitted as `myAdm`): my
approval, and the admission too when mine completes the tally. Reads the
request, my admission and the approvals so far. -/
def approveReq (c req myAdm : Id) (d : Device) (esk : ByteArray := .empty) :
    View Fact Write := do
  let ok := approve c req myAdm d
  let rq ← View.read { key := opKey req, limit := some 1 }
  let me ← View.read { key := opKey myAdm, limit := some 1 }
  let aps ← approval.byRequest.read [c, req]
  -- The requester's device gets this device's content key for c,
  -- wrapped to its encryption key: the approval is where key material
  -- hangs (the user's decision, 2026-10-27).
  let ks ← key.byCommunity.read [c] (limit := some 1)
  let wrapTo (e : ByteArray) : List Op := match ks.rows.head? with
    | some (_, .key _ _ k) => if esk.size = 32 then [wrapKey c k esk e] else []
    | _ => []
  match rq.rows.head?, me.rows.head? with
  | some (_, .request _ _ _ e _ t), some (_, .admission _ u _ _) =>
    let others := firstPerUser (aps.rows.filterMap fun (p, f) => match f with
      | .approval _ _ v => if v = u then none else some (p.2, v)
      | _ => none)
    let chosen := ok.id :: others.map (·.1)
    pure (if t ≤ chosen.length then ⟨[ok, admit c req (chosen.take t)] ++ wrapTo e⟩
      else ⟨[ok] ++ wrapTo e⟩)
  | _, _ => pure ⟨[ok]⟩

/-- Rename c as device d of an admin (admitted as `myAdm`, shown admin by
`auth`): a name superseding the current one, its counter one past it. -/
def rename (c myAdm auth : Id) (d : Device) (name : ByteArray) : View Fact Write := do
  let cur ← named.current.read [c] (limit := some 1)
  let (prev, n) := match cur.rows.head? with
    | some ((_, x), .named _ _ _ k) => ([x], k + 1)
    | _ => ([], 1)
  pure ⟨[setName c myAdm auth prev n d name]⟩

/-- Send a message to c as device d, its text sealed under content key k
with nonce `nonce`, and attach files to it: the post, then each file's
attachment (a child of the post) and its chunks. Everything is ops; no
bytes live beside the store. -/
def send (c myAdm : Id) (d : Device) (k nonce text : ByteArray) (time : Nat)
    (files : List NewFile := []) : Write :=
  let p := sealedPost c myAdm d k nonce text time
  ⟨p :: files.flatMap (fun f => let (a, cs) := attach c myAdm p.id d k f; a :: cs)⟩

/-- The ids of the content keys of c this device holds. -/
def heldKids (c : Id) : View Fact (List ByteArray) := do
  let ks ← key.byCommunity.read [c] (limit := none)
  pure (ks.rows.filterMap fun (_, f) => match f with | .key _ kid _ => some kid | _ => none)

/-- The messages of c this device can read: the union of the lists of
messages under each content key it holds (`message.byKey [c, kid]`). A
message sealed under a key not yet held is not listed. When the key
arrives, `key.byCommunity [c]` is filed, so a live reader of this view
reads again and the message appears. Ranges and limits are a list's
(`after`, `before`, `limit`, `desc`), so pages and counts are the
union's. -/
def readable (c : Id) (limit : Option Nat := some 50) (desc : Bool := true)
    (after before : Option Pos := none) : View Fact (Answer Fact) := do
  let kids ← heldKids c
  View.union (kids.map fun kid => message.byKey.query [c, kid] (after := after) (before := before)) limit desc

/-- This device's newest content key for c, if it holds one. -/
def currentKey (c : Id) : View Fact (Option ByteArray) := do
  let ks ← key.byCommunity.read [c] (limit := some 1)
  pure (ks.rows.head?.bind fun (_, f) => match f with | .key _ _ k => some k | _ => none)

/-- The content keys of c wrapped to device d that it does not hold
yet, opened with its encryption secret: each becomes a local `key`. -/
def unwrap (c : Id) (d : Device) : View Fact Write := do
  let ws ← wrap.byRecipient.read [c, d.enc]
  let mut out : List Op := []
  for (_, f) in ws.rows do
    let .wrap _ kid _ bx := f | continue
    let held ← key.byId.read [kid] (limit := some 0)
    if held.total ≠ 0 then continue
    match unbox cryptoSeal d.encSecret kid bx with
    | some k => if k.size = 32 && !out.any (fun o => o.body == (contentKey c k).body) then
        out := out ++ [contentKey c k]
    | none => pure ()
  pure ⟨out⟩

/-- Remove user t from c (libquiet's remover flow), as this device's
user u: the removal cites the root, this device's admission, what makes
u an admin (its own admission for the founder, else a grant), and an
admission of t. Nothing when u is not an admin, t is u, or t is already
removed (`removeMember_valid`). -/
def removeMember (c t : Id) (d : Device) : View Fact Write := do
  let me ← admission.byDevice.read [c, d.pk] (limit := some 1)
  let gone ← removal.byUser.read [c, t] (limit := some 0)
  let tgt ← admission.byUser.read [c, t] (limit := some 1)
  match me.rows.head? with
  | some ((_, myAdm), .admission _ u _ _) =>
    let grant ← admin.byUser.read [c, u] (limit := some 1)
    let auth := if u = c then some myAdm else grant.rows.head?.map (·.1.2)
    match auth, tgt.rows.head? with
    | some a, some ((_, ta), _) =>
      pure ⟨if u = t ∨ gone.total ≠ 0 then [] else [remove c myAdm a ta d]⟩
    | _, _ => pure ⟨[]⟩
  | _ => pure ⟨[]⟩

/-- React to a message as device d. -/
def reactTo (c myAdm target : Id) (d : Device) (emoji : ByteArray) (time : Nat) : Write :=
  ⟨[react c myAdm target d emoji time]⟩

/-! ## Laws -/

theorem body_mkOp (reqs : List Id) (b : Body) : (Codec.decode (mkOp reqs b).body : Option Body) = some b :=
  Codec.decode_encode b

theorem shared_mkOp (C : Crypto) (reqs : List Id) (b : Body) :
    (family C).shared (mkOp reqs b) = !b.isLocal := by
  cases hs : b.isLocal <;> simp [Family.shared, Family.room, family, scopeOf, body_mkOp, hs]

/-- **Joining is just ops, and only the request leaves the device.** The
join intent writes the device's secret, the request, the acceptance and
the pending join; of these, sync may offer only the request. -/
theorem joinOps_travels (C : Crypto) (i : Invite) (seed name : ByteArray) :
    (joinOps i seed name).ops.filter (family C).shared = [i.request (Device.ofSeed seed)] := by
  simp [joinOps, Invite.request, Community.request, secret, accept, joining, shared_mkOp, Body.isLocal]

/-- **Stopping waiting is local.** -/
theorem stopWaiting_local (C : Crypto) (j : Id) : (stopWaiting j).ops.filter (family C).shared = [] := by
  simp [stopWaiting, abandon, shared_mkOp, Body.isLocal]

/-- **Founding is just ops**; the secret, the acceptance and the
content key stay. Only the key's wrap travels. -/
theorem found_travels (C : Crypto) (seed name myName : ByteArray) (time : Nat) (k esk : ByteArray) :
    (found seed name myName time k esk).ops.filter (family C).shared =
      let d := Device.ofSeed seed; let r := root d
      [r, setName r.id r.id r.id [] 1 d name, profile r.id r.id d myName time,
        wrapKey r.id k esk d.enc] := by
  simp [found, root, secret, accept, setName, profile, contentKey, wrapKey, wrap, shared_mkOp,
    Body.isLocal]

/-! ## What a device can read

`readable` lists exactly the messages under keys this device holds:
`readable_held` (each row is a Valid message of c, under a key a Valid
local key fact holds) and `readable_complete` (with no limit, every such
message is listed). -/

section
variable {s : DB Fact} {C : Crypto}
theorem matching_also_nil (q : ListQ) (h : q.also = []) :
    matching s q = matching s { key := q.key, limit := q.limit } := by
  unfold matching; simp [h]

theorem mem_eval_matching {q : ListQ} {pf : Pos × Fact} (h : pf ∈ (Engine.eval s q).rows) :
    pf ∈ matching s q := by
  unfold Engine.eval at h
  simp only at h
  have h1 : pf ∈ (if q.desc then ((matching s q).filter fun p => q.inside p.1).reverse
      else (matching s q).filter fun p => q.inside p.1) := by
    unfold ListQ.cut at h; split at h
    · exact h
    · exact List.mem_of_mem_take h
  have h2 : pf ∈ (matching s q).filter fun p => q.inside p.1 := by
    split at h1
    · exact List.mem_reverse.1 h1
    · exact h1
  exact (List.mem_filter.1 h2).1

theorem readable_held (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (lim : Option Nat)
    (desc : Bool) (after before : Option Pos) {pf : Pos × Fact}
    (hp : pf ∈ ((readable c lim desc after before).eval s).rows) :
    ∃ y u d kid sealed tm, pf.2 = .message c u d kid sealed tm ∧ V C s.ops y pf.2 ∧
      ∃ x k, V C s.ops x (.key c kid k) := by
  unfold readable at hp
  rw [View.eval_bind, eval_union] at hp
  obtain ⟨a, ha, hpa⟩ := mem_union hp
  rw [List.map_map, List.mem_map] at ha
  obtain ⟨kid, hkid, rfl⟩ := ha
  have hm := mem_eval_matching hpa
  rw [matching_also_nil _ rfl] at hm
  obtain ⟨y, f, rfl, hy, hf⟩ := (mem_matching _ _).1 hm
  obtain ⟨hv, hargs⟩ := (filed (C := C) (r := message.byKey) (by simp [rels]) h hq [c, kid] y f).1 ⟨hy, hf⟩
  cases f <;> simp [message.byKey] at hargs
  obtain ⟨rfl, rfl⟩ := hargs
  refine ⟨y, _, _, _, _, _, rfl, hv, ?_⟩
  -- the key: kid came from a key.byCommunity row
  unfold heldKids at hkid
  rw [View.eval_bind] at hkid
  simp only [View.eval_pure, List.mem_filterMap] at hkid
  obtain ⟨⟨p, g⟩, hg, hk⟩ := hkid
  cases g <;> simp at hk
  rename_i c' kid' k
  subst hk
  have hm2 := mem_eval_matching hg
  rw [matching_also_nil _ rfl] at hm2
  obtain ⟨x, g, hpx, hx, hgx⟩ := (mem_matching _ _).1 hm2
  simp only [Prod.mk.injEq] at hpx
  obtain ⟨_, rfl⟩ := hpx
  obtain ⟨hv2, hargs2⟩ := (filed (C := C) (r := key.byCommunity) (by simp [rels]) h hq _ x _).1 ⟨hx, hgx⟩
  simp [key.byCommunity] at hargs2
  subst hargs2
  exact ⟨x, k, hv2⟩


theorem mem_eval_all {q : ListQ} (ha : q.after = none) (hb : q.before = none) (hl : q.limit = none)
    {pf : Pos × Fact} : pf ∈ (Engine.eval s q).rows ↔ pf ∈ matching s q := by
  unfold Engine.eval ListQ.cut ListQ.inside
  simp only [ha, hb, hl, Bool.and_self]
  split <;> simp

theorem readable_complete (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (desc : Bool)
    {y x : Id} {u d kid sealed k : ByteArray} {tm : Nat}
    (hm : V C s.ops y (.message c u d kid sealed tm)) (hk : V C s.ops x (.key c kid k)) :
    ((SortKey.sortOf (Fact.message c u d kid sealed tm), y), Fact.message c u d kid sealed tm) ∈
      ((readable c none desc).eval s).rows := by
  unfold readable
  rw [View.eval_bind, eval_union, mem_union_all]
  have hkid : kid ∈ (heldKids c).eval s := by
    unfold heldKids
    rw [View.eval_bind]
    simp only [View.eval_pure, List.mem_filterMap]
    have hf := (filed (C := C) (r := key.byCommunity) (by simp [rels]) h hq [c] x (.key c kid k)).2
      ⟨hk, by simp [key.byCommunity]⟩
    refine ⟨((SortKey.sortOf (Fact.key c kid k), x), .key c kid k), ?_, rfl⟩
    show _ ∈ (Engine.eval s (key.byCommunity.query [c] (limit := none))).rows
    rw [mem_eval_all rfl rfl rfl, matching_also_nil _ rfl, mem_matching]
    exact ⟨x, _, rfl, hf.1, hf.2⟩
  refine ⟨_, List.mem_map.2 ⟨_, List.mem_map.2 ⟨kid, hkid, rfl⟩, rfl⟩, ?_⟩
  have hf := (filed (C := C) (r := message.byKey) (by simp [rels]) h hq [c, kid] y _).2
    ⟨hm, by simp [message.byKey]⟩
  rw [mem_eval_all rfl rfl rfl, matching_also_nil _ rfl, mem_matching]
  exact ⟨y, _, rfl, hf.1, hf.2⟩

theorem admission_byUser_args {c u : Id} {f : Fact} :
    admission.byUser.args f = some [c, u] ↔ ∃ d e, f = .admission c u d e := by
  cases f <;> simp [admission.byUser, eq_comm]

/-- A row of a list read at rest is a Valid fact filed under it. -/
theorem row_filed {r : Rel Fact} (hr : r ∈ rels) (h : Inv (family C) s) (hq : s.queue = [])
    {as : List ByteArray} {lim : Option Nat} {p : Pos} {f : Fact}
    (hp : (p, f) ∈ (Engine.eval s (r.query as lim)).rows) : V C s.ops p.2 f ∧ r.args f = some as := by
  have hm := mem_eval_matching hp
  rw [matching_also_nil (s := s) (r.query as lim) rfl] at hm
  obtain ⟨y', f', he, hy, hf⟩ := (mem_matching _ _).1 hm
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact (filed (C := C) hr h hq as _ _).1 ⟨hy, hf⟩

/-- **A removal the remover flow writes stands.** Every op
`removeMember c t d` writes is, once stored, a Valid removal of t by
an admin u other than t (d's signatures verifying under the suite). -/
theorem removeMember_valid (h : Inv (family C) s) (hq : s.queue = []) {c t : Id} {d : Device}
    (hsig : ∀ m, C.verify d.pk m (edSign d.sk m) = true)
    {o : Op} (ho : o ∈ ((removeMember c t d).eval s).ops)
    {ops' : Id → Option Op} (he : Extends s.ops ops') (hs : ops' o.id = some o) :
    ∃ u, u ≠ t ∧ IsAdmin C s.ops c u ∧ V C ops' o.id (.removal c t u) := by
  unfold removeMember at ho
  simp only [Rel.read, View.eval_bind, View.eval_read] at ho
  split at ho
  · rename_i p myAdm c' u dv ev hme
    simp only [View.eval_bind, View.eval_read] at ho
    split at ho
    · rename_i a pt ta g hauth htg
      simp only [View.eval_pure] at ho
      by_cases hcond : u = t ∨ (Engine.eval s (removal.byUser.query [c, t] (some 0))).total ≠ 0
      · simp [hcond] at ho
      · simp only [not_or, ne_eq, Decidable.not_not] at hcond
        obtain ⟨hut, hgone⟩ := hcond
        simp only [hut, hgone, ne_eq, not_true_eq_false, or_self, ↓reduceIte,
          List.mem_singleton] at ho
        subst ho
        have hmeV := row_filed (r := admission.byDevice) (by simp [rels]) h hq
          (List.mem_of_mem_head? (by rw [hme]; rfl))
        obtain ⟨hmv, hma⟩ := hmeV
        obtain ⟨u', e', hfe⟩ := byDevice_args.1 hma
        simp only [Fact.admission.injEq] at hfe
        obtain ⟨hc', _, hdv, _⟩ := hfe
        subst c'
        have htgV := row_filed (r := admission.byUser) (by simp [rels]) h hq
          (List.mem_of_mem_head? (by rw [htg]; rfl))
        obtain ⟨htv, hta⟩ := htgV
        obtain ⟨dt, et, hg⟩ := admission_byUser_args.1 hta
        rw [hg] at htv
        obtain ⟨d0, e0, hroot⟩ := root_of_admission h.key hmv
        -- what makes u an admin
        have hadm : ∃ g, V C s.ops a g ∧ isAdmin c u g = true := by
          by_cases hu : u = c
          · rw [if_pos hu] at hauth
            cases hauth
            exact ⟨_, hmv, by simp [isAdmin, hu]⟩
          · rw [if_neg hu] at hauth
            obtain ⟨⟨⟨p2, a'⟩, g2⟩, hg2, ha'⟩ := Option.map_eq_some_iff.1 hauth
            simp only at ha'
            subst ha'
            obtain ⟨hgv, hga⟩ := row_filed (r := admin.byUser) (by simp [rels]) h hq
              (List.mem_of_mem_head? hg2)
            refine ⟨g2, hgv, ?_⟩
            cases g2 <;> simp [admin.byUser] at hga
            simp [isAdmin, hga]
        obtain ⟨g, hgv, hga⟩ := hadm
        refine ⟨u, hut, isAdmin_sound hgv hga, ?_⟩
        rw [hdv] at hmv
        exact admin_removal_stands hs (Codec.decode_encode _) rfl rfl
          (valid_stays he hroot) (valid_stays he hmv) (valid_stays he hgv) hga (valid_stays he htv)
          (hsig _)
    · simp at ho
  · simp at ho

/-! ## An attachment's download progress

`progress` is one count of one list: the Valid chunks of an attachment
(`chunk.byAttachment`), over the file's chunk count. For an attachment
whose root is a file's root:
- `progress_exact`: the count is the number of distinct chunk indices
  held, each below the chunk count;
- `progress_le`: it never passes the total;
- `progress_full`: it reaches the total exactly when every chunk is held;
- `progress_done`: then the length is the file's, and the store holds
  each of the attachment's chunk ops, whose slices are the file. -/

/-- The key of an attachment's chunk list. -/
def chunkKey (c att : Id) : ByteArray := chunk.byAttachment.key [c, att]

/-- How many of an attachment's chunks this device holds (Valid), and
how many its file has (len is the attachment's). -/
def progress (c att : Id) (len : Nat) : View Fact (Nat × Nat) := do
  let a ← chunk.byAttachment.read [c, att] (limit := some 0)
  pure (a.total, Merkle.nChunks len)

/-- A list of distinct elements of M is no longer than M. -/
theorem nodup_sub_length_le : ∀ {l M : List Nat}, l.Nodup → (∀ y ∈ l, y ∈ M) → l.length ≤ M.length
  | [], _, _, _ => Nat.zero_le _
  | a :: t, M, hn, hs => by
    rw [List.nodup_cons] at hn
    have ha : a ∈ M := hs a (by simp)
    have ih := nodup_sub_length_le (M := M.erase a) hn.2 fun y hy => by
      have hne : y ≠ a := fun e => hn.1 (e ▸ hy)
      exact (List.mem_erase_of_ne hne).2 (hs y (List.mem_cons_of_mem _ hy))
    rw [List.length_erase_of_mem ha] at ih
    have : 0 < M.length := List.length_pos_of_mem ha
    simp only [List.length_cons]; omega

/-- Distinct numbers below n: n of them exactly when all of them. -/
theorem nodup_full {l : List Nat} {n : Nat} (hn : l.Nodup) (hb : ∀ i ∈ l, i < n) :
    l.length = n ↔ ∀ i < n, i ∈ l := by
  constructor
  · intro hl i hi
    by_cases hni : i ∈ l
    · exact hni
    · have := nodup_sub_length_le (M := (List.range n).erase i) hn fun y hy => by
        have hne : y ≠ i := fun e => hni (e ▸ hy)
        exact (List.mem_erase_of_ne hne).2 (List.mem_range.2 (hb y hy))
      rw [List.length_erase_of_mem (List.mem_range.2 hi), List.length_range] at this
      omega
  · intro hall
    have h1 := nodup_sub_length_le hn fun y hy => List.mem_range.2 (hb y hy)
    have h2 := nodup_sub_length_le (l := List.range n) List.nodup_range
      fun y hy => hall y (List.mem_range.1 hy)
    rw [List.length_range] at h1 h2; omega


/-- **What an attachment writes are its file's chunk ops**: chunk i of
`attach` is `fileChunk` of the file at i, for every i below the chunk
count, so the progress laws count the ops `send` writes. -/
theorem attach_chunks (c adm msg : Id) (d : Device) (k : ByteArray) (f : NewFile) :
    (attach c adm msg d k f).2 = (List.range (Merkle.nChunks (fileCipher f).size)).map
      (fileChunk c (attach c adm msg d k f).1.id (fileCipher f)) := by
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  have hs : (Merkle.slices (fileCipher f)).getD i .empty = Merkle.slice (fileCipher f) i := by
    simp [List.getD, Merkle.getElem?_slices, hi]
  have hp : ((List.range (Merkle.nChunks (fileCipher f).size)).map
      (Merkle.proof sha256 (fileCipher f))).getD i [] = Merkle.proof sha256 (fileCipher f) i := by
    simp [List.getD, hi]
  simp only [fileChunk, mkOp, Merkle.rootAndProofs, hs, hp, attach]

section
variable (hsize : ∀ x, (sha256 x).size = 32) {ct : ByteArray}
  (hspr : Merkle.NoSecondPreimage sha256 (Merkle.treeInputs sha256 ct))
include hsize hspr

/-- **Download progress is exact.** The count `progress` reads is the
number of distinct indices i at which this device holds a Valid chunk
of the attachment, each below the chunk count; the total is the chunk
count. -/
theorem progress_exact (h : Inv (family C) s) (hq : s.queue = []) {c att m u : Id} {len : Nat}
    {k x : ByteArray} (ha : V C s.ops att (.attachment c m u (Merkle.fileRoot sha256 ct) len k x)) :
    ∃ is : List Nat, is.Nodup ∧
      (∀ i, i ∈ is ↔ ∃ y, V C s.ops y (.chunk c att (Merkle.fileRoot sha256 ct) len i)) ∧
      (∀ i ∈ is, i < Merkle.nChunks len) ∧
      (progress c att len).eval s = (is.length, Merkle.nChunks len) := by
  let root := Merkle.fileRoot sha256 ct
  let M := matching s { key := chunkKey c att }
  let ix : Pos × Fact → Nat := fun p => match p.2 with | .chunk _ _ _ _ i => i | _ => 0
  have hrow : ∀ p ∈ M, ∃ y i, p = ((SortKey.sortOf (Fact.chunk c att root len i), y), .chunk c att root len i) ∧
      V C s.ops y (.chunk c att root len i) := by
    intro p hp
    obtain ⟨y, f, rfl, hy, hf⟩ := (mem_matching _ _).1 hp
    obtain ⟨hv, hargs⟩ := (filed (C := C) (r := chunk.byAttachment) (by simp [rels]) h hq _ y f).1 ⟨hy, hf⟩
    cases f <;> simp [chunk.byAttachment] at hargs
    obtain ⟨rfl, rfl⟩ := hargs
    obtain ⟨_, _, _, _, _, _, _, hav⟩ := chunk_of_attachment hv
    have := spec_det hav ha
    simp only [Verdict.valid.injEq, Fact.attachment.injEq] at this
    obtain ⟨_, _, _, rfl, rfl, _, _⟩ := this
    exact ⟨y, _, rfl, hv⟩
  have hheld : ∀ i, (∃ p ∈ M, ix p = i) ↔ ∃ y, V C s.ops y (.chunk c att root len i) := by
    intro i; constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨y, j, rfl, hv⟩ := hrow p hp
      exact ⟨y, hv⟩
    · rintro ⟨y, hv⟩
      have hf := (filed (C := C) (r := chunk.byAttachment) (by simp [rels]) h hq [c, att] y _).2
        ⟨hv, by simp [chunk.byAttachment]⟩
      exact ⟨_, (mem_matching _ _).2 ⟨y, _, rfl, hf.1, hf.2⟩, rfl⟩
  refine ⟨M.map ix, ?_, ?_, ?_, ?_⟩
  · show List.Pairwise _ _
    rw [List.pairwise_map]
    have hn' : List.Pairwise (fun a b : Pos × Fact => a.1.2 ≠ b.1.2) M := by
      have := matching_nodup h { key := chunkKey c att }
      unfold List.Nodup at this; rwa [List.pairwise_map] at this
    refine hn'.imp_of_mem fun ha hb hne heq => hne ?_
    obtain ⟨y1, i1, rfl, hv1⟩ := hrow _ ha
    obtain ⟨y2, i2, rfl, hv2⟩ := hrow _ hb
    simp only [ix] at heq; subst heq
    exact chunk_unique h.key hsize hspr hv1 hv2
  · intro i; rw [List.mem_map]; exact hheld i
  · intro i hi
    obtain ⟨y, hv⟩ := (hheld i).1 (List.mem_map.1 hi)
    obtain ⟨o, b, fs, _, _, _, hc⟩ := valid_inv hv
    obtain ⟨_, _, _, _, _, hver, _⟩ := check_chunk hc
    exact (Merkle.index_bound hver).1
  · unfold progress
    simp only [View.eval_bind, View.eval_pure, List.length_map]
    show ((Engine.eval s _).total, _) = _
    unfold Engine.eval
    rw [matching_also_nil _ rfl]
    rfl

/-- **Progress never passes the total.** -/
theorem progress_le (h : Inv (family C) s) (hq : s.queue = []) {c att m u : Id} {len : Nat}
    {k x : ByteArray} (ha : V C s.ops att (.attachment c m u (Merkle.fileRoot sha256 ct) len k x)) :
    ((progress c att len).eval s).1 ≤ ((progress c att len).eval s).2 := by
  obtain ⟨is, hnd, _, hb, he⟩ := progress_exact hsize hspr h hq ha
  rw [he]
  have := nodup_sub_length_le hnd fun y hy => List.mem_range.2 (hb y hy)
  simpa using this

/-- **Progress is full exactly when every chunk is here.** -/
theorem progress_full (h : Inv (family C) s) (hq : s.queue = []) {c att m u : Id} {len : Nat}
    {k x : ByteArray} (ha : V C s.ops att (.attachment c m u (Merkle.fileRoot sha256 ct) len k x)) :
    ((progress c att len).eval s).1 = ((progress c att len).eval s).2 ↔
      ∀ i < Merkle.nChunks len, ∃ y, V C s.ops y (.chunk c att (Merkle.fileRoot sha256 ct) len i) := by
  obtain ⟨is, hnd, hmem, hb, he⟩ := progress_exact hsize hspr h hq ha
  rw [he]
  simp only
  rw [nodup_full hnd hb]
  exact forall_congr' fun i => imp_congr_right fun _ => hmem i

/-- **Full progress is the whole file.** When the count reaches the
total, the attachment's length is the file's and the store holds each
of the attachment's chunk ops (`fileChunk`), whose slices are the file
(`Merkle.assemble_slices`). -/
theorem progress_done (h : Inv (family C) s) (hq : s.queue = []) {c att m u : Id} {len : Nat}
    {k x : ByteArray} (ha : V C s.ops att (.attachment c m u (Merkle.fileRoot sha256 ct) len k x))
    (hd : ((progress c att len).eval s).1 = ((progress c att len).eval s).2) :
    len = ct.size ∧ ∀ i < Merkle.nChunks ct.size,
      V C s.ops (fileChunk c att ct i).id (.chunk c att (Merkle.fileRoot sha256 ct) ct.size i) := by
  have hall := (progress_full hsize hspr h hq ha).1 hd
  obtain ⟨y0, h0⟩ := hall 0 (Merkle.one_le_nChunks len)
  obtain ⟨o, b, fs, _, _, _, hc⟩ := valid_inv h0
  obtain ⟨_, _, rfl, _⟩ := chunk_is_slice hsize hspr hc
  refine ⟨rfl, fun i hi => ?_⟩
  obtain ⟨y, hy⟩ := hall i hi
  rw [← chunk_id h.key hsize hspr hy]
  exact hy

end

end

end Community
