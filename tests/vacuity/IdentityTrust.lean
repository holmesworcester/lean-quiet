import tests.vacuity.IdentityFixture
import app.community.Proofs

namespace Vacuity.IdentityTrust
open Engine Community Codec Tests Vacuity.Identity

-- All six fields of the database invariant come from the production invariant
-- preservation laws, rather than assuming the constructed store is sound.
def load : List Op → DB Fact
  | [] => DB.empty
  | o :: os => ingestS o (load os)

theorem loadReach (ops : List Op) : Reach (family ed25519) ops (load ops) := by
  induction ops with
  | nil => exact .empty
  | cons o os ih => exact .ingest o ih

def run (ops : List Op) := drainS (family ed25519) 400 (load ops)
theorem runReach (ops : List Op) : Reach (family ed25519) ops (run ops) :=
  reach_drain (loadReach ops) 400
theorem runInv (ops : List Op) : Inv (family ed25519) (run ops) := reach_inv (runReach ops)

def certifyDB (ops : List Op) (o : Op) (f : Fact) : Option (PLift (V ed25519 (run ops).ops o.id f)) :=
  if h : (run ops).status o.id = some (.valid f) then some ⟨(runInv ops).sound _ _ h⟩ else none

/-- The store before Alice approves: her community, the invitation and
Bob's request. -/
def pending : List Op := [r, invitation, requestB]

/-- Alice's approval write over a store, as the intent runs it. -/
def approvalWrite (ops : List Op) : Write := (approveReq c requestB.id c alice).eval (run ops)

/-- `approveReq_wrap_admits` applied to Alice's actual approval of Bob's
request over the real store: unless her write is the bare approval, it
is her approval, then the admission citing exactly it, then the rest. -/
def wrapAdmits (ops : List Op) : Option (PLift (∃ rest, (approvalWrite ops).ops =
    approve c requestB.id c alice :: admit c requestB.id (approve c requestB.id c alice).id :: rest)) :=
  if h : (approvalWrite ops).ops = [approve c requestB.id c alice] then none
  else some ⟨(Engine.View.always_eval (run ops) (approveReq_wrap_admits c requestB.id c alice .empty)).resolve_left h⟩

def connectIff := if hq : (run before).queue = [] then
  some (PLift.up (connect_iff (runInv before) hq c (keyOf bob))) else none

def deviceLiveIff := if hq : (run before).queue = [] then
  some (PLift.up (deviceLive_iff (runInv before) hq c bob.pk)) else none

def membersIff := if hq : (run before).queue = [] then
  some (PLift.up (members_iff (runInv before) hq c bob.pk)) else none

def recipientsIff := if hq : (run before).queue = [] then
  some (PLift.up (recipients_iff (runInv before) hq c (keyOf bob))) else none

def removalsIff := if hq : (run after).queue = [] then
  some (PLift.up (removals_iff (runInv after) hq c requestB.id)) else none

def connectApproved := if hq : (run before).queue = [] then
  if ha : (allowPeer c (keyOf bob)).eval (run before) = true then
    some (PLift.up (connect_approved (runInv before) hq c (keyOf bob) ha))
  else none
else none

def cut : Option (PLift (Cut ed25519 (run after).ops c bob.pk)) := do
  let ⟨ha⟩ ← certifyDB after admission bobFact
  let ⟨hr⟩ ← certifyDB after removeB (.removal c requestB.id c)
  pure ⟨requestB.id, keyOf bob, ⟨admission.id, ha⟩, ⟨removeB.id, c, hr⟩⟩

def cutConsented := applyLaw cut cut_consented

def nodeRows := [((sortOf bobFact, admission.id), bobFact)]

theorem nodeOnlyBob (hq : (run after).queue = [])
    (rows : (eval (run after) (admission.byKey.query [c, keyOf bob])).rows = nodeRows)
    (u : Id) (d : Key) (ha : Admitted ed25519 (run after).ops c u d (keyOf bob)) :
    u = requestB.id ∧ d = bob.pk := by
  obtain ⟨y, hv⟩ := ha
  obtain ⟨p, hp⟩ := (exists_row (runInv after) hq (by simp [rels]) [c, keyOf bob]
    (.admission c u d (keyOf bob))).2 ⟨y,hv,byKey_args.2 ⟨u,d,rfl⟩⟩
  rw [rows] at hp
  simp only [nodeRows, bobFact, List.mem_singleton, Prod.mk.injEq, Fact.admission.injEq] at hp
  exact ⟨hp.2.2.1, hp.2.2.2.1⟩

def refuseNonmember := do
  let ⟨hc⟩ ← cut
  if hq : (run after).queue = [] then
    if rows : (eval (run after) (admission.byKey.query [c, keyOf bob])).rows = nodeRows then
      return PLift.up (refuse_nonmember (runInv after) hq c (keyOf bob)
        (fun u d ha => (nodeOnlyBob hq rows u d ha).2 ▸ hc))
    else none
  else none

def removalCutsOff := do
  let ⟨ha⟩ ← certifyDB after admission bobFact
  let ⟨hr⟩ ← certifyDB after removeB (.removal c requestB.id c)
  if hq : (run after).queue = [] then
    if rows : (eval (run after) (admission.byKey.query [c, keyOf bob])).rows = nodeRows then
      return PLift.up (removal_cuts_off (runInv after) hq
        (show Removed ed25519 (run after).ops c requestB.id from ⟨removeB.id,c,hr⟩)
        (fun u d had => ⟨keyOf bob, admission.id, (nodeOnlyBob hq rows u d had).2 ▸ ha⟩))
    else none
  else none

theorem sameOps (ops : List Op)
    (hm : ∀ o ∈ ops, (run ops).ops o.id = (run ops.reverse).ops o.id) :
    (run ops).ops = (run ops.reverse).ops := by
  funext i
  cases hs : (run ops).ops i with
  | some o =>
    obtain ⟨ho, hi⟩ := reach_stored (runReach ops) i o hs
    have h := hm o ho
    rw [hi, hs] at h
    exact h
  | none =>
    cases ht : (run ops.reverse).ops i with
    | none => rfl
    | some o =>
      obtain ⟨ho, hi⟩ := reach_stored (runReach ops.reverse) i o ht
      have h := hm o (by simpa using ho)
      rw [hi, hs, ht] at h
      exact h

def connectAgree :=
  if hs : (run before).queue = [] then
    if ht : (run before.reverse).queue = [] then
      if hm : before.all (fun o => decide ((run before).ops o.id = (run before.reverse).ops o.id)) = true then
        some (PLift.up (connect_agree (runInv before) (runInv before.reverse) hs ht
          (sameOps before (by simpa using hm)) c (keyOf bob)))
      else none
    else none
  else none

def connectAdmitted := do
  let ⟨hc⟩ ← certifyDB before r rootFact
  let ⟨hr⟩ ← certifyDB before requestB (.request c requestB.id bob.pk (keyOf bob) false)
  let ⟨ha⟩ ← certifyDB before approval (.approval c requestB.id c)
  if hq : (run before).queue = [] then
    if hy : (run before).ops admission.id = some admission then
      if hl : (deviceLive c bob.pk).eval (run before) = true then
        return PLift.up (connect_admitted (runInv before) hq hy
          (decode_encode _) rfl rfl hc hr ha
          ((deviceLive_iff (runInv before) hq c bob.pk).1 hl).2)
      else none
    else none
  else none

def later := post c c alice "content-key-1".toUTF8 "A later signed op".toUTF8 2 29880002

theorem ingestExtends (s : DB Fact) (o : Op) : Extends s.ops (ingestS o s).ops := by
  intro i p hp
  unfold ingestS
  split
  · exact hp
  · rename_i hn
    show (if i = o.id then some o else s.ops i) = some p
    by_cases hi : i = o.id
    · subst hi; rw [hn] at hp; cases hp
    · simp [hi, hp]

-- A genuinely new op arrives after removal.
def cutStays := applyLaw cut (fun h => cut_stays (ingestExtends (run after) later) h)

def endpointSigned := applyLaw (certifyDB before admission bobFact) endpoint_signed

def nodeSecret := Bytes.digest "vacuity-node-secret".toUTF8
def nodeEndpoint := endpoint nodeSecret
def endpointDerives := applyLaw
  (certifyDB [nodeEndpoint] nodeEndpoint (.endpoint (cryptoSeal.pub nodeSecret) nodeSecret)) endpoint_derives

def bobProfile := profile c admission.id bob "Bob".toUTF8 29880001
def profileAuthorized := applyLaw
  (certifyDB (before ++ [bobProfile]) bobProfile (.profile c requestB.id "Bob".toUTF8 29880001)) profile_authorized

def noRenaming (Signed : Key → ByteArray → Prop) := applyLaw
  (certifyDB (before ++ [bobProfile]) bobProfile (.profile c requestB.id "Bob".toUTF8 29880001))
  (fun h => fun hU : Unforgeable ed25519 _ Signed => no_renaming hU h)

def requestC := request c invitation.id carol (keyOf bob) bearer.sk
def approvalC := approve c requestC.id c alice
def admissionC := admit c requestC.id approvalC.id
def rejoined := after ++ [requestC,approvalC,admissionC]

def newDeviceTrusted := do
  let ⟨ha⟩ ← certifyDB rejoined admission bobFact
  let ⟨hr⟩ ← certifyDB rejoined removeB (.removal c requestB.id c)
  let ⟨hc⟩ ← certifyDB rejoined admissionC (.admission c requestC.id carol.pk (keyOf bob))
  if hq : (run rejoined).queue = [] then
    if hl : (deviceLive c carol.pk).eval (run rejoined) = true then
      return PLift.up (new_device_trusted (runInv rejoined) hq
        (show Admitted ed25519 (run rejoined).ops c requestB.id bob.pk (keyOf bob) from ⟨admission.id,ha⟩)
        (show Removed ed25519 (run rejoined).ops c requestB.id from ⟨removeB.id,c,hr⟩)
        (show Admitted ed25519 (run rejoined).ops c requestC.id carol.pk (keyOf bob) from ⟨admissionC.id,hc⟩)
        ((deviceLive_iff (runInv rejoined) hq c carol.pk).1 hl))
    else none
  else none

def acceptedBob := accept c bob.pk
def secretBob := secret (sha256 "vacuity-bob".toUTF8)
def mineNotRemoved :=
  if hq : (run (before ++ [acceptedBob, secretBob])).queue = [] then
    if hm : (mine c).eval (run (before ++ [acceptedBob, secretBob])) = some (bob.pk, acceptedBob.id) then
      some (PLift.up (mine_not_removed (runInv (before ++ [acceptedBob, secretBob])) hq hm))
    else none
  else none

/-- Bob removes himself, citing his own admission as the authority. -/
def selfOwn := remove c admission.id admission.id admission.id bob
/-- The control: the same self-removal citing his message as the
authority, which the old rule (any shared fact) took. -/
def selfMsg := remove c admission.id message.id admission.id bob
/-- Another control: citing another member's admission (Alice's root). -/
def selfOther := remove c admission.id c admission.id bob

def removalAnchored := do
  let ⟨hr⟩ ← certifyDB (before ++ [selfOwn]) selfOwn (.removal c requestB.id requestB.id)
  pure (PLift.up (removal_anchored hr))

def main : IO UInt32 := do
  let t ← Checks.new
  t.ok "connect_iff with admitted Bob" connectIff.isSome
  t.ok "approveReq_wrap_admits: Alice's approval of Bob's pending request writes the admission citing it"
    (wrapAdmits pending).isSome
  t.ok "approveReq_wrap_admits control: without the request the write is the bare approval"
    (decide ((approvalWrite [r, invitation]).ops = [approve c requestB.id c alice]))
  t.ok "deviceLive_iff with admitted Bob" deviceLiveIff.isSome
  t.ok "members_iff with admitted Bob" membersIff.isSome
  t.ok "recipients_iff with admitted Bob" recipientsIff.isSome
  t.ok "removals_iff with removed Bob" removalsIff.isSome
  t.ok "removal_anchored: Bob's self-removal citing his own admission is Valid" removalAnchored.isSome
  t.ok "control: a self-removal citing a message as its authority is refused"
    ((run (before ++ [selfMsg])).status selfMsg.id == some .invalid)
  t.ok "control: a self-removal citing another member's admission as its authority is refused"
    ((run (before ++ [selfOther])).status selfOther.id == some .invalid)
  t.ok "connect_approved accepts non-founder Bob" connectApproved.isSome
  t.ok "cut_consented with actual Bob request and removal" cutConsented.isSome
  t.ok "refuse_nonmember with actually admitted then cut Bob" refuseNonmember.isSome
  t.ok "removal_cuts_off with actual removal and node admission" removalCutsOff.isSome
  t.ok "cut_stays after new op arrival" cutStays.isSome
  t.ok "new op is absent before arrival" ((run after).ops later.id == none)
  t.ok "connect_agree across reversed arrival order" connectAgree.isSome
  t.ok "connect_admitted: exact approver and live device" connectAdmitted.isSome
  t.ok "before: Bob connects" ((allowPeer c (keyOf bob)).eval (run before))
  t.ok "after: Bob cannot connect" (!(allowPeer c (keyOf bob)).eval (run after))
  t.ok "Mallory never connects" (!(allowPeer c (keyOf mallory)).eval (run before))
  t.ok "before: two members" (((members c).eval (run before)).length == 2)
  t.ok "after: no members" ((members c).eval (run after) |>.isEmpty)
  t.ok "before: wraps include Bob" ((recipients c).eval (run before) |>.contains (keyOf bob))
  t.ok "after: wraps exclude Bob" (!((recipients c).eval (run after) |>.contains (keyOf bob)))
  t.ok "endpoint_signed: Bob signed node binding" endpointSigned.isSome
  t.ok "endpoint_derives: real 32-byte seed and X25519 public key" endpointDerives.isSome
  t.ok "profile_authorized: Bob's signed name" profileAuthorized.isSome
  t.ok "new_device_trusted: Carol joins using Bob's node key" newDeviceTrusted.isSome
  t.ok "Bob stays cut after Carol joins" (!(deviceLive c bob.pk).eval (run rejoined))
  t.ok "new device differs from removed one" (carol.pk != bob.pk && requestC.id != requestB.id)
  t.ok "mine_not_removed: accepted Bob before removal" mineNotRemoved.isSome
  t.ok "mine rejects acceptance without device secret" ((mine c).eval (run (before ++ [acceptedBob])) == none)
  t.ok "mine rejects Bob after removal" ((mine c).eval (run (after ++ [acceptedBob, secretBob])) == none)
  let forgedProfile := profile c admission.id mallory "Mallory".toUTF8 29880002
  t.ok "profile signed by wrong device rejected" ((run (before ++ [forgedProfile])).status forgedProfile.id == some .invalid)
  t.finish "identity trust vacuity (runtime premises)"

end Vacuity.IdentityTrust
