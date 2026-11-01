import tests.vacuity.IdentityFixture

/-! Runtime witnesses for the identity laws. The inputs are deterministic synthetic
users and messages, composed and checked with the production SHA-256/Ed25519
implementation. Each successful `certify` branch constructs the actual `V`
premise; `applyLaw` packages the production theorem's conclusion.

These are runtime premise checks, not closed kernel proofs of the extern crypto
functions. Lean checks the bridge from each successful check to the theorem.
No `native_decide`, extra axiom or assumed fixture validity is used. -/
namespace Vacuity.Identity
open Engine Community Codec Tests

-- A proper extension, not reflexivity: add two opposing removals.
theorem table_append_extends (xs ys : List Op) : Extends (table xs) (table (xs ++ ys)) := by
  intro x o h
  unfold table at h ⊢
  rw [List.find?_append, h]
  rfl

def adminRemoval : Option (PLift (V ed25519 (table after) removeB.id (.removal c requestB.id c))) := do
  let ⟨hc⟩ ← certify after r rootFact
  let ⟨hb⟩ ← certify after admission bobFact
  if hx : table after removeB.id = some removeB then
    if hs : ed25519.verify alice.pk (signed removeB (.remove (sig alice.sk [c,c,c,admission.id] (.remove .empty))))
        (sig alice.sk [c,c,c,admission.id] (.remove .empty)) = true then
      return ⟨admin_removal_stands hx (decode_encode _) rfl rfl hc hc hc
        (by simp [rootFact, isAdmin]) hb hs⟩
    else none
  else none

-- The same request approved before removal is admitted after both admins leave.
def removedApprover : Option (PLift (V ed25519 (table after) admission.id bobFact)) := do
  let ⟨hc⟩ ← certify after r rootFact
  let ⟨hr⟩ ← certify after requestB (.request c requestB.id bob.pk (keyOf bob) false 1)
  let ⟨ha⟩ ← certify after approval (.approval c requestB.id c)
  let ⟨hm⟩ ← certify after removeA (.removal c c requestB.id)
  if hy : table after admission.id = some admission then
    return ⟨removed_approver_admits hy (decode_encode _) rfl rfl hc hr ha ⟨removeA.id, requestB.id, hm⟩⟩
  else none

def requestValid : Option (PLift (V ed25519 (table after) requestB.id
    (.request c requestB.id bob.pk (keyOf bob) false 1))) := do
  let ⟨hc⟩ ← certify after r rootFact
  let ⟨hi⟩ ← certify after invitation (.invitation c c bearer.pk false 1)
  let cs := sig bob.sk [c, invitation.id] (.request bob.pk (keyOf bob) .empty .empty)
  let bs := sig bearer.sk [c, invitation.id] (.request bob.pk (keyOf bob) .empty .empty)
  if hx : table after requestB.id = some requestB then
    if hs : ed25519.verify bob.pk (signed requestB (.request bob.pk (keyOf bob) cs bs)) cs = true ∧
        ed25519.verify bearer.pk (signed requestB (.request bob.pk (keyOf bob) cs bs)) bs = true then
      return ⟨request_valid (keyed after) hx (decode_encode _) rfl rfl hc hi hs.1 hs.2⟩
    else none
  else none

def approveValid : Option (PLift (V ed25519 (table after) approval.id (.approval c requestB.id c))) := do
  let ⟨hc⟩ ← certify after r rootFact
  let ⟨hr⟩ ← certify after requestB (.request c requestB.id bob.pk (keyOf bob) false 1)
  let sg := sig alice.sk [c, requestB.id, c] (.approve .empty)
  if hx : table after approval.id = some approval then
    if hs : ed25519.verify alice.pk (signed approval (.approve sg)) sg = true ∧ alice.pk ≠ bob.pk then
      return ⟨approve_valid hx (decode_encode _) rfl rfl hc hr hc (by simp) hs.2 hs.1⟩
    else none
  else none

def admitAdmits : Option (PLift (V ed25519 (table after) admission.id bobFact)) := do
  let ⟨hc⟩ ← certify after r rootFact
  let ⟨hr⟩ ← certify after requestB (.request c requestB.id bob.pk (keyOf bob) false 1)
  let ⟨ha⟩ ← certify after approval (.approval c requestB.id c)
  if hx : table after admission.id = some admission then
    return ⟨admit_admits (us := [c]) hx (decode_encode _) rfl rfl hc hr
      (.cons ha .nil) (by simp) rfl⟩
  else none

-- Named certificates make the README's evidence traceable one law at a time.
def noImpersonation (Signed : Key → ByteArray → Prop) :=
  applyLaw (certify after message messageFact)
    (fun h => fun hU : Unforgeable ed25519 _ Signed => no_impersonation hU h)

def messageAuthorized := applyLaw (certify after message messageFact) message_authorized
def admissionNeedsApproval := applyLaw (certify after admission bobFact)
  (admission_needs_approval (keyed after))
def admissionApproved := applyLaw (certify after admission bobFact)
  (admission_approved (keyed after))
def requestInvited := applyLaw
  (certify after requestB (.request c requestB.id bob.pk (keyOf bob) false 1))
  (request_invited (keyed after))
def removalAuthorized := applyLaw
  (certify after removeB (.removal c requestB.id c)) removal_authorized
def adminGranted := applyLaw (certify after grantB (.admin c requestB.id)) admin_granted
def approvalSigned := applyLaw
  (certify after approval (.approval c requestB.id c)) approval_signed
def invitationIssued := applyLaw
  (certify after invitation (.invitation c c bearer.pk false 1)) invitation_issued
def admissionConsented := applyLaw (certify after admission bobFact) admission_consented
def namedByAdmin := applyLaw
  (certify after renamed (.named c c "Vacuity test community".toUTF8 1)) named_by_admin

def mutualRemoval := do
  let ⟨h1⟩ ← certify after removeB (.removal c requestB.id c)
  let ⟨h2⟩ ← certify after removeA (.removal c c requestB.id)
  pure (PLift.up (mutual_removal h1 h2))

def validStays := applyLaw (certify before message messageFact)
  (valid_stays (table_append_extends before [removeB,removeA]))

def laterMessage := post c c alice "content-key-1".toUTF8 "A later signed op".toUTF8 2 29880002

def removedStays := applyLaw (certify after removeB (.removal c requestB.id c))
  (fun h => removed_stays (table_append_extends after [laterMessage])
    (show Removed ed25519 (table after) c requestB.id from ⟨removeB.id,c,h⟩))

def main : IO UInt32 := do
  let t ← Checks.new
  t.ok "admission_needs_approval: non-founder Bob" admissionNeedsApproval.isSome
  t.ok "admission_approved: one distinct approver" admissionApproved.isSome
  t.ok "request_invited: both signatures and actual invitation" requestInvited.isSome
  t.ok "removal_authorized: Alice removes another user" removalAuthorized.isSome
  t.ok "admin_granted: Alice grants Bob admin" adminGranted.isSome
  t.ok "removed_stays: removed Bob survives later op delivery" removedStays.isSome
  t.ok "valid_stays: Bob's post remains after removals" validStays.isSome
  t.ok "message_authorized: actual Bob post" messageAuthorized.isSome
  t.ok "approval_signed: Alice is distinct from Bob" approvalSigned.isSome
  t.ok "invitation_issued: one-approval invitation" invitationIssued.isSome
  t.ok "named_by_admin: Alice names community" namedByAdmin.isSome
  t.ok "admission_consented: Bob's admission" admissionConsented.isSome
  t.ok "admin_removal_stands: explicit premises" adminRemoval.isSome
  t.ok "mutual_removal: two different admins" mutualRemoval.isSome
  t.ok "removed_approver_admits: removed Alice's approval still admits Bob" removedApprover.isSome
  t.ok "request_valid: invitation and two checked signatures" requestValid.isSome
  t.ok "approve_valid: distinct member signs approval" approveValid.isSome
  t.ok "admit_admits: exact threshold of distinct approvals" admitAdmits.isSome
  -- Independently observed outcomes and failures: these are executed, not erased proofs.
  t.ok "non-founder and distinct devices" (requestB.id != c && alice.pk != bob.pk)
  t.ok "removals do not erase Bob's history" (certify after message messageFact).isSome
  t.ok "actual extension has a new op" (table after laterMessage.id == none)
  t.ok "real content and counter" (!message.body.isEmpty && messageFact != rootFact)
  let forged := post c admission.id mallory "content-key-1".toUTF8 "I am Bob".toUTF8 2 29880001
  let bare := admit c requestB.id []
  let selfApproval := approve c requestB.id admission.id bob
  let duplicateAdmission := admit c requestB.id [approval.id, approval.id]
  let noBearer := request c invitation.id mallory (keyOf mallory) mallory.sk
  let forgedRemoval := remove c admission.id admission.id c bob
  for (label,o) in [("forged post",forged),("missing approval",bare),
      ("self approval",selfApproval),("duplicate approvals",duplicateAdmission),
      ("wrong bearer signature",noBearer),("unauthorized removal",forgedRemoval)] do
    t.ok label (specAt (family ed25519) (table (after ++ [o])) 8 o.id == some .invalid)
  -- Unforgeable is universally quantified over every key/message/signature.
  -- Runtime samples cannot discharge it; do not certify no_impersonation here.
  t.finish "identity vacuity (runtime premises; no_impersonation conditional)"

end Vacuity.Identity
