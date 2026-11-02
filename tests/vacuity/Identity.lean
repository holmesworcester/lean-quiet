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

def adminRemoval : Option (PLift (V ed25519 (table after) removeB.id removeBFact)) := do
  let ⟨hc⟩ ← certify after r rootFact
  let ⟨hb⟩ ← certify after admission bobFact
  if hx : table after removeB.id = some removeB then
    if hs : ed25519.verify alice.pk (signed removeB (.remove (sig alice.sk [c,c,c,admission.id] (.remove .empty))))
        (sig alice.sk [c,c,c,admission.id] (.remove .empty)) = true then
      return ⟨admin_removal_stands (ys := []) (ps := []) hx (decode_encode _) rfl rfl hc hc hc
        (by simp [rootFact, isAdmin]) hb .nil rfl hs⟩
    else none
  else none

-- The same request approved before removal is admitted after both admins leave.
def removedApprover : Option (PLift (V ed25519 (table after) admission.id bobFact)) := do
  let ⟨hc⟩ ← certify after r rootFact
  let ⟨hr⟩ ← certify after requestB (.request c requestB.id bob.pk (keyOf bob) false)
  let ⟨ha⟩ ← certify after approval approvalFact
  let ⟨hm⟩ ← certify after removeA removeAFact
  if hy : table after admission.id = some admission then
    return ⟨removed_approver_admits hy (decode_encode _) rfl rfl hc hr ha rfl rfl ⟨removeA.id, requestB.id, [], hm⟩⟩
  else none

def requestValid : Option (PLift (V ed25519 (table after) requestB.id
    (.request c requestB.id bob.pk (keyOf bob) false))) := do
  let ⟨hc⟩ ← certify after r rootFact
  let ⟨hi⟩ ← certify after invitation (.invitation c c bearer.pk false)
  let cs := sig bob.sk [c, invitation.id] (.request bob.pk (keyOf bob) .empty .empty)
  let bs := sig bearer.sk [c, invitation.id] (.request bob.pk (keyOf bob) .empty .empty)
  if hx : table after requestB.id = some requestB then
    if hs : ed25519.verify bob.pk (signed requestB (.request bob.pk (keyOf bob) cs bs)) cs = true ∧
        ed25519.verify bearer.pk (signed requestB (.request bob.pk (keyOf bob) cs bs)) bs = true then
      return ⟨request_valid (keyed after) hx (decode_encode _) rfl rfl hc hi hs.1 hs.2⟩
    else none
  else none

def approveValid : Option (PLift (V ed25519 (table after) approval.id approvalFact)) := do
  let ⟨hc⟩ ← certify after r rootFact
  let ⟨hr⟩ ← certify after requestB (.request c requestB.id bob.pk (keyOf bob) false)
  let sg := sig alice.sk [c, requestB.id, c] (.approve .empty)
  if hx : table after approval.id = some approval then
    if hs : ed25519.verify alice.pk (signed approval (.approve sg)) sg = true ∧ alice.pk ≠ bob.pk then
      return ⟨approve_valid (ys := []) (ps := []) (t := (.empty, 0, .empty, 0)) hx (decode_encode _) rfl rfl
        hc hr hc .nil (by simp [Approve.links]) (by simp) hs.2 hs.1⟩
    else none
  else none

def admitAdmits : Option (PLift (V ed25519 (table after) admission.id bobFact)) := do
  let ⟨hc⟩ ← certify after r rootFact
  let ⟨hr⟩ ← certify after requestB (.request c requestB.id bob.pk (keyOf bob) false)
  let ⟨ha⟩ ← certify after approval approvalFact
  if hx : table after admission.id = some admission then
    return ⟨admit_admits hx (decode_encode _) rfl rfl hc hr ha rfl rfl⟩
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
  (certify after requestB (.request c requestB.id bob.pk (keyOf bob) false))
  (request_invited (keyed after))
def removalAuthorized := applyLaw
  (certify after removeB removeBFact) removal_authorized
def adminGranted := applyLaw (certify after grantB (.admin c requestB.id)) admin_granted
def approvalSigned := applyLaw
  (certify after approval approvalFact) approval_signed
def invitationIssued := applyLaw
  (certify after invitation (.invitation c c bearer.pk false)) invitation_issued
def admissionConsented := applyLaw (certify after admission bobFact) admission_consented
def namedByAdmin := applyLaw
  (certify after renamed (.named c c "Vacuity test community".toUTF8 1)) named_by_admin

-- Alice (founder) removes Bob and Bob (granted admin) removes Alice. The
-- law derives both removals from the two signed ops, both admins' admin
-- facts and both admissions; neither removal's validity is an input.
def mutualRemoval := do
  let ⟨hc⟩ ← certify after r rootFact
  let ⟨hb⟩ ← certify after admission bobFact
  let ⟨hg⟩ ← certify after grantB (.admin c requestB.id)
  let sa := sig alice.sk [c, c, c, admission.id] (.remove .empty)
  let sb := sig bob.sk [c, admission.id, grantB.id, c] (.remove .empty)
  if hx : table after removeB.id = some removeB then
    if hy : table after removeA.id = some removeA then
      if hs : ed25519.verify alice.pk (signed removeB (.remove sa)) sa = true ∧
          ed25519.verify bob.pk (signed removeA (.remove sb)) sb = true then
        return PLift.up (mutual_removal (hsx := []) (hsy := []) (psx := []) (psy := []) hc hx
          (decode_encode _) rfl rfl hc hc (by simp [rootFact, isAdmin, c]) hb .nil rfl hs.1
          hy (decode_encode _) rfl rfl hb hg (by simp [isAdmin, c]) hc .nil rfl hs.2)
      else none
    else none
  else none

def validStays := applyLaw (certify before message messageFact)
  (valid_stays (table_append_extends before [removeB,removeA]))

def laterMessage := post c c alice keyId "A later signed op".toUTF8 2 29880002

def removedStays := applyLaw (certify after removeB removeBFact)
  (fun h => removed_stays (table_append_extends after [laterMessage])
    (show Removed ed25519 (table after) c requestB.id from ⟨removeB.id, c, [], h⟩))

-- Alice's second device: her own approval of its device link's request,
-- and its admission into her user (the founder's, c).
/-- Alice's approval of the link request, as the store judges it. -/
def linkApprovalFact : Option Approve.Fact :=
  match specAt (family ed25519) (table linked) 8 linkApproval.id with
  | some (.valid (.ofApproval g)) => some g
  | _ => none

def linkApproved : Option (PLift (∃ g : Approve.Fact, g.u = c ∧
    (∃ o i k, table linked requestA2.id = some o ∧ o.reqs = [c, i] ∧
      V ed25519 (table linked) i (Fact.invitation c g.u k true)) ∧
    ∃ ra ea ka, V ed25519 (table linked) ra (Fact.admission c g.u g.dev ea ka) ∧ g.dev ≠ alice2.pk)) := do
  let g ← linkApprovalFact
  let ⟨hx⟩ ← certify linked linkApproval (.ofApproval g)
  let ⟨hr⟩ ← certify linked requestA2 (.request c c alice2.pk (keyOf alice2) true)
  if hgc : g.c = c then
    if hgr : g.req = requestA2.id then
      return PLift.up ⟨g, link_approved_by_issuer (g := g) (keyed linked) hx hgc hgr hr⟩
    else none
  else none

def linkAdmits := applyLaw (certify linked linkAdmission (.admission c c alice2.pk (keyOf alice2) keyId))
  (link_admits_issuer (keyed linked))

def main : IO UInt32 := do
  let t ← Checks.new
  t.ok "link_approved_by_issuer: Alice approves her second device's request" linkApproved.isSome
  t.ok "link_admits_issuer: her second device is admitted into her user" linkAdmits.isSome
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
  t.ok "admit_admits: one approval" admitAdmits.isSome
  -- Independently observed outcomes and failures: these are executed, not erased proofs.
  t.ok "non-founder and distinct devices" (requestB.id != c && alice.pk != bob.pk)
  t.ok "removals do not erase Bob's history" (certify after message messageFact).isSome
  t.ok "actual extension has a new op" (table after laterMessage.id == none)
  t.ok "real content and counter" (!message.body.isEmpty && messageFact != rootFact)
  let forged := post c admission.id mallory keyId "I am Bob".toUTF8 2 29880001
  let bare := mkOp [c, requestB.id] .admit
  let selfApproval := approve c requestB.id admission.id bob
  let duplicateAdmission := mkOp [c, requestB.id, approval.id, approval.id] .admit
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
