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

/-- Alice's ephemeral secret for her wrap to Bob. -/
def eskA : ByteArray := (Bytes.digest "vacuity-alice-esk".toUTF8).1

/-- The store before Alice approves, holding her copy of the community's
key (a local op, as `found` writes it). -/
def keyed : List Op := pending ++ [contentKey c communityKey.1]

/-- Alice's approval write over a store, as the intent runs it. -/
def approvalWrite (ops : List Op) (esk : ByteArray := .empty) : Write :=
  (approveReq c requestB.id c alice esk).eval (run ops)

def okB := approve c requestB.id c alice
def admB := admit c requestB.id okB.id

/-- `approveReq_wrap_admits` applied to Alice's actual approval of Bob's
request over a real store holding the community's key: the write is
three ops, so (the law's third case) it is her approval, the admission
citing it, and her wrap of the key `currentKey` reads. -/
def wrapAdmits : Option (PLift (∃ up prev k esk' e, (currentKey c).eval (run keyed) = some k ∧
    (approvalWrite keyed eskA).ops = [approve c requestB.id c alice up prev,
      admit c requestB.id (approve c requestB.id c alice up prev).id,
      wrapKey c c (admit c requestB.id (approve c requestB.id c alice up prev).id).id alice k esk' e])) :=
  if h : (approvalWrite keyed eskA).ops.length = 3 then
    some ⟨by
      obtain ⟨up, prev, hw⟩ := approveReq_wrap_admits (run keyed) c requestB.id c alice eskA
      rcases hw with hw | hw | ⟨k, esk', e, hk, hw⟩
      · simp [approvalWrite, hw] at h
      · simp [approvalWrite, hw] at h
      · exact ⟨up, prev, k, esk', e, hk, hw⟩⟩
  else none

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
  let ⟨hr⟩ ← certifyDB after removeB removeBFact
  pure ⟨requestB.id, keyOf bob, ⟨admission.id, _, ha⟩, ⟨removeB.id, c, [], hr⟩⟩

def cutConsented := applyLaw cut cut_consented

def nodeRows := [((sortOf bobFact, admission.id), bobFact)]

theorem nodeOnlyBob (hq : (run after).queue = [])
    (rows : (eval (run after) (admission.byKey.query [c, keyOf bob])).rows = nodeRows)
    (u : Id) (d : Key) (ha : Admitted ed25519 (run after).ops c u d (keyOf bob)) :
    u = requestB.id ∧ d = bob.pk := by
  obtain ⟨y, k, hv⟩ := ha
  obtain ⟨p, hp⟩ := (exists_row (runInv after) hq (by simp [rels]) [c, keyOf bob]
    (.admission c u d (keyOf bob) k)).2 ⟨y,hv,byKey_args.2 ⟨u,d,k,rfl⟩⟩
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
  let ⟨hr⟩ ← certifyDB after removeB removeBFact
  if hq : (run after).queue = [] then
    if rows : (eval (run after) (admission.byKey.query [c, keyOf bob])).rows = nodeRows then
      return PLift.up (removal_cuts_off (runInv after) hq
        (show Removed ed25519 (run after).ops c requestB.id from ⟨removeB.id, c, [], hr⟩)
        (fun u d had => ⟨keyOf bob, admission.id, keyId, (nodeOnlyBob hq rows u d had).2 ▸ ha⟩))
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
  let ⟨ha⟩ ← certifyDB before approval approvalFact
  if hq : (run before).queue = [] then
    if hy : (run before).ops admission.id = some admission then
      if hl : (deviceLive c bob.pk).eval (run before) = true then
        -- Alice's approval counts: read off the store by the counts view
        if hct : (counts c 1 approval.id approvalF).eval (run before) = true then
          return PLift.up (connect_admitted (runInv before) hq hy
            (decode_encode _) rfl rfl hc hr ha rfl rfl
            ((counts_iff (runInv before) hq 0 approval.id approvalF rfl ha rfl).1 hct)
            ((deviceLive_iff (runInv before) hq c bob.pk).1 hl).2)
        else none
      else none
    else none
  else none

def later := post c c alice keyId "A later signed op".toUTF8 2 29880002

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
def approvalC := approve c requestC.id c alice none (some approval.id)
def admissionC := admit c requestC.id approvalC.id
/-- Alice removes Bob (alone: Bob does not remove Alice here), then
approves Carol, a new device on Bob's node: a current member's
approval, so it counts. -/
def afterB := before ++ [removeB]
def rejoined := afterB ++ [requestC,approvalC,admissionC]

def newDeviceTrusted := do
  let ⟨ha⟩ ← certifyDB rejoined admission bobFact
  let ⟨hr⟩ ← certifyDB rejoined removeB removeBFact
  let ⟨hc⟩ ← certifyDB rejoined admissionC (.admission c requestC.id carol.pk (keyOf bob) keyId)
  if hq : (run rejoined).queue = [] then
    if hl : (deviceLive c carol.pk).eval (run rejoined) = true then
      if ht : (trusted c requestC.id carol.pk (keyOf bob)).eval (run rejoined) = true then
        return PLift.up (new_device_trusted (runInv rejoined) hq
          (show Admitted ed25519 (run rejoined).ops c requestB.id bob.pk (keyOf bob) from ⟨admission.id,_,ha⟩)
          (show Removed ed25519 (run rejoined).ops c requestB.id from ⟨removeB.id, c, [], hr⟩)
          ((trusted_iff' (runInv rejoined) hq ⟨admissionC.id, _, hc⟩).1 ht)
          ((deviceLive_iff (runInv rejoined) hq c carol.pk).1 hl))
      else none
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

/-! ## The causal cut, on real signed ops

Bob, admitted by Alice, approves Dave. Alice removes Bob, citing the
head of Bob's approval chain she holds (his approval of Dave): her cut.
Then Bob, removed, invites and approves a fresh device on his own node,
continuing his chain past the head. -/

def bearerD := Device.named "vacuity-bearer-dave"
def dave := Device.named "vacuity-dave"
def invD := invite c admission.id bob bearerD.pk false
def reqD := request c invD.id dave (keyOf dave) bearerD.sk
def okD := approve c reqD.id admission.id bob (some approval.id)
def admD := admit c reqD.id okD.id
def removeCut := remove c c c admission.id alice [okD.id]
def bearerR := Device.named "vacuity-bearer-again"
def bobAgain := Device.named "vacuity-bob-again"
def invR := invite c admission.id bob bearerR.pk false
def reqR := request c invR.id bobAgain (keyOf bob) bearerR.sk
def okR := approve c reqR.id admission.id bob (some approval.id) (some okD.id)
def admR := admit c reqR.id okR.id
/-- What Alice had seen when she removed Bob. -/
def seen := before ++ [invD, reqD, okD, admD]
def cutOps := seen ++ [removeCut, invR, reqR, okR, admR]

/-- Bob's approval of Dave: up Alice's approval of Bob, his chain's first. -/
def fD : Approve.Fact := ⟨c, reqD.id, requestB.id, bob.pk, reqD.id, dave.pk, keyOf dave, approval.id, 1, .empty, 0⟩
/-- Bob's approval after his removal: one place past the head Alice kept. -/
def fR : Approve.Fact := ⟨c, reqR.id, requestB.id, bob.pk, reqR.id, bobAgain.pk, keyOf bob, approval.id, 1, okD.id, 1⟩
def kCut : List (Key × Id × Nat) := [(bob.pk, okD.id, 0)]
def removeCutFact := Fact.removal c requestB.id c kCut

def admIntoBob (rows : List (Pos × Fact)) : Bool :=
  rows.any fun (_, g) => match g with
    | .admission c' u _ _ _ => decide (c' = c ∧ u = requestB.id)
    | _ => false

theorem admIntoBob_sound {s : DB Fact} (h : Inv (family ed25519) s) (hq : s.queue = []) {d : Key}
    (hb : admIntoBob (eval s (admission.byDevice.query [c, d])).rows = true) :
    ∃ e', Admitted ed25519 s.ops c requestB.id d e' := by
  obtain ⟨⟨p, g⟩, hm, hg⟩ := List.any_eq_true.1 hb
  obtain ⟨y, g', he, hv, hk⟩ := (mem_rows h hq (by simp [rels]) _).1 hm
  simp only [Prod.mk.injEq] at he; obtain ⟨_, rfl⟩ := he
  obtain ⟨u, e, k, rfl⟩ := byDevice_args.1 hk
  simp only [decide_eq_true_eq] at hg
  obtain ⟨_, rfl⟩ := hg
  exact ⟨e, y, k, hv⟩

/-- An approval naming Bob's node key is for a device of Bob's (cut), or
is by a device of Bob's outside the cut. -/
def readmitCheck (s : DB Fact) (x : Id) (f : Approve.Fact) : Bool :=
  !decide (f.c = c ∧ f.re = keyOf bob) ||
  admIntoBob (eval s (admission.byDevice.query [c, f.rd])).rows ||
  (admIntoBob (eval s (admission.byDevice.query [c, f.dev])).rows &&
    !inCut (eval s (approval.byDev.query [c, f.dev])).rows x f kCut)

theorem readmitCheck_sound {s : DB Fact} (h : Inv (family ed25519) s) (hq : s.queue = []) {z : Id}
    (hz : V ed25519 s.ops z removeCutFact) {x : Id} {f : Approve.Fact}
    (hx : V ed25519 s.ops x (.ofApproval f)) (hb : readmitCheck s x f = true) (hc : f.c = c) (he : f.re = keyOf bob) :
    (∃ e', Admitted ed25519 s.ops c requestB.id f.rd e') ∨
      ∃ y g e', Above ed25519 s.ops y x ∧ V ed25519 s.ops y (.ofApproval g) ∧
        Admitted ed25519 s.ops c requestB.id g.dev e' ∧ ¬ InCut ed25519 s.ops y g kCut := by
  simp only [readmitCheck, hc, he, and_self, decide_true, Bool.not_true, Bool.false_or,
    Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at hb
  rcases hb with hb | ⟨hb, hi⟩
  · exact Or.inl (admIntoBob_sound h hq hb)
  · obtain ⟨e', ha⟩ := admIntoBob_sound h hq hb
    refine Or.inr ⟨x, f, e', .here, hx, ha, fun hin => ?_⟩
    rw [(inCut_iff h hq hx hz).2 hin] at hi; cases hi

/-- Every Valid approval in a store built from these ops is one of them. -/
theorem all_approvals (ops : List Op) (hq : (run ops).queue = []) (P : Id → Approve.Fact → Prop)
    (hall : ∀ o ∈ ops, ∀ f, (run ops).status o.id = some (.valid (.ofApproval f)) → P o.id f) :
    ∀ x f, V ed25519 (run ops).ops x (.ofApproval f) → P x f := by
  intro x f hv
  have hs := (status_iff_spec (runInv ops) hq x _).2 hv
  have hst : ((run ops).ops x).isSome := by
    cases ho : (run ops).ops x with
    | some _ => rfl
    | none =>
      obtain ⟨n, hn⟩ := hv
      cases n with
      | zero => simp [specAt] at hn
      | succ n => simp [specAt, ho] at hn
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 hst
  obtain ⟨hm, hi⟩ := reach_stored (runReach ops) x o ho
  subst hi
  exact hall o hm f hs

def outsideCut := do
  let ⟨hz⟩ ← certifyDB cutOps removeCut removeCutFact
  let ⟨hx⟩ ← certifyDB cutOps okR (.ofApproval fR)
  let ⟨ha⟩ ← certifyDB cutOps admission bobFact
  if hq : (run cutOps).queue = [] then
    if hi : inCut (eval (run cutOps) (approval.byDev.query [c, fR.dev])).rows okR.id fR kCut = false then
      return PLift.up (outside_cut_admits_none (C := ed25519) hz hx ⟨admission.id, _, ha⟩
        (fun hin => by rw [(inCut_iff (runInv cutOps) hq hx hz).2 hin] at hi; cases hi))
    else none
  else none

def noSelfReadmission := do
  let ⟨hz⟩ ← certifyDB cutOps removeCut removeCutFact
  let ⟨hr⟩ ← certifyDB cutOps r rootFact
  if hq : (run cutOps).queue = [] then
    if hk : keyOf alice = keyOf bob then none else
    if hall : cutOps.all (fun o => match (run cutOps).status o.id with
        | some (.valid (.ofApproval f)) => readmitCheck (run cutOps) o.id f
        | _ => true) = true then
      return PLift.up (no_self_readmission (runInv cutOps) hq hz
        (fun u' d k hv => by
          have := spec_det hr hv
          simp only [rootFact, Verdict.valid.injEq, Fact.admission.injEq] at this
          exact hk this.2.2.2.1)
        (all_approvals cutOps hq _ fun o ho f hs hc he => by
          have := (List.all_eq_true.1 hall) o ho
          rw [hs] at this
          exact readmitCheck_sound (runInv cutOps) hq hz ((runInv cutOps).sound _ _ hs) this hc he))
    else none
  else none

theorem seenExtends (he : seen.all (fun o => decide ((run cutOps).ops o.id = some o)) = true) :
    Extends (run seen).ops (run cutOps).ops := by
  intro x o ho
  obtain ⟨hm, hi⟩ := reach_stored (runReach seen) x o ho
  have hh := of_decide_eq_true ((List.all_eq_true.1 he) o hm)
  rw [hi] at hh; exact hh

def insideCutStays := do
  let ⟨hdS⟩ ← certifyDB seen okD (.ofApproval fD)
  let ⟨haS⟩ ← certifyDB seen approval approvalFact
  let ⟨hdC⟩ ← certifyDB cutOps okD (.ofApproval fD)
  let ⟨haC⟩ ← certifyDB cutOps approval approvalFact
  if hqS : (run seen).queue = [] then
    if hqC : (run cutOps).queue = [] then
      if he : seen.all (fun o => decide ((run cutOps).ops o.id = some o)) = true then
        if hc : (counts c 2 okD.id fD).eval (run seen) = true then
          if hkD : (kept c okD.id fD).eval (run cutOps) = true then
            if hkA : (kept c approval.id approvalF).eval (run cutOps) = true then
              return PLift.up (inside_cut_stays (seenExtends he)
                ((counts_iff (runInv seen) hqS 1 okD.id fD rfl hdS rfl).1 hc)
                (fun y g hab hy => by
                  cases hab with
                  | here =>
                    have := spec_det hdS hy
                    simp only [Verdict.valid.injEq, Fact.ofApproval.injEq] at this; subst this
                    exact (kept_iff (runInv cutOps) hqC hdC).1 hkD
                  | up hv hd hab' =>
                    rename_i f'
                    have := spec_det hdS hv
                    simp only [Verdict.valid.injEq, Fact.ofApproval.injEq] at this; subst this
                    cases hab' with
                    | here =>
                      have := spec_det haS hy
                      simp only [approvalFact, Verdict.valid.injEq, Fact.ofApproval.injEq] at this; subst this
                      exact (kept_iff (runInv cutOps) hqC haC).1 hkA
                    | up hv' hd' _ =>
                      have := spec_det haS hv'
                      simp only [approvalFact, Verdict.valid.injEq, Fact.ofApproval.injEq] at this; subst this
                      simp [approvalF] at hd'))
            else none
          else none
        else none
      else none
    else none
  else none

def trustAgree :=
  if hs : (run cutOps).queue = [] then
    if ht : (run cutOps.reverse).queue = [] then
      if hm : cutOps.all (fun o => decide ((run cutOps).ops o.id = (run cutOps.reverse).ops o.id)) = true then
        some (PLift.up (trust_agree (runInv cutOps) (runInv cutOps.reverse) hs ht
          (sameOps cutOps (by simpa using hm)) c reqR.id bobAgain.pk (keyOf bob)))
      else none
    else none
  else none

def distinctCut : Option (PLift (Distinct (cutOps ++ cutOps.reverse))) :=
  let L := cutOps ++ cutOps.reverse
  if hd : L.all (fun a => L.all fun b => decide (a.id = b.id → a = b)) = true then
    some ⟨by
      intro a ha b hb he
      exact of_decide_eq_true ((List.all_eq_true.1 ((List.all_eq_true.1 hd) a ha)) b hb) he⟩
  else none

def trustOrderFree := do
  let ⟨hd⟩ ← distinctCut
  if hs : (run cutOps).queue = [] then
    if ht : (run cutOps.reverse).queue = [] then
      return PLift.up (trust_order_free (runReach cutOps) (runReach cutOps.reverse) hd
        (fun _ => List.mem_reverse.symm) hs ht c reqR.id bobAgain.pk (keyOf bob))
    else none
  else none

def trustedIff := if hq : (run cutOps).queue = [] then
  some (PLift.up (trusted_iff (runInv cutOps) hq c reqR.id bobAgain.pk (keyOf bob))) else none

def countsIff := do
  let ⟨hx⟩ ← certifyDB cutOps okD (.ofApproval fD)
  if hq : (run cutOps).queue = [] then
    return PLift.up (counts_iff (runInv cutOps) hq 1 okD.id fD rfl hx rfl)
  else none

def keptIff := do
  let ⟨hx⟩ ← certifyDB cutOps okR (.ofApproval fR)
  if hq : (run cutOps).queue = [] then
    return PLift.up (kept_iff (c := c) (runInv cutOps) hq hx)
  else none

def inCutIff := do
  let ⟨hz⟩ ← certifyDB cutOps removeCut removeCutFact
  let ⟨hx⟩ ← certifyDB cutOps okD (.ofApproval fD)
  if hq : (run cutOps).queue = [] then
    return PLift.up (inCut_iff (runInv cutOps) hq hx hz)
  else none

def approvalLinks := applyLaw (certifyDB cutOps okR (.ofApproval fR)) approval_links

def removalCut := applyLaw (certifyDB cutOps removeCut removeCutFact)
  (fun h => removal_cut h (List.mem_singleton.2 rfl))

/-- What Alice's remover flow writes over the store she had seen. -/
def removeWrite := (removeMember c requestB.id alice).eval (run seen)

/-- `removeMember_keeps` on Alice's actual removal of Bob: every finite
premise checked on the store she had seen (Bob's chain unforked, places
small, under the heads cap), conditional on Ed25519's universal
correctness, as `removeMember_valid` is. -/
def removeKeeps := do
  let ⟨hx⟩ ← certifyDB seen okD (.ofApproval fD)
  let ⟨ha⟩ ← certifyDB seen admission bobFact
  if hq : (run seen).queue = [] then
    if ho : removeCut ∈ removeWrite.ops then
      if hs : (run cutOps).ops removeCut.id = some removeCut then
        if he : seen.all (fun o => decide ((run cutOps).ops o.id = some o)) = true then
          if hcap : ((headsOf c [] (eval (run seen) (admission.byUser.query [c, requestB.id])).rows).eval
              (run seen)).length ≤ maxHeads then
            if hsm : seen.all (fun o => match (run seen).status o.id with
                | some (.valid (.ofApproval g)) => decide (g.c = c → g.dev = fD.dev → g.n < 2 ^ 64)
                | _ => true) = true then
              if hon : seen.all (fun o => seen.all fun o' =>
                  match (run seen).status o.id, (run seen).status o'.id with
                  | some (.valid (.ofApproval g)), some (.valid (.ofApproval g')) =>
                    decide (g.c = c → g'.c = c → g.dev = fD.dev → g'.dev = fD.dev → g.n = g'.n → o.id = o'.id)
                  | _, _ => true) = true then
                let small := all_approvals seen hq (fun _ g => g.c = c → g.dev = fD.dev → g.n < 2 ^ 64)
                  fun o hm g hst => by
                    have := (List.all_eq_true.1 hsm) o hm
                    rw [hst] at this; exact of_decide_eq_true this
                let one := all_approvals seen hq (fun y g => ∀ y' g', V ed25519 (run seen).ops y' (.ofApproval g') →
                    g.c = c → g'.c = c → g.dev = fD.dev → g'.dev = fD.dev → g.n = g'.n → y = y')
                  fun o hm g hst => all_approvals seen hq (fun y' g' => g.c = c → g'.c = c → g.dev = fD.dev →
                      g'.dev = fD.dev → g.n = g'.n → o.id = y')
                    fun o' hm' g' hst' => by
                      have := (List.all_eq_true.1 ((List.all_eq_true.1 hon) o hm)) o' hm'
                      rw [hst, hst'] at this; exact of_decide_eq_true this
                some (PLift.up (fun hsig : ∀ m, ed25519.verify alice.pk m (edSign alice.sk m) = true =>
                  removeMember_keeps (runInv seen) hq hsig ho (seenExtends he) hs hcap hx rfl ⟨admission.id, _, ha⟩
                    small (fun y y' g g' hv hv' => one y g hv y' g' hv')))
              else none
            else none
          else none
        else none
      else none
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
  let ⟨hr⟩ ← certifyDB (before ++ [selfOwn]) selfOwn (.removal c requestB.id requestB.id [])
  pure (PLift.up (removal_anchored hr))

def main : IO UInt32 := do
  let t ← Checks.new
  t.ok "connect_iff with admitted Bob" connectIff.isSome
  t.ok "approveReq_wrap_admits: Alice's approval of Bob's request writes the admission and her wrap of the community key"
    wrapAdmits.isSome
  t.ok "approveReq_wrap_admits control: without the community key there is no wrap"
    (decide ((approvalWrite pending eskA).ops = [okB, admB]))
  t.ok "approveReq_wrap_admits control: without the request the write is the bare approval"
    (decide ((approvalWrite [r, invitation]).ops = [approve c requestB.id c alice]))
  t.ok "approveReq cites the founder's chain: a second approval's prev is the first"
    (((approveReq c requestC.id c alice).eval (run before)).ops.head?.map (·.reqs) ==
      some [c, requestC.id, c, approval.id])
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
  t.ok "outside_cut_admits_none: Bob's approval past Alice's cut counts for nothing" outsideCut.isSome
  t.ok "no_self_readmission: removed Bob's own approval does not let his node in" noSelfReadmission.isSome
  t.ok "inside_cut_stays: Bob's approval of Dave, inside the cut, still counts" insideCutStays.isSome
  t.ok "trust_agree across reversed arrival order" trustAgree.isSome
  t.ok "trust_order_free across reversed arrival order" trustOrderFree.isSome
  t.ok "trusted_iff on the cut store" trustedIff.isSome
  t.ok "counts_iff on Bob's approval of Dave" countsIff.isSome
  t.ok "kept_iff on Bob's approval past the cut" keptIff.isSome
  t.ok "inCut_iff on Bob's approval of Dave" inCutIff.isSome
  t.ok "approval_links on Bob's approval past the cut" approvalLinks.isSome
  t.ok "removal_cut on Alice's removal of Bob" removalCut.isSome
  t.ok "removeMember_keeps: Alice's actual removal keeps Bob's approval of Dave (finite premises; signing universal)"
    removeKeeps.isSome
  t.ok "cut: removed Bob's node is refused" (!(allowPeer c (keyOf bob)).eval (run cutOps))
  t.ok "cut: Dave, approved by Bob inside the cut, is let in" ((allowPeer c (keyOf dave)).eval (run cutOps))
  t.ok "cut: Bob's approval of Dave counts, his later one does not"
    ((counts c 2 okD.id fD).eval (run cutOps) && !(counts c 2 okR.id fR).eval (run cutOps))
  t.ok "cut: the removal the remover flow writes cites Bob's chain head"
    (((removeMember c requestB.id alice).eval (run seen)).ops.map (·.reqs) == [[c, c, c, admission.id, okD.id]])
  t.finish "identity trust vacuity (runtime premises)"

end Vacuity.IdentityTrust
