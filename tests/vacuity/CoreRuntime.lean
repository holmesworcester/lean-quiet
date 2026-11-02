import tests.vacuity.IdentityTrust
import tests.vacuity.Identity
import engine.core.IdemLaws
import engine.core.Termination
import engine.core.Budget
import engine.core.WindowLaws

namespace Vacuity.CoreRuntime
open Engine Community Tests Vacuity.Identity Vacuity.IdentityTrust
set_option linter.defProp false

instance distinctDec (ops : List Op) : Decidable (Distinct ops) := by
  unfold Distinct
  infer_instance

-- Same real signed histories as the identity tests, received in opposite orders.
def distinct := if h : Distinct (before ++ before.reverse) then some (PLift.up h) else none
def stored := (load before).ops message.id

def alreadyKnown := if h : (load before).ops message.id = some message then
  some (PLift.up (ingestS_known h)) else none

def twice := ingestS_twice message (load before)
def runningTwice := ingest_twice message (load before)
def loop := run_ingestEach before (DB.empty : DB Fact)
def again := ingestAll_again before (DB.empty : DB Fact) (o := message) (by simp [before])
def freshMessage := post c c alice keyId "Another message".toUTF8 2 29880002
def invariantIngest := inv_ingest (runInv before) freshMessage
def invariantStep := inv_step (reach_inv (loadReach before))
def reachableDrain := reach_drain (loadReach before) 400

def verdictMatches := if hq : (run before).queue = [] then
  some (PLift.up (status_iff_spec (runInv before) hq message.id (.valid messageFact))) else none

def terminate := do
  let ⟨hd⟩ ← distinct
  let dl : Distinct before := fun a ha b hb => hd a (List.mem_append_left _ ha) b (List.mem_append_left _ hb)
  pure (PLift.up (drain_settles dl (loadReach before)))

def bounded := if hd : Distinct before then
  some (PLift.up (drain_bounded hd (budget before (load before)) (load before) (loadReach before) (Nat.le_refl _)))
else none

def opsExact := if hd : Distinct before then
  some (PLift.up (reach_ops (runReach before) hd message.id message)) else none

def ordersAgree := do
  let ⟨hd⟩ ← distinct
  if hq : (run before).queue = [] then
    if hq' : (run before.reverse).queue = [] then
      return PLift.up (order_free (runReach before) (runReach before.reverse) hd
        (fun _ => List.mem_reverse.symm) hq hq')
    else none
  else none

def eventuallyAgree := do
  let ⟨hd⟩ ← distinct
  pure (PLift.up (same_ops_same_verdicts (loadReach before) (loadReach before.reverse) hd
    (fun _ => List.mem_reverse.symm)))

instance collisionDec (ops : List Op) : Decidable (CollisionFree ops) := by
  unfold CollisionFree
  infer_instance

def collisionFree := if h : CollisionFree before then some (PLift.up h) else none
def distinctFromHash := applyLaw collisionFree distinct_of_collisionFree

/-- One op per id: the store the loaded history reaches, and the same
message arriving again, over the measured collision-free history. -/
def oneOpPerId := if hc : CollisionFree (before ++ Change.ingests [.ingest message]) then
  some (PLift.up (oneOpPerId_of (loadReach before) hc)) else none

def terminates := if hd : Distinct before then
  some (PLift.up (drain_terminates hd (load before) (loadReach before))) else none

def budgetDecreases := if hd : Distinct before then
  match hq : (load before).queue with
  | [] => none
  | x :: q => some (PLift.up (step_budget (loadReach before) hd hq))
else none

def localSecret := secret (sha256 "vacuity-purge-secret".toUTF8)
def sharedDependent := post c localSecret.id alice keyId "malicious dependency".toUTF8 3 29880003
def purgeOps := before ++ [localSecret, sharedDependent]
def purgeIds := [localSecret.id]
def pState := run purgeOps

def purgeInvariant := purge_inv (runInv purgeOps) purgeIds

-- The engine's purge, run on this store, is purgeS and returns purgeSet:
-- a nonempty purge (a local secret and the shared op citing it).
def runPurge := run_purge (family ed25519) purgeIds pState

def purgeMembership := mem_purgeSet (runInv purgeOps) purgeIds localSecret.id

def purgeGone := if h : has (purgeSet (family ed25519) pState purgeIds) localSecret.id = true then
  some (PLift.up (purge_gone pState purgeIds ((has_iff _ _).1 h))) else none

def purgeShared := if h : pState.ops sharedDependent.id = some sharedDependent then
  if hs : ((family ed25519).room sharedDependent).isSome then
    some (PLift.up (purge_shared (fam := family ed25519) pState purgeIds h hs)) else none
else none

def purgeUndecides := if h : pState.ops sharedDependent.id = some sharedDependent then
  if hs : ((family ed25519).room sharedDependent).isSome then
    some (PLift.up (purge_undecides (runInv purgeOps) purgeIds h hs
      ⟨localSecret.id, by simp [purgeIds], Sync.Reach.step .refl h (by simp [sharedDependent, post, mkOp])⟩)) else none
else none

def purgeSettles := if hd : Distinct purgeOps then
  some (PLift.up (purge_settles (runReach purgeOps) hd purgeIds)) else none

def actualInvariant := runInv before

def validEncoding := applyLaw (certify before message messageFact) op_of_valid

def extendedVerdict := applyLaw (certify before message messageFact)
  (spec_extends (table_append_extends before [removeB, removeA]))

-- This receiver omits the unrelated admin grant and rename. It holds just the
-- post's requirement closure, including the non-founder approval chain.
def partialOps := [r, invitation, requestB, approval, admission, message]
def partialIds := partialOps.map Op.id

theorem closureHeld
    (start : message.id ∈ partialIds)
    (closed : ∀ o ∈ before, o.id ∈ partialIds → ∀ x ∈ o.reqs, x ∈ partialIds)
    (agree : ∀ x ∈ partialIds, table partialOps x = table before x)
    (y : Id) (o : Op) (hy : Sync.Reach (table before) message.id y)
    (ho : table before y = some o) : table partialOps y = some o := by
  have hm : y ∈ partialIds := by
    clear ho o
    induction hy with
    | refl => exact start
    | @step y p x _ hp hx ih =>
      have hi := keyed before y p hp
      have hmem : p ∈ before := List.mem_of_find?_eq_some hp
      exact closed p hmem (hi ▸ ih) x hx
  rw [agree y hm, ho]

def closureVerdict := do
  let ⟨hv⟩ ← certify before message messageFact
  if hstart : has partialIds message.id = true then
    if hclosed : before.all (fun o => !has partialIds o.id || o.reqs.all (has partialIds)) = true then
      if hagree : partialOps.all (fun o => decide (table partialOps o.id = table before o.id)) = true then
        some (PLift.up (Sync.spec_local (family ed25519) hv (closureHeld
          ((has_iff _ _).1 hstart)
          (by
            intro o ho hi x hx
            have h := List.all_eq_true.1 hclosed o ho
            have present := (has_iff _ _).2 hi
            simp only [present, Bool.not_true, Bool.false_or] at h
            exact (has_iff _ _).1 (List.all_eq_true.1 h x hx))
          (by
            intro x hx
            obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hx
            exact of_decide_eq_true (List.all_eq_true.1 hagree o ho)))))
      else none
    else none
  else none

def sharedReads :=
  match (Codec.decode message.body : Option Body) with
  | none => none
  | some b => if hc : check ed25519 message b [rootFact, bobFact] = some messageFact then
      if hl : b.isLocal = false then some (PLift.up (check_reads_shared hc hl)) else none
    else none

-- All finite premises are checked; the signing theorem's universal premise
-- remains explicit. A successful finite signature sample cannot prove it.
def removeIntent := (removeMember c requestB.id alice).eval (run before)
def intentRemoval :=
  if hq : (run before).queue = [] then
    if ho : removeB ∈ removeIntent.ops then
      if hs : (ingestS removeB (run before)).ops removeB.id = some removeB then
        some (PLift.up (fun hsig : ∀ m, ed25519.verify alice.pk m (edSign alice.sk m) = true =>
          removeMember_valid (runInv before) hq hsig ho
            (ingestExtends (run before) removeB) hs))
      else none
    else none
  else none

def main : IO UInt32 := do
  let t ← Checks.new
  t.ok "distinct signed history" distinct.isSome
  t.ok "ingest known" alreadyKnown.isSome
  t.ok "settled status iff spec" verdictMatches.isSome
  t.ok "nonempty workload terminates" terminate.isSome
  t.ok "budget suffices" bounded.isSome
  t.ok "received ops exactly" opsExact.isSome
  t.ok "reverse arrival order agrees" ordersAgree.isSome
  t.ok "both arrival orders eventually agree" eventuallyAgree.isSome
  t.ok "fixture has nonempty queue before drain" (!(load before).queue.isEmpty)
  t.ok "actual message is valid after drain" ((run before).status message.id == some (.valid messageFact))
  t.ok "replaying message does not duplicate queue" ((ingestS message (load before)).queue == (load before).queue)
  t.ok "finite collision-free signed history" collisionFree.isSome
  t.ok "distinct ids follow from measured hash premise" distinctFromHash.isSome
  t.ok "one op per id over the reached store and a replayed message" oneOpPerId.isSome
  t.ok "nonempty queue termination" terminates.isSome
  t.ok "a real queued step decreases budget" budgetDecreases.isSome
  t.ok "local secret is purged" purgeGone.isSome
  t.ok "shared dependent is retained" purgeShared.isSome
  t.ok "shared dependent loses its verdict and is requeued" purgeUndecides.isSome
  t.ok "purged store settles" purgeSettles.isSome
  t.ok "shared message is not a purge member" (!(has (purgeSet (family ed25519) pState purgeIds) message.id))
  t.ok "valid op has canonical body encoding" validEncoding.isSome
  t.ok "verdict persists on proper extension" extendedVerdict.isSome
  t.ok "receiver holding closure derives same verdict" closureVerdict.isSome
  t.ok "partial receiver omits unrelated grant and rename" (table partialOps grantB.id == none && table partialOps renamed.id == none)
  t.ok "partial receiver independently validates message" (certify partialOps message messageFact).isSome
  t.ok "shared post validator reads only two shared dependency facts" sharedReads.isSome
  t.ok "removeMember finite premises are inhabited; universal signing premise remains open" intentRemoval.isSome
  t.ok "removeMember actually emits one removal" (removeIntent.ops.length == 1)
  t.ok "actual generated removal is valid" (removeIntent.ops.all fun o =>
    (certify (before ++ removeIntent.ops) o (.removal c requestB.id c [])).isSome)
  t.ok "self removal emits no operation" (((removeMember c c alice).eval (run before)).ops.isEmpty)
  t.ok "already removed member emits no operation" (((removeMember c requestB.id alice).eval (run after)).ops.isEmpty)
  return ← t.finish "core vacuity"
end Vacuity.CoreRuntime
