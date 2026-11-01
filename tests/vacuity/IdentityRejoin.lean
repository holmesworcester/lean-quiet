import tests.vacuity.IdentityTrust
import tests.vacuity.IdentityLifecycle

namespace Vacuity.IdentityRejoin
open Engine Community Codec Tests Vacuity.Identity Vacuity.IdentityTrust
open Vacuity.IdentityConnection (staticB pkB)
open Vacuity.IdentityLifecycle (pendingInvite pendingJoin localBob acceptB)
set_option linter.defProp false

def oldOps := before ++ [removeB] ++ localBob
def freshSeed := sha256 "vacuity-carol".toUTF8
def freshName := "Carol rejoining".toUTF8
def unusedFresh := Bytes.digest "unused-node-seed".toUTF8
def freshRequest := pendingInvite.request (Device.ofSeed freshSeed) pkB
def freshOps := (joinOps pendingInvite freshSeed freshName pkB).ops
def freshApproval := approve c freshRequest.id c alice
def freshAdmission := admit c freshRequest.id [freshApproval.id]
def extendedOps := oldOps ++ freshOps ++ [freshApproval,freshAdmission]
def acceptedRows := [((sortOf (.accepted c bob.pk),(accept c bob.pk).id),Fact.accepted c bob.pk)]
def joiningRows := [((sortOf (.joining c Vacuity.IdentityConnection.pkA [Vacuity.IdentityLifecycle.addr]
  requestB.id "Bob".toUTF8 bob.pk 0),pendingJoin.id),
  Fact.joining c Vacuity.IdentityConnection.pkA [Vacuity.IdentityLifecycle.addr] requestB.id "Bob".toUTF8 bob.pk 0)]

def rejoinFresh := do
  let ⟨had⟩ ← certifyDB oldOps admission bobFact
  let ⟨hrem⟩ ← certifyDB oldOps removeB (.removal c requestB.id c)
  if hq : (run oldOps).queue = [] then
    if hk : nodeKey.eval (run oldOps) = some (pkB, Bytes.fit 32 staticB) then
      if ha : (eval (run oldOps) (accepted.all.query [])).rows = acceptedRows then
        if hj : (eval (run oldOps) (joining.all.query [])).rows = joiningRows then
          if hn : (eval (run oldOps) (admission.byDevice.query [c,(Device.ofSeed freshSeed).pk] (limit := some 0))).total = 0 then
            pure (PLift.up (rejoin_fresh (runInv oldOps) hq (i := pendingInvite) (seed := freshSeed)
              (name := freshName) (fresh := unusedFresh) hk
              (by
                intro x d hv
                have hp := at_row (r := accepted.all) (by simp [rels]) (runInv oldOps) hq hv (as := []) (desc := true) rfl
                rw [ha] at hp
                have hf := congrArg Prod.snd (List.mem_singleton.1 hp)
                have hd := (Fact.accepted.inj hf).2
                subst d
                exact ⟨requestB.id,keyOf bob,⟨admission.id,had⟩,⟨removeB.id,c,hrem⟩⟩)
              (by
                intro x k hs req nm d n hv
                have hp := at_row (r := joining.all) (by simp [rels]) (runInv oldOps) hq hv (as := []) (desc := true) rfl
                rw [hj] at hp
                have hf := congrArg Prod.snd (List.mem_singleton.1 hp)
                have hd := (Fact.joining.inj hf).2.2.2.2.2.1
                subst d
                exact ⟨requestB.id,keyOf bob,admission.id,had⟩)
              (by
                intro u e had'
                have hh := (admitted_total (runInv oldOps) hq c (Device.ofSeed freshSeed).pk).2 ⟨u,e,had'⟩
                exact hh hn)))
          else none
        else none
      else none
    else none
  else none

def joinNewDevice : Option (PLift (∀ u e, ¬ Admitted ed25519 (run oldOps).ops c u carol.pk e)) :=
  if hq : (run oldOps).queue = [] then
    if ho : (((join pendingInvite freshSeed freshName unusedFresh).eval (run oldOps)).ops).any
        (fun o => decide (o = freshRequest)) = true then
      match hb : (decode freshRequest.body : Option Body) with
      | some (.request d e cs bs) =>
        if hd : d = carol.pk then
          some ⟨by
            subst d
            exact join_new_device (runInv oldOps) hq (i := pendingInvite) (seed := freshSeed)
              (name := freshName) (fresh := unusedFresh)
              (by obtain ⟨o,ho,he⟩ := List.any_eq_true.1 ho; exact (of_decide_eq_true he) ▸ ho) hb⟩
        else none
      | _ => none
    else none
  else none

def removedStaysRemoved := do
  let ⟨hr⟩ ← certifyDB oldOps removeB (.removal c requestB.id c)
  if hq : (run extendedOps).queue = [] then
    if he : oldOps.all (fun o => decide ((run extendedOps).ops o.id = some o)) = true then
      pure (PLift.up (removed_stays_removed (runInv extendedOps) hq (s := run oldOps)
        (by
          intro x o ho
          obtain ⟨hm,hi⟩ := reach_stored (runReach oldOps) x o ho
          have hh := of_decide_eq_true ((List.all_eq_true.1 he) o hm)
          rw [hi] at hh; exact hh)
        (show Removed ed25519 (run oldOps).ops c requestB.id from ⟨removeB.id,c,hr⟩)))
    else none
  else none

def main : IO UInt32 := do
  let t ← Checks.new
  t.ok "rejoin_fresh all real cut/join/new-device premises" rejoinFresh.isSome
  t.ok "join_new_device actual newly emitted signed request" joinNewDevice.isSome
  t.ok "removed_stays_removed after actual new-device admission" removedStaysRemoved.isSome
  t.ok "all invite fields valid" (decide pendingInvite.Valid)
  t.ok "old Bob is removed and not held" ((mine c).eval (run oldOps) == none && !(deviceLive c bob.pk).eval (run oldOps))
  t.ok "fresh rejoin emits precisely fresh join ops" (((join pendingInvite freshSeed freshName unusedFresh).eval (run oldOps)).ops == freshOps)
  t.ok "old seed cannot request cut Bob again" (((join pendingInvite (sha256 "vacuity-bob".toUTF8) "Bob".toUTF8 unusedFresh).eval (run oldOps)).ops.isEmpty)
  t.ok "new signed request validates under invitation" ((run extendedOps).status freshRequest.id == some (.valid (.request c freshRequest.id carol.pk pkB false 1)))
  t.ok "new admission actually validates" ((run extendedOps).status freshAdmission.id == some (.valid (.admission c freshRequest.id carol.pk pkB)))
  t.ok "old Bob remains cut after same node rejoins" (!(deviceLive c bob.pk).eval (run extendedOps))
  t.ok "new Carol is live on same node key" ((deviceLive c carol.pk).eval (run extendedOps) && (allowPeer c pkB).eval (run extendedOps))
  t.ok "rejoin user and device differ from removed user and device" (freshRequest.id != requestB.id && carol.pk != bob.pk)
  t.finish "rejoin freshness and permanent removal premises"

end Vacuity.IdentityRejoin
