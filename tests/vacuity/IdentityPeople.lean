import tests.vacuity.IdentityTrust
import app.community.Screen

namespace Vacuity.IdentityPeople
set_option linter.defProp false
open Engine Community Tests Kinds Vacuity.Identity Vacuity.IdentityTrust

def presentIff := if hq : (run before).queue = [] then
  some (PLift.up (PeopleLaws.present_iff (runInv before) hq c requestB.id)) else none

def presentNotRemoved := if hq : (run before).queue = [] then
  if hp : (((Profile.present c).eval (run before)).map (fun p : Id × List Key => p.1)).any (fun u => decide (u = requestB.id)) = true then
    some (PLift.up (PeopleLaws.present_not_removed (runInv before) hq (by
      obtain ⟨u,hu,he⟩ := List.any_eq_true.1 hp
      have he' : u = requestB.id := of_decide_eq_true he
      simpa [he'] using hu)))
  else none
else none

def presentNodup := PeopleLaws.present_nodup (run before) c

def rows := ((admission.all.read [c]).eval (run before)).rows

def unremovedLists := PeopleLaws.unremoved_lists (run before) c rows
def deviceLiveLists := PeopleLaws.deviceLive_lists (run before) c bob.pk
def liveListsGe := PeopleLaws.live_lists_ge (run before) c rows
def presentWListsEq := PeopleLaws.presentW_lists_eq (run before) c 1 3
def presentListsEq := PeopleLaws.present_lists_eq (run before) c
def presentScans := PeopleLaws.present_scans (run before) c

def windowPrefix := PeopleLaws.presentW_prefix (run before) c 1 3

def windowComplete := if h : ((Profile.presentW c 1 3).eval (run before)).2 = true then
  some (PLift.up (PeopleLaws.presentW_complete (run before) c 1 3 h)) else none

def countComplete := if h : ((Profile.presentCount c 1 3).eval (run before)).2 = true then
  some (PLift.up (PeopleLaws.presentCount_complete (run before) c 1 3 h)) else none

-- Derive a finite bound for EVERY device key, not only the two named devices.
-- All index entries correspond to stored valid ops, and index lists are distinct.
theorem indexBound {s : DB Fact} (hi : Inv (family ed25519) s) (k : ByteArray) :
    (s.idx k).length ≤ s.stored.length := by
  apply (hi.nodup k).length_le_of_subset
  intro x hx
  obtain ⟨f, hv, _⟩ := (hi.idx k x).1 hx
  obtain ⟨o, fs, ho, _, _⟩ := spec_valid_inv (hi.sound x (.valid f) hv)
  exact (hi.stored x).2 (by rw [ho]; rfl)

theorem rowsBound (s : DB Fact) (k : ByteArray) :
    (eval s {key := k, limit := none}).rows.length ≤ (s.idx k).length := by
  simp only [eval, ListQ.cut, ↓reduceIte, List.length_reverse]
  apply Nat.le_trans (List.length_filter_le _ _)
  unfold matching
  rw [(perm_sortPos _).length_eq]
  exact List.length_filterMap_le _ _

theorem everyDeviceBound (d : Key) :
    ((admission.byDevice.read [c,d]).eval (run before)).rows.length ≤ (run before).stored.length := by
  exact Nat.le_trans (rowsBound _ _) (indexBound (runInv before) _)

def liveListsLe := PeopleLaws.live_lists_le (run before) c (run before).stored.length everyDeviceBound rows

def presentWLists := PeopleLaws.presentW_lists (run before) c 1 3 (run before).stored.length everyDeviceBound

-- After Alice removes Bob, the running `deviceCut` marks Bob's device: the
-- premise of `deviceCut_removal` holds of a real signed store, and the law
-- then names the admission and the removal it read.
def deviceCutRemoval := if h : (deviceCut c bob.pk).eval (run after) = true then
  some (PLift.up (PeopleLaws.deviceCut_removal (run after) c bob.pk h)) else none

def main : IO UInt32 := do
  let t ← Checks.new
  t.ok "present_iff with Bob admitted" presentIff.isSome
  t.ok "present_not_removed with nonempty member list" presentNotRemoved.isSome
  t.ok "window_complete with all admissions read" windowComplete.isSome
  t.ok "count_complete with cap smaller than population" countComplete.isSome
  let users := ((Profile.present c).eval (run before)).map (fun p : Id × List Key => p.1)
  let gone := ((Profile.present c).eval (run after)).map (fun p : Id × List Key => p.1)
  t.ok "exactly Alice and Bob" (users.length == 2 && users.contains c && users.contains requestB.id)
  t.ok "members are distinct" (users.eraseDups.length == users.length)
  t.ok "removed users absent" gone.isEmpty
  t.ok "window contains one real user" (((Profile.presentW c 1 3).eval (run before)).1.length == 1)
  t.ok "count cap is respected" (((Profile.presentCount c 1 3).eval (run before)).1 == 1)
  t.ok "too-short admission scan is incomplete" (!((Profile.presentW c 1 1).eval (run before)).2)
  t.ok "live device performs actual queries" (View.listsAt (run before) (deviceLive c bob.pk) == 2)
  t.ok "whole people list scans two admissions" (View.listsAt (run before) (Profile.present c) == 5)
  t.ok "nonzero rows for cost witnesses" (rows.length == 2)
  t.ok "window query count formula" (View.listsAt (run before) (Profile.presentW c 1 3) ==
    1 + View.listsAt (run before) (live c rows))
  t.ok "global stored bound is finite and nontrivial" ((run before).stored.length == 8)
  t.ok "deviceCut_removal: removed Bob's device is cut, by a removal read" deviceCutRemoval.isSome
  t.ok "Bob's device is not cut before his removal" (!(deviceCut c bob.pk).eval (run before))
  t.ok "Alice's device is cut once Bob removes her" ((deviceCut c alice.pk).eval (run after))
  t.finish "people vacuity (signed community, actual nonempty query results)"

end Vacuity.IdentityPeople
