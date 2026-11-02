import tests.engine.Lib

/-! Deterministic synthetic signed community shared by the runtime premise checks. -/
namespace Vacuity.Identity
open Engine Community Codec Tests

def table (ops : List Op) (x : Id) : Option Op :=
  ops.find? (fun o => decide (o.id = x))

theorem keyed (ops : List Op) : Keyed (table ops) := by
  intro x o h
  unfold table at h
  have hp := List.find?_some h
  exact of_decide_eq_true hp

def certify (ops : List Op) (o : Op) (f : Fact) : Option (PLift (V ed25519 (table ops) o.id f)) :=
  if h : specAt (family ed25519) (table ops) 8 o.id = some (.valid f) then
    some ⟨⟨8, h⟩⟩
  else none

def applyLaw {P Q : Prop} (p : Option (PLift P)) (law : P → Q) : Option (PLift Q) :=
  p.map fun ⟨h⟩ => ⟨law h⟩

-- Actual devices and a non-founder admission, so the approval branch is exercised.
def alice := Device.named "vacuity-alice"
def bob := Device.named "vacuity-bob"
def carol := Device.named "vacuity-carol"
def mallory := Device.named "vacuity-mallory"
def bearer := Device.named "vacuity-invitation"
def r := root alice (keyOf alice)
def c := r.id
def invitation := invite c c alice bearer.pk false
def requestB := request c invitation.id bob (keyOf bob) bearer.sk
def approval := approve c requestB.id c alice
def admission := admit c requestB.id approval.id
def message := post c admission.id bob "content-key-1".toUTF8 "Hello Alice, this is Bob.".toUTF8 1 29880000
def grantB := grant c c c admission.id alice
def removeB := remove c c c admission.id alice
def removeA := remove c admission.id grantB.id c bob
def renamed := setName c c c [] 1 alice "Vacuity test community".toUTF8

def before : List Op := [r, invitation, requestB, approval, admission, message, grantB, renamed]
def after : List Op := before ++ [removeB, removeA]
-- Alice's second device, by a device link she issued and approved.
def alice2 := Device.named "vacuity-alice-2"
def linkBearer := Device.named "vacuity-device-link"
def linkInvitation := invite c c alice linkBearer.pk true
def requestA2 := request c linkInvitation.id alice2 (keyOf alice2) linkBearer.sk
def linkApproval := approve c requestA2.id c alice
def linkAdmission := admit c requestA2.id linkApproval.id
def linked : List Op := before ++ [linkInvitation, requestA2, linkApproval, linkAdmission]
def rootFact := Fact.admission c c alice.pk (keyOf alice)
def bobFact := Fact.admission c requestB.id bob.pk (keyOf bob)
def messageFact := Fact.message c requestB.id bob.pk "content-key-1".toUTF8
  "Hello Alice, this is Bob.".toUTF8 1 29880000


end Vacuity.Identity
