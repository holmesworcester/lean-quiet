import ops.connection.bootstrap.FairExecution
import ops.connection.bootstrap.Bridge
import tests.engine.Lib

/-! Five actual signature verifications and finite key/ID checks certify
this deterministic synthetic scene. The infinite FIFO run, its fairness and
its no-drop property are constructed in the kernel independently of those
checks. No universal signature-correctness assumption or bootstrap conclusion
is used to manufacture the scheduler's premises. This remains the bootstrap
model, whose trust/validation decisions are noncomputable. -/
namespace Vacuity.Bootstrap
open Engine Community Net
set_option linter.defProp false

def scene : Scene := {
  A := Device.named "vacuity/bootstrap/alice"
  B := Device.named "vacuity/bootstrap/bob"
  kA := cryptoSeal.pub (sha256 "vacuity/node/alice".toUTF8)
  kB := cryptoSeal.pub (sha256 "vacuity/node/bob".toUTF8)
  secret := sha256 "vacuity/bootstrap/invite".toUTF8 }

noncomputable def afterTick : Sys := step ed25519 scene.approval scene.init .tickB

theorem tickReach : Reachable ed25519 scene.approval scene.init afterTick :=
  .step .tickB .init trivial

theorem noBeforeLaw (g : scene.Good ed25519) :
    (scene.c, scene.kB) ∉ afterTick.a.sessions ∧
    (scene.c, scene.kA) ∉ afterTick.b.sessions ∧
    scene.answer ∉ afterTick.net ∧
    (∀ os, Msg.push scene.c scene.kA scene.kB os ∉ afterTick.net) ∧
    (∀ o ∈ afterTick.b.ops, o = scene.req) := by
  apply Scene.no_connection_before_approval g tickReach
  have h := Scene.out_tickB g (Scene.inv_init g)
  unfold afterTick Net.step
  rw [h]
  simp only [Scene.init, Scene.a0, List.mem_cons, List.mem_nil_iff, or_false]
  exact fun h => h.elim (fun h => scene.adm_ne.1 h) (fun h => scene.adm_ne.2.1 h)

theorem pathReach {s t : Sys} {acts : List Act}
    (h : Path ed25519 scene.approval s acts t)
    (hr : Reachable ed25519 scene.approval scene.init s) :
    Reachable ed25519 scene.approval scene.init t := by
  induction h with
  | nil => exact hr
  | cons he _ ih => exact ih (.step _ hr he)

-- Nine protocol actions exist under Good, with deliveries actually enabled.
def possibleLaw (g : scene.Good ed25519) := Scene.bootstrap_possible g

theorem trustedOutcomeLaw (g : scene.Good ed25519) : ∃ acts t,
    Path ed25519 scene.approval scene.init acts t ∧ scene.Goal ed25519 t ∧
    (∀ p ∈ t.a.sessions, Allowed ed25519 t.a.ops p.1 p.2) ∧
    (∀ p ∈ t.b.sessions, Trusts ed25519 t.b p.1 p.2) := by
  obtain ⟨acts, t, _, hp, hg⟩ := possibleLaw g
  exact ⟨acts, t, hp, hg, Scene.sessions_trusted g (pathReach hp .init)⟩

theorem completedInvariantLaw (g : scene.Good ed25519) : ∃ acts t,
    Path ed25519 scene.approval scene.init acts t ∧ scene.Goal ed25519 t ∧ scene.Inv t := by
  obtain ⟨acts, t, _, hp, hg⟩ := possibleLaw g
  exact ⟨acts, t, hp, hg, Scene.reachable_inv g (pathReach hp .init)⟩

theorem admissionClassifiedLaw (g : scene.Good ed25519) :
    (scene.B.pk = scene.A.pk ∧ scene.kB = scene.kA ∧ scene.r ∈ scene.S) ∨
    (scene.B.pk = scene.B.pk ∧ scene.kB = scene.kB ∧ scene.adm ∈ scene.S) :=
  Scene.admitted_inv g (fun _ h => h) ⟨scene.adm.id, Scene.v_adm g (fun _ h => h) (fun _ h => h)⟩

theorem founderAllowedLaw (g : scene.Good ed25519) : Allowed ed25519 scene.S scene.c scene.kA :=
  (Scene.allowedA g (fun _ h => h)).mpr (by simp [Scene.S])

theorem joinerAllowedLaw (g : scene.Good ed25519) : Allowed ed25519 scene.S scene.c scene.kB :=
  (Scene.allowedB g (fun _ h => h) (fun _ _ h => h)).mpr (by simp [Scene.S])

-- This run and both infinite scheduling premises are closed kernel terms.
noncomputable def execution := scene.fairExecution ed25519
theorem executionFair : execution.Fair := Scene.fairExecution_fair scene ed25519
theorem executionIdeal : execution.Ideal := Scene.fairExecution_ideal scene ed25519

def eventuallyBootstrapLaw (g : scene.Good ed25519) := Scene.bootstrap g executionFair
def eventuallyIdealLaw (g : scene.Good ed25519) := Scene.bootstrap_ideal g executionFair executionIdeal

def certifyScene : Option (PLift (scene.Good ed25519)) :=
  if hroot : ed25519.verify scene.A.pk scene.rootMessage (edSign scene.A.sk scene.rootMessage) = true then
    if hinv : ed25519.verify scene.A.pk scene.invitationMessage (edSign scene.A.sk scene.invitationMessage) = true then
      if hreq : ed25519.verify scene.B.pk scene.requestMessage (edSign scene.B.sk scene.requestMessage) = true then
        if hbearer : ed25519.verify scene.K.pk scene.requestMessage (edSign scene.K.sk scene.requestMessage) = true then
          if happ : ed25519.verify scene.A.pk scene.approvalMessage (edSign scene.A.sk scene.approvalMessage) = true then
            if hab : scene.A.pk ≠ scene.B.pk then
              if hkeys : scene.kA ≠ scene.kB then
                if hdist : scene.S.all (fun a => scene.S.all fun b => decide (a.id = b.id → a = b)) = true then
                  some ⟨⟨hroot,hinv,hreq,hbearer,happ,hab,hkeys,by
                    intro a ha b hb he
                    exact of_decide_eq_true ((List.all_eq_true.1 ((List.all_eq_true.1 hdist) a ha)) b hb) he⟩⟩
                else none
              else none
            else none
          else none
        else none
      else none
    else none
  else none

def withScene {P : Prop} (law : scene.Good ed25519 → P) : Option (PLift P) :=
  certifyScene.map fun ⟨g⟩ => ⟨law g⟩

def noBefore := withScene noBeforeLaw
def possible := withScene possibleLaw
def trustedOutcome := withScene trustedOutcomeLaw
def completedInvariant := withScene completedInvariantLaw
def admissionClassified := withScene admissionClassifiedLaw
def founderAllowed := withScene founderAllowedLaw
def joinerAllowed := withScene joinerAllowedLaw
def eventuallyBootstrap := withScene eventuallyBootstrapLaw
def eventuallyIdeal := withScene eventuallyIdealLaw

def loaded : List Op → DB Fact
  | [] => DB.empty
  | o :: os => ingestS o (loaded os)
def judged := drainS (family ed25519) 100 (loaded scene.S)

def main : IO UInt32 := do
  let t ← Tests.Checks.new
  t.ok "five real signatures and finite scene constraints" certifyScene.isSome
  for (label,ok) in [("no connection before approval",noBefore.isSome),
      ("finite ideal bootstrap path",possible.isSome),("trusted completed sessions",trustedOutcome.isSome),
      ("completed invariant",completedInvariant.isSome),("actual admission classified",admissionClassified.isSome),
      ("founder allowed",founderAllowed.isSome),("joiner allowed",joinerAllowed.isSome),
      ("bootstrap on constructed infinite fair execution",eventuallyBootstrap.isSome),
      ("bootstrap on constructed infinite ideal execution",eventuallyIdeal.isSome)] do
    t.ok label ok
  t.ok "node keys have real X25519 sizes" (scene.kA.size == 32 && scene.kB.size == 32)
  t.ok "all five real operations validate through production engine"
    (scene.S.length == 5 && scene.S.all fun o => match judged.status o.id with | some (.valid _) => true | _ => false)
  t.ok "actual production query admits founder and joiner"
    ((allowPeer scene.c scene.kA).eval judged && (allowPeer scene.c scene.kB).eval judged)
  t.ok "wrong founder key cannot authorize root"
    (!ed25519.verify scene.B.pk scene.rootMessage (edSign scene.A.sk scene.rootMessage))
  t.ok "changed invitation bytes fail signature"
    (!ed25519.verify scene.A.pk (scene.invitationMessage.push 0) (edSign scene.A.sk scene.invitationMessage))
  t.ok "bearer cannot replace device request signer"
    (!ed25519.verify scene.K.pk scene.requestMessage (edSign scene.B.sk scene.requestMessage))
  t.ok "device cannot replace bearer request signer"
    (!ed25519.verify scene.B.pk scene.requestMessage (edSign scene.K.sk scene.requestMessage))
  t.ok "joiner cannot approve itself as founder"
    (!ed25519.verify scene.B.pk scene.approvalMessage (edSign scene.A.sk scene.approvalMessage))
  t.finish "bootstrap finite premises with kernel infinite fair execution"

end Vacuity.Bootstrap
