import ops.connection.bootstrap.Laws
import ops.connection.bootstrap.Bridge

/-! Audited applications, deliberately CONDITIONAL. `Scene.Good` asks for
correctness of external Ed25519 signing for *every* message. Testing this
scene's finite signatures cannot supply that theorem. These declarations keep
that premise visible and are never reported as successful vacuity witnesses. -/
namespace Vacuity.Bootstrap
open Engine Community Net

def scene : Scene := {
  A := Device.named "vacuity/bootstrap/alice"
  B := Device.named "vacuity/bootstrap/bob"
  kA := "vacuity/node/alice".toUTF8
  kB := "vacuity/node/bob".toUTF8
  secret := sha256 "vacuity/bootstrap/invite".toUTF8 }

noncomputable def afterTick : Sys := step ed25519 scene.approval scene.init .tickB

theorem tickReach : Reachable ed25519 scene.approval scene.init afterTick :=
  .step .tickB .init trivial

theorem noBefore (g : scene.Good ed25519) :
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
def possible (g : scene.Good ed25519) := Scene.bootstrap_possible g

theorem trustedOutcome (g : scene.Good ed25519) : ∃ acts t,
    Path ed25519 scene.approval scene.init acts t ∧ scene.Goal ed25519 t ∧
    (∀ p ∈ t.a.sessions, Allowed ed25519 t.a.ops p.1 p.2) ∧
    (∀ p ∈ t.b.sessions, Trusts ed25519 t.b p.1 p.2) := by
  obtain ⟨acts, t, _, hp, hg⟩ := possible g
  exact ⟨acts, t, hp, hg, Scene.sessions_trusted g (pathReach hp .init)⟩

theorem completedInvariant (g : scene.Good ed25519) : ∃ acts t,
    Path ed25519 scene.approval scene.init acts t ∧ scene.Goal ed25519 t ∧ scene.Inv t := by
  obtain ⟨acts, t, _, hp, hg⟩ := possible g
  exact ⟨acts, t, hp, hg, Scene.reachable_inv g (pathReach hp .init)⟩

theorem admissionClassified (g : scene.Good ed25519) :
    (scene.B.pk = scene.A.pk ∧ scene.kB = scene.kA ∧ scene.r ∈ scene.S) ∨
    (scene.B.pk = scene.B.pk ∧ scene.kB = scene.kB ∧ scene.adm ∈ scene.S) :=
  Scene.admitted_inv g (fun _ h => h) ⟨scene.adm.id, Scene.v_adm g (fun _ h => h) (fun _ h => h)⟩

theorem founderAllowed (g : scene.Good ed25519) : Allowed ed25519 scene.S scene.c scene.kA :=
  (Scene.allowedA g (fun _ h => h)).mpr (by simp [Scene.S])

theorem joinerAllowed (g : scene.Good ed25519) : Allowed ed25519 scene.S scene.c scene.kB :=
  (Scene.allowedB g (fun _ h => h) (fun _ _ h => h)).mpr (by simp [Scene.S])

-- A concrete scene alone is insufficient for the infinite-run laws: a
-- scheduler/delivery witness satisfying Fair is also still required.
def eventuallyBootstrap (g : scene.Good ed25519)
    (r : Run ed25519 scene.approval scene.init) (hf : r.Fair) := Scene.bootstrap g hf

def eventuallyIdeal (g : scene.Good ed25519)
    (r : Run ed25519 scene.approval scene.init) (hf : r.Fair) (hi : r.Ideal) := Scene.bootstrap_ideal g hf hi

end Vacuity.Bootstrap
