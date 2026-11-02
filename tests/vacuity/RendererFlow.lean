import app.community.member.remove.View
import engine.renderer.Nav
import app.Screen

namespace Vacuity.RendererFlow
open Engine Data
attribute [local instance] LiveLaws.byteArray_lawful LiveLaws.listQ_lawful LiveLaws.q_lawful

def alice : Id := ByteArray.mk #[0x61, 0x6c, 0x69, 0x63, 0x65]
def bob : Id := ByteArray.mk #[0x62, 0x6f, 0x62]

theorem secondYes :
    (Remove.Step.second bob = .second bob ∨ ∃ why, Remove.Step.second bob = .failed bob why) ∧ True :=
  Remove.writes_only_after_two (.second bob) .yes bob rfl
example : (Remove.step (.first bob) .yes).2 = none := rfl
example : (Remove.step (.second bob) .yes).2 = some bob := rfl

theorem cancellation : (Remove.step (.second bob) .cancel).2 = none :=
  Remove.cancel_writes_nothing (.second bob)

theorem freshAttempt : Remove.step (.failed alice "not authorized") (.start bob) = (.first bob, none) :=
  Remove.open_fresh (.failed alice "not authorized") bob (by intro v h; cases h)

theorem noReplace : Remove.step (.sending alice) (.start bob) = (.sending alice, none) :=
  Remove.no_replace alice bob

theorem offered : true = true ∧ true = true ∧ bob ≠ alice :=
  Remove.offered_only true true alice bob (by decide)
example : Remove.offered false true alice bob = false := by decide
example : Remove.offered true false alice bob = false := by decide
example : Remove.offered true true alice alice = false := by decide

def nav : Nav.Nav Nat := ⟨2, [1, 0]⟩
theorem back : Nav.back (Nav.go 3 nav) = nav :=
  Nav.back_go 3 nav (by decide) (by decide)
theorem noDuplicates : Nav.Inv (Nav.go 1 nav) :=
  Nav.go_inv 1 nav (by unfold Nav.Inv; decide)
example : (Nav.go 1 nav).stack = [0] := by decide
example : (Nav.back (Nav.go 3 nav)).page = 2 := by decide
example : ¬ (1 : Nat) ∉ nav.stack := by decide

theorem offerSplit :
    let r := (NodeOffer.offerList NodeOffer.offerM [101, 102, 103]).run ([true, false, true], [100])
    r.2.2 ++ r.1 = [100] ++ [101, 102, 103] :=
  NodeOffer.offer_split [101, 102, 103] [true, false, true] [100]
example :
    (NodeOffer.offerList NodeOffer.offerM [101, 102, 103]).run ([true, false, true], [100]) =
      ([102, 103], [true], [100, 101]) := by rfl

theorem offers :
    let r := (NodeOffer.run [some 102, none, some 103] [101]).run ([false, true, true, false], [100])
    r.2.2 ++ r.1 = [100] ++ [101] ++ NodeOffer.submitted [some 102, none, some 103] :=
  NodeOffer.offer_runs [some 102, none, some 103] [101] [false, true, true, false] [100]
example : (NodeOffer.run [some 102, none, some 103] [101]).run ([false, true, true, false], [100]) =
    ([103], [], [100, 101, 102]) := by rfl

def queryA : Q := .op alice
def queryB : Q := .op bob
def life : Lifecycle.Mount := ⟨7, true⟩
-- State effect makes the denial meaningful: if invoked, the counter grows.
def countedAction : StateM Nat Nat := do modify (· + 1); get

theorem unmounted : Lifecycle.owned life.unmount ⟨7⟩ countedAction = pure none :=
  Lifecycle.unmounted_quiet life ⟨7⟩ countedAction

theorem oldCallback : Lifecycle.owned life.unmount.mount life.lease countedAction = pure none :=
  Lifecycle.old_quiet life countedAction
example : (Lifecycle.owned life life.lease countedAction).run 3 = (some 4, 4) := by rfl
example : (Lifecycle.owned life.unmount.mount life.lease countedAction).run 3 = (none, 3) := by rfl

theorem mountedWork : Lifecycle.owned (m := _root_.Id)
    ({ generation := 7 } : Lifecycle.Mount) ⟨7⟩ (pure 7) = some 7 :=
  Lifecycle.mounted_runs 7

def cache : Live := (({} : Live).store queryA (.bytes (some "hello".toUTF8))).store queryB (.bytes none)
/-- The reads two mounted wants hold: queryA's and queryB's. -/
def held (q : Data.Q) : Bool := q == queryA || q == queryB
private theorem complete : ∀ q, held q = true → cache.entries[q]?.isSome = true := by
  intro q h
  simp only [held, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | rfl <;> simp [cache, Live.store, queryA, queryB, alice, bob]

theorem liveExact : (cache.keep held).entries[queryA]?.isSome = true ↔ held queryA = true :=
  Lifecycle.live_exact cache held complete queryA
example : (cache.keep fun q => q == queryB).entries[queryA]?.isSome = false := by
  simp [Live.keep, cache, Live.store, queryA, queryB, alice, bob]

theorem resize : (600 : Int) - Lifecycle.offset 600 180 = 180 :=
  Lifecycle.resize_anchor 600 180 (by decide)
example : Lifecycle.offset 600 180 = 420 := by decide
example : ¬ (1800 : Nat) ≤ 600 := by decide

def checkpoint : Lifecycle.Checkpoint :=
  (1, 2, alice, bob, 180, ["Draft message".toUTF8, "Community name".toUTF8])
theorem restore : Lifecycle.restore (Codec.encode checkpoint) = some checkpoint :=
  Lifecycle.restore_checkpoint checkpoint

end Vacuity.RendererFlow
