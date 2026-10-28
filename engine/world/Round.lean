/-
A round at one connection, proven of the running code: what `onRbsr`
answers to a round message, whatever regime the round is in.

- A claim of ids is answered with a have, in the round's room, of every
  id of the snapshot in its range that the claim does not list
  (`onRbsr_holds`): the reverse leg's first step.
- Claims of ids only are answered with no claims: the round's reply ends
  it at the other end, and this end keeps no snapshot of the room
  (`onRbsr_ids_ends`).
- An empty round message ends the round here: no snapshot of the room
  stays, and nothing is sent (`onRbsr_empty`).
-/
import engine.world.Settle
namespace Engine.World
open Engine Engine.Sync
variable {F : Type}

/-- A list of claims of ids only. -/
def IdsOnly (cs : List Claim) : Prop := ∀ cl ∈ cs, ∃ rg L, cl = .ids rg L

/-- Claims of ids are answered with no claims. -/
theorem answer_ids_noclaims (P : Params) (mine : List Item) (cs : List Claim) (hcs : IdsOnly cs)
    (f : Out → Option Claim) (hf : ∀ xs, f (.hold xs) = none) (hf' : ∀ xs, f (.want xs) = none) :
    (cs.flatMap (answer Prod.fst Prod.snd sha256 P mine)).filterMap f = [] := by
  rw [List.filterMap_eq_nil_iff]
  intro o ho
  obtain ⟨cl, hcl, ho⟩ := List.mem_flatMap.1 ho
  obtain ⟨rg, L, rfl⟩ := hcs cl hcl
  simp only [answer, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl
  · exact hf _
  · exact hf' _

/-- **The reverse leg's first step: a claim of ids is answered with a
have of every id of the snapshot in its range that it does not list.** -/
theorem onRbsr_holds (cfg : Config) (ix : Index) (c : Conn) (r : Id) (k : Nat) (cs : List Claim) (rg : Range)
    (L : List Id) (now : Nat) (it : Item) (hr : r ∈ c.rooms) (hc : Claim.ids rg L ∈ cs)
    (hit : it ∈ Conn.snap ix c r k) (hin : rg.has it.1 = true) (hL : it.2 ∉ L) (hmax : 0 < cfg.maxIds) :
    ∃ H, it.2 ∈ H ∧ H.length ≤ cfg.maxIds ∧ (Msg.hold r H).op ∈ (c.onRbsr cfg ix r k cs now).send := by
  have hne : cs.isEmpty = false := by
    cases cs with
    | nil => cases hc
    | cons _ _ => rfl
  have hh : it.2 ∈ (cs.flatMap (answer Prod.fst Prod.snd sha256 cfg.params (c.snap ix r k))).flatMap
      (fun | .hold xs => xs | _ => [] : Out → List Id) := by
    refine List.mem_flatMap.2 ⟨.hold (((within Prod.fst rg (Conn.snap ix c r k)).filter
      fun a => !L.any fun i => Decidable.decide (a.2 = i)).map Prod.snd),
      List.mem_flatMap.2 ⟨.ids rg L, hc, by simp [answer]⟩, ?_⟩
    simp only
    refine List.mem_map.2 ⟨it, List.mem_filter.2 ⟨mem_within.2 ⟨hit, hin⟩, ?_⟩, rfl⟩
    simp only [Bool.not_eq_true', List.any_eq_false, decide_eq_true_eq]
    intro i hi e; exact hL (e ▸ hi)
  obtain ⟨H, hxH, hl, hm⟩ := chunks_cover cfg _ (Msg.hold r) hmax hh
  refine ⟨H, hxH, hl, ?_⟩
  unfold Conn.onRbsr
  simp only [has_of_mem hr, Bool.not_true, Bool.false_eq_true, ite_false, hne, Step.limit_send]
  split
  · exact List.mem_cons_of_mem _ (List.mem_append_left _ hm)
  · exact List.mem_cons_of_mem _ (List.mem_append_left _ hm)

/-- **Claims of ids only end the round here**: the reply's round message
carries no claims, and this end keeps no snapshot of the room. -/
theorem onRbsr_ids_ends (cfg : Config) (ix : Index) (c : Conn) (r : Id) (k : Nat) (cs : List Claim) (now : Nat)
    (hr : r ∈ c.rooms) (hne : cs ≠ []) (hcs : IdsOnly cs) :
    (Msg.rbsr r k []).op ∈ (c.onRbsr cfg ix r k cs now).send ∧
      ∀ e ∈ (c.onRbsr cfg ix r k cs now).conn.snaps, e.1.1 ≠ r := by
  have hne' : cs.isEmpty = false := by
    cases cs with
    | nil => exact absurd rfl hne
    | cons _ _ => rfl
  unfold Conn.onRbsr
  simp only [has_of_mem hr, Bool.not_true, Bool.false_eq_true, ite_false, hne', Step.limit_send,
    Step.limit_snaps]
  rw [answer_ids_noclaims cfg.params _ cs hcs]
  rotate_left
  · intro _; rfl
  · intro _; rfl
  simp only [List.isEmpty_nil, ite_true, List.mem_cons, true_or, true_and]
  intro e he
  simp only [List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not] at he
  exact he.2

/-- **An empty round message ends the round here**: no snapshot of the
room stays, and nothing is sent. -/
theorem onRbsr_empty (cfg : Config) (ix : Index) (c : Conn) (r : Id) (k : Nat) (now : Nat) (hr : r ∈ c.rooms) :
    (c.onRbsr cfg ix r k [] now).send = [] ∧ ∀ e ∈ (c.onRbsr cfg ix r k [] now).conn.snaps, e.1.1 ≠ r := by
  unfold Conn.onRbsr
  simp only [has_of_mem hr, Bool.not_true, Bool.false_eq_true, ite_false, List.isEmpty_nil, ite_true]
  refine ⟨by simp, fun e he => ?_⟩
  simp only [List.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not] at he
  exact he.2

end Engine.World
