/-
Negative controls for exact notices: the two simpler matchers are not
precise.

- `key_notice_imprecise`: notices by key, as the app's `Live` gives them
  today (every watch on a key the journal names goes stale), notify a
  window for a row filed below it. One op, filed under k with sort key
  0, against the window of k from sort key 5 up: the key-level notice
  fires and the window is unchanged. The exact matcher, on the same
  step, is silent (`exact_silent`).
- `unnetted_imprecise`: matching the journal's rows without netting them
  notifies a window for a row filed and purged in one batch: a session's
  local op, filed then purged, as between two reader passes.
-/
import engine.core.WindowLaws

namespace Engine.Mutants
open Engine

/-! ## A one-op world -/

/-- Facts carry nothing; every fact sorts at byte 0. -/
instance : SortKey Unit := ⟨fun _ => ⟨#[0]⟩⟩

/-- The key the op is filed under. -/
def k : ByteArray := ⟨#[1]⟩

/-- Every op is Valid, filed under k, and local to this node. -/
def fam : Family Unit where
  validate _ _ := some ()
  keys _ := [k]
  scope _ := .local

/-- The op. -/
def o : Op := Op.make 0 [] .empty

/-- o stored and queued, nothing decided. -/
def σ : DB Unit where
  ops i := if i = o.id then some o else none
  stored := [o.id]
  status _ := none
  waits _ := []
  queue := [o.id]
  idx _ := []

theorem σ_inv : Inv fam σ where
  key x p h := by
    simp only [σ] at h
    split at h
    · cases h; rename_i hx; exact hx.symm
    · cases h
  sound x v h := by cases h
  wait x p h _ := by
    simp only [σ] at h
    split at h
    · rename_i hx; left; simp [σ, hx]
    · cases h
  idx k x := by simp [σ]
  nodup _ := List.nodup_nil
  stored x := by
    simp only [σ, List.mem_singleton]
    by_cases hx : x = o.id <;> simp [hx]

theorem σ_one : OneOpPerId σ [] := ⟨σ.ops, fun _ _ h => h, fun _ h => by cases h⟩
theorem σ_one_step : OneOpPerId σ [.step] := ⟨σ.ops, fun _ _ h => h, fun _ h => by cases h⟩
theorem σ_one_purge : OneOpPerId σ [.step, .purge [o.id]] := ⟨σ.ops, fun _ _ h => h, fun _ h => by cases h⟩

/-- The step: o is judged Valid and filed under its own key and k. -/
theorem stepJ_σ : stepJ fam σ = fileJ fam o.id () true := by
  have hq : σ.queue = [o.id] := rfl
  have hs : σ.status o.id = none := rfl
  have ho : σ.ops o.id = some o := by simp [σ]
  have hj : judge fam o (o.reqs.map σ.status) = some (.valid ()) := rfl
  unfold stepJ
  rw [hq]; simp only
  rw [hs]; simp only
  rw [ho]; simp only
  rw [hj]

/-- The step's journal has a row under k at o's position. -/
theorem stepJ_hits : (⟨k, (⟨#[0]⟩, o.id), true⟩ : Filing) ∈ stepJ fam σ := by
  rw [stepJ_σ]
  unfold fileJ
  apply List.mem_map.2
  refine ⟨k, mem_nubB.2 ?_, rfl⟩
  simp [Family.fileKeys, fam]

/-! ## Key-level notices -/

/-- Notices by key: a window is notified when the journal names its key. -/
def keyNotified (J : List Filing) (w : Win) : Bool := J.any fun e => Decidable.decide (e.key = w.key)

/-- The window of k from sort key 5 up. -/
def w5 : Win := { key := k, lo := some ((⟨#[5]⟩, .empty), true) }

/-- Nothing is ever in w5: every row sorts at 0. -/
theorem window_w5 (s : DB Unit) : window s w5 = [] := by
  apply List.eq_nil_iff_forall_not_mem.2
  intro r hr
  obtain ⟨hin, hf, _⟩ := mem_window.1 hr
  obtain ⟨_, _, _, hsk⟩ := filed_iff.1 hf
  have h0 : r.1.1 = ⟨#[0]⟩ := hsk.symm
  have : Pos.cmp r.1 (⟨#[5]⟩, .empty) = .lt := by
    unfold Pos.cmp
    rw [h0]
    have : bcmp ⟨#[0]⟩ ⟨#[5]⟩ = .lt := by rw [bcmp_eq_lexCmp]; decide
    rw [this]; rfl
  simp [w5, Win.inside, above, this] at hin

/-- **Key-level notices are not precise.** A row filed below the window
notifies it by key, and the window did not change. -/
theorem key_notice_imprecise :
    keyNotified (runJ fam [.step] σ).2 w5 = true ∧ window σ w5 = window (runJ fam [.step] σ).1 w5 := by
  refine ⟨?_, by rw [window_w5, window_w5]⟩
  simp only [runJ, Change.journal, List.append_nil, keyNotified, List.any_eq_true]
  exact ⟨_, stepJ_hits, by simp [w5]⟩

/-- **The exact matcher is silent on that step.** -/
theorem exact_silent (x : Nat) :
    x ∉ (Subs.ofList [(x, w5)]).notify (runJ fam [.step] σ).2.toArray := by
  rw [notice_iff σ_inv σ_one_step (Subs.ofList_wf _)]
  rintro ⟨w, hw, hne⟩
  rw [Subs.has_ofList, List.mem_singleton] at hw
  cases hw
  exact hne (by rw [window_w5, window_w5])

/-! ## Unnetted notices -/

/-- Matching the journal's rows as they are, without netting. -/
def rawNotified (J : List Filing) (w : Win) : Bool := J.any fun e => w.has e.key e.pos

/-- k's whole list. -/
def wk : Win := Win.all k

/-- After the step and the purge of o, nothing is filed. -/
theorem purged_empty : window (runJ fam [.step, .purge [o.id]] σ).1 wk = [] := by
  apply List.eq_nil_iff_forall_not_mem.2
  intro r hr
  obtain ⟨_, hf, _⟩ := mem_window.1 hr
  obtain ⟨_, hx, _, _⟩ := filed_iff.1 hf
  simp only [runJ, Change.apply] at hx
  rw [mem_purgeS_idx] at hx
  obtain ⟨hx, hc⟩ := hx
  -- the step filed only o, and the purge took it
  have hs : stepS fam σ = decideS fam o.id (.valid ()) { σ with queue := [] } := by
    have ho : σ.ops o.id = some o := by simp [σ]
    unfold stepS
    show (match σ.queue with
      | [] => σ
      | x :: q => _) = _
    simp only [σ]
    simp only [if_pos]
    rfl
  rw [hs] at hx hc
  obtain ⟨_, _, _, _, hidx⟩ := decideS_fields (fam := fam) o.id (.valid ()) { σ with queue := [] }
  rcases (hidx _ _).1 hx with h | ⟨e, _⟩
  · simp [σ] at h
  · exact hc (by rw [e]; exact closeUp_sub _ _ (List.mem_singleton_self _))

/-- **Unnetted notices are not precise.** A row filed and purged in one
batch notifies its window, and the window did not change. -/
theorem unnetted_imprecise :
    rawNotified (runJ fam [.step, .purge [o.id]] σ).2 wk = true ∧
      window σ wk = window (runJ fam [.step, .purge [o.id]] σ).1 wk := by
  refine ⟨?_, ?_⟩
  · simp only [runJ, Change.journal, rawNotified, List.any_eq_true]
    refine ⟨_, List.mem_append_left _ stepJ_hits, ?_⟩
    simp [wk, Win.all, Win.has, Win.inside, above, below]
  · rw [purged_empty]
    apply List.eq_nil_iff_forall_not_mem.2
    intro r hr
    obtain ⟨_, hf, _⟩ := mem_window.1 hr
    obtain ⟨_, hx, _, _⟩ := filed_iff.1 hf
    simp [σ] at hx

end Engine.Mutants
