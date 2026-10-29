/-
The people list is the community's present members, over the running
code (Kinds.Profile.present, which the people list and its count read):

- `present_iff`: at rest, a user is listed exactly when one of their
  devices is live: admitted, and none of the users it is admitted into
  removed (by the engine's `mem_live_all`), so the user is not removed
  either (`present_not_removed`): a removed member is in neither the
  list nor the count;
- `present_nodup`: each user is listed once, so the count is the number
  of people, not of devices.
-/
import ops.community.profile.View
import ops.community.reaction.RowLaws

namespace PeopleLaws
open Engine Community Kinds

theorem byUser_mem (ls : List (Id × Key × Key)) (u : Id) :
    u ∈ (Profile.byUser ls).map (·.1) ↔ ∃ d e, (u, d, e) ∈ ls := by
  simp only [Profile.byUser, List.map_map, Function.comp_def, List.map_id']
  rw [RowLaws.uniq_mem]
  simp only [List.mem_map]
  constructor
  · rintro ⟨⟨u', d, e⟩, hm, rfl⟩; exact ⟨d, e, hm⟩
  · rintro ⟨d, e, hm⟩; exact ⟨(u, d, e), hm, rfl⟩

/-- **The people list is exactly the present members.** -/
theorem present_iff {C : Community.Crypto} {s : DB Fact} (h : Inv (family C) s) (hq : s.queue = [])
    (c u : Id) :
    u ∈ ((Profile.present c).eval s).map (·.1) ↔ ∃ d e, Admitted C s.ops c u d e ∧ Live C s.ops c d := by
  simp only [Profile.present, View.eval_bind, View.eval_read, View.eval_pure]
  rw [byUser_mem]
  constructor
  · rintro ⟨d, e, hm⟩; exact ⟨d, e, (mem_live_all h hq c u d e).1 hm⟩
  · rintro ⟨d, e, hm⟩; exact ⟨d, e, (mem_live_all h hq c u d e).2 hm⟩

/-- **A removed member is not listed.** -/
theorem present_not_removed {C : Community.Crypto} {s : DB Fact} (h : Inv (family C) s)
    (hq : s.queue = []) {c u : Id} (hp : u ∈ ((Profile.present c).eval s).map (·.1)) :
    ¬ Removed C s.ops c u := by
  obtain ⟨d, e, ha, hl⟩ := (present_iff h hq c u).1 hp
  exact hl.2 u e ha

/-- **Each person is listed once.** -/
theorem present_nodup (s : DB Fact) (c : Id) : (((Profile.present c).eval s).map (·.1)).Nodup := by
  simp only [Profile.present, View.eval_bind, View.eval_read, View.eval_pure, Profile.byUser,
    List.map_map, Function.comp_def, List.map_id']
  exact RowLaws.uniq_nodup _

/-! ## The people list by window, and its capped count -/

theorem uniq_cons {α : Type} [DecidableEq α] (x : α) (t : List α) :
    React.uniq (x :: t) = x :: React.uniq (t.filter fun y => !decide (y = x)) := by
  rw [React.uniq]

/-- The distinct of a prefix are a prefix of the distinct. -/
theorem uniq_prefix {α : Type} [DecidableEq α] : ∀ (l1 l2 : List α), React.uniq l1 <+: React.uniq (l1 ++ l2)
  | [], _ => by rw [React.uniq]; exact List.nil_prefix
  | x :: t, l2 => by
    rw [List.cons_append, uniq_cons, uniq_cons, List.filter_append]
    have : (t.filter fun y => !decide (y = x)).length < (x :: t).length :=
      Nat.lt_succ_of_le (List.length_filter_le _ _)
    exact (List.prefix_cons_inj x).2 (uniq_prefix _ _)
termination_by l1 => l1.length

/-- Liveness is per row: the live admissions of two runs of rows are
each's, in order. -/
theorem live_append (s : DB Fact) (c : Id) : ∀ (l1 l2 : List (Pos × Fact)),
    (live c (l1 ++ l2)).eval s = (live c l1).eval s ++ (live c l2).eval s
  | [], l2 => by simp only [List.nil_append, live]; rfl
  | (p, f) :: t, l2 => by
    have ih := live_append s c t l2
    cases f
    case admission c' u d e =>
      simp only [List.cons_append, live]
      split
      · rw [View.eval_bind', View.eval_bind', View.eval_bind', View.eval_bind', ih]
        show (if _ then _ else _) = (if _ then _ else _) ++ _
        split <;> simp
      · exact ih
    all_goals simpa [live] using ih

/-- A list of at most m rows is the first m of the whole list. -/
theorem all_take (s : DB Fact) (c : Id) (m : Nat) :
    ((admission.all.read [c] (limit := some m)).eval s).rows = ((admission.all.read [c]).eval s).rows.take m := rfl

theorem byUser_users (ls : List (Id × Key × Key)) : (Profile.byUser ls).map (·.1) = React.uniq (ls.map (·.1)) := by
  simp only [Profile.byUser, List.map_map, Function.comp_def, List.map_id']

/-- **The window lists `present`'s first members, in its order**: its
users are a prefix of the people list's. -/
theorem presentW_prefix (s : DB Fact) (c : Id) (n m : Nat) :
    ((Profile.presentW c n m).eval s).1.map (·.1) <+: ((Profile.present c).eval s).map (·.1) := by
  simp only [Profile.presentW, Profile.present, View.eval_bind, View.eval_pure]
  rw [all_take, List.map_take, byUser_users, byUser_users]
  conv => rhs; rw [← List.take_append_drop m ((admission.all.read [c]).eval s).rows]
  rw [live_append, List.map_append]
  exact (List.take_prefix _ _).trans (uniq_prefix _ _)

/-- **With all of c's admissions read, the window is `present`'s first n**,
keys and all. -/
theorem presentW_complete (s : DB Fact) (c : Id) (n m : Nat) (h : ((Profile.presentW c n m).eval s).2 = true) :
    ((Profile.presentW c n m).eval s).1 = ((Profile.present c).eval s).take n := by
  simp only [Profile.presentW, Profile.present, View.eval_bind, View.eval_pure] at h ⊢
  rw [all_take] at h ⊢
  have hl : ((admission.all.read [c]).eval s).rows.length < m := by
    have := of_decide_eq_true h
    rw [List.length_take] at this
    omega
  rw [List.take_of_length_le (l := ((admission.all.read [c]).eval s).rows) (by omega)]

/-- **The header's count is the people count, capped**, when all of c's
admissions were read. -/
theorem presentCount_complete (s : DB Fact) (c : Id) (cap m : Nat)
    (h : ((Profile.presentCount c cap m).eval s).2 = true) :
    ((Profile.presentCount c cap m).eval s).1 = min cap ((Profile.present c).eval s).length := by
  simp only [Profile.presentCount, View.eval_bind, View.eval_pure] at h ⊢
  rw [presentW_complete s c cap m h, List.length_take]

/-! ### What a window costs, against the whole list -/

/-- Whether a row is an admission into c. -/
def admIn (c : Id) (r : Pos × Fact) : Bool :=
  match r.2 with
  | .admission c' .. => decide (c' = c)
  | _ => false

theorem unremoved_lists (s : DB Fact) (c : Id) : ∀ (l : List (Pos × Fact)),
    View.listsAt s (unremoved c l) ≤ l.length
  | [] => by simp [unremoved, View.listsAt]
  | (p, f) :: t => by
    have ih := unremoved_lists s c t
    cases f
    case admission c' u d e =>
      simp only [unremoved]
      split
      · simp only [View.listsAt, List.length_cons]
        split
        · omega
        · simp [View.listsAt]
      · simp only [List.length_cons]; omega
    all_goals simp only [unremoved, List.length_cons]; omega

theorem deviceLive_lists (s : DB Fact) (c : Id) (d : Key) :
    1 ≤ View.listsAt s (deviceLive c d) ∧
      View.listsAt s (deviceLive c d) ≤ 1 + ((admission.byDevice.read [c, d]).eval s).rows.length := by
  simp only [deviceLive]
  rw [View.listsAt_bindOp]
  have e1 : View.listsAt s (admission.byDevice.read [c, d]) = 1 := rfl
  rw [e1]
  generalize ((admission.byDevice.read [c, d]).eval s).rows = rs
  have := unremoved_lists s c rs
  constructor
  · omega
  · by_cases h : rs.isEmpty = true
    · rw [if_pos h, View.listsAt_pure]; omega
    · rw [if_neg h]; omega

/-- **Liveness costs at most 1 + D lists a row**, when no device is
admitted more than D times. -/
theorem live_lists_le (s : DB Fact) (c : Id) (D : Nat)
    (hD : ∀ d, ((admission.byDevice.read [c, d]).eval s).rows.length ≤ D) :
    ∀ (l : List (Pos × Fact)), View.listsAt s (live c l) ≤ l.length * (1 + D)
  | [] => by simp [live, View.listsAt]
  | (p, f) :: t => by
    have ih := live_lists_le s c D hD t
    cases f
    case admission c' u d e =>
      simp only [live]
      split
      · rw [View.listsAt_bind, View.listsAt_bind]
        have := (deviceLive_lists s c d).2
        have := hD d
        simp only [View.listsAt, List.length_cons, Nat.succ_mul]
        omega
      · simp only [List.length_cons, Nat.succ_mul]; omega
    all_goals simp only [live, List.length_cons, Nat.succ_mul]; omega

/-- **And at least a list for each admission into c.** -/
theorem live_lists_ge (s : DB Fact) (c : Id) :
    ∀ (l : List (Pos × Fact)), (l.filter (admIn c)).length ≤ View.listsAt s (live c l)
  | [] => by simp [live, View.listsAt]
  | (p, f) :: t => by
    have ih := live_lists_ge s c t
    cases f
    case admission c' u d e =>
      by_cases hc : c' = c
      · have hf : List.filter (admIn c) ((p, Fact.admission c' u d e) :: t) =
            (p, Fact.admission c' u d e) :: List.filter (admIn c) t := by
          simp [List.filter_cons, admIn, hc]
        have hl : live c ((p, Fact.admission c' u d e) :: t) = ((deviceLive c d).bind fun ok =>
            (live c t).bind fun rest => View.pure (if ok = true then (u, d, e) :: rest else rest)) := by
          simp only [live, if_pos hc]
        rw [hf, hl, View.listsAt_bind, View.listsAt_bind, List.length_cons]
        have := (deviceLive_lists s c d).1
        omega
      · have hf : List.filter (admIn c) ((p, Fact.admission c' u d e) :: t) = List.filter (admIn c) t := by
          simp [List.filter_cons, admIn, hc]
        have hl : live c ((p, Fact.admission c' u d e) :: t) = live c t := by simp only [live, if_neg hc]
        rw [hf, hl]; exact ih
    all_goals simpa [live, List.filter_cons, admIn] using ih

/-- The lists of the people list's views: one list of admissions, and
each one's liveness. -/
theorem presentW_lists_eq (s : DB Fact) (c : Id) (n m : Nat) :
    View.listsAt s (Profile.presentW c n m) =
      1 + View.listsAt s (live c ((admission.all.read [c] (limit := some m)).eval s).rows) := by
  simp only [Profile.presentW]
  rw [View.listsAt_bindOp]
  have e1 : View.listsAt s (admission.all.read [c] (limit := some m)) = 1 := rfl
  rw [e1, View.listsAt_bindOp, View.listsAt_pure, Nat.add_zero]

theorem present_lists_eq (s : DB Fact) (c : Id) :
    View.listsAt s (Profile.present c) = 1 + View.listsAt s (live c ((admission.all.read [c]).eval s).rows) := by
  simp only [Profile.present]
  rw [View.listsAt_bindOp]
  have e1 : View.listsAt s (admission.all.read [c]) = 1 := rfl
  rw [e1, View.listsAt_bindOp, View.listsAt_pure, Nat.add_zero]

/-- **A window costs O(m) lists, whatever the community's size**: one
list of at most m admissions, and each one's liveness. -/
theorem presentW_lists (s : DB Fact) (c : Id) (n m D : Nat)
    (hD : ∀ d, ((admission.byDevice.read [c, d]).eval s).rows.length ≤ D) :
    View.listsAt s (Profile.presentW c n m) ≤ 1 + m * (1 + D) := by
  rw [presentW_lists_eq]
  have h1 := live_lists_le s c D hD ((admission.all.read [c] (limit := some m)).eval s).rows
  have h2 : ((admission.all.read [c] (limit := some m)).eval s).rows.length ≤ m := by
    rw [all_take, List.length_take]; omega
  have h3 := Nat.mul_le_mul_right (1 + D) h2
  omega

/-- The mutant: the whole list reads a list for every admission into c,
the community's size, on every re-read. -/
theorem present_scans (s : DB Fact) (c : Id) :
    1 + (((admission.all.read [c]).eval s).rows.filter (admIn c)).length ≤ View.listsAt s (Profile.present c) := by
  rw [present_lists_eq]
  have := live_lists_ge s c ((admission.all.read [c]).eval s).rows
  omega

end PeopleLaws
