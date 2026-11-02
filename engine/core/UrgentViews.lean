/-
Urgent facts are final after every turn, so a view that reads only keys
urgent facts are filed under answers on a store as on the same store
drained to rest (engine/core/TurnLaws.lean has the capped turn): draining
decides no Valid urgent fact (each is decided already), so it files
nothing under such a key, and no urgent fact's verdict changes. Every
law of such views at rest (an empty queue) thus holds after every turn.

- `UrgentKey uc k`: every fact filed under k is urgent (`uc.uf`).
- `Final uc s`: every Valid urgent fact the spec gives is s's verdict;
  `final_of_settled`: UrgentSettled and the family's UrgentCites give it.
- `step_final`, `drain_final`: a step, and a drain, keep `Final`, every
  urgent key's list, and every urgent fact's verdict.
- `view_rest`: **a view reading only urgent keys answers on s as on any
  drain of s**; `status_rest`: an urgent fact's verdict is the same.
-/
import engine.core.CarryLaws
import engine.core.Project

namespace Engine
variable {F : Type} {fam : Family F}

variable (fam) in
/-- Every fact filed under k is urgent. -/
def UrgentKey (uc : UrgentCites fam) (k : ByteArray) : Prop :=
  ∀ x f, k ∈ fam.fileKeys x f → uc.uf f = true

variable (fam) in
/-- Every urgent fact Valid by the spec over s's ops is s's verdict. -/
def Final (uc : UrgentCites fam) (s : DB F) : Prop :=
  ∀ x f, uc.uf f = true → Spec fam s.ops x (.valid f) → s.status x = some (.valid f)

/-- **Urgent work settled makes every urgent fact final.** -/
theorem final_of_settled (uc : UrgentCites fam) {s : DB F} (hi : Inv fam s) (hu : UrgentSettled fam s) :
    Final fam uc s := by
  intro x f hf hs
  obtain ⟨n, hn⟩ := hs
  cases n with
  | zero => cases hn
  | succ n =>
    obtain ⟨o, fs, ho, -, hv⟩ := specAt_valid_inv hn
    exact (urgent_valid_spec uc hi hu ho (uc.fact o fs f hv hf) f).2 ⟨n + 1, hn⟩

theorem indexAllS_other (x : Id) : ∀ (ks : List ByteArray) (s : DB F) (k : ByteArray), k ∉ ks →
    (indexAllS x ks s).idx k = s.idx k
  | [], _, _, _ => rfl
  | k' :: ks, s, k, hk => by
    show (indexAllS x ks (s.index k' x)).idx k = _
    rw [indexAllS_other x ks _ k (fun h => hk (List.mem_cons_of_mem _ h))]
    show (if k = k' then _ else s.idx k) = _
    rw [if_neg (by intro e; subst e; exact hk (List.mem_cons_self ..))]

theorem decide_idx_other {t : DB F} {x : Id} {v : Verdict F} {k : ByteArray}
    (hk : ∀ f, v = .valid f → k ∉ fam.fileKeys x f) : (decideS fam x v t).idx k = t.idx k := by
  cases v with
  | valid f =>
    show (indexAllS x (fam.fileKeys x f) (t.setStatus x (.valid f))).idx k = _
    rw [indexAllS_other x _ _ k (hk f rfl)]; rfl
  | invalid => rfl

/-- A step that decides op y, undecided and with its verdict the spec's,
in a state where urgent facts are final: no urgent fact is new. -/
theorem decide_not_urgent (uc : UrgentCites fam) {t : DB F} (hf : Final fam uc t) {y : Id} (hy : t.status y = none)
    {v : Verdict F} (hv : Spec fam t.ops y v) : ∀ f, v = .valid f → uc.uf f = false := by
  rintro f rfl
  cases h : uc.uf f
  · rfl
  · rw [hf y f h hv] at hy; cases hy

/-- **A step keeps urgent facts final, every urgent key's list, and every
urgent fact's verdict.** -/
theorem step_final (uc : UrgentCites fam) {t : DB F} (hi : Inv fam t) (hf : Final fam uc t) :
    Final fam uc (stepS fam t) ∧ (∀ k, UrgentKey fam uc k → (stepS fam t).idx k = t.idx k) ∧
      (∀ y g, uc.uf g = true → ((stepS fam t).status y = some (.valid g) ↔ t.status y = some (.valid g))) := by
  have g := grows_step (fam := fam) t
  have hfin : Final fam uc (stepS fam t) := fun x f hu hs => by
    rw [stepS_ops] at hs; exact g.1 x _ (hf x f hu hs)
  refine ⟨hfin, ?_⟩
  have hi' := inv_step (fam := fam) hi
  cases hq : t.queue with
  | nil =>
    have e : stepS fam t = t := by unfold stepS; rw [hq]
    rw [e]; exact ⟨fun _ _ => rfl, fun _ _ _ => Iff.rfl⟩
  | cons y q =>
    cases hs : t.status y with
    | some _ =>
      have e : stepS fam t = { t with queue := q } := by unfold stepS; rw [hq]; simp only [hs]
      rw [e]; exact ⟨fun _ _ => rfl, fun _ _ _ => Iff.rfl⟩
    | none =>
      cases ho : t.ops y with
      | none =>
        have e : stepS fam t = { t with queue := q } := by unfold stepS; rw [hq]; simp only [hs, ho]
        rw [e]; exact ⟨fun _ _ => rfl, fun _ _ _ => Iff.rfl⟩
      | some o =>
        cases hj : judge fam o (o.reqs.map t.status) with
        | none =>
          have e : stepS fam t = waitOnS y o.reqs { t with queue := q } := by
            unfold stepS; rw [hq]; simp only [hs, ho, hj]
          rw [e]
          exact ⟨fun _ _ => by rw [waitOnS_idx], fun _ _ _ => by rw [waitOnS_status]⟩
        | some v =>
          have hd : stepS fam t = decideS fam y v { t with queue := q } := by
            unfold stepS; rw [hq]; simp only [hs, ho, hj]
          obtain ⟨-, h2, -⟩ := decideS_fields (fam := fam) y v { t with queue := q }
          have hsv : (stepS fam t).status y = some v := by rw [hd, h2]; simp
          have hspec : Spec fam t.ops y v := by
            have := hi'.sound y v hsv; rwa [stepS_ops] at this
          have hnot := decide_not_urgent uc hf hs hspec
          refine ⟨fun k hk => ?_, fun z gz hgz => ?_⟩
          · rw [hd]
            exact decide_idx_other fun f hvf hkf => by
              have := hk y f hkf; rw [hnot f hvf] at this; cases this
          · rw [hd, h2]
            by_cases hzy : z = y
            · subst hzy
              simp only [ite_true]
              rw [hs]
              constructor
              · intro h; cases h; rw [hnot gz rfl] at hgz; cases hgz
              · intro h; cases h
            · simp only [hzy, ite_false]

/-- **A drain keeps them too.** -/
theorem drain_final (uc : UrgentCites fam) : ∀ (n : Nat) {t : DB F}, Inv fam t → Final fam uc t →
    Final fam uc (drainS fam n t) ∧ (∀ k, UrgentKey fam uc k → (drainS fam n t).idx k = t.idx k) ∧
      (∀ y g, uc.uf g = true → ((drainS fam n t).status y = some (.valid g) ↔ t.status y = some (.valid g)))
  | 0, _, _, hf => ⟨hf, fun _ _ => rfl, fun _ _ _ => Iff.rfl⟩
  | n + 1, t, hi, hf => by
    obtain ⟨f1, i1, s1⟩ := step_final uc hi hf
    unfold drainS
    split
    · exact ⟨f1, i1, s1⟩
    · obtain ⟨f2, i2, s2⟩ := drain_final uc n (inv_step hi) f1
      exact ⟨f2, fun k hk => (i2 k hk).trans (i1 k hk), fun y g hg => (s2 y g hg).trans (s1 y g hg)⟩

/-- A list under an urgent key answers alike on two stores that agree on
urgent keys' lists and urgent facts' verdicts. -/
theorem eval_urgent [SortKey F] (uc : UrgentCites fam) {s t : DB F} (hs : Inv fam s) (ht : Inv fam t)
    (hidx : ∀ k, UrgentKey fam uc k → t.idx k = s.idx k)
    (hst : ∀ y g, uc.uf g = true → (t.status y = some (.valid g) ↔ s.status y = some (.valid g)))
    {q : ListQ} (hk : UrgentKey fam uc q.key) : eval t q = eval s q := by
  have hm : matching t q = matching s q := by
    unfold matching
    rw [hidx _ hk]
    congr 1
    refine filterMap_congr' fun x hx => ?_
    obtain ⟨f, hf, hkf⟩ := (hs.idx q.key x).1 hx
    have htf := (hst x f (hk x f hkf)).2 hf
    have hhas : (fun k => has (t.idx k) x) = fun k => has (s.idx k) x := by
      funext k
      refine Bool.eq_iff_iff.2 ((has_iff _ x).trans (Iff.trans ?_ (has_iff _ x).symm))
      rw [ht.idx k x, hs.idx k x]
      constructor
      · rintro ⟨g, hg, hkg⟩; rw [htf] at hg; cases hg; exact ⟨f, hf, hkg⟩
      · rintro ⟨g, hg, hkg⟩; rw [hf] at hg; cases hg; exact ⟨f, htf, hkg⟩
    rw [hhas, htf, hf]
  unfold eval
  rw [hm]

theorem view_urgent [SortKey F] (uc : UrgentCites fam) {s t : DB F} (hs : Inv fam s) (ht : Inv fam t)
    (hidx : ∀ k, UrgentKey fam uc k → t.idx k = s.idx k)
    (hst : ∀ y g, uc.uf g = true → (t.status y = some (.valid g) ↔ s.status y = some (.valid g)))
    {α : Type} {v : View F α} (hv : v.Reads (UrgentKey fam uc)) : v.eval t = v.eval s := by
  induction hv with
  | pure x => rfl
  | @list q k hk _ ih =>
    show View.eval t (k (Engine.eval t q)) = View.eval s (k (Engine.eval s q))
    rw [eval_urgent uc hs ht hidx hst hk]
    exact ih _

/-- **A view reading only urgent keys answers on a store whose urgent
work is settled as on any drain of it**, in particular at rest. -/
theorem view_rest [SortKey F] (uc : UrgentCites fam) {s : DB F} (hi : Inv fam s) (hu : UrgentSettled fam s)
    (n : Nat) {α : Type} {v : View F α} (hv : v.Reads (UrgentKey fam uc)) :
    v.eval s = v.eval (drainS fam n s) := by
  obtain ⟨-, hidx, hst⟩ := drain_final uc n hi (final_of_settled uc hi hu)
  exact (view_urgent uc hi (inv_drainS hi n) hidx hst hv).symm

/-- **An urgent fact's verdict is the same at rest.** -/
theorem status_rest (uc : UrgentCites fam) {s : DB F} (hi : Inv fam s) (hu : UrgentSettled fam s)
    (n : Nat) {y : Id} {g : F} (hg : uc.uf g = true) :
    s.status y = some (.valid g) ↔ (drainS fam n s).status y = some (.valid g) :=
  ((drain_final uc n hi (final_of_settled uc hi hu)).2.2 y g hg).symm

/-- A lifted view reads the lists the view reads. -/
theorem View.Reads.liftL {A B α : Type} {P : ByteArray → Prop} {v : View A α} (hv : v.Reads P) :
    (v.liftL : View (A ⊕ B) α).Reads P := by
  induction hv with
  | pure x => exact .pure x
  | list hq _ ih => exact .list hq fun _ => ih _

end Engine
