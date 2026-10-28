/-
Laws of connection, dialing and sealing, about the views a node runs
(Community.Query) as lists over its persisted tables: at rest (queue
empty), `allowPeer` lets in exactly the devices admitted into users not
removed, `members` names exactly their devices and `recipients` exactly
their admissions, each with its encryption key. On SQLite the same
views run with `listSql`, which the query differential checks against
`eval`.
-/
import ops.community.Laws
import ops.community.Query

namespace Community
open Engine

/-! ## The relations -/

theorem rels_distinct : Rel.Distinct rels := by unfold Rel.Distinct; decide

theorem rels_short : ∀ r ∈ rels, r.kind.toUTF8.size < 128 := by decide

variable {s : DB Fact} {C : Crypto}

/-- At rest, the Valid facts filed under a community relation. -/
theorem filed {r : Rel Fact} (hr : r ∈ rels) (h : Inv (family C) s) (hq : s.queue = [])
    (as : List ByteArray) (y : Id) (f : Fact) :
    (y ∈ s.idx (r.key as) ∧ s.status y = some (.valid f)) ↔ V C s.ops y f ∧ r.args f = some as := by
  exact filed_rel (fam := family C) rfl rels_distinct hr (rels_short r hr) h hq as y f

theorem byDevice_args {c d : Id} {f : Fact} :
    admission.byDevice.args f = some [c, d] ↔ ∃ u e, f = .admission c u d e := by
  cases f <;> simp [admission.byDevice, eq_comm]

theorem all_args {c : Id} {f : Fact} :
    admission.all.args f = some [c] ↔ ∃ u d e, f = .admission c u d e := by
  cases f <;> simp [admission.all, eq_comm]

theorem byUser_args {c u : Id} {f : Fact} :
    removal.byUser.args f = some [c, u] ↔ ∃ r, f = .removal c u r := by
  cases f <;> simp [removal.byUser, eq_comm]

/-! ## The views, evaluated -/

theorem removals_iff (h : Inv (family C) s) (hq : s.queue = []) (c u : Id) :
    (eval s (removals c u)).total ≠ 0 ↔ Removed C s.ops c u := by
  rw [← Nat.pos_iff_ne_zero, removals]
  show 0 < (eval s { key := removal.byUser.key [c, u], limit := some 0 }).total ↔ _
  rw [total_pos]
  constructor
  · rintro ⟨y, f, hy, hf⟩
    obtain ⟨hv, hk⟩ := (filed (by simp [rels]) h hq [c, u] y f).1 ⟨hy, hf⟩
    obtain ⟨r, rfl⟩ := byUser_args.1 hk
    exact ⟨y, r, hv⟩
  · rintro ⟨y, r, hv⟩
    obtain ⟨hy, hf⟩ := (filed (by simp [rels]) h hq [c, u] y _).2 ⟨hv, byUser_args.2 ⟨r, rfl⟩⟩
    exact ⟨y, _, hy, hf⟩

theorem eval_live_adm {c c' : Id} {k : ByteArray} {y u : Id} {d e : Key} {t : List (Pos × Fact)}
    (hc : c' = c) :
    (live c (((k, y), .admission c' u d e) :: t)).eval s =
      if (eval s (removals c u)).total = 0 then (y, u, d, e) :: (live c t).eval s
      else (live c t).eval s := by
  subst hc
  show View.eval s (if c' = c' then _ else _) = _
  rw [if_pos rfl]
  show View.eval s ((live c' t).bind _) = _
  rw [View.eval_bind']
  split <;> rfl

theorem mem_live (c : Id) (rows : List (Pos × Fact)) (y u : Id) (d e : Key) :
    (y, u, d, e) ∈ (live c rows).eval s ↔
      (∃ k, ((k, y), .admission c u d e) ∈ rows) ∧ (eval s (removals c u)).total = 0 := by
  induction rows with
  | nil => simp [live, View.eval]
  | cons pf t ih =>
    obtain ⟨⟨k, y'⟩, f⟩ := pf
    have tail : (∃ q, ((q, y), Fact.admission c u d e) ∈ ((k, y'), f) :: t) ↔
        (((k, y'), f) = ((k, y), .admission c u d e)) ∨ ∃ q, ((q, y), Fact.admission c u d e) ∈ t := by
      constructor
      · rintro ⟨q, hq⟩
        rcases List.mem_cons.1 hq with hq | hq
        · simp only [Prod.mk.injEq] at hq; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hq; exact Or.inl rfl
        · exact Or.inr ⟨q, hq⟩
      · rintro (hq | ⟨q, hq⟩)
        · rw [hq]; exact ⟨k, List.mem_cons_self ..⟩
        · exact ⟨q, List.mem_cons_of_mem _ hq⟩
    rw [tail]
    cases f with
    | admission c' u' d' e' =>
      by_cases hc : c' = c
      · rw [eval_live_adm hc]
        subst hc
        by_cases hz : (eval s (removals c' u')).total = 0
        · rw [if_pos hz, List.mem_cons, ih]
          constructor
          · rintro (he | ⟨hq, hr⟩)
            · simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl, rfl, rfl⟩ := he
              exact ⟨Or.inl rfl, hz⟩
            · exact ⟨Or.inr hq, hr⟩
          · rintro ⟨he | hq, hr⟩
            · simp only [Prod.mk.injEq, Fact.admission.injEq] at he
              obtain ⟨⟨_, rfl⟩, _, rfl, rfl, rfl⟩ := he; exact Or.inl rfl
            · exact Or.inr ⟨hq, hr⟩
        · rw [if_neg hz, ih]
          constructor
          · rintro ⟨hq, hr⟩; exact ⟨Or.inr hq, hr⟩
          · rintro ⟨he | hq, hr⟩
            · simp only [Prod.mk.injEq, Fact.admission.injEq] at he
              obtain ⟨_, _, rfl, _, _⟩ := he; exact absurd hr hz
            · exact ⟨hq, hr⟩
      · have : (live c (((k, y'), .admission c' u' d' e') :: t)).eval s = (live c t).eval s := by
          show View.eval s (if c' = c then _ else _) = _
          rw [if_neg hc]
        rw [this, ih]
        constructor
        · rintro ⟨hq, hr⟩; exact ⟨Or.inr hq, hr⟩
        · rintro ⟨he | hq, hr⟩
          · simp only [Prod.mk.injEq, Fact.admission.injEq] at he; exact absurd he.2.1 hc
          · exact ⟨hq, hr⟩
    | _ =>
      show (y, u, d, e) ∈ (live c t).eval s ↔ _
      rw [ih]
      simp

/-- At rest, the live admissions of a whole list of a community relation. -/
theorem live_iff (h : Inv (family C) s) (hq : s.queue = []) {r : Rel Fact} (hr : r ∈ rels)
    (as : List ByteArray) (c y u : Id) (d e : Key) :
    (y, u, d, e) ∈ (live c (eval s (r.query as)).rows).eval s ↔
      (V C s.ops y (.admission c u d e) ∧ r.args (.admission c u d e) = some as) ∧
        ¬ Removed C s.ops c u := by
  rw [mem_live]
  apply and_congr
  · show (∃ k, ((k, y), _) ∈ (eval s { key := r.key as, limit := none }).rows) ↔ _
    constructor
    · rintro ⟨k, hp⟩
      obtain ⟨y', f, he, hy, hf⟩ := (mem_rows_all _).1 hp
      simp only [Prod.mk.injEq] at he
      obtain ⟨⟨_, rfl⟩, rfl⟩ := he
      exact (filed hr h hq as _ _).1 ⟨hy, hf⟩
    · rintro ⟨hv, hk⟩
      obtain ⟨hy, hf⟩ := (filed hr h hq as y _).2 ⟨hv, hk⟩
      exact ⟨_, (mem_rows_all _).2 ⟨y, _, rfl, hy, hf⟩⟩
  · rw [← removals_iff h hq]; simp

/-! ## The laws -/

/-- **Who we connect to.** At rest, the `allowPeer` view, read over the
node's persisted tables, accepts device d for community c exactly when d
is admitted into a user of c that has not been removed. -/
theorem connect_iff (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (d : Key) :
    (allowPeer c d).eval s = true ↔ ∃ u e, Admitted C s.ops c u d e ∧ ¬ Removed C s.ops c u := by
  simp only [allowPeer, View.eval_bind, View.eval_read, View.eval_pure, List.any_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨⟨y, u, d', e⟩, hm, rfl⟩
    obtain ⟨⟨hv, _⟩, hr⟩ := (live_iff h hq (by simp [rels]) [c, d'] c y u d' e).1 hm
    exact ⟨u, e, ⟨y, hv⟩, hr⟩
  · rintro ⟨u, e, ⟨y, hv⟩, hr⟩
    exact ⟨(y, u, d, e), (live_iff h hq (by simp [rels]) [c, d] c y u d e).2
      ⟨⟨hv, byDevice_args.2 ⟨u, e, rfl⟩⟩, hr⟩, rfl⟩

/-- **No connection to non-members or removed members.** -/
theorem refuse_nonmember (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (d : Key)
    (hd : ∀ u e, Admitted C s.ops c u d e → Removed C s.ops c u) :
    (allowPeer c d).eval s = false := by
  cases hb : (allowPeer c d).eval s
  · rfl
  · obtain ⟨u, e, ha, hr⟩ := (connect_iff h hq c d).1 hb; exact absurd (hd u e ha) hr

/-- **Approved devices are let in.** A device whose request is tallied
by an admit op with its invitation's threshold of approvals by distinct
users is accepted, unless that user has been removed. -/
theorem connect_admitted (h : Inv (family C) s) (hq : s.queue = []) {y c r : Id} {o : Op}
    {aps us : List Id} {d0 e0 : Key} {u : Id} {d e : Key} {l : Bool} {t : Nat}
    (hy : s.ops y = some o) (hb : (Codec.decode o.body : Option Body) = some .admit)
    (hkd : o.kind = Body.tag .admit) (hreq : o.reqs = c :: r :: aps) (hc : V C s.ops c (.admission c c d0 e0))
    (hr : V C s.ops r (.request c u d e l t))
    (hap : All2 (fun a v => V C s.ops a (.approval c r v)) aps us) (hn : us.Nodup)
    (ht : us.length = t) (hnr : ¬ Removed C s.ops c u) :
    (allowPeer c d).eval s = true :=
  (connect_iff h hq c d).2 ⟨_, e, ⟨y, admit_admits hy hb hkd hreq hc hr hap hn ht⟩, hnr⟩

/-- **Only the founder and approved devices are let in.** At rest, a
device `allowPeer` accepts is admitted into a user not removed, by the
root (the founder) or by an admit op tallying exactly the threshold of
approvals, by distinct users, of a Valid request for that device. A
request alone never connects: requests sit under keys of their own. -/
theorem connect_approved (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (d : Key)
    (ha : (allowPeer c d).eval s = true) :
    ∃ u e y, V C s.ops y (.admission c u d e) ∧ ¬ Removed C s.ops c u ∧
      ((y = c ∧ u = c) ∨
        ∃ o r aps l t us, s.ops y = some o ∧ (Codec.decode o.body : Option Body) = some .admit ∧
          o.reqs = c :: r :: aps ∧ V C s.ops r (.request c u d e l t) ∧
          All2 (fun a v => V C s.ops a (.approval c r v)) aps us ∧ us.Nodup ∧ us.length = t) := by
  obtain ⟨u, e, ⟨y, hy⟩, hnr⟩ := (connect_iff h hq c d).1 ha
  exact ⟨u, e, y, hy, hnr, admission_approved h.key hy⟩

theorem mem_live_all (h : Inv (family C) s) (hq : s.queue = []) (c y u : Id) (d e : Key) :
    (y, u, d, e) ∈ (live c (eval s (admission.all.query [c])).rows).eval s ↔
      V C s.ops y (.admission c u d e) ∧ ¬ Removed C s.ops c u := by
  rw [live_iff h hq (by simp [rels])]
  constructor
  · rintro ⟨⟨hv, _⟩, hr⟩; exact ⟨hv, hr⟩
  · rintro ⟨hv, hr⟩; exact ⟨⟨hv, all_args.2 ⟨u, d, e, rfl⟩⟩, hr⟩

/-- **Whom we dial.** At rest, `members` names exactly the devices
admitted into users of c not removed. -/
theorem members_iff (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (d : Key) :
    d ∈ (members c).eval s ↔ ∃ u e, Admitted C s.ops c u d e ∧ ¬ Removed C s.ops c u := by
  simp only [members, View.eval_bind, View.eval_read, View.eval_pure, List.mem_map]
  constructor
  · rintro ⟨⟨y, u, d', e⟩, hm, rfl⟩
    obtain ⟨hv, hr⟩ := (mem_live_all h hq c y u d' e).1 hm
    exact ⟨u, e, ⟨y, hv⟩, hr⟩
  · rintro ⟨u, e, ⟨y, hv⟩, hr⟩; exact ⟨(y, u, d, e), (mem_live_all h hq c y u d e).2 ⟨hv, hr⟩, rfl⟩

/-- **Who a content key is wrapped to.** At rest, `recipients` names
exactly the live admissions of c, each with its encryption key: an
admission into a user of c not removed. No outsider, no removed user's
admission, and no member left out. `shareKey`, the running wrap writer,
wraps to these. -/
theorem recipients_iff (h : Inv (family C) s) (hq : s.queue = []) (c y : Id) (e : Key) :
    (y, e) ∈ (recipients c).eval s ↔
      ∃ u d, V C s.ops y (.admission c u d e) ∧ ¬ Removed C s.ops c u := by
  simp only [recipients, View.eval_bind, View.eval_read, View.eval_pure, List.mem_map]
  constructor
  · rintro ⟨⟨y', u, d, e'⟩, hm, he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨u, d, (mem_live_all h hq c y' u d e').1 hm⟩
  · rintro ⟨u, d, hm⟩; exact ⟨(y, u, d, e), (mem_live_all h hq c y u d e).2 hm, rfl⟩

/-! ## Partitions -/

/-- **Nodes that hold the same ops agree on whom to connect to.** -/
theorem connect_agree {s t : DB Fact} (hs : Inv (family C) s) (ht : Inv (family C) t)
    (qs : s.queue = []) (qt : t.queue = []) (hops : s.ops = t.ops) (c : Id) (d : Key) :
    (allowPeer c d).eval s = (allowPeer c d).eval t := by
  have hs' := connect_iff hs qs c d
  have ht' := connect_iff ht qt c d
  rw [hops] at hs'
  cases h1 : (allowPeer c d).eval s <;> cases h2 : (allowPeer c d).eval t
  · rfl
  · rw [h1] at hs'; rw [h2] at ht'
    exact absurd (hs'.2 (ht'.1 rfl)) (by simp)
  · rw [h1] at hs'; rw [h2] at ht'
    exact absurd (ht'.2 (hs'.1 rfl)) (by simp)
  · rfl

/-- **A removal, once held, cuts off every device of the removed user**
that is admitted into no other live user. -/
theorem removal_cuts_off (h : Inv (family C) s) (hq : s.queue = []) {c u : Id} {d : Key}
    (hr : Removed C s.ops c u) (only : ∀ u' e, Admitted C s.ops c u' d e → u' = u) :
    (allowPeer c d).eval s = false :=
  refuse_nonmember h hq c d fun u' e ha => (only u' e ha) ▸ hr

end Community
