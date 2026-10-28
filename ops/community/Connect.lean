/-
Laws of connection, dialing and sealing, about the views a node runs
(Community.Query) as lists over its persisted tables. At rest (queue
empty):
- a device is live (`deviceLive`) exactly when it is admitted and none
  of its users is removed (`Live`);
- `allowPeer` lets in exactly the node keys a live device is admitted
  under;
- `members` names exactly the live devices, and `recipients` exactly the
  keys they are admitted under, the keys `allowPeer` lets in.

On SQLite the same views run with `listSql`, which the query
differential checks against `eval`.
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

theorem byKey_args {c e : Id} {f : Fact} :
    admission.byKey.args f = some [c, e] ↔ ∃ u d, f = .admission c u d e := by
  cases f <;> simp [admission.byKey, eq_comm]

/-- At rest, a fact is a row of a community relation's list exactly when
it is Valid and filed in it. -/
theorem exists_row (h : Inv (family C) s) (hq : s.queue = []) {r : Rel Fact} (hr : r ∈ rels)
    (as : List ByteArray) (f : Fact) :
    (∃ p, (p, f) ∈ (eval s (r.query as)).rows) ↔ ∃ y, V C s.ops y f ∧ r.args f = some as := by
  show (∃ p, (p, f) ∈ (eval s { key := r.key as, limit := none }).rows) ↔ _
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨y, f', he, hy, hf⟩ := (mem_rows_all _).1 hp
    simp only [Prod.mk.injEq] at he
    obtain ⟨_, rfl⟩ := he
    exact ⟨y, (filed hr h hq as y _).1 ⟨hy, hf⟩⟩
  · rintro ⟨y, hv, hk⟩
    obtain ⟨hy, hf⟩ := (filed hr h hq as y _).2 ⟨hv, hk⟩
    exact ⟨_, (mem_rows_all _).2 ⟨y, _, rfl, hy, hf⟩⟩

theorem mem_cons_row {p : Pos} {f g : Fact} {t : List (Pos × Fact)} :
    (∃ q, (q, g) ∈ (p, f) :: t) ↔ f = g ∨ ∃ q, (q, g) ∈ t := by
  constructor
  · rintro ⟨q, hq⟩
    rcases List.mem_cons.1 hq with hq | hq
    · simp only [Prod.mk.injEq] at hq; exact Or.inl hq.2.symm
    · exact Or.inr ⟨q, hq⟩
  · rintro (rfl | ⟨q, hq⟩)
    · exact ⟨p, List.mem_cons_self ..⟩
    · exact ⟨q, List.mem_cons_of_mem _ hq⟩

/-- `unremoved` holds of rows exactly when every admission into c among
them is into a user whose removals count none. -/
theorem unremoved_iff (c : Id) (rows : List (Pos × Fact)) :
    (unremoved c rows).eval s = true ↔
      ∀ u d e, (∃ p, (p, .admission c u d e) ∈ rows) → (eval s (removals c u)).total = 0 := by
  induction rows with
  | nil => simp [unremoved, View.eval]
  | cons pf t ih =>
    obtain ⟨p, f⟩ := pf
    simp only [mem_cons_row]
    cases f with
    | admission c' u' d' e' =>
      by_cases hc : c' = c
      · subst hc
        show View.eval s (if c' = c' then _ else _) = true ↔ _
        rw [if_pos rfl]
        show View.eval s (if (eval s (removals c' u')).total = 0 then _ else _) = true ↔ _
        by_cases hz : (eval s (removals c' u')).total = 0
        · rw [if_pos hz, ih]
          constructor
          · rintro hall u d e (he | hm)
            · simp only [Fact.admission.injEq] at he; obtain ⟨_, rfl, _, _⟩ := he; exact hz
            · exact hall u d e hm
          · intro hall u d e hm; exact hall u d e (Or.inr hm)
        · rw [if_neg hz]
          show (false = true) ↔ _
          constructor
          · intro hf; cases hf
          · intro hall; exact absurd (hall u' d' e' (Or.inl rfl)) hz
      · show View.eval s (if c' = c then _ else _) = true ↔ _
        rw [if_neg hc, ih]
        constructor
        · rintro hall u d e (he | hm)
          · simp only [Fact.admission.injEq] at he; exact absurd he.1 hc
          · exact hall u d e hm
        · intro hall u d e hm; exact hall u d e (Or.inr hm)
    | _ =>
      show (unremoved c t).eval s = true ↔ _
      rw [ih]
      simp

/-- **A device is live exactly when the view says so.** At rest,
`deviceLive c d` holds exactly when d is admitted into c and none of its
users is removed. -/
theorem deviceLive_iff (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (d : Key) :
    (deviceLive c d).eval s = true ↔ Live C s.ops c d := by
  have hrow : ∀ u e, (∃ p, (p, .admission c u d e) ∈ (eval s (admission.byDevice.query [c, d])).rows) ↔
      Admitted C s.ops c u d e := by
    intro u e
    rw [exists_row h hq (by simp [rels])]
    exact ⟨fun ⟨y, hv, _⟩ => ⟨y, hv⟩, fun ⟨y, hv⟩ => ⟨y, hv, byDevice_args.2 ⟨u, e, rfl⟩⟩⟩
  have hd : ∀ u d' e, (∃ p, (p, .admission c u d' e) ∈ (eval s (admission.byDevice.query [c, d])).rows) →
      d' = d := by
    rintro u d' e ⟨p, hp⟩
    obtain ⟨_, hv, hk⟩ := (exists_row h hq (by simp [rels]) [c, d] _).1 ⟨p, hp⟩
    obtain ⟨_, _, he⟩ := byDevice_args.1 hk
    simp only [Fact.admission.injEq] at he; exact he.2.2.1
  have hev : (deviceLive c d).eval s =
      if (eval s (admission.byDevice.query [c, d])).rows.isEmpty then false
      else (unremoved c (eval s (admission.byDevice.query [c, d])).rows).eval s := by
    unfold deviceLive
    rw [View.eval_bind]
    by_cases he : (eval s (admission.byDevice.query [c, d])).rows.isEmpty = true
    · simp only [Rel.read, View.eval_read, he, ite_true]; rfl
    · simp only [Rel.read, View.eval_read, he, ite_false, Bool.false_eq_true]
  rw [hev]
  split
  · rename_i he
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨⟨u, e, ha⟩, _⟩
    obtain ⟨p, hp⟩ := (hrow u e).2 ha
    rw [List.isEmpty_iff] at he; rw [he] at hp; cases hp
  · rename_i he
    rw [unremoved_iff]
    constructor
    · intro hall
      obtain ⟨⟨p, f⟩, hm⟩ := List.exists_mem_of_ne_nil _ (by simpa using he)
      obtain ⟨_, hv, hk⟩ := (exists_row h hq (by simp [rels]) [c, d] f).1 ⟨p, hm⟩
      obtain ⟨u, e, rfl⟩ := byDevice_args.1 hk
      refine ⟨⟨u, e, _, hv⟩, fun u' e' ha => ?_⟩
      rw [← removals_iff h hq]
      exact fun hne => hne (hall u' d e' ((hrow u' e').2 ha))
    · rintro ⟨_, hall⟩ u d' e hm
      have := hd u d' e hm; subst this
      exact Decidable.of_not_not fun hne => hall u e ((hrow u e).1 hm) ((removals_iff h hq c u).1 hne)

theorem eval_live_adm {c c' : Id} {p : Pos} {u : Id} {d e : Key} {t : List (Pos × Fact)}
    (hc : c' = c) :
    (live c ((p, .admission c' u d e) :: t)).eval s =
      if (deviceLive c d).eval s then (u, d, e) :: (live c t).eval s
      else (live c t).eval s := by
  subst hc
  show View.eval s (if c' = c' then _ else _) = _
  rw [if_pos rfl, View.eval_bind', View.eval_bind']
  split <;> rfl

theorem mem_live (c : Id) (rows : List (Pos × Fact)) (u : Id) (d e : Key) :
    (u, d, e) ∈ (live c rows).eval s ↔
      (∃ p, (p, .admission c u d e) ∈ rows) ∧ (deviceLive c d).eval s = true := by
  induction rows with
  | nil => simp [live, View.eval]
  | cons pf t ih =>
    obtain ⟨p, f⟩ := pf
    rw [mem_cons_row]
    cases f with
    | admission c' u' d' e' =>
      by_cases hc : c' = c
      · rw [eval_live_adm hc]
        subst hc
        by_cases hz : (deviceLive c' d').eval s = true
        · rw [if_pos hz, List.mem_cons, ih]
          constructor
          · rintro (he | ⟨hq, hr⟩)
            · simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl, rfl⟩ := he
              exact ⟨Or.inl rfl, hz⟩
            · exact ⟨Or.inr hq, hr⟩
          · rintro ⟨he | hq, hr⟩
            · simp only [Fact.admission.injEq] at he
              obtain ⟨_, rfl, rfl, rfl⟩ := he; exact Or.inl rfl
            · exact Or.inr ⟨hq, hr⟩
        · rw [if_neg hz, ih]
          constructor
          · rintro ⟨hq, hr⟩; exact ⟨Or.inr hq, hr⟩
          · rintro ⟨he | hq, hr⟩
            · simp only [Fact.admission.injEq] at he
              obtain ⟨_, _, rfl, _⟩ := he; exact absurd hr hz
            · exact ⟨hq, hr⟩
      · have : (live c ((p, .admission c' u' d' e') :: t)).eval s = (live c t).eval s := by
          show View.eval s (if c' = c then _ else _) = _
          rw [if_neg hc]
        rw [this, ih]
        constructor
        · rintro ⟨hq, hr⟩; exact ⟨Or.inr hq, hr⟩
        · rintro ⟨he | hq, hr⟩
          · simp only [Fact.admission.injEq] at he; exact absurd he.1 hc
          · exact ⟨hq, hr⟩
    | _ =>
      show (u, d, e) ∈ (live c t).eval s ↔ _
      rw [ih]
      simp

/-- At rest, the live admissions of a whole list of a community relation:
its Valid admissions whose device is live. -/
theorem live_iff (h : Inv (family C) s) (hq : s.queue = []) {r : Rel Fact} (hr : r ∈ rels)
    (as : List ByteArray) (c u : Id) (d e : Key) :
    (u, d, e) ∈ (live c (eval s (r.query as)).rows).eval s ↔
      (∃ y, V C s.ops y (.admission c u d e) ∧ r.args (.admission c u d e) = some as) ∧
        Live C s.ops c d := by
  rw [mem_live, exists_row h hq hr, deviceLive_iff h hq]

/-- A cut device is not live. -/
theorem cut_not_live {ops : Id → Option Op} {c : Id} {d : Key} (h : Cut C ops c d) :
    ¬ Live C ops c d := by
  obtain ⟨u, e, ha, hr⟩ := h
  exact fun ⟨_, hall⟩ => hall u e ha hr

/-! ## The laws -/

/-- **Who we connect to.** At rest, the `allowPeer` view, read over the
node's persisted tables, accepts node key e for community c exactly when
a live device is admitted under e. -/
theorem connect_iff (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (e : Key) :
    (allowPeer c e).eval s = true ↔ ∃ u d, Admitted C s.ops c u d e ∧ Live C s.ops c d := by
  simp only [allowPeer, View.eval_bind, View.eval_read, View.eval_pure, List.any_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨⟨u, d, e'⟩, hm, rfl⟩
    obtain ⟨⟨y, hv, _⟩, hl⟩ := (live_iff h hq (by simp [rels]) [c, e'] c u d e').1 hm
    exact ⟨u, d, ⟨y, hv⟩, hl⟩
  · rintro ⟨u, d, ⟨y, hv⟩, hl⟩
    exact ⟨(u, d, e), (live_iff h hq (by simp [rels]) [c, e] c u d e).2
      ⟨⟨y, hv, byKey_args.2 ⟨u, d, rfl⟩⟩, hl⟩, rfl⟩

/-- **No connection to a node with no live device.** -/
theorem refuse_nonmember (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (e : Key)
    (hd : ∀ u d, Admitted C s.ops c u d e → Cut C s.ops c d) :
    (allowPeer c e).eval s = false := by
  cases hb : (allowPeer c e).eval s
  · rfl
  · obtain ⟨u, d, ha, hl⟩ := (connect_iff h hq c e).1 hb
    exact absurd hl (cut_not_live (hd u d ha))

/-- **Approved devices' nodes are let in.** A request tallied by an admit
op with its invitation's threshold of approvals by distinct users lets
in the key it names, unless one of its device's users is removed. -/
theorem connect_admitted (h : Inv (family C) s) (hq : s.queue = []) {y c r : Id} {o : Op}
    {aps us : List Id} {d0 e0 : Key} {u : Id} {d e : Key} {l : Bool} {t : Nat}
    (hy : s.ops y = some o) (hb : (Codec.decode o.body : Option Body) = some .admit)
    (hkd : o.kind = Body.tag .admit) (hreq : o.reqs = c :: r :: aps) (hc : V C s.ops c (.admission c c d0 e0))
    (hr : V C s.ops r (.request c u d e l t))
    (hap : All2 (fun a v => V C s.ops a (.approval c r v)) aps us) (hn : us.Nodup)
    (ht : us.length = t) (hnr : ∀ u' e', Admitted C s.ops c u' d e' → ¬ Removed C s.ops c u') :
    (allowPeer c e).eval s = true :=
  have ha : Admitted C s.ops c u d e := ⟨y, admit_admits hy hb hkd hreq hc hr hap hn ht⟩
  (connect_iff h hq c e).2 ⟨u, d, ha, ⟨u, e, ha⟩, hnr⟩

/-- **Only the founder's and approved devices' nodes are let in.** At
rest, a key `allowPeer` accepts has a live device admitted under it, by
the root (the founder) or by an admit op tallying exactly the threshold
of approvals, by distinct users, of a Valid request naming that device
and key. A request alone never connects: requests sit under keys of
their own. -/
theorem connect_approved (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (e : Key)
    (ha : (allowPeer c e).eval s = true) :
    ∃ u d y, V C s.ops y (.admission c u d e) ∧ Live C s.ops c d ∧
      ((y = c ∧ u = c) ∨
        ∃ o r aps l t us, s.ops y = some o ∧ (Codec.decode o.body : Option Body) = some .admit ∧
          o.reqs = c :: r :: aps ∧ V C s.ops r (.request c u d e l t) ∧
          All2 (fun a v => V C s.ops a (.approval c r v)) aps us ∧ us.Nodup ∧ us.length = t) := by
  obtain ⟨u, d, ⟨y, hy⟩, hl⟩ := (connect_iff h hq c e).1 ha
  exact ⟨u, d, y, hy, hl, admission_approved h.key hy⟩

theorem mem_live_all (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (u : Id) (d e : Key) :
    (u, d, e) ∈ (live c (eval s (admission.all.query [c])).rows).eval s ↔
      Admitted C s.ops c u d e ∧ Live C s.ops c d := by
  rw [live_iff h hq (by simp [rels])]
  constructor
  · rintro ⟨⟨y, hv, _⟩, hl⟩; exact ⟨⟨y, hv⟩, hl⟩
  · rintro ⟨⟨y, hv⟩, hl⟩; exact ⟨⟨y, hv, all_args.2 ⟨u, d, e, rfl⟩⟩, hl⟩

/-- **Whom we dial.** At rest, `members` names exactly the live devices. -/
theorem members_iff (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (d : Key) :
    d ∈ (members c).eval s ↔ Live C s.ops c d := by
  simp only [members, View.eval_bind, View.eval_read, View.eval_pure, List.mem_map]
  constructor
  · rintro ⟨⟨u, d', e⟩, hm, rfl⟩; exact ((mem_live_all h hq c u d' e).1 hm).2
  · rintro hl
    obtain ⟨u, e, ha⟩ := hl.1
    exact ⟨(u, d, e), (mem_live_all h hq c u d e).2 ⟨ha, hl⟩, rfl⟩

/-- **Content keys go exactly where connections go.** At rest,
`recipients` names exactly the keys a live device is admitted under: the
keys `allowPeer` lets in. No outsider, no node with only cut devices,
and no live device's node left out. -/
theorem recipients_iff (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (e : Key) :
    e ∈ (recipients c).eval s ↔ ∃ u d, Admitted C s.ops c u d e ∧ Live C s.ops c d := by
  simp only [recipients, View.eval_bind, View.eval_read, View.eval_pure, List.mem_map]
  constructor
  · rintro ⟨⟨u, d, e'⟩, hm, rfl⟩; exact ⟨u, d, (mem_live_all h hq c u d e').1 hm⟩
  · rintro ⟨u, d, hm⟩; exact ⟨(u, d, e), (mem_live_all h hq c u d e).2 hm, rfl⟩

/-! ## Partitions -/

/-- **Nodes that hold the same ops agree on whom to connect to.** -/
theorem connect_agree {s t : DB Fact} (hs : Inv (family C) s) (ht : Inv (family C) t)
    (qs : s.queue = []) (qt : t.queue = []) (hops : s.ops = t.ops) (c : Id) (e : Key) :
    (allowPeer c e).eval s = (allowPeer c e).eval t := by
  have hs' := connect_iff hs qs c e
  have ht' := connect_iff ht qt c e
  rw [hops] at hs'
  cases h1 : (allowPeer c e).eval s <;> cases h2 : (allowPeer c e).eval t
  · rfl
  · rw [h1] at hs'; rw [h2] at ht'
    exact absurd (hs'.2 (ht'.1 rfl)) (by simp)
  · rw [h1] at hs'; rw [h2] at ht'
    exact absurd (ht'.2 (hs'.1 rfl)) (by simp)
  · rfl

/-- **A removal, once held, cuts off the removed user's node.** Every
device of u is cut, wherever else it is admitted; so a node key that
names only u's devices is refused. A node is let in again only through
a live device under its key (`new_device_trusted`). -/
theorem removal_cuts_off (h : Inv (family C) s) (hq : s.queue = []) {c u : Id} {e : Key}
    (hr : Removed C s.ops c u)
    (only : ∀ u' d, Admitted C s.ops c u' d e → ∃ e', Admitted C s.ops c u d e') :
    (allowPeer c e).eval s = false :=
  refuse_nonmember h hq c e fun u' d ha =>
    let ⟨e', ha'⟩ := only u' d ha
    ⟨u, e', ha', hr⟩

end Community
