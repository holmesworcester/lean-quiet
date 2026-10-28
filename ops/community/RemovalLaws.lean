/-
The Community side of docs/REMOVAL.md: laws of the views and intents
that run, at rest (queue empty) over the persisted tables. The laws of
whom a node lets in, dials and seals to, by node key and live device
(`connect_iff`, `refuse_nonmember`, `removal_cuts_off`,
`connect_admitted`, `connect_approved`, `members_iff`,
`recipients_iff`), are in Connect.lean.

One device, two users: a device may be admitted into several users of
c. It is live (`Live`) when it is admitted and none of those users is
removed; removing any of them cuts it (`Cut`), wherever else it is
admitted. Liveness is a view's; validators are untouched.
- `cut_stays`: a cut device stays cut whatever arrives later.
- `cut_consented`: only the device's own consent ties it to a user, so
  only a removal of a user it signed into cuts it.

E3, a node's key:
- `endpoint_signed`: the binding. An admission's key was signed by its
  device: the root or request it came from carries both, signed by it.
- `endpoint_derives`: a Valid endpoint fact's key is its secret's.
- `new_device_trusted`: a removed user's device does not block a new
  device on the same node: one live device under a key is enough.
- `removals_at`: `removalsAt c e` lists exactly the removals that cut
  the devices admitted under e: the notices owed to the node at e.

E4, a removed entry is not held:
- `mine_not_removed`: `mine c` never names a cut device.
- `rejoin_fresh`: after removal, `join` writes a fresh join for the new
  seed's device, from the node's key.
- `join_new_device`: a join never asks for a device already admitted in
  the community, so never for a cut one.
- `removed_stays_removed`: whatever is written after, u stays removed,
  every device of u stays cut, and no key is let in for one.
-/
import ops.community.Intents

namespace Community
open Engine

variable {C : Crypto}

/-! ## One device, two users -/

/-- **The binding (`endpoint_signed`).** Every admission's key was
signed by its device: the admission came from a root or a request whose
body carries the device key d and the key e, and d signed that body. -/
theorem endpoint_signed {ops : Id → Option Op} {y c u : Id} {d e : Key}
    (hv : V C ops y (.admission c u d e)) :
    ∃ x o b sg, (x = y ∨ ∃ oy, ops y = some oy ∧ oy.reqs.getD 1 .empty = x) ∧ ops x = some o ∧
      (Codec.decode o.body : Option Body) = some b ∧
      (b = .root d e sg ∨ ∃ bs, b = .request d e sg bs) ∧ C.verify d (signed o b) sg = true := by
  obtain ⟨o, b, fs, hx, hb, hr, hc⟩ := valid_inv hv
  rcases check_admission hc with ⟨sg, rfl, _, _, _, hs⟩ | ⟨d0, e0, l, t, aps, rfl, rfl, _, _⟩
  · exact ⟨y, o, _, sg, Or.inl rfl, hx, hb, Or.inl rfl, hs⟩
  · obtain ⟨_, r, _, hreq, _, hrv, _⟩ := all2_cons2 hr
    obtain ⟨or, br, fsr, hor, hbr, _, hvr⟩ := valid_inv hrv
    obtain ⟨cs, bs, _, _, _, _, rfl, _, _, _, hcs, _⟩ := check_request hvr
    exact ⟨r, or, _, cs, Or.inr ⟨o, hx, by rw [hreq]; rfl⟩, hor, hbr, Or.inr ⟨bs, rfl⟩, hcs⟩

/-- **Cut stays cut (`cut_stays`).** More ops never make a cut device
live again: no later admission, of any id into any user, undoes it. -/
theorem cut_stays {ops ops' : Id → Option Op} {c : Id} {d : Key} (he : Extends ops ops')
    (h : Cut C ops c d) : Cut C ops' c d ∧ ¬ Live C ops' c d := by
  obtain ⟨u, e, ⟨y, hy⟩, hr⟩ := h
  have hc : Cut C ops' c d := ⟨u, e, ⟨y, valid_stays he hy⟩, removed_stays he hr⟩
  exact ⟨hc, cut_not_live hc⟩

/-- **Only a device's own consent cuts it (`cut_consented`).** A cut
device signed the root or request that admitted it into the removed
user: nobody else can tie it to a user, so nobody else can cut it. -/
theorem cut_consented {ops : Id → Option Op} {c : Id} {d : Key} (h : Cut C ops c d) :
    ∃ u e y x o b sg, V C ops y (.admission c u d e) ∧ Removed C ops c u ∧
      (x = y ∨ ∃ oy, ops y = some oy ∧ oy.reqs.getD 1 .empty = x) ∧ ops x = some o ∧
      (Codec.decode o.body : Option Body) = some b ∧
      (b = .root d e sg ∨ ∃ bs, b = .request d e sg bs) ∧ C.verify d (signed o b) sg = true := by
  obtain ⟨u, e, ⟨y, hy⟩, hr⟩ := h
  obtain ⟨x, o, b, sg, hx, ho, hb, hbody, hs⟩ := endpoint_signed hy
  exact ⟨u, e, y, x, o, b, sg, hy, hr, hx, ho, hb, hbody, hs⟩

/-! ## E3: a node's key -/

theorem check_endpoint {o : Op} {b : Body} {fs : List Fact} {pk sk : ByteArray}
    (h : check C o b fs = some (.endpoint pk sk)) : pk = cryptoSeal.pub sk ∧ sk.size = 32 := by
  unfold check at h
  split at h <;> (try split at h) <;> (try simp at h; done)
  simp only [Option.some.injEq, Fact.endpoint.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rename_i hc
  exact ⟨rfl, hc⟩

/-- **A node's key is its secret's (`endpoint_derives`).** -/
theorem endpoint_derives {ops : Id → Option Op} {x : Id} {pk sk : ByteArray}
    (h : V C ops x (.endpoint pk sk)) : pk = cryptoSeal.pub sk ∧ sk.size = 32 := by
  obtain ⟨o, b, fs, _, _, _, hc⟩ := valid_inv h
  exact check_endpoint hc

section
variable {s : DB Fact}

/-- **A new device on a removed user's node is let in
(`new_device_trusted`).** A node whose key names a removed user's device
is let in once a live device is admitted under the same key: the cut
device does not block the node. -/
theorem new_device_trusted (h : Inv (family C) s) (hq : s.queue = []) {c u u2 : Id} {d d2 e : Key}
    (_ha : Admitted C s.ops c u d e) (_hr : Removed C s.ops c u)
    (ha2 : Admitted C s.ops c u2 d2 e) (hl : Live C s.ops c d2) : (allowPeer c e).eval s = true :=
  (connect_iff h hq c e).2 ⟨u2, d2, ha2, hl⟩

/-- At rest, a row of a community relation's list, read whole, is
exactly a Valid fact filed in it, at its own id. -/
theorem mem_rows (h : Inv (family C) s) (hq : s.queue = []) {r : Rel Fact} (hr : r ∈ rels)
    (as : List ByteArray) {pf : Pos × Fact} :
    pf ∈ (Engine.eval s (r.query as)).rows ↔
      ∃ y f, pf = ((SortKey.sortOf f, y), f) ∧ V C s.ops y f ∧ r.args f = some as :=
  mem_rows_rel (fam := family C) rfl rels_distinct hr (rels_short r hr) h hq as

/-- At rest, the ids of a user's removals list are its Valid removals. -/
theorem byUser_ids (h : Inv (family C) s) (hq : s.queue = []) (c u x : Id) :
    x ∈ (Engine.eval s (removal.byUser.query [c, u])).rows.map (·.1.2) ↔
      ∃ by_, V C s.ops x (.removal c u by_) := by
  simp only [List.mem_map]
  constructor
  · rintro ⟨pf, hm, rfl⟩
    obtain ⟨y, f, rfl, hv, hk⟩ := (mem_rows h hq (by simp [rels]) _).1 hm
    obtain ⟨r, rfl⟩ := byUser_args.1 hk
    exact ⟨r, hv⟩
  · rintro ⟨r, hv⟩
    exact ⟨_, (mem_rows h hq (by simp [rels]) _).2 ⟨x, _, rfl, hv, byUser_args.2 ⟨r, rfl⟩⟩, rfl⟩

theorem mem_removalsOf (h : Inv (family C) s) (hq : s.queue = []) (c x : Id) (rows : List (Pos × Fact)) :
    x ∈ (removalsOf c rows).eval s ↔
      ∃ p c' u d e by_, (p, .admission c' u d e) ∈ rows ∧ V C s.ops x (.removal c u by_) := by
  induction rows with
  | nil => simp [removalsOf, View.eval]
  | cons pf t ih =>
    obtain ⟨p, f⟩ := pf
    cases f with
    | admission c' u d e =>
      show x ∈ View.eval s ((removalsOf c t).bind _) ↔ _
      rw [View.eval_bind']
      simp only [View.eval, List.mem_append, ih, byUser_ids h hq, List.mem_cons, Prod.mk.injEq]
      constructor
      · rintro (⟨r, hv⟩ | ⟨p', c'', u', d', e', r, hm, hv⟩)
        · exact ⟨p, c', u, d, e, r, Or.inl ⟨rfl, rfl⟩, hv⟩
        · exact ⟨p', c'', u', d', e', r, Or.inr hm, hv⟩
      · rintro ⟨p', c'', u', d', e', r, ⟨_, he⟩ | hm, hv⟩
        · simp only [Fact.admission.injEq] at he
          obtain ⟨_, rfl, _, _⟩ := he
          exact Or.inl ⟨r, hv⟩
        · exact Or.inr ⟨p', c'', u', d', e', r, hm, hv⟩
    | _ =>
      show x ∈ (removalsOf c t).eval s ↔ _
      rw [ih]
      constructor
      · rintro ⟨p', c'', u', d', e', r, hm, hv⟩; exact ⟨p', c'', u', d', e', r, List.mem_cons_of_mem _ hm, hv⟩
      · rintro ⟨p', c'', u', d', e', r, hm, hv⟩
        rcases List.mem_cons.1 hm with he | hm
        · simp at he
        · exact ⟨p', c'', u', d', e', r, hm, hv⟩

theorem mem_deviceRemovals (h : Inv (family C) s) (hq : s.queue = []) (c x : Id) (rows : List (Pos × Fact)) :
    x ∈ (deviceRemovals c rows).eval s ↔
      ∃ p c' u0 d e, (p, .admission c' u0 d e) ∈ rows ∧
        ∃ u e' by_, Admitted C s.ops c u d e' ∧ V C s.ops x (.removal c u by_) := by
  have hdev : ∀ d, x ∈ (removalsOf c (Engine.eval s (admission.byDevice.query [c, d])).rows).eval s ↔
      ∃ u e' by_, Admitted C s.ops c u d e' ∧ V C s.ops x (.removal c u by_) := by
    intro d
    rw [mem_removalsOf h hq]
    constructor
    · rintro ⟨p, c', u, d', e', r, hm, hv⟩
      obtain ⟨y, f, he, hy, hk⟩ := (mem_rows h hq (by simp [rels]) _).1 hm
      simp only [Prod.mk.injEq] at he; obtain ⟨_, rfl⟩ := he
      obtain ⟨u'', e'', hf⟩ := byDevice_args.1 hk
      simp only [Fact.admission.injEq] at hf; obtain ⟨rfl, rfl, rfl, rfl⟩ := hf
      exact ⟨u, e', r, ⟨y, hy⟩, hv⟩
    · rintro ⟨u, e', r, ⟨y, hy⟩, hv⟩
      exact ⟨_, c, u, d, e', r, (mem_rows h hq (by simp [rels]) _).2
        ⟨y, _, rfl, hy, byDevice_args.2 ⟨u, e', rfl⟩⟩, hv⟩
  induction rows with
  | nil => simp [deviceRemovals, View.eval]
  | cons pf t ih =>
    obtain ⟨p, f⟩ := pf
    cases f with
    | admission c' u0 d e =>
      show x ∈ View.eval s ((removalsOf c _).bind _) ↔ _
      rw [View.eval_bind', View.eval_bind']
      simp only [View.eval, List.mem_append, ih, hdev, List.mem_cons, Prod.mk.injEq]
      constructor
      · rintro (hm | ⟨p', c'', u0', d', e', hm, rest⟩)
        · exact ⟨p, c', u0, d, e, Or.inl ⟨rfl, rfl⟩, hm⟩
        · exact ⟨p', c'', u0', d', e', Or.inr hm, rest⟩
      · rintro ⟨p', c'', u0', d', e', ⟨_, he⟩ | hm, rest⟩
        · simp only [Fact.admission.injEq] at he
          obtain ⟨_, _, rfl, _⟩ := he
          exact Or.inl rest
        · exact Or.inr ⟨p', c'', u0', d', e', hm, rest⟩
    | _ =>
      show x ∈ (deviceRemovals c t).eval s ↔ _
      refine ih.trans ⟨?_, ?_⟩
      · rintro ⟨p', c'', u0', d', e', hm, rest⟩
        exact ⟨p', c'', u0', d', e', List.mem_cons_of_mem _ hm, rest⟩
      · rintro ⟨p', c'', u0', d', e', hm, rest⟩
        rcases List.mem_cons.1 hm with he | hm
        · simp at he
        · exact ⟨p', c'', u0', d', e', hm, rest⟩

/-- **The notices owed to a node (`removals_at`).** At rest,
`removalsAt c e` lists exactly the Valid removals that cut a device
admitted under e: removals of any user such a device is admitted into,
under any key. -/
theorem removals_at (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (e : Key) (x : Id) :
    x ∈ (removalsAt c e).eval s ↔
      ∃ u0 d u e' by_, Admitted C s.ops c u0 d e ∧ Admitted C s.ops c u d e' ∧
        V C s.ops x (.removal c u by_) := by
  unfold removalsAt
  rw [View.eval_bind]
  simp only [Rel.read, View.eval_read]
  rw [mem_deviceRemovals h hq]
  constructor
  · rintro ⟨p, c', u0, d, e'', hm, u, e', r, ha, hv⟩
    obtain ⟨y, f, he, hy, hk⟩ := (mem_rows h hq (by simp [rels]) _).1 hm
    simp only [Prod.mk.injEq] at he; obtain ⟨_, rfl⟩ := he
    obtain ⟨u'', d'', hf⟩ := byKey_args.1 hk
    simp only [Fact.admission.injEq] at hf; obtain ⟨rfl, rfl, rfl, rfl⟩ := hf
    exact ⟨u0, d, u, e', r, ⟨y, hy⟩, ha, hv⟩
  · rintro ⟨u0, d, u, e', r, ⟨y, hy⟩, ha, hv⟩
    exact ⟨_, c, u0, d, e, (mem_rows h hq (by simp [rels]) _).2
      ⟨y, _, rfl, hy, byKey_args.2 ⟨u0, d, rfl⟩⟩, u, e', r, ha, hv⟩

/-! ## E4: a removed entry is not held -/

theorem eval_list {α : Type} (q : ListQ) (k : Answer Fact → View Fact α) :
    (View.list q k).eval s = (k (Engine.eval s q)).eval s := rfl

theorem deviceLive_eval (c : Id) (d : Key) : (deviceLive c d).eval s =
    if (Engine.eval s (admission.byDevice.query [c, d])).rows.isEmpty then false
    else (unremoved c (Engine.eval s (admission.byDevice.query [c, d])).rows).eval s := by
  unfold deviceLive
  rw [View.eval_bind]
  by_cases he : (Engine.eval s (admission.byDevice.query [c, d])).rows.isEmpty = true
  · simp only [Rel.read, View.eval_read, he, ite_true]; rfl
  · simp only [Rel.read, View.eval_read, he, ite_false, Bool.false_eq_true]

/-- With no rows of d's admissions, d is admitted nowhere in c. -/
theorem not_admitted_of_empty (h : Inv (family C) s) (hq : s.queue = []) {c : Id} {d : Key}
    (he : (Engine.eval s (admission.byDevice.query [c, d])).rows.isEmpty = true) :
    ∀ u e, ¬ Admitted C s.ops c u d e := by
  rintro u e ⟨y, hy⟩
  obtain ⟨p, hp⟩ := (exists_row h hq (by simp [rels]) [c, d] _).2 ⟨y, hy, byDevice_args.2 ⟨u, e, rfl⟩⟩
  rw [List.isEmpty_iff] at he; rw [he] at hp; cases hp

/-- At rest, d's admissions counted are nonzero exactly when d is admitted. -/
theorem admitted_total (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (d : Key) :
    (Engine.eval s (admission.byDevice.query [c, d] (limit := some 0))).total ≠ 0 ↔
      ∃ u e, Admitted C s.ops c u d e := by
  rw [← Nat.pos_iff_ne_zero,
    total_rel (fam := family C) rfl rels_distinct (by simp [rels]) (rels_short _ (by simp [rels])) h hq]
  constructor
  · rintro ⟨y, f, hv, hk⟩
    obtain ⟨u, e, rfl⟩ := byDevice_args.1 hk
    exact ⟨u, e, y, hv⟩
  · rintro ⟨u, e, y, hv⟩
    exact ⟨y, _, hv, byDevice_args.2 ⟨u, e, rfl⟩⟩

theorem standing_eval (c : Id) (d : Key) (joins : List (Pos × Fact)) :
    (standing c d joins).eval s =
      if (Engine.eval s (secret.byKey.query [d] (limit := some 0))).total = 0 then none
      else if (Engine.eval s (admission.byDevice.query [c, d])).rows.isEmpty then
        (if (waiting c d joins).eval s then some false else none)
      else if (deviceLive c d).eval s then some true else none := by
  rw [deviceLive_eval]
  unfold standing
  rw [eval_list]
  by_cases h0 : (Engine.eval s (secret.byKey.query [d] (limit := some 0))).total = 0
  · simp only [h0, ite_true]; rfl
  · simp only [h0, ite_false]
    rw [eval_list]
    by_cases he : (Engine.eval s (admission.byDevice.query [c, d])).rows.isEmpty = true
    · simp only [he, ite_true]; rw [View.eval_bind']; rfl
    · simp only [he, ite_false, Bool.false_eq_true]; rw [View.eval_bind']; rfl

/-- What a held acceptance's standing says of its device: admitted and
live, or not admitted at all. -/
theorem standing_some (h : Inv (family C) s) (hq : s.queue = []) {c : Id} {d : Key}
    {joins : List (Pos × Fact)} {adm : Bool} (hs : (standing c d joins).eval s = some adm) :
    Live C s.ops c d ∨ ∀ u e, ¬ Admitted C s.ops c u d e := by
  rw [standing_eval] at hs
  split at hs
  · cases hs
  · split at hs
    · rename_i he; exact Or.inr (not_admitted_of_empty h hq he)
    · split at hs
      · rename_i hl; exact Or.inl ((deviceLive_iff h hq c d).1 hl)
      · cases hs

/-- A cut device's acceptance is not held. -/
theorem standing_cut (h : Inv (family C) s) (hq : s.queue = []) {c : Id} {d : Key}
    (joins : List (Pos × Fact)) (hc : Cut C s.ops c d) : (standing c d joins).eval s = none := by
  rw [standing_eval]
  split
  · rfl
  · have ⟨u, e, ha, _⟩ := hc
    have hne : (Engine.eval s (admission.byDevice.query [c, d])).rows.isEmpty = false := by
      cases he : (Engine.eval s (admission.byDevice.query [c, d])).rows.isEmpty
      · rfl
      · exact absurd ha (not_admitted_of_empty h hq he u e)
    rw [if_neg (by simp [hne])]
    have hl : (deviceLive c d).eval s = false := by
      cases hd : (deviceLive c d).eval s
      · rfl
      · exact absurd ((deviceLive_iff h hq c d).1 hd) (cut_not_live hc)
    rw [hl]; rfl

theorem better_cases (a b : Key × Id × Bool) : better a b = a ∨ better a b = b := by
  unfold better; split <;> simp

theorem pick_some {c : Id} {joins : List (Pos × Fact)} :
    ∀ {rows : List (Pos × Fact)} {d : Key} {a : Id} {adm : Bool},
      (pick c joins rows).eval s = some (d, a, adm) →
      ∃ k, ((k, a), Fact.accepted c d) ∈ rows ∧ (standing c d joins).eval s = some adm
  | [], _, _, _, hp => by cases hp
  | ((k, aid), f) :: t, d, a, adm, hp => by
    cases f with
    | accepted c' d' =>
      by_cases hc : c' = c
      · subst hc
        have hp' : (match (standing c' d' joins).eval s, (pick c' joins t).eval s with
            | some adm', some b => some (better (d', aid, adm') b)
            | some adm', none => some (d', aid, adm')
            | none, r => r) = some (d, a, adm) := by
          have := hp
          simp only [pick, ite_true] at this
          rw [View.eval_bind', View.eval_bind'] at this
          exact this
        have tail : ∀ {d a adm}, (pick c' joins t).eval s = some (d, a, adm) →
            ∃ k', ((k', a), Fact.accepted c' d) ∈ ((k, aid), Fact.accepted c' d') :: t ∧
              (standing c' d joins).eval s = some adm := by
          intro d a adm ht
          obtain ⟨k', hm, hs⟩ := pick_some ht
          exact ⟨k', List.mem_cons_of_mem _ hm, hs⟩
        cases hst : (standing c' d' joins).eval s with
        | none => rw [hst] at hp'; exact tail hp'
        | some adm' =>
          cases hr : (pick c' joins t).eval s with
          | none =>
            rw [hst, hr] at hp'
            simp only [Option.some.injEq, Prod.mk.injEq] at hp'
            obtain ⟨rfl, rfl, rfl⟩ := hp'
            exact ⟨k, List.mem_cons_self .., hst⟩
          | some b =>
            rw [hst, hr] at hp'
            simp only [Option.some.injEq] at hp'
            rcases better_cases (d', aid, adm') b with hb | hb
            · rw [hb] at hp'
              simp only [Prod.mk.injEq] at hp'
              obtain ⟨rfl, rfl, rfl⟩ := hp'
              exact ⟨k, List.mem_cons_self .., hst⟩
            · rw [hb] at hp'; subst hp'; exact tail hr
      · have : (pick c joins (((k, aid), Fact.accepted c' d') :: t)).eval s = (pick c joins t).eval s := by
          simp only [pick, if_neg hc]
        rw [this] at hp
        obtain ⟨k', hm, hs⟩ := pick_some hp
        exact ⟨k', List.mem_cons_of_mem _ hm, hs⟩
    | _ =>
      obtain ⟨k', hm, hs⟩ := pick_some (rows := t) hp
      exact ⟨k', List.mem_cons_of_mem _ hm, hs⟩

theorem pick_none {c : Id} {joins : List (Pos × Fact)} :
    ∀ {rows : List (Pos × Fact)},
      (∀ k a d, ((k, a), Fact.accepted c d) ∈ rows → (standing c d joins).eval s = none) →
      (pick c joins rows).eval s = none
  | [], _ => rfl
  | ((k, aid), f) :: t, hall => by
    have ht := pick_none (rows := t) fun k a d hm => hall k a d (List.mem_cons_of_mem _ hm)
    cases f with
    | accepted c' d' =>
      by_cases hc : c' = c
      · subst hc
        simp only [pick, ite_true]
        rw [View.eval_bind', View.eval_bind', hall k aid d' (List.mem_cons_self ..), ht]
        rfl
      · simp only [pick, if_neg hc]; exact ht
    | _ => exact ht

/-- **A removed entry is not held (`mine_not_removed`).** At rest, the
device `mine c` names is live, or not admitted at all (a join still
waiting): never a cut device. -/
theorem mine_not_removed (h : Inv (family C) s) (hq : s.queue = []) {c : Id} {d : Key} {a : Id}
    (hm : (mine c).eval s = some (d, a)) : Live C s.ops c d ∨ ∀ u e, ¬ Admitted C s.ops c u d e := by
  have hm' : ((pick c (Engine.eval s (joining.all.query [])).rows
      (Engine.eval s (accepted.all.query [])).rows).eval s).map (fun (d, a, _) => (d, a)) =
      some (d, a) := by
    have := hm
    unfold mine at this
    rw [show ∀ q (k : Answer Fact → View Fact _), View.eval s (.list q k) = View.eval s (k (Engine.eval s q))
      from fun _ _ => rfl, show ∀ q (k : Answer Fact → View Fact _), View.eval s (.list q k) =
      View.eval s (k (Engine.eval s q)) from fun _ _ => rfl, View.eval_bind'] at this
    exact this
  obtain ⟨⟨d', a', adm⟩, hp, he⟩ := Option.map_eq_some_iff.1 hm'
  simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
  obtain ⟨_, _, hs⟩ := pick_some hp
  exact standing_some h hq hs

theorem dormant_none {c : Id} :
    ∀ {rows : List (Pos × Fact)},
      (∀ p k hs r nm d n, (p, Fact.joining c k hs r nm d n) ∈ rows →
        (Engine.eval s (admission.byDevice.query [c, d] (limit := some 0))).total ≠ 0) →
      (dormant c rows).eval s = none
  | [], _ => rfl
  | (p, f) :: t, hall => by
    have ht := dormant_none (rows := t) fun p k hs r nm d n hm =>
      hall p k hs r nm d n (List.mem_cons_of_mem _ hm)
    cases f with
    | joining c' k hs r nm d n =>
      by_cases hc : c' = c
      · subst hc
        show View.eval s (if c' = c' then _ else _) = none
        rw [if_pos rfl]
        show View.eval s ((dormant c' t).bind _) = none
        rw [View.eval_bind', ht]
        show (if _ ≠ 0 then none else _) = none
        rw [if_pos (hall p k hs r nm d n (List.mem_cons_self ..))]
      · show View.eval s (if c' = c then _ else _) = none
        rw [if_neg hc]; exact ht
    | _ => exact ht

theorem nodeKeyOr_held {fresh key sk : ByteArray} (hk : nodeKey.eval s = some (key, sk)) :
    (nodeKeyOr fresh).eval s = (key, []) := by
  unfold nodeKeyOr
  rw [View.eval_bind', hk]; rfl

/-- **Rejoining is a fresh join (`rejoin_fresh`).** At rest, on a node
holding its key, if every acceptance of the link's community held here
is of a cut device, every join of it here is of an admitted device (so
none is waiting), and the new seed's device is not admitted, `join`
writes a fresh join: the new seed's secret, its request from this
node's key, acceptance and pending join. The request is for the new
seed's device, never the cut one (`joinOps_travels`). -/
theorem rejoin_fresh (h : Inv (family C) s) (hq : s.queue = []) {i : Invite}
    {seed name fresh key sk : ByteArray} (hk : nodeKey.eval s = some (key, sk))
    (hacc : ∀ x d, V C s.ops x (.accepted i.community d) → Cut C s.ops i.community d)
    (hjoin : ∀ x k hs r nm d n, V C s.ops x (.joining i.community k hs r nm d n) →
      ∃ u e, Admitted C s.ops i.community u d e)
    (hnew : ∀ u e, ¬ Admitted C s.ops i.community u (Device.ofSeed seed).pk e) :
    ((join i seed name fresh).eval s).ops = (joinOps i seed name key).ops := by
  have hmine : (mine i.community).eval s = none := by
    show ((pick i.community _ _).bind _).eval s = none
    rw [View.eval_bind', pick_none]
    · rfl
    · intro k a d hm
      obtain ⟨y, f, he, hv, _⟩ := (mem_rows h hq (by simp [rels]) _).1 hm
      simp only [Prod.mk.injEq] at he; obtain ⟨⟨_, _⟩, rfl⟩ := he
      exact standing_cut h hq _ (hacc _ d hv)
  have hdorm : (dormant i.community (Engine.eval s (joining.all.query [])).rows).eval s = none :=
    dormant_none fun p k hs r nm d n hm => by
      obtain ⟨y, f, he, hv, _⟩ := (mem_rows h hq (by simp [rels]) _).1 hm
      simp only [Prod.mk.injEq] at he; obtain ⟨_, rfl⟩ := he
      exact (admitted_total h hq _ d).2 (hjoin y k hs r nm d n hv)
  have hz : (Engine.eval s (admission.byDevice.query [i.community, (Device.ofSeed seed).pk]
      (limit := some 0))).total = 0 :=
    Decidable.of_not_not fun hne => by
      obtain ⟨u, e, ha⟩ := (admitted_total h hq _ _).1 hne
      exact hnew u e ha
  unfold join
  rw [View.eval_bind', hmine]
  simp only [Option.isSome_none, Bool.false_eq_true, ite_false]
  rw [eval_list, View.eval_bind', hdorm, eval_list]
  simp only [hz, ne_eq, not_true_eq_false, ite_false]
  rw [View.eval_bind', nodeKeyOr_held hk]
  rfl

theorem body_endpoint (sk : ByteArray) : (Codec.decode (endpoint sk).body : Option Body) = some (.endpoint sk) :=
  body_mkOp _ _

/-- **A join never asks for an admitted device (`join_new_device`).** At
rest, every request `join` writes is for a device with no admission in
the link's community: never a cut device, whatever seed is passed. -/
theorem join_new_device (h : Inv (family C) s) (hq : s.queue = []) {i : Invite}
    {seed name fresh : ByteArray} {o : Op} {d e cs bs : ByteArray}
    (ho : o ∈ ((join i seed name fresh).eval s).ops)
    (hb : (Codec.decode o.body : Option Body) = some (.request d e cs bs)) :
    ∀ u e', ¬ Admitted C s.ops i.community u d e' := by
  unfold join at ho
  rw [View.eval_bind'] at ho
  split at ho
  · cases ho
  · rw [eval_list, View.eval_bind'] at ho
    split at ho
    · simp only [View.eval, List.mem_singleton] at ho
      subst ho; rw [body_mkOp] at hb; cases hb
    · rw [eval_list] at ho
      split at ho
      · cases ho
      · rename_i hz
        rw [View.eval_bind'] at ho
        simp only [View.eval, List.mem_append] at ho
        rcases ho with ho | ho
        · -- the node's key, if it had none: not a request
          unfold nodeKeyOr at ho
          rw [View.eval_bind'] at ho
          split at ho
          · cases ho
          · simp only [View.eval, List.mem_singleton] at ho
            subst ho; rw [body_endpoint] at hb; cases hb
        · simp only [joinOps, Invite.request, Community.request, secret, accept, joining,
            List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ho
          rcases ho with rfl | rfl | rfl | rfl
          · rw [body_mkOp] at hb; cases hb
          · rw [body_mkOp] at hb
            simp only [Option.some.injEq, Body.request.injEq] at hb
            obtain ⟨rfl, _, _, _⟩ := hb
            intro u e' ha
            exact hz ((admitted_total h hq _ _).2 ⟨u, e', ha⟩)
          · rw [body_mkOp] at hb; cases hb
          · rw [body_mkOp] at hb; cases hb

end

/-- **Removed stays removed (`removed_stays_removed`).** Whatever is
written after, the rejoining node's new device and its admission
included: u stays removed, every device ever admitted into u is cut, and
every key `allowPeer` lets in is let in for a live device that was never
u's. -/
theorem removed_stays_removed {s s' : DB Fact} (h' : Inv (family C) s') (hq' : s'.queue = [])
    {c u : Id} (he : Extends s.ops s'.ops) (hr : Removed C s.ops c u) :
    Removed C s'.ops c u ∧
      (∀ d e, Admitted C s'.ops c u d e → Cut C s'.ops c d ∧ ¬ Live C s'.ops c d) ∧
      ∀ e, (allowPeer c e).eval s' = true →
        ∃ u' d, Admitted C s'.ops c u' d e ∧ Live C s'.ops c d ∧ ∀ e', ¬ Admitted C s'.ops c u d e' := by
  have hr' := removed_stays he hr
  refine ⟨hr', fun d e ha => ⟨⟨u, e, ha, hr'⟩, cut_not_live ⟨u, e, ha, hr'⟩⟩, fun e hp => ?_⟩
  obtain ⟨u', d, ha, hl⟩ := (connect_iff h' hq' c e).1 hp
  exact ⟨u', d, ha, hl, fun e' hu => hl.2 u e' hu hr'⟩

end Community
