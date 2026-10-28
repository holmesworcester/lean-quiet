/-
Laws of connection, dialing and sealing, about the views a node runs
(Community.Query) as lists over its persisted tables: at rest (queue
empty), `allowPeer` lets in exactly the devices admitted into users not
removed, `members` names exactly their devices and `recipients` exactly
their encryption keys. On SQLite the same views run with `listSql`,
which the query differential checks against `eval`.
-/
import Community.Laws
import Community.Query

namespace Community
open Engine

/-! ## Keys -/

theorem key_eq_iff {t t' : Nat} {c c' x x' : ByteArray} :
    key t c x = key t' c' x' ↔ t = t' ∧ c = c' ∧ x = x' := by
  constructor
  · intro h; have := Codec.encode_inj h; simp only [Prod.mk.injEq] at this; exact this
  · rintro ⟨rfl, rfl, rfl⟩; rfl

theorem encNat_small {n : Nat} (h : n < 128) : Codec.encNat n = [n.toUInt8] := by
  rw [Codec.encNat]; simp [h]

/-- A community key is never an op's own key: its first byte is its
type number, an op key's is 0xFF. -/
theorem key_ne_opKey {t : Nat} (ht : t < 128) (c x y : ByteArray) : key t c x ≠ opKey y := by
  intro h
  have := congrArg (fun b : ByteArray => b.data.toList.head?) h
  simp only [key, Codec.encode, opKey] at this
  change (Codec.encNat t ++ Codec.enc (c, x)).toArray.toList.head? = _ at this
  rw [encNat_small ht] at this
  simp at this
  have h2 := congrArg UInt8.toNat this
  simp at h2
  omega

theorem keys_admission_device {c d : ByteArray} {f : Fact} :
    key 0 c d ∈ keys f ↔ ∃ u e, f = .admission c u d e := by
  cases f <;> simp [keys, key_eq_iff, eq_comm]

theorem keys_admission_all {c : ByteArray} {f : Fact} :
    key 1 c c ∈ keys f ↔ ∃ u d e, f = .admission c u d e := by
  cases f <;> simp [keys, key_eq_iff, eq_comm]

theorem keys_removal {c u : ByteArray} {f : Fact} :
    key 2 c u ∈ keys f ↔ ∃ r, f = .removal c u r := by
  cases f <;> simp [keys, key_eq_iff, eq_comm]

/-! ## A whole list -/

theorem mem_insertBy {α} {p a : Pos × α} {l : List (Pos × α)} : a ∈ insertBy p l ↔ a = p ∨ a ∈ l := by
  induction l with
  | nil => simp [insertBy]
  | cons q t ih =>
    unfold insertBy; split
    · simp only [List.mem_cons, ih, or_left_comm]
    · simp only [List.mem_cons]

theorem mem_sortPos {α} {l : List (Pos × α)} {a : Pos × α} : a ∈ sortPos l ↔ a ∈ l := by
  induction l with
  | nil => rfl
  | cons p t ih => show a ∈ insertBy p (sortPos t) ↔ _; rw [mem_insertBy, ih]; simp

variable {s : DB Fact}

theorem mem_matching (k : ByteArray) (lim : Option Nat) {pf : Pos × Fact} :
    pf ∈ matching s { key := k, limit := lim } ↔
      ∃ x f, pf = ((sortOf f, x), f) ∧ x ∈ s.idx k ∧ s.status x = some (.valid f) := by
  unfold matching
  rw [mem_sortPos, List.mem_filterMap]
  constructor
  · rintro ⟨x, hx, h⟩
    simp only [List.all_nil, ite_true] at h
    split at h
    · rename_i f hf; cases h; exact ⟨x, f, rfl, hx, hf⟩
    · cases h
  · rintro ⟨x, f, rfl, hx, hf⟩
    exact ⟨x, hx, by simp [hf]; rfl⟩

/-- A whole, unranged list's rows are exactly its matches. -/
theorem mem_rows_all (k : ByteArray) {pf : Pos × Fact} :
    pf ∈ (eval s { key := k, limit := none }).rows ↔
      ∃ x f, pf = ((sortOf f, x), f) ∧ x ∈ s.idx k ∧ s.status x = some (.valid f) := by
  unfold eval
  simp only [ListQ.cut, ite_true, List.mem_reverse, List.mem_filter, ListQ.inside, Bool.and_self,
    and_true]
  exact mem_matching k none

theorem total_pos (k : ByteArray) :
    0 < (eval s { key := k, limit := some 0 }).total ↔
      ∃ x f, x ∈ s.idx k ∧ s.status x = some (.valid f) := by
  show 0 < (matching s _).length ↔ _
  rw [List.length_pos_iff_exists_mem]
  constructor
  · rintro ⟨pf, h⟩; obtain ⟨x, f, _, hx, hf⟩ := (mem_matching k _).1 h; exact ⟨x, f, hx, hf⟩
  · rintro ⟨x, f, hx, hf⟩; exact ⟨_, (mem_matching k _).2 ⟨x, f, rfl, hx, hf⟩⟩

variable {C : Crypto}

/-- At rest, a community key's rows are exactly the Valid facts with
that key. -/
theorem filed_iff (h : Inv (family C) s) (hq : s.queue = []) {t : Nat} (ht : t < 128)
    (c x' : ByteArray) (y : Id) (f : Fact) :
    (y ∈ s.idx (key t c x') ∧ s.status y = some (.valid f)) ↔
      V C s.ops y f ∧ key t c x' ∈ keys f := by
  constructor
  · rintro ⟨hy, hf⟩
    obtain ⟨g, hg, hk⟩ := (h.idx _ y).1 hy
    rw [hf] at hg; cases hg
    refine ⟨(status_iff_spec h hq y _).1 hf, ?_⟩
    rcases List.mem_cons.1 hk with he | hk
    · exact absurd he (key_ne_opKey ht c x' y)
    · exact hk
  · rintro ⟨hv, hk⟩
    have hf := (status_iff_spec h hq y _).2 hv
    exact ⟨(h.idx _ y).2 ⟨f, hf, List.mem_cons_of_mem _ hk⟩, hf⟩

/-! ## The views, evaluated -/

theorem removals_iff (h : Inv (family C) s) (hq : s.queue = []) (c u : Id) :
    (eval s (removals c u)).total ≠ 0 ↔ Removed C s.ops c u := by
  rw [← Nat.pos_iff_ne_zero, removals, total_pos]
  constructor
  · rintro ⟨y, f, hy, hf⟩
    obtain ⟨hv, hk⟩ := (filed_iff h hq (by decide) c u y f).1 ⟨hy, hf⟩
    obtain ⟨r, rfl⟩ := keys_removal.1 hk
    exact ⟨y, r, hv⟩
  · rintro ⟨y, r, hv⟩
    obtain ⟨hy, hf⟩ := (filed_iff h hq (by decide) c u y _).2 ⟨hv, keys_removal.2 ⟨r, rfl⟩⟩
    exact ⟨y, _, hy, hf⟩

theorem eval_live_adm {c c' : Id} {p : Pos} {u : Id} {d e : Key} {t : List (Pos × Fact)}
    (hc : c' = c) :
    (live c ((p, .admission c' u d e) :: t)).eval s =
      if (eval s (removals c u)).total = 0 then (u, d, e) :: (live c t).eval s
      else (live c t).eval s := by
  subst hc
  show View.eval s (if c' = c' then _ else _) = _
  rw [if_pos rfl]
  show View.eval s ((live c' t).bind _) = _
  rw [View.eval_bind']
  split <;> rfl

theorem mem_live (c : Id) (rows : List (Pos × Fact)) (u : Id) (d e : Key) :
    (u, d, e) ∈ (live c rows).eval s ↔
      (∃ p, (p, .admission c u d e) ∈ rows) ∧ (eval s (removals c u)).total = 0 := by
  induction rows with
  | nil => simp [live, View.eval]
  | cons pf t ih =>
    obtain ⟨p, f⟩ := pf
    have tail : (∃ q, (q, Fact.admission c u d e) ∈ (p, f) :: t) ↔
        ((p, f) = (p, .admission c u d e)) ∨ ∃ q, (q, Fact.admission c u d e) ∈ t := by
      constructor
      · rintro ⟨q, hq⟩
        rcases List.mem_cons.1 hq with hq | hq
        · simp only [Prod.mk.injEq] at hq; obtain ⟨rfl, rfl⟩ := hq; exact Or.inl rfl
        · exact Or.inr ⟨q, hq⟩
      · rintro (hq | ⟨q, hq⟩)
        · simp only [Prod.mk.injEq] at hq; rw [hq.2]; exact ⟨p, List.mem_cons_self ..⟩
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
            · simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl, rfl⟩ := he
              exact ⟨Or.inl rfl, hz⟩
            · exact ⟨Or.inr hq, hr⟩
          · rintro ⟨he | hq, hr⟩
            · simp only [Prod.mk.injEq, Fact.admission.injEq] at he
              obtain ⟨_, _, rfl, rfl, rfl⟩ := he; exact Or.inl rfl
            · exact Or.inr ⟨hq, hr⟩
        · rw [if_neg hz, ih]
          constructor
          · rintro ⟨hq, hr⟩; exact ⟨Or.inr hq, hr⟩
          · rintro ⟨he | hq, hr⟩
            · simp only [Prod.mk.injEq, Fact.admission.injEq] at he
              obtain ⟨_, _, rfl, _, _⟩ := he; exact absurd hr hz
            · exact ⟨hq, hr⟩
      · have : (live c ((p, .admission c' u' d' e') :: t)).eval s = (live c t).eval s := by
          show View.eval s (if c' = c then _ else _) = _
          rw [if_neg hc]
        rw [this, ih]
        constructor
        · rintro ⟨hq, hr⟩; exact ⟨Or.inr hq, hr⟩
        · rintro ⟨he | hq, hr⟩
          · simp only [Prod.mk.injEq, Fact.admission.injEq] at he; exact absurd he.2.1 hc
          · exact ⟨hq, hr⟩
    | _ =>
      show (u, d, e) ∈ (live c t).eval s ↔ _
      rw [ih]
      simp

/-- At rest, the live admissions of a whole list under a community key. -/
theorem live_iff (h : Inv (family C) s) (hq : s.queue = []) {t : Nat} (ht : t < 128)
    (c c0 x0 : Id) (u : Id) (d e : Key) :
    (u, d, e) ∈ (live c (eval s { key := key t c0 x0, limit := none }).rows).eval s ↔
      (∃ y, V C s.ops y (.admission c u d e) ∧ key t c0 x0 ∈ keys (.admission c u d e)) ∧
        ¬ Removed C s.ops c u := by
  rw [mem_live]
  apply and_congr
  · constructor
    · rintro ⟨p, hp⟩
      obtain ⟨y, f, he, hy, hf⟩ := (mem_rows_all _).1 hp
      simp only [Prod.mk.injEq] at he
      obtain ⟨_, rfl⟩ := he
      exact ⟨y, (filed_iff h hq ht c0 x0 y _).1 ⟨hy, hf⟩⟩
    · rintro ⟨y, hv, hk⟩
      obtain ⟨hy, hf⟩ := (filed_iff h hq ht c0 x0 y _).2 ⟨hv, hk⟩
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
  · rintro ⟨⟨u, d', e⟩, hm, rfl⟩
    obtain ⟨⟨y, hv, _⟩, hr⟩ := (live_iff h hq (by decide) c c d' u d' e).1 hm
    exact ⟨u, e, ⟨y, hv⟩, hr⟩
  · rintro ⟨u, e, ⟨y, hv⟩, hr⟩
    exact ⟨(u, d, e), (live_iff h hq (by decide) c c d u d e).2
      ⟨⟨y, hv, keys_admission_device.2 ⟨u, e, rfl⟩⟩, hr⟩, rfl⟩

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
    (hreq : o.reqs = c :: r :: aps) (hc : V C s.ops c (.admission c c d0 e0))
    (hr : V C s.ops r (.request c u d e l t))
    (hap : All2 (fun a v => V C s.ops a (.approval c r v)) aps us) (hn : us.Nodup)
    (ht : us.length = t) (hnr : ¬ Removed C s.ops c u) :
    (allowPeer c d).eval s = true :=
  (connect_iff h hq c d).2 ⟨_, e, ⟨y, admit_admits hy hb hreq hc hr hap hn ht⟩, hnr⟩

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

theorem mem_live_all (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (u : Id) (d e : Key) :
    (u, d, e) ∈ (live c (eval s { key := key 1 c c, limit := none }).rows).eval s ↔
      Admitted C s.ops c u d e ∧ ¬ Removed C s.ops c u := by
  rw [live_iff h hq (by decide)]
  constructor
  · rintro ⟨⟨y, hv, _⟩, hr⟩; exact ⟨⟨y, hv⟩, hr⟩
  · rintro ⟨⟨y, hv⟩, hr⟩; exact ⟨⟨y, hv, keys_admission_all.2 ⟨u, d, e, rfl⟩⟩, hr⟩

/-- **Whom we dial.** At rest, `members` names exactly the devices
admitted into users of c not removed. -/
theorem members_iff (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (d : Key) :
    d ∈ (members c).eval s ↔ ∃ u e, Admitted C s.ops c u d e ∧ ¬ Removed C s.ops c u := by
  simp only [members, View.eval_bind, View.eval_read, View.eval_pure, List.mem_map]
  constructor
  · rintro ⟨⟨u, d', e⟩, hm, rfl⟩; exact ⟨u, e, (mem_live_all h hq c u d' e).1 hm⟩
  · rintro ⟨u, e, hm⟩; exact ⟨(u, d, e), (mem_live_all h hq c u d e).2 hm, rfl⟩

/-- **Who a content key is sealed to.** At rest, `recipients` names
exactly the encryption keys of devices admitted into users of c not
removed: no outsider, no removed user's device, and no member left out. -/
theorem recipients_iff (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (e : Key) :
    e ∈ (recipients c).eval s ↔ ∃ u d, Admitted C s.ops c u d e ∧ ¬ Removed C s.ops c u := by
  simp only [recipients, View.eval_bind, View.eval_read, View.eval_pure, List.mem_map]
  constructor
  · rintro ⟨⟨u, d, e'⟩, hm, rfl⟩; exact ⟨u, d, (mem_live_all h hq c u d e').1 hm⟩
  · rintro ⟨u, d, hm⟩; exact ⟨(u, d, e), (mem_live_all h hq c u d e).2 hm, rfl⟩

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
