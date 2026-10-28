/-
Laws of connection and sealing, about the queries as the engine runs
them on its persisted tables: at rest (queue empty), `allowPeer` lets
in exactly the devices admitted into users not removed, and
`recipients` names exactly their encryption keys.
-/
import Community.Laws
import Community.Query

namespace Community
open Engine

variable {C : Crypto} {s : DB Fact}

theorem mem_validOfP (l : List Id) (f : Fact) :
    f ∈ validOfP s l ↔ ∃ x ∈ l, s.status x = some (.valid f) := by
  unfold validOfP
  simp only [List.mem_filterMap]
  constructor
  · rintro ⟨x, hx, hf⟩
    refine ⟨x, hx, ?_⟩
    split at hf
    · rename_i g hg; cases hf; exact hg
    · cases hf
  · rintro ⟨x, hx, hf⟩
    exact ⟨x, hx, by rw [hf]⟩

/-- At rest, the facts under a key are exactly the Valid facts with
that key. -/
theorem validOfP_key (h : Inv (family C) s) (hq : s.queue = []) (k : ByteArray) (f : Fact) :
    f ∈ validOfP s (s.idx k) ↔ ∃ x, V C s.ops x f ∧ k ∈ keys f := by
  rw [mem_validOfP]
  constructor
  · rintro ⟨x, hx, hf⟩
    obtain ⟨g, hg, hk⟩ := (h.idx k x).1 hx
    rw [hf] at hg; cases hg
    exact ⟨x, (status_iff_spec h hq x _).1 hf, hk⟩
  · rintro ⟨x, hv, hk⟩
    have hf := (status_iff_spec h hq x _).2 hv
    exact ⟨x, (h.idx k x).2 ⟨f, hf, hk⟩, hf⟩

theorem removedP_iff (h : Inv (family C) s) (hq : s.queue = []) (c u : Id) :
    removedP s c u = true ↔ Removed C s.ops c u := by
  unfold removedP
  rw [List.any_eq_true]
  constructor
  · rintro ⟨f, hf, hr⟩
    obtain ⟨x, hv, _⟩ := (validOfP_key h hq _ f).1 hf
    cases f with
    | removal c' u' r =>
      simp [isRemovalOf] at hr; obtain ⟨rfl, rfl⟩ := hr; exact ⟨x, r, hv⟩
    | _ => simp [isRemovalOf] at hr
  · rintro ⟨x, r, hv⟩
    exact ⟨_, (validOfP_key h hq _ _).2 ⟨x, hv, by simp [keys]⟩, by simp [isRemovalOf]⟩

theorem allowP_iff (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (d : Key) :
    allowP s c d = true ↔ ∃ u e, Admitted C s.ops c u d e ∧ ¬ Removed C s.ops c u := by
  unfold allowP
  rw [List.any_eq_true]
  constructor
  · rintro ⟨f, hf, hl⟩
    obtain ⟨x, hv, _⟩ := (validOfP_key h hq _ f).1 hf
    cases f with
    | admission c' u d' e =>
      simp only [liveP, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hl
      obtain ⟨⟨rfl, rfl⟩, hr⟩ := hl
      refine ⟨u, e, ⟨x, hv⟩, fun hR => ?_⟩
      rw [(removedP_iff h hq _ _).2 hR] at hr; cases hr
    | _ => simp [liveP] at hl
  · rintro ⟨u, e, ⟨x, hv⟩, hR⟩
    refine ⟨_, (validOfP_key h hq _ _).2 ⟨x, hv, by simp [keys]⟩, ?_⟩
    simp only [liveP, and_self, decide_true, Bool.true_and, Bool.not_eq_true']
    cases hr : removedP s c u
    · rfl
    · exact absurd ((removedP_iff h hq _ _).1 hr) hR

theorem recipientsP_iff (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (e : Key) :
    e ∈ recipientsP s c ↔ ∃ u d, Admitted C s.ops c u d e ∧ ¬ Removed C s.ops c u := by
  unfold recipientsP
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨f, hf, hk⟩
    obtain ⟨x, hv, _⟩ := (validOfP_key h hq _ f).1 hf
    cases f with
    | admission c' u d e' =>
      simp only [keyOfP] at hk
      split at hk
      · rename_i hc
        obtain ⟨rfl, hr⟩ := hc
        cases hk
        refine ⟨u, d, ⟨x, hv⟩, fun hR => ?_⟩
        rw [(removedP_iff h hq _ _).2 hR] at hr; cases hr
      · cases hk
    | _ => simp [keyOfP] at hk
  · rintro ⟨u, d, ⟨x, hv⟩, hR⟩
    refine ⟨_, (validOfP_key h hq _ _).2 ⟨x, hv, by simp [keys]⟩, ?_⟩
    have : removedP s c u = false := by
      cases hr : removedP s c u
      · rfl
      · exact absurd ((removedP_iff h hq _ _).1 hr) hR
    simp [keyOfP, this]

/-! ## The laws, about the running queries -/

/-- **Who we connect to.** At rest, the engine's own `allowPeer`, run on
its persisted tables, accepts device d for community c exactly when d is
admitted into a user of c that has not been removed. -/
theorem connect_iff (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (d : Key) :
    ((allowPeer c d : Model Fact Bool).run s).1 = true ↔
      ∃ u e, Admitted C s.ops c u d e ∧ ¬ Removed C s.ops c u := by
  rw [run_allowPeer]; exact allowP_iff h hq c d

/-- **No connection to non-members or removed members.** -/
theorem refuse_nonmember (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (d : Key)
    (hd : ∀ u e, Admitted C s.ops c u d e → Removed C s.ops c u) :
    ((allowPeer c d : Model Fact Bool).run s).1 = false := by
  cases hb : ((allowPeer c d : Model Fact Bool).run s).1
  · rfl
  · obtain ⟨u, e, ha, hr⟩ := (connect_iff h hq c d).1 hb; exact absurd (hd u e ha) hr

/-- **Approved devices are let in.** A device whose request is tallied
by an admit op with its invitation's threshold of approvals by distinct
users is accepted (into the issuer's user for a link, into the user its
request names for a member invitation), unless that user has been
removed. -/
theorem connect_admitted (h : Inv (family C) s) (hq : s.queue = []) {y c r : Id} {o : Op}
    {aps us : List Id} {d0 e0 : Key} {u : Id} {d e : Key} {l : Bool} {t : Nat}
    (hy : s.ops y = some o) (hb : (Codec.decode o.body : Option Body) = some .admit)
    (hreq : o.reqs = c :: r :: aps) (hc : V C s.ops c (.admission c c d0 e0))
    (hr : V C s.ops r (.request c u d e l t))
    (hap : All2 (fun a v => V C s.ops a (.approval c r v)) aps us) (hn : us.Nodup)
    (ht : us.length = t) (hnr : ¬ Removed C s.ops c u) :
    ((allowPeer c d : Model Fact Bool).run s).1 = true :=
  (connect_iff h hq c d).2 ⟨_, e, ⟨y, admit_admits hy hb hreq hc hr hap hn ht⟩, hnr⟩

/-- **Only the founder and approved devices are let in.** At rest, a
device `allowPeer` accepts is admitted into a user not removed, by the
root (the founder) or by an admit op tallying exactly the threshold of
approvals, by distinct users, of a Valid request for that device. A
request alone never connects: requests sit under keys of their own. -/
theorem connect_approved (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (d : Key)
    (ha : ((allowPeer c d : Model Fact Bool).run s).1 = true) :
    ∃ u e y, V C s.ops y (.admission c u d e) ∧ ¬ Removed C s.ops c u ∧
      ((y = c ∧ u = c) ∨
        ∃ o r aps l t us, s.ops y = some o ∧ (Codec.decode o.body : Option Body) = some .admit ∧
          o.reqs = c :: r :: aps ∧ V C s.ops r (.request c u d e l t) ∧
          All2 (fun a v => V C s.ops a (.approval c r v)) aps us ∧ us.Nodup ∧ us.length = t) := by
  obtain ⟨u, e, ⟨y, hy⟩, hnr⟩ := (connect_iff h hq c d).1 ha
  exact ⟨u, e, y, hy, hnr, admission_approved h.key hy⟩

/-- **Who a content key is sealed to.** At rest, `recipients` names
exactly the encryption keys of devices admitted into users of c not
removed: no outsider, no removed user's device, and no member left out. -/
theorem recipients_iff (h : Inv (family C) s) (hq : s.queue = []) (c : Id) (e : Key) :
    e ∈ ((recipients c : Model Fact (List Key)).run s).1 ↔
      ∃ u d, Admitted C s.ops c u d e ∧ ¬ Removed C s.ops c u := by
  rw [run_recipients]; exact recipientsP_iff h hq c e

/-! ## Partitions -/

/-- **Nodes that hold the same ops agree on whom to connect to.** So the
side a removal cuts off is exactly the removed user's devices plus the
nodes that have not yet received the removal: any node that has it
refuses them, and nodes holding the same ops never disagree. -/
theorem connect_agree {s t : DB Fact} (hs : Inv (family C) s) (ht : Inv (family C) t)
    (qs : s.queue = []) (qt : t.queue = []) (hops : s.ops = t.ops) (c : Id) (d : Key) :
    ((allowPeer c d : Model Fact Bool).run s).1 = ((allowPeer c d : Model Fact Bool).run t).1 := by
  have hs' := connect_iff hs qs c d
  have ht' := connect_iff ht qt c d
  rw [hops] at hs'
  cases h1 : ((allowPeer c d : Model Fact Bool).run s).1 <;>
    cases h2 : ((allowPeer c d : Model Fact Bool).run t).1
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
    ((allowPeer c d : Model Fact Bool).run s).1 = false :=
  refuse_nonmember h hq c d fun u' e ha => (only u' e ha) ▸ hr

end Community
