/-
A store of two families, seen as the first family's alone.

The node's store holds the ops of A and B composed (`Family.sum`). Its
A part (`DB.proj`) is a store of A alone: the A ops (those whose kinds
B does not own), A's own verdicts over them, and the index rows of
their facts. Its verdicts are those of any store of A alone that holds
the same ops at rest (`proj_unique`).

Law: `sum_project`. At rest, the A part keeps A's invariant and is at
rest too, so every law proven of A over a store at rest holds of it.
And a view of A, lifted to the composed store (`View.liftL`), answers
as it does on the A part, if it reads only keys B files nothing under
(`View.Reads`, `LeftKey`): a relation of A's whose name none of B's has
is one (`leftKey_rel`). So those laws speak of what the composed store's
views answer.

The verdicts are A's spec over the A ops, not the composed store's read
back. An A op citing a B op is Invalid in the composed store (A never
reads a B fact), but among the A ops alone it waits, its requirement
missing. Valid verdicts agree (`spec_sum_left`), and a list reads only
Valid facts. A list under a key B files under counts B's facts too, so
the lifted view's counts would differ there: hence the condition on the
keys a view reads.
-/
import engine.core.Families

namespace Engine

variable {A B : Type}

/-! ## The A part -/

/-- The ops among these whose kinds `owns` does not name: the first
family's. -/
def leftOps (owns : UInt8 → Bool) (ops : Id → Option Op) (x : Id) : Option Op :=
  match ops x with
  | some o => if owns o.kind then none else some o
  | none => none

theorem leftOps_eq_some {owns : UInt8 → Bool} {ops : Id → Option Op} {x : Id} {o : Op} :
    leftOps owns ops x = some o ↔ ops x = some o ∧ owns o.kind = false := by
  unfold leftOps
  cases ops x with
  | none => simp
  | some p =>
    by_cases hp : owns p.kind = true
    · simp only [hp, ite_true]
      constructor
      · intro e; cases e
      · rintro ⟨e, h⟩; cases e; rw [hp] at h; cases h
    · have hp' : owns p.kind = false := by simpa using hp
      simp only [hp', Bool.false_eq_true, ite_false, Option.some.injEq]
      exact ⟨fun e => ⟨e, e ▸ hp'⟩, fun ⟨e, _⟩ => e⟩

theorem leftOps_isSome {owns : UInt8 → Bool} {ops : Id → Option Op} {x : Id}
    (h : (leftOps owns ops x).isSome) : (ops x).isSome := by
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 h
  rw [(leftOps_eq_some.1 ho).1]; rfl

/-- Whether a verdict is Valid with a fact of the first family. -/
def leftValid : Option (Verdict (A ⊕ B)) → Bool
  | some (.valid (.inl _)) => true
  | _ => false

open Classical in
/-- x's verdict among these ops, by the spec, if it has one. -/
noncomputable def specVerdict (fam : Family A) (ops : Id → Option Op) (x : Id) : Option (Verdict A) :=
  if h : ∃ v, Spec fam ops x v then some h.choose else none

theorem specVerdict_eq_some {fam : Family A} {ops : Id → Option Op} {x : Id} {v : Verdict A} :
    specVerdict fam ops x = some v ↔ Spec fam ops x v := by
  unfold specVerdict
  split
  · rename_i h
    constructor
    · intro e; cases e; exact h.choose_spec
    · intro hv; exact congrArg some (spec_det h.choose_spec hv)
  · rename_i h
    constructor
    · intro e; cases e
    · intro hv; exact absurd ⟨v, hv⟩ h

/-- **The first family's part of a store of two**: its ops, with its
own verdicts over them, and the index rows of its facts. Each op waits
on its requirements, and the queue is the store's. Nothing runs it: it
is what the laws are read over, its verdicts the spec's. -/
noncomputable def DB.proj (a : Family A) (owns : UInt8 → Bool) (s : DB (A ⊕ B)) : DB A where
  ops := leftOps owns s.ops
  stored := s.stored.filter fun x => (leftOps owns s.ops x).isSome
  status := specVerdict a (leftOps owns s.ops)
  waits r := s.stored.filter fun x => match leftOps owns s.ops x with
    | some o => has o.reqs r
    | none => false
  queue := s.queue
  idx k := (s.idx k).filter fun x => leftValid (s.status x)

/-! ## Valid verdicts agree -/

section
variable {F : Type}

/-- A Valid verdict at depth n + 1: the op, its requirements Valid at
depth n, and the validator's answer. -/
theorem specAt_valid_inv {fam : Family F} {ops : Id → Option Op} {n : Nat} {x : Id} {f : F}
    (h : specAt fam ops (n + 1) x = some (.valid f)) :
    ∃ o fs, ops x = some o ∧ All2 (fun r g => specAt fam ops n r = some (.valid g)) o.reqs fs ∧
      fam.validate o fs = some f := by
  unfold specAt at h
  cases hx : ops x with
  | none => rw [hx] at h; simp at h
  | some o =>
    rw [hx] at h; simp only at h
    unfold judge at h
    split at h
    · simp at h
    · cases ha : allValid (o.reqs.map (specAt fam ops n)) with
      | none => rw [ha] at h; simp at h
      | some fs =>
        rw [ha] at h; simp only at h
        refine ⟨o, fs, rfl, allValid_forall2 ha, ?_⟩
        cases hv : fam.validate o fs with
        | none => rw [hv] at h; simp at h
        | some g => rw [hv] at h; simp at h; rw [h]

theorem All2.of_map {α β γ : Type} {R : α → γ → Prop} {g : β → γ} :
    ∀ {l : List α} {m : List β}, All2 R l (m.map g) → All2 (fun a b => R a (g b)) l m
  | [], [], _ => .nil
  | _ :: _, _ :: _, .cons hr t => .cons hr (All2.of_map t)

theorem All2.to_map {α β γ : Type} {R : α → γ → Prop} {g : β → γ} :
    ∀ {l : List α} {m : List β}, All2 (fun a b => R a (g b)) l m → All2 R l (m.map g)
  | _, _, .nil => .nil
  | _, _, .cons hr t => .cons hr (All2.to_map t)

end

theorem lefts_some {fs : List (A ⊕ B)} {xs : List A} (h : lefts fs = some xs) :
    fs = xs.map .inl := by
  induction fs generalizing xs with
  | nil => simp [lefts] at h; subst h; rfl
  | cons f t ih =>
    cases f with
    | inr _ => simp [lefts] at h
    | inl x =>
      simp only [lefts, List.mapM_cons] at h
      change (lefts t).bind (fun l => some (x :: l)) = some xs at h
      cases ht : lefts t with
      | none => rw [ht] at h; cases h
      | some ys =>
        rw [ht] at h
        simp only [Option.bind_some, Option.some.injEq] at h
        subst h
        rw [ih ht]; rfl

variable {a : Family A} {b : Family₂ A B}

theorem specAt_inl {ops : Id → Option Op} :
    ∀ n x f, specAt (a.sum b) ops n x = some (.valid (.inl f)) →
      Spec a (leftOps b.owns ops) x (.valid f) := by
  intro n
  induction n with
  | zero => intro x f h; simp [specAt] at h
  | succ n ih =>
    intro x f h
    obtain ⟨o, fs, hx, hr, hv⟩ := specAt_valid_inv h
    have hown : b.owns o.kind = false := by
      cases hb : b.owns o.kind
      · rfl
      · simp [Family.sum, hb] at hv
    simp only [Family.sum, hown, Bool.false_eq_true, ite_false] at hv
    cases hl : lefts fs with
    | none => rw [hl] at hv; simp at hv
    | some xs =>
      rw [hl] at hv
      simp only [Option.bind_some, Option.map_eq_some_iff, Sum.inl.injEq] at hv
      obtain ⟨g, hg, rfl⟩ := hv
      rw [lefts_some hl] at hr
      refine spec_valid_of (leftOps_eq_some.2 ⟨hx, hown⟩) ?_ hg
      exact (All2.of_map hr).imp fun hr' => ih _ _ hr'

theorem specAt_left {ops : Id → Option Op} :
    ∀ n x f, specAt a (leftOps b.owns ops) n x = some (.valid f) →
      Spec (a.sum b) ops x (.valid (.inl f)) := by
  intro n
  induction n with
  | zero => intro x f h; simp [specAt] at h
  | succ n ih =>
    intro x f h
    obtain ⟨o, fs, hx, hr, hv⟩ := specAt_valid_inv h
    obtain ⟨hx, hown⟩ := leftOps_eq_some.1 hx
    refine spec_valid_of hx (All2.to_map (hr.imp fun hr' => ih _ _ hr')) ?_
    rw [sum_left a b o fs hown, hv]; rfl

/-- **Valid verdicts agree:** an op is Valid with A's fact f in the
composed store exactly when it is Valid with f among the A ops alone. -/
theorem spec_sum_left {ops : Id → Option Op} {x : Id} {f : A} :
    Spec (a.sum b) ops x (.valid (.inl f)) ↔ Spec a (leftOps b.owns ops) x (.valid f) :=
  ⟨fun ⟨n, hn⟩ => specAt_inl n x f hn, fun ⟨n, hn⟩ => specAt_left n x f hn⟩

/-! ## The A part at rest -/

section
variable {s : DB (A ⊕ B)}

theorem proj_ops (x : Id) : (s.proj a b.owns).ops x = leftOps b.owns s.ops x := rfl

/-- At rest, the A part's verdict is Valid with f exactly when the
store's is Valid with A's fact f. -/
theorem proj_status (h : Inv (a.sum b) s) (hq : s.queue = []) (x : Id) (f : A) :
    (s.proj a b.owns).status x = some (.valid f) ↔ s.status x = some (.valid (.inl f)) := by
  show specVerdict a _ x = _ ↔ _
  rw [specVerdict_eq_some, status_iff_spec h hq, spec_sum_left]

theorem mem_proj_idx (k : ByteArray) (x : Id) :
    x ∈ (s.proj a b.owns).idx k ↔ x ∈ s.idx k ∧ leftValid (s.status x) = true :=
  List.mem_filter

/-- **At rest, the A part keeps A's invariant.** -/
theorem proj_inv (h : Inv (a.sum b) s) (hq : s.queue = []) : Inv a (s.proj a b.owns) where
  key x o hx := h.key x o (leftOps_eq_some.1 hx).1
  sound _ _ hv := specVerdict_eq_some.1 hv
  wait x o hx hs := by
    right
    refine ⟨?_, fun r hr _ => ?_⟩
    · cases hj : judge a o (o.reqs.map (s.proj a b.owns).status) with
      | none => rfl
      | some v =>
        have hv : specVerdict a (leftOps b.owns s.ops) x = some v :=
          specVerdict_eq_some.2 (spec_of_judge hx _ (fun _ _ _ hw => specVerdict_eq_some.1 hw) hj)
        have hs' : specVerdict a (leftOps b.owns s.ops) x = none := hs
        rw [hv] at hs'; cases hs'
    · show x ∈ s.stored.filter _
      rw [List.mem_filter]
      refine ⟨(h.stored x).2 (leftOps_isSome (by rw [proj_ops] at hx; rw [hx]; rfl)), ?_⟩
      rw [← proj_ops, hx]; exact (has_iff _ _).2 hr
  idx k x := by
    rw [mem_proj_idx, h.idx]
    constructor
    · rintro ⟨⟨g, hg, hk⟩, hl⟩
      rw [hg] at hl
      cases g with
      | inr _ => simp [leftValid] at hl
      | inl f => exact ⟨f, (proj_status h hq x f).2 hg, hk⟩
    · rintro ⟨f, hf, hk⟩
      have hg := (proj_status h hq x f).1 hf
      exact ⟨⟨.inl f, hg, hk⟩, by rw [hg]; rfl⟩
  nodup k := (h.nodup k).sublist List.filter_sublist
  stored x := by
    show x ∈ s.stored.filter (fun x => (leftOps b.owns s.ops x).isSome) ↔
      (leftOps b.owns s.ops x).isSome
    rw [List.mem_filter]
    exact ⟨fun h' => h'.2, fun h' => ⟨(h.stored x).2 (leftOps_isSome h'), h'⟩⟩

/-- **The A part's verdicts are any A store's that holds the same ops,
at rest:** a node of A alone that received exactly the A ops. -/
theorem proj_unique (h : Inv (a.sum b) s) (hq : s.queue = []) {t : DB A} (ht : Inv a t)
    (qt : t.queue = []) (hops : t.ops = leftOps b.owns s.ops) :
    t.status = (s.proj a b.owns).status :=
  status_eq_of_ops ht (proj_inv h hq) qt hq hops

end

/-! ## Views agree -/

/-- Keys under which a store of A and B files only A's facts. -/
def LeftKey (s : DB (A ⊕ B)) (k : ByteArray) : Prop :=
  ∀ x ∈ s.idx k, ∃ f, s.status x = some (.valid (.inl f))

/-- Every list view v may read, whatever the answers, is under a key P
holds of. -/
inductive View.Reads {F α : Type} (P : ByteArray → Prop) : View F α → Prop
  | pure (x : α) : Reads P (.pure x)
  | list {q : ListQ} {k : Answer F → View F α} :
      P q.key → (∀ ans, Reads P (k ans)) → Reads P (.list q k)

namespace View.Reads
variable {F α β : Type} {P Q : ByteArray → Prop}

theorem bind {v : View F α} {f : α → View F β} (hv : v.Reads P) (hf : ∀ x, (f x).Reads P) :
    (v >>= f).Reads P := by
  induction hv with
  | pure x => exact hf x
  | list hq _ ih => exact .list hq ih

theorem read {q : ListQ} (hq : P q.key) : (View.read q : View F (Answer F)).Reads P :=
  .list hq fun _ => .pure _

theorem mono (h : ∀ k, P k → Q k) {v : View F α} (hv : v.Reads P) : v.Reads Q := by
  induction hv with
  | pure x => exact .pure x
  | list hq _ ih => exact .list (h _ hq) ih

end View.Reads

/-- A key that is no op's own key and none of B's keys holds only A's
facts. -/
theorem leftKey_of {s : DB (A ⊕ B)} (h : Inv (a.sum b) s) {k : ByteArray}
    (hop : ∀ y, k ≠ opKey y) (hb : ∀ g, k ∉ b.keys g) : LeftKey s k := by
  intro x hx
  obtain ⟨f, hf, hk⟩ := (h.idx k x).1 hx
  cases f with
  | inl f => exact ⟨f, hf⟩
  | inr g =>
    rcases List.mem_cons.1 hk with e | e
    · exact absurd e (hop x)
    · exact absurd e (hb g)

/-- Relations of two families' facts share a key only if they share
both names. -/
theorem Rel.key_names {F G : Type} {r : Rel F} {r' : Rel G} {as as' : List ByteArray}
    (h : r.key as = r'.key as') : r.kind = r'.kind ∧ r.name = r'.name := by
  have := Codec.encode_inj h
  simp only [Prod.mk.injEq, String.toUTF8_eq_toByteArray, String.toByteArray_inj] at this
  exact ⟨this.1, this.2.1⟩

/-- Keys of these relations, at any arguments. -/
def RelKey {F : Type} (rels : List (Rel F)) (k : ByteArray) : Prop := ∃ r ∈ rels, ∃ as, k = r.key as

/-- **A relation of A's whose names none of B's relations has holds only
A's facts.** -/
theorem leftKey_rel {s : DB (A ⊕ B)} (h : Inv (a.sum b) s) {rels : List (Rel B)}
    (hk : b.keys = keysOf rels) {r : Rel A} (hs : r.kind.toUTF8.size < 128)
    (apart : ∀ r' ∈ rels, ¬ (r'.kind = r.kind ∧ r'.name = r.name)) (as : List ByteArray) :
    LeftKey s (r.key as) := by
  refine leftKey_of h (fun y => r.key_ne_opKey hs as y) fun g hg => ?_
  rw [hk, keysOf, List.mem_filterMap] at hg
  obtain ⟨r', hr', he⟩ := hg
  cases ha : r'.args g with
  | none => rw [ha] at he; cases he
  | some as' =>
    rw [ha] at he
    exact apart r' hr' (Rel.key_names (Option.some.inj he))

/-- So does every key of A's relations, if each is short-named and none
shares its names with one of B's. -/
theorem leftKey_rels {s : DB (A ⊕ B)} (h : Inv (a.sum b) s) {relsB : List (Rel B)}
    (hk : b.keys = keysOf relsB) {relsA : List (Rel A)} (hs : ∀ r ∈ relsA, r.kind.toUTF8.size < 128)
    (apart : ∀ r ∈ relsA, ∀ r' ∈ relsB, ¬ (r'.kind = r.kind ∧ r'.name = r.name)) {k : ByteArray}
    (hr : RelKey relsA k) : LeftKey s k := by
  obtain ⟨r, hr, as, rfl⟩ := hr
  exact leftKey_rel h hk (hs r hr) (apart r hr) as

section
variable [SortKey A] [SortKey B] {s : DB (A ⊕ B)}

/-- An A row as a row of the composed store. -/
def inlRow (p : Pos × A) : Pos × (A ⊕ B) := (p.1, .inl p.2)

theorem insertBy_map {α β : Type} {g : Pos × α → Pos × β} (hg : ∀ p, (g p).1 = p.1) (p : Pos × α) :
    ∀ l : List (Pos × α), insertBy (g p) (l.map g) = (insertBy p l).map g
  | [] => rfl
  | q :: t => by
    simp only [List.map_cons, insertBy, hg]
    split
    · rw [insertBy_map hg p t]; rfl
    · rfl

theorem sortPos_map {α β : Type} {g : Pos × α → Pos × β} (hg : ∀ p, (g p).1 = p.1) :
    ∀ l : List (Pos × α), sortPos (l.map g) = (sortPos l).map g
  | [] => rfl
  | p :: t => by
    show insertBy (g p) (sortPos (t.map g)) = (insertBy p (sortPos t)).map g
    rw [sortPos_map hg t, insertBy_map hg]

theorem matching_proj (h : Inv (a.sum b) s) (hq : s.queue = []) {q : ListQ}
    (hk : LeftKey s q.key) :
    matching s q = (matching (s.proj a b.owns) q).map inlRow := by
  unfold matching
  rw [← sortPos_map (g := inlRow) (fun _ => rfl)]
  congr 1
  rw [show (s.proj a b.owns).idx q.key = (s.idx q.key).filter _ from rfl,
    List.filter_eq_self.2 fun x hx => by obtain ⟨f, hf⟩ := hk x hx; rw [hf]; rfl,
    List.map_filterMap]
  refine filterMap_congr' fun x hx => ?_
  obtain ⟨f, hf⟩ := hk x hx
  have hp := (proj_status h hq x f).2 hf
  have hhas : (fun k => has ((s.proj a b.owns).idx k) x) = fun k => has (s.idx k) x := by
    funext k
    refine Bool.eq_iff_iff.2 ((has_iff _ x).trans (Iff.trans ?_ (has_iff _ x).symm))
    rw [mem_proj_idx, hf]; simp [leftValid]
  rw [hhas, hp, hf]
  split <;> rfl

/-- **A list under a key holding only A's facts answers, row for row, as
it does on the A part.** -/
theorem eval_proj (h : Inv (a.sum b) s) (hq : s.queue = []) {q : ListQ} (hk : LeftKey s q.key) :
    eval s q = ⟨(eval (s.proj a b.owns) q).rows.map inlRow, (eval (s.proj a b.owns) q).inRange,
      (eval (s.proj a b.owns) q).total⟩ := by
  unfold eval
  rw [matching_proj h hq hk]
  simp only [List.filter_map, List.length_map]
  have hf : ((fun p : Pos × (A ⊕ B) => q.inside p.1) ∘ (inlRow : Pos × A → Pos × (A ⊕ B))) =
      fun p => q.inside p.1 := rfl
  rw [hf]
  congr 1
  have hcut : ∀ l : List (Pos × A), q.cut (l.map inlRow) = (q.cut l).map (inlRow (B := B)) := by
    intro l; unfold ListQ.cut; split
    · rfl
    · rw [List.map_take]
  split <;> simp only [← List.map_reverse, hcut]

omit [SortKey A] [SortKey B] in
theorem filterMap_inlRow {φ : Pos × (A ⊕ B) → Option (Pos × A)} (hφ : ∀ p, φ (inlRow p) = some p)
    (l : List (Pos × A)) : (l.map inlRow).filterMap φ = l := by
  rw [List.filterMap_map, show φ ∘ inlRow = some from funext hφ, List.filterMap_some]

/-- **A lifted view of A answers as it does on the A part,** if it reads
only keys holding A's facts. -/
theorem view_proj (h : Inv (a.sum b) s) (hq : s.queue = []) {α : Type} {v : View A α}
    (hv : v.Reads (LeftKey s)) : (v.liftL : View (A ⊕ B) α).eval s = v.eval (s.proj a b.owns) := by
  induction hv with
  | pure x => rfl
  | @list q k hk _ ih =>
    show View.eval s ((k ⟨(eval s q).rows.filterMap _, (eval s q).inRange, (eval s q).total⟩).liftL) =
      View.eval (s.proj a b.owns) (k (eval (s.proj a b.owns) q))
    rw [eval_proj h hq hk, filterMap_inlRow]
    · exact ih _
    · intro _; rfl

/-- **`sum_project`: a store of two families, at rest, answers the first
family's views as its own part does.** The A part (`DB.proj`) holds
exactly the A ops, keeps A's invariant, and is at rest. Its Valid facts
are exactly the store's Valid A facts. Every view of A that reads only
keys holding A's facts answers, lifted to the store, as it does on the
A part. So every law of A over a store at rest holds of the A part. -/
theorem sum_project (h : Inv (a.sum b) s) (hq : s.queue = []) :
    Inv a (s.proj a b.owns) ∧ (s.proj a b.owns).queue = [] ∧
      (∀ x o, (s.proj a b.owns).ops x = some o ↔ s.ops x = some o ∧ b.owns o.kind = false) ∧
      (∀ x f, Spec a (s.proj a b.owns).ops x (.valid f) ↔ s.status x = some (.valid (.inl f))) ∧
      ∀ {α : Type} (v : View A α), v.Reads (LeftKey s) →
        (v.liftL : View (A ⊕ B) α).eval s = v.eval (s.proj a b.owns) :=
  ⟨proj_inv h hq, hq, fun _ _ => leftOps_eq_some,
    fun x f => by
      show Spec a (leftOps b.owns s.ops) x _ ↔ _
      rw [← spec_sum_left, status_iff_spec h hq],
    fun _ hv => view_proj h hq hv⟩

end

end Engine
