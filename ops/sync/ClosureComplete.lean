/-
Completeness of the running window walk when a finite requirement-closed
set fits its budget. The set is a proof witness, never computed or kept
by the connection. Known or previously streamed ids need no repeated have.
-/
import ops.sync.ClosureLaws
import ops.sync.OfferLaws
import engine.core.Locality

namespace Engine.Sync
local instance : LawfulBEq ByteArray where
  eq_of_beq {a b} h := ByteArray.ext (eq_of_beq (show a.data == b.data from h))
  rfl {a} := show a.data == a.data from beq_self_eq_true a.data

@[simp] theorem mem_closureIds (ids : List Id) (x : Id) : x ∈ closureIds ids ↔ x ∈ ids := by
  induction ids generalizing x with
  | nil => simp [closureIds]
  | cons i ids ih =>
    simp only [closureIds]
    split
    · next hi =>
      have hi' : i ∈ ids := (ih i).mp (List.contains_iff_mem.mp hi)
      simp only [ih, List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (rfl | hx) <;> assumption
    · simp [ih]

theorem closureIds_nodup (ids : List Id) : (closureIds ids).Nodup := by
  induction ids with
  | nil => simp [closureIds]
  | cons i ids ih =>
    simp only [closureIds]
    split
    · exact ih
    · next hi => exact List.nodup_cons.mpr ⟨by simpa using hi, ih⟩

/-- Pending and visited slots, each exactly once. -/
def slots (c : Conn) : List Id := c.closed.toList ++ c.frontier

@[simp] theorem mem_slots (c : Conn) (x : Id) : x ∈ slots c ↔ x ∈ c.closed ∨ x ∈ c.frontier := by
  simp [slots]

/-- Admission does not cut anything when all distinct slots fit. -/
theorem queue_fits (cap : Nat) (closed : Std.HashSet Id) (frontier ids whole : List Id)
    (hu : (closed.toList ++ frontier).Nodup)
    (hs : closed.toList ++ frontier ⊆ whole) (hr : ids ⊆ whole) (hc : whole.length ≤ cap) :
    let fresh := closureIds (ids.filter fun i => !closed.contains i && !frontier.contains i)
    queueClosure cap closed frontier ids = (frontier ++ fresh, false) ∧
    (closed.toList ++ (frontier ++ fresh)).Nodup ∧
    (closed.toList ++ (frontier ++ fresh)) ⊆ whole ∧
    ∀ i ∈ ids, i ∈ closed ∨ i ∈ frontier ++ fresh := by
  intro fresh
  have hf : ∀ x ∈ fresh, x ∈ ids ∧ x ∉ closed ∧ x ∉ frontier := by
    intro x hx
    simpa [fresh] using hx
  have hnew : ((closed.toList ++ frontier) ++ fresh).Nodup := by
    refine List.nodup_append.mpr ⟨hu, closureIds_nodup _, ?_⟩
    intro a ha b hb hab
    subst hab
    have h := hf a hb
    simpa using (show a ∉ closed.toList ++ frontier by simp [h.2.1, h.2.2]) ha
  have hsub : ((closed.toList ++ frontier) ++ fresh) ⊆ whole := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hs hx
    · exact hr (hf x hx).1
  have hn := hnew.length_le_of_subset hsub
  have hfit : fresh.length ≤ cap - (closed.size + frontier.length) := by
    simp only [List.length_append, Std.HashSet.length_toList] at hn
    omega
  refine ⟨?_, by simpa [List.append_assoc] using hnew, by simpa [List.append_assoc] using hsub, ?_⟩
  · simp only [queueClosure]
    change (frontier ++ fresh.take _, Decidable.decide (_ < fresh.length)) = _
    rw [List.take_of_length_le hfit]
    simp [show ¬cap - (closed.size + frontier.length) < fresh.length by omega]
  · intro i hi
    by_cases hclosed : i ∈ closed
    · exact Or.inl hclosed
    · right
      by_cases hfront : i ∈ frontier
      · exact List.mem_append_left _ hfront
      · apply List.mem_append_right
        simp [fresh, hi, hclosed, hfront]

/-- An id has already been advertised, or the peer is known to hold it. -/
def covered (c : Conn) (offers : List (Id × Id)) (i : Id) : Prop :=
  i ∈ c.known ∨ i ∈ c.offered ∨ ∃ r, (r, i) ∈ offers

/-- Inductive facts about the running walk; `whole` is a finite proof witness. -/
structure WalkInv {F} (h : Held F) (whole : List Id) (c : Conn) (offers : List (Id × Id)) : Prop where
  unique : (slots c).Nodup
  inside : slots c ⊆ whole
  edges : ∀ i ∈ c.closed, ∀ o, h.db.ops i = some o → o.reqs ⊆ slots c
  sent : ∀ i ∈ c.closed, covered c offers i

variable {F : Type} (fam : Family F) (cfg : Config)

/-- All members of the witness exist, are shown, and require only members. -/
def Whole (h : Held F) (c : Conn) (ids : List Id) : Prop :=
  ∀ i ∈ ids, ∃ o, h.db.ops i = some o ∧ c.shows fam o = true ∧ o.reqs ⊆ ids

theorem visit_inv (h : Held F) (whole : List Id) (c : Conn) (offers : List (Id × Id))
    (hv : WalkInv h whole c offers) (hw : Whole fam h c whole) (hcap : whole.length ≤ cfg.closureCap)
    (hwindow : 1 < c.roundFloor) (x : Id) (rest : List Id) (hf : c.frontier = x :: rest) :
    ∃ o, h.db.ops x = some o ∧ c.shows fam o = true ∧ x ∉ c.closed ∧
      let d := ({ c with frontier := rest, closed := c.closed.insert x } : Conn).queue cfg o.reqs
      let out := if !c.known.contains x && !c.offered.contains x then
        ((fam.room o).getD .empty, x) :: offers else offers
      WalkInv h whole d out ∧ slots c ⊆ slots d ∧
        d.closed.size = c.closed.size + 1 ∧ d.roundFloor = c.roundFloor := by
  have hxslot : x ∈ slots c := by simp [hf]
  obtain ⟨o, ho, hs, hr⟩ := hw x (hv.inside hxslot)
  have hu := List.nodup_append.mp hv.unique
  have hrest : rest.Nodup := (List.nodup_cons.mp (hf ▸ hu.2.1)).2
  have hxrest : x ∉ rest := (List.nodup_cons.mp (hf ▸ hu.2.1)).1
  have hx : x ∉ c.closed := by
    intro hc
    exact hu.2.2 x (by simpa using hc) x (by simp [hf]) rfl
  let b : Conn := { c with frontier := rest, closed := c.closed.insert x }
  have he : ∀ i, i ∈ slots b ↔ i ∈ slots c := by
    intro i
    simp only [mem_slots, b, hf, List.mem_cons, Std.HashSet.mem_insert]
    grind only
  have hbu : (slots b).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨?_, hrest, ?_⟩
    · simpa [List.Nodup] using (Std.HashSet.distinct_toList (m := b.closed))
    · intro a ha z hz haz
      have ha : a = x ∨ a ∈ c.closed := by
        have hh := Std.HashSet.mem_insert.mp (Std.HashSet.mem_toList.mp ha)
        exact hh.elim (fun e => Or.inl (eq_of_beq e).symm) Or.inr
      subst haz
      rcases ha with rfl | ha
      · exact hxrest hz
      · exact hu.2.2 a (by simpa using ha) a (by rw [hf]; exact List.mem_cons_of_mem _ hz) rfl
  have hbs : slots b ⊆ whole := fun i hi => hv.inside ((he i).mp hi)
  obtain ⟨hq, hqu, hqs, hqr⟩ := queue_fits cfg.closureCap b.closed b.frontier o.reqs whole hbu hbs hr hcap
  let fresh := closureIds (o.reqs.filter fun i => !b.closed.contains i && !b.frontier.contains i)
  let d := b.queue cfg o.reqs
  have hd : d = { b with frontier := rest ++ fresh } := by
    simp [d, Conn.queue, hq, b, show ¬ c.roundFloor ≤ 1 by omega, fresh]
  have hmono : slots c ⊆ slots d := by
    intro i hi
    have := (he i).mpr hi
    simpa [hd, b, or_assoc] using (show i ∈ b.closed ∨ i ∈ rest ++ fresh from
      (mem_slots b i).mp this |>.elim Or.inl (fun hi => Or.inr (List.mem_append_left _ hi)))
  refine ⟨o, ho, hs, hx, ?_⟩
  change WalkInv h whole d _ ∧ _
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hmono, ?_, rfl⟩
  · rw [hd]
    exact hqu
  · rw [hd]
    exact hqs
  · intro i hi p hp y hy
    have hi : i = x ∨ i ∈ c.closed := by
      have hh := Std.HashSet.mem_insert.mp hi
      exact hh.elim (fun e => Or.inl (eq_of_beq e).symm) Or.inr
    rcases hi with hi | hi
    · subst i
      have hop : o = p := Option.some.inj (ho.symm.trans hp)
      subst hop
      have := hqr y hy
      apply (mem_slots d y).mpr
      rw [hd]
      exact this
    · exact hmono (hv.edges i hi p hp hy)
  · intro i hi
    have hi : i = x ∨ i ∈ c.closed := by
      have hh := Std.HashSet.mem_insert.mp hi
      exact hh.elim (fun e => Or.inl (eq_of_beq e).symm) Or.inr
    rcases hi with hi | hi
    · subst i
      unfold covered
      split
      · exact Or.inr (Or.inr ⟨_, List.mem_cons_self ..⟩)
      · next hn =>
        simp only [Bool.and_eq_true, Bool.not_eq_true', not_and] at hn
        by_cases hk : x ∈ c.known
        · exact Or.inl hk
        · exact Or.inr (Or.inl (by change x ∈ c.offered; simpa using hn (by simpa using hk)))
    · obtain hk | hk | ⟨r, hr⟩ := hv.sent i hi
      · exact Or.inl hk
      · exact Or.inr (Or.inl hk)
      · right; right; refine ⟨r, ?_⟩; split
        · exact List.mem_cons_of_mem _ hr
        · exact hr
  · simp [d, Conn.queue, b, Std.HashSet.size_insert, hx]

/-- Enough walk fuel empties the frontier and closes all admitted edges. -/
theorem walk_complete (h : Held F) (whole : List Id) (hcap : whole.length ≤ cfg.closureCap) :
    ∀ fuel (c : Conn) offers, WalkInv h whole c offers → Whole fam h c whole →
      1 < c.roundFloor → whole.length - c.closed.size ≤ fuel →
      let result := ((c.walkN fam cfg offers fuel : HeldM F _) h).1
      result.1.frontier = [] ∧ WalkInv h whole result.1 result.2 ∧ slots c ⊆ slots result.1 := by
  intro fuel
  induction fuel with
  | zero =>
    intro c offers hv hw hwindow hfuel
    have hn := hv.unique.length_le_of_subset hv.inside
    have hempty : c.frontier = [] := by
      simp only [slots, List.length_append, Std.HashSet.length_toList] at hn
      apply List.eq_nil_of_length_eq_zero
      omega
    refine ⟨hempty, ⟨hv.unique, hv.inside, hv.edges, ?_⟩, fun _ h => h⟩
    intro i hi
    obtain hk | hk | ⟨r, hr⟩ := hv.sent i hi
    · exact Or.inl hk
    · exact Or.inr (Or.inl hk)
    · exact Or.inr (Or.inr ⟨r, List.mem_reverse.mpr hr⟩)
  | succ fuel ih =>
    intro c offers hv hw hwindow hfuel
    cases hf : c.frontier with
    | nil =>
      rw [Conn.walkN, hf]
      refine ⟨hf, ⟨hv.unique, hv.inside, hv.edges, ?_⟩, fun _ h => h⟩
      intro i hi
      obtain hk | hk | ⟨r, hr⟩ := hv.sent i hi
      · exact Or.inl hk
      · exact Or.inr (Or.inl hk)
      · exact Or.inr (Or.inr ⟨r, List.mem_reverse.mpr hr⟩)
    | cons x rest =>
      obtain ⟨o, ho, hs, hx, hv', hmono, hsize, hfloor⟩ := visit_inv fam cfg h whole c offers hv hw hcap hwindow x rest hf
      rw [Conn.walkN, hf]
      simp only [Std.HashSet.contains_iff_mem, hx, ite_false, HeldM.bind_apply, HeldM.getOp_apply, ho]
      rw [show Conn.shows fam { c with frontier := rest, closed := c.closed.insert x } o = true from hs]
      simp only [ite_true]
      have hfuel' : whole.length - (c.closed.insert x).size ≤ fuel := by
        simp only [Std.HashSet.size_insert, hx, ite_false]
        omega
      obtain ⟨he, hi, hm⟩ := ih _ _ hv' hw hwindow hfuel'
      exact ⟨he, hi, fun _ h => hm (hmono h)⟩

/-- A window's whole requirement closure fits: after enough visits every
reachable id is advertised, previously streamed, or known held by the peer.
`whole` is any finite requirement-closed superset of the served ops' seeds. -/
theorem closure_complete_under_cap (h : Held F) (c : Conn) (whole : List Id)
    (hwindow : 1 < c.roundFloor) (hempty : c.closed = {})
    (hunique : c.frontier.Nodup) (hseeds : c.frontier ⊆ whole)
    (hwhole : Whole fam h c whole) (hcap : whole.length ≤ cfg.closureCap)
    (hfuel : whole.length ≤ cfg.walk) :
    let result := ((c.walk fam cfg : HeldM F _) h).1
    result.1.frontier = [] ∧ ∀ seed ∈ c.frontier, ∀ i,
      Reach h.db.ops seed i → covered result.1 result.2 i := by
  have hv : WalkInv h whole c [] := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [slots, hempty] using hunique
    · simpa [slots, hempty] using hseeds
    · simp [hempty]
    · simp [hempty]
  obtain ⟨he, hi, hm⟩ := walk_complete fam cfg h whole hcap cfg.walk c [] hv hwhole hwindow (by simpa [hempty] using hfuel)
  refine ⟨he, ?_⟩
  intro seed hseed i reach
  apply hi.sent
  have hseed' := hm ((mem_slots c seed).mpr (Or.inr hseed))
  have hseed' : seed ∈ ((c.walk fam cfg : HeldM F _) h).1.1.closed := by
    simpa only [mem_slots, Conn.walk, he, List.not_mem_nil, or_false] using hseed'
  induction reach with
  | refl => exact hseed'
  | step _ ho hr ih =>
    have := hi.edges _ ih _ ho hr
    simpa only [mem_slots, Conn.walk, he, List.not_mem_nil, or_false] using this

/-- A nonempty instance of the completeness premises, using a stored leaf. -/
theorem closure_under_cap_runs :
    ∃ (fam : Family Unit) (h : Held Unit) (c : Conn) (whole : List Id),
      c.frontier ≠ [] ∧ 1 < c.roundFloor ∧ c.closed = {} ∧ c.frontier.Nodup ∧
      c.frontier ⊆ whole ∧ Whole fam h c whole ∧ whole.length ≤ 1 := by
  let o := Op.make 1 [] .empty
  let fam : Family Unit := { validate := fun _ _ => some (), keys := fun _ => [], scope := fun _ => .shared .empty }
  let h : Held Unit := { db := { DB.empty with ops := fun i => if i = o.id then some o else none, stored := [o.id] } }
  let c : Conn := { dialer := false, rooms := [.empty], floor := 2, roundFloor := 2, frontier := [o.id] }
  refine ⟨fam, h, c, [o.id], by simp [c], by simp [c], rfl, by simp [c], fun _ hi => hi, ?_, by simp⟩
  intro i hi
  have hi : i = o.id := List.mem_singleton.mp hi
  subst i
  refine ⟨o, by simp [h], ?_, ?_⟩
  · simp [c, Conn.shows, Family.room, fam, Engine.has]
  · simp [o, Op.make]

end Engine.Sync
