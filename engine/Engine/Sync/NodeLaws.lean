/-
What a node does with hostile frames and with its room index, proven of
`Node`'s code run on held data (`HeldM`, Engine/Sync/Held.lean).

- `onFrame_sealed`, `onSealed_none`, `sealed_unopened`: a sealed frame
  reaches the node only as `openFrame` gives it (`onSealed` never sees
  the frame's bytes), and one that does not open changes nothing and
  sends nothing. With the Connection family's `openFrame`, that is
  `sealed_auth` (Connection/Laws.lean): authenticate before parsing.
- **The cache law** (`Cached`): the node's room index is the index of
  the ops stored. A write turn keeps it so (`write_cached`), and so does
  a purge, which takes no shared op (`purge_cached`); booting from the
  store starts it so (`boot_cached`). Read per room it is exactly the
  stored ops of that room, each under its key (`cached_items`), whatever
  order they came in.
-/
import Engine.Sync.Node

namespace Engine.Sync


section
variable {F : Type}

@[simp] theorem HeldM.bind_apply {α β} (m : HeldM F α) (k : α → HeldM F β) (h : Held F) :
    (m >>= k) h = k (m h).1 (m h).2 := rfl
@[simp] theorem HeldM.pure_apply {α} (a : α) (h : Held F) : (pure a : HeldM F α) h = (a, h) := rfl
@[simp] theorem HeldM.getOp_apply (x : Id) (h : Held F) :
    (Store.getOp x : HeldM F _) h = (h.db.ops x, h) := rfl
@[simp] theorem HeldM.getStatus_apply (x : Id) (h : Held F) :
    (Store.getStatus x : HeldM F _) h = (h.db.status x, h) := rfl

/-- A loop whose body only reads, as a fold. -/
theorem HeldM.forIn_reads {α β} (l : List α) (b : β) (f : α → β → HeldM F (ForInStep β))
    (g : β → α → β) (h : Held F) (hf : ∀ a b, f a b h = (.yield (g b a), h)) :
    forIn l b f h = (l.foldl g b, h) := by
  induction l generalizing b with
  | nil => rfl
  | cons a t ih => rw [List.forIn_cons, HeldM.bind_apply, hf]; exact ih _

theorem bytes_beq_self (a : ByteArray) : (a == a) = true := by
  show (a.data == a.data) = true
  exact beq_self_eq_true _

end

/-! ## Sealed frames -/

section
variable {F : Type} {m : Type → Type} [Monad m] [Store F m] [Turn F m]

/-- **A sealed frame reaches the node only through `openFrame`.** Its
bytes go to `openFrame`, and the node goes on with what that returns,
through `onSealed`, which never sees them. -/
theorem onFrame_sealed (x : Sync F m) (n : Node) (addr bytes : ByteArray) (now : Nat)
    (h : bytes[0]? = some 1) :
    n.onFrame x addr bytes now =
      x.hooks.openFrame (bytes.extract 1 bytes.size) >>= fun r => n.onSealed x addr r now := by
  unfold Node.onFrame; rw [h]; rfl

/-- A frame that did not open is ignored. -/
theorem onSealed_none (x : Sync F m) (n : Node) (addr : ByteArray) (now : Nat) :
    n.onSealed x addr none now = pure (n, {}) := rfl

end

/-- **A sealed frame that does not open changes nothing and sends
nothing**: if `openFrame` reads only and opens nothing, the node and the
store are as they were, and there are no effects. -/
theorem sealed_unopened {F : Type} (x : Sync F (HeldM F)) (n : Node) (addr bytes : ByteArray) (now : Nat)
    (h : Held F) (h1 : bytes[0]? = some 1)
    (ho : x.hooks.openFrame (bytes.extract 1 bytes.size) h = (none, h)) :
    n.onFrame x addr bytes now h = ((n, {}), h) := by
  rw [onFrame_sealed x n addr bytes now h1, HeldM.bind_apply, ho]; rfl

section
variable {F : Type}

/-! ## The room index -/

variable (fam : Family F)

theorem items_mk (rooms : List (Id × List Item)) (r : Id) :
    Index.items ⟨rooms⟩ r = ((rooms.find? fun p => Decidable.decide (p.1 = r)).map (·.2)).getD [] := by
  unfold Index.items
  cases rooms.find? fun p => Decidable.decide (p.1 = r) <;> rfl

/-- **Adding an op files it under its room only.** -/
theorem items_add (ix : Index) (o : Op) (r : Id) :
    (ix.add fam o).items r =
      if fam.room o = some r then ins (keyOf fam o, o.id) (ix.items r) else ix.items r := by
  obtain ⟨rooms⟩ := ix
  unfold Index.add
  cases hr : fam.room o with
  | none => simp
  | some c =>
    simp only [Option.some.injEq]
    split
    · rename_i hany
      rw [items_mk, items_mk, List.find?_map]
      have e : ((fun p : Id × List Item => Decidable.decide (p.1 = r)) ∘
          fun p => if p.1 = c then (p.1, ins (keyOf fam o, o.id) p.2) else p) =
          fun p => Decidable.decide (p.1 = r) := by
        funext p; simp only [Function.comp]; split <;> rfl
      rw [e]
      cases hf : rooms.find? fun p => Decidable.decide (p.1 = r) with
      | none =>
        simp only [Option.map_none, Option.getD_none]
        split
        · rename_i hc; subst hc
          exfalso
          obtain ⟨p, hp, hpc⟩ := List.any_eq_true.1 hany
          have := List.find?_eq_none.1 hf p hp
          exact this hpc
        · rfl
      | some p =>
        have hpr := List.find?_some hf
        simp only [decide_eq_true_eq] at hpr
        simp only [Option.map_some, Option.getD_some]
        by_cases hc : c = r
        · subst hc; simp [hpr]
        · have : ¬ p.1 = c := fun e => hc (e ▸ hpr)
          simp [this, hc]
    · rename_i hany
      rw [items_mk, items_mk]
      simp only [List.find?_cons]
      by_cases hc : c = r
      · subst hc
        have hn : (rooms.find? fun p => Decidable.decide (p.1 = c)) = none := by
          apply List.find?_eq_none.2
          intro p hp hpc
          exact hany (List.any_eq_true.2 ⟨p, hp, hpc⟩)
        simp [hn, ins]
      · simp [hc]

theorem mem_ins_of {a b : Item} {l : List Item} (h : b ∈ ins a l) : b = a ∨ b ∈ l := by
  induction l with
  | nil => simp [ins] at h; exact Or.inl h
  | cons c t ih =>
    unfold ins at h
    split at h
    · rcases List.mem_cons.1 h with rfl | h
      · exact Or.inl rfl
      · exact Or.inr h
    · split at h
      · exact Or.inr h
      · rcases List.mem_cons.1 h with rfl | h
        · exact Or.inr (List.mem_cons_self ..)
        · rcases ih h with h | h
          · exact Or.inl h
          · exact Or.inr (List.mem_cons_of_mem _ h)

theorem mem_ins_keep {a b : Item} {l : List Item} (h : b ∈ l) : b ∈ ins a l := by
  induction l with
  | nil => cases h
  | cons c t ih =>
    unfold ins
    split
    · exact List.mem_cons_of_mem _ h
    · split
      · exact h
      · rcases List.mem_cons.1 h with rfl | h
        · exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (ih h)

/-- An insert keeps an item of the inserted key. -/
theorem ins_key (a : Item) (l : List Item) : ∃ b ∈ ins a l, b.1 = a.1 := by
  induction l with
  | nil => exact ⟨a, by simp [ins], rfl⟩
  | cons c t ih =>
    unfold ins
    split
    · exact ⟨a, List.mem_cons_self .., rfl⟩
    · split
      · rename_i he; exact ⟨c, List.mem_cons_self .., he.symm⟩
      · obtain ⟨b, hb, e⟩ := ih
        exact ⟨b, List.mem_cons_of_mem _ hb, e⟩

/-- **An index only grows.** -/
theorem items_add_mono {ix : Index} {o : Op} {r : Id} {a : Item} (h : a ∈ ix.items r) :
    a ∈ (ix.add fam o).items r := by
  rw [items_add]; split
  · exact mem_ins_keep h
  · exact h

theorem items_foldl (ix : Index) (L : List Op) (r : Id) :
    (L.foldl (Index.add fam) ix).items r =
      L.foldl (fun l o => if fam.room o = some r then ins (keyOf fam o, o.id) l else l) (ix.items r) := by
  induction L generalizing ix with
  | nil => rfl
  | cons o t ih => rw [List.foldl_cons, ih, items_add]; rfl

/-- What room r's list holds after adding these ops: what it held, or
one of them, of room r, with its key. -/
theorem mem_items_foldl {ix : Index} {L : List Op} {r : Id} {a : Item}
    (h : a ∈ (L.foldl (Index.add fam) ix).items r) :
    a ∈ ix.items r ∨ ∃ o ∈ L, a = (keyOf fam o, o.id) ∧ fam.room o = some r := by
  induction L generalizing ix with
  | nil => exact Or.inl h
  | cons o t ih =>
    rw [List.foldl_cons] at h
    rcases ih h with h | ⟨p, hp, e⟩
    · rw [items_add] at h
      split at h
      · rename_i hr
        rcases mem_ins_of h with rfl | h
        · exact Or.inr ⟨o, List.mem_cons_self .., rfl, hr⟩
        · exact Or.inl h
      · exact Or.inl h
    · exact Or.inr ⟨p, List.mem_cons_of_mem _ hp, e⟩

theorem items_foldl_mono {ix : Index} {L : List Op} {r : Id} {a : Item} (h : a ∈ ix.items r) :
    a ∈ (L.foldl (Index.add fam) ix).items r := by
  induction L generalizing ix with
  | nil => exact h
  | cons o t ih => exact ih (items_add_mono fam h)

/-- Every op added of room r has an item of its key in r's list. -/
theorem items_foldl_key {ix : Index} {L : List Op} {o : Op} {r : Id} (ho : o ∈ L)
    (hr : fam.room o = some r) : ∃ a ∈ (L.foldl (Index.add fam) ix).items r, a.1 = keyOf fam o := by
  induction L generalizing ix with
  | nil => cases ho
  | cons p t ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.1 ho with rfl | ho
    · obtain ⟨b, hb, e⟩ := ins_key (keyOf fam o, o.id) (ix.items r)
      refine ⟨b, items_foldl_mono fam ?_, e⟩
      rw [items_add]; simpa [hr] using hb
    · exact ih ho

/-- Ops of no room leave an index as it was. -/
theorem foldl_add_shared (ix : Index) (L : List Op) :
    L.foldl (Index.add fam) ix = (L.filter fun o => (fam.room o).isSome).foldl (Index.add fam) ix := by
  induction L generalizing ix with
  | nil => rfl
  | cons o t ih =>
    rw [List.foldl_cons, List.filter_cons]
    cases hr : fam.room o with
    | none =>
      have : ix.add fam o = ix := by unfold Index.add; rw [hr]
      rw [this, ih]; rfl
    | some c => simp only [Option.isSome_some, ite_true, List.foldl_cons]; exact ih _

/-! ## The cache law -/

theorem filterMap_ext {α β} {f g : α → Option β} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) →
    l.filterMap f = l.filterMap g
  | [], _ => rfl
  | x :: t, h => by
    rw [List.filterMap_cons, List.filterMap_cons, h x (List.mem_cons_self ..),
      filterMap_ext fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-- **The node's room index is the index of the ops stored,** in the
order they were stored: what booting the node from its store computes
(`Node.boot`). -/
def Cached (n : Node) (s : DB F) : Prop :=
  n.ix = Index.ofOps fam (s.stored.filterMap s.ops)

theorem boot_cached (s : DB F) (floor : Nat) :
    Cached fam (Node.boot fam (s.stored.filterMap s.ops) floor) s := rfl

theorem keyOf_id {o p : Op} (h : keyOf fam o = keyOf fam p) : o.id = p.id := by
  have := congrArg Key.n h
  simp only [keyOf] at this
  have := num_inj this
  cases ho : o.id; cases hp : p.id
  rw [ho, hp] at this
  simp at this
  rw [this]

/-- **The cache holds exactly the stored ops of each room**, each under
its key. -/
theorem cached_items {n : Node} {s : DB F} (hi : Inv fam s) (hc : Cached fam n s) (r : Id) (a : Item) :
    a ∈ n.ix.items r ↔ ∃ o, s.ops a.2 = some o ∧ fam.room o = some r ∧ a.1 = keyOf fam o := by
  rw [hc]
  constructor
  · intro h
    rcases mem_items_foldl fam h with h | ⟨o, ho, rfl, hr⟩
    · simp [Index.items] at h
    · obtain ⟨x, _, hx⟩ := List.mem_filterMap.1 ho
      have := hi.key x o hx
      subst this
      exact ⟨o, hx, hr, rfl⟩
  · rintro ⟨o, ho, hr, hk⟩
    have hs : a.2 ∈ s.stored := (hi.stored _).2 (by rw [ho]; rfl)
    obtain ⟨b, hb, e⟩ := items_foldl_key fam (ix := {}) (List.mem_filterMap.2 ⟨a.2, hs, ho⟩) hr
    rcases mem_items_foldl fam hb with h | ⟨p, hp, rfl, _⟩
    · simp [Index.items] at h
    · obtain ⟨x, _, hx⟩ := List.mem_filterMap.1 hp
      have hpx := hi.key x p hx
      have hoa := hi.key _ o ho
      have hid := keyOf_id fam e
      obtain ⟨k, i⟩ := a
      simp only at *
      rw [hk, ← e, ← hoa, ← hid]; exact hb

theorem foldl_ingest_keep {s : DB F} {i : Id} {q : Op} (L : List Op) (h : s.ops i = some q) :
    (L.foldl (fun s o => ingestS o s) s).ops i = some q := by
  induction L generalizing s with
  | nil => exact h
  | cons o t ih =>
    apply ih
    show (ingestS o s).ops i = some q
    unfold ingestS
    split
    · exact h
    · show (if i = o.id then some o else s.ops i) = some q
      rename_i hn
      have : i ≠ o.id := by rintro rfl; rw [h] at hn; cases hn
      simp [this, h]

/-- What the stored ops become when ops new to the store, with distinct
ids, are taken in: the same, then the new ones. -/
theorem foldl_ingest_new {s : DB F} (hi : Inv fam s) (news : List Op)
    (hn : ∀ o ∈ news, s.ops o.id = none) (hd : (news.map (·.id)).Nodup) :
    let t := news.foldl (fun s o => ingestS o s) s
    Inv fam t ∧ t.stored.filterMap t.ops = s.stored.filterMap s.ops ++ news ∧
      ∀ o ∈ news, t.ops o.id = some o := by
  induction news generalizing s with
  | nil => exact ⟨hi, by simp, by simp⟩
  | cons o rest ih =>
    intro t
    have ho := hn o (List.mem_cons_self ..)
    have hd' := List.nodup_cons.1 hd
    let s' := ingestS o s
    have e1 : s'.ops = fun i => if i = o.id then some o else s.ops i := by
      show (ingestS o s).ops = _; unfold ingestS; rw [ho]; rfl
    have e2 : s'.stored = s.stored ++ [o.id] := by
      show (ingestS o s).stored = _; unfold ingestS; rw [ho]
      show Engine.ins s.stored o.id = _
      unfold Engine.ins
      have : has s.stored o.id = false := by
        rw [has_false, hi.stored]; rw [ho]; simp
      rw [this]; rfl
    have hn' : ∀ p ∈ rest, s'.ops p.id = none := by
      intro p hp
      rw [e1]
      have : p.id ≠ o.id := fun e => hd'.1 (List.mem_map.2 ⟨p, hp, e⟩)
      simp [this, hn p (List.mem_cons_of_mem _ hp)]
    obtain ⟨hI, hF, hS⟩ := ih (inv_ingest hi o) hn' hd'.2
    refine ⟨hI, ?_, ?_⟩
    rotate_left
    · intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact foldl_ingest_keep rest (by show s'.ops p.id = some p; rw [e1]; simp)
      · exact hS p hp
    show (rest.foldl _ s').stored.filterMap (rest.foldl _ s').ops = _
    rw [hF, e2, e1, List.filterMap_append]
    have : s.stored.filterMap (fun i => if i = o.id then some o else s.ops i) =
        s.stored.filterMap s.ops := by
      apply filterMap_ext
      intro x hx
      have : x ≠ o.id := by
        rintro rfl
        have := (hi.stored _).1 hx
        rw [ho] at this; cases this
      simp [this]
    rw [this]
    simp

theorem drainS_stored (n : Nat) (s : DB F) : (drainS fam n s).stored = s.stored := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => unfold drainS; split <;> simp only [ih, stepS_stored]

theorem inv_drain {s : DB F} (hi : Inv fam s) (n : Nat) : Inv fam (drainS fam n s) := by
  induction n generalizing s with
  | zero => exact hi
  | succ n ih => unfold drainS; split
                 · exact inv_step hi
                 · exact ih (inv_step hi)

end

section
variable {F : Type}

/-- One step of `write`'s first loop: o, unless an op of its id is
stored or already kept. -/
def absentStep (s : DB F) (b : List Op) (o : Op) : List Op :=
  if (!b.any fun p => p.id == o.id) = true then
    (if (s.ops o.id).isNone = true then o :: b else b) else b

/-- One step of `write`'s second loop: o filed, if it is stored. -/
def fileStep (fam : Family F) (s : DB F) (a : Index × List Id) (o : Op) : Index × List Id :=
  if (s.ops o.id).isSome = true then (a.1.add fam o, o.id :: a.2) else a

theorem absentOf_new (s : DB F) (ops : List Op) :
    (∀ o ∈ ops.foldl (absentStep s) [], s.ops o.id = none) ∧
      ((ops.foldl (absentStep s) []).map (·.id)).Nodup := by
  suffices ∀ b : List Op, (∀ o ∈ b, s.ops o.id = none) → (b.map (·.id)).Nodup →
      (∀ o ∈ ops.foldl (absentStep s) b, s.ops o.id = none) ∧
        ((ops.foldl (absentStep s) b).map (·.id)).Nodup from
    this [] (by simp) (by simp)
  induction ops with
  | nil => intro b h1 h2; exact ⟨h1, h2⟩
  | cons o t ih =>
    intro b h1 h2
    simp only [List.foldl_cons]
    apply ih
    · intro p hp
      unfold absentStep at hp
      split at hp
      · split at hp
        · rename_i hn
          rcases List.mem_cons.1 hp with rfl | hp
          · simpa using hn
          · exact h1 p hp
        · exact h1 p hp
      · exact h1 p hp
    · unfold absentStep
      split
      · rename_i hany
        split
        · rw [List.map_cons, List.nodup_cons]
          refine ⟨fun hm => ?_, h2⟩
          obtain ⟨p, hp, e⟩ := List.mem_map.1 hm
          simp only [Bool.not_eq_true', List.any_eq_false] at hany
          exact hany p hp (by rw [e]; exact bytes_beq_self _)
        · exact h2
      · exact h2

theorem foldl_fileStep (fam : Family F) (s : DB F) (L : List Op) (a : Index × List Id)
    (h : ∀ o ∈ L, (s.ops o.id).isSome = true) : (L.foldl (fileStep fam s) a).1 = L.foldl (Index.add fam) a.1 := by
  induction L generalizing a with
  | nil => rfl
  | cons o t ih =>
    rw [List.foldl_cons, List.foldl_cons, ih _ fun p hp => h p (List.mem_cons_of_mem _ hp)]
    unfold fileStep; rw [ite_eq_left (h o (List.mem_cons_self ..))]

theorem turn_apply (fam : Family F) (ops : List Op) (h : Held F) :
    (Turn.turn fam ops : HeldM F Unit) h =
      ((), Held.mk (h.log ++ ops) (drainS fam (budget (h.log ++ ops) (ops.foldl (fun s o => ingestS o s) h.db))
        (ops.foldl (fun s o => ingestS o s) h.db))) := rfl

/-- **A write turn keeps the cache law**: the index grows by exactly
the ops it newly stores. -/
theorem write_cached (x : Sync F (HeldM F)) {n : Node} {h : Held F} (ops : List Op)
    (hi : Inv x.fam h.db) (hc : Cached x.fam n h.db) :
    Inv x.fam (n.write x ops h).2.db ∧ Cached x.fam (n.write x ops h).1.1 (n.write x ops h).2.db := by
  unfold Node.write
  simp only [HeldM.bind_apply]
  rw [HeldM.forIn_reads (g := absentStep h.db)]
  · dsimp only
    obtain ⟨hn, hd⟩ := absentOf_new h.db ops
    generalize ops.foldl (absentStep h.db) [] = absent at hn hd
    by_cases he : absent.isEmpty = true
    · rw [ite_eq_left he]; exact ⟨hi, hc⟩
    · rw [ite_eq_right he]
      simp only [HeldM.bind_apply, turn_apply]
      have hn' : ∀ o ∈ absent.reverse, h.db.ops o.id = none := fun o ho => hn o (List.mem_reverse.1 ho)
      have hd' : (absent.reverse.map (·.id)).Nodup := by rw [List.map_reverse]; exact (List.reverse_perm _).nodup_iff.2 hd
      obtain ⟨hI, hF, hS⟩ := foldl_ingest_new x.fam hi absent.reverse hn' hd'
      generalize absent.reverse = news at hI hF hS ⊢
      generalize List.foldl (fun s o => ingestS o s) h.db news = t at hI hF hS ⊢
      generalize budget (h.log ++ news) t = k
      have hS' : ∀ o ∈ news, ((drainS x.fam k t).ops o.id).isSome = true := by
        intro o ho; rw [drainS_ops, hS o ho]; rfl
      rw [HeldM.forIn_reads (g := fileStep x.fam (drainS x.fam k t))]
      · simp only [HeldM.pure_apply]
        refine ⟨inv_drain x.fam hI k, ?_⟩
        show (news.foldl (fileStep x.fam (drainS x.fam k t)) (n.ix, [])).1 =
          Index.ofOps x.fam ((drainS x.fam k t).stored.filterMap (drainS x.fam k t).ops)
        rw [foldl_fileStep x.fam _ news _ hS', drainS_ops, drainS_stored, hF, hc]
        simp only [Index.ofOps, List.foldl_append]
      · intro a b
        rw [HeldM.bind_apply, HeldM.getOp_apply]
        unfold fileStep
        by_cases h1 : ((drainS x.fam k t).ops a.id).isSome = true
        · rw [ite_eq_left h1, ite_eq_left h1]; rfl
        · rw [ite_eq_right h1, ite_eq_right h1]; rfl
  · intro a b
    unfold absentStep
    by_cases h1 : (!b.any fun p => p.id == a.id) = true
    · rw [ite_eq_left h1, ite_eq_left h1, HeldM.bind_apply, HeldM.getOp_apply]
      by_cases h2 : (h.db.ops a.id).isNone = true
      · rw [ite_eq_left h2, ite_eq_left h2]; rfl
      · rw [ite_eq_right h2, ite_eq_right h2]; rfl
    · rw [ite_eq_right h1, ite_eq_right h1]; rfl

theorem purge_apply (fam : Family F) (ids : List Id) (scrub : Bool) (h : Held F) :
    (Turn.purge fam ids scrub : HeldM F Unit) h =
      ((), Held.mk (h.log.filter fun o => !has (purgeSet fam h.db ids) o.id)
        (drainS fam (budget (h.log.filter fun o => !has (purgeSet fam h.db ids) o.id) (purgeS fam ids h.db))
          (purgeS fam ids h.db))) := rfl

theorem filter_purged (fam : Family F) (s : DB F) (P : List Id)
    (hP : ∀ x ∈ P, ∀ o, s.ops x = some o → (fam.room o).isSome = false) (l : List Id) :
    ((l.filter fun x => !has P x).filterMap (fun x => if has P x then none else s.ops x)).filter
        (fun o => (fam.room o).isSome) =
      (l.filterMap s.ops).filter (fun o => (fam.room o).isSome) := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    rw [List.filter_cons, List.filterMap_cons]
    by_cases hx : has P x = true
    · simp only [hx, Bool.not_true, Bool.false_eq_true, ite_false, ih]
      cases ho : s.ops x with
      | none => rfl
      | some o =>
        rw [List.filter_cons, hP x ((Engine.has_iff P x).1 hx) o ho]; rfl
    · simp only [Bool.not_eq_true] at hx
      simp only [hx, Bool.not_false, ite_true, List.filterMap_cons, Bool.false_eq_true, ite_false]
      cases s.ops x with
      | none => exact ih
      | some o => rw [List.filter_cons, List.filter_cons, ih]

/-- **A purge keeps the cache law**: it takes no shared op, so the
index is unchanged. -/
theorem purge_cached (fam : Family F) {n : Node} {h : Held F} (ids : List Id) (scrub : Bool)
    (hi : Inv fam h.db) (hc : Cached fam n h.db) :
    Inv fam ((Turn.purge fam ids scrub : HeldM F Unit) h).2.db ∧
      Cached fam n ((Turn.purge fam ids scrub : HeldM F Unit) h).2.db := by
  rw [purge_apply]
  refine ⟨inv_drain fam (purge_inv hi ids) _, ?_⟩
  show n.ix = Index.ofOps fam ((drainS fam _ (purgeS fam ids h.db)).stored.filterMap
    (drainS fam _ (purgeS fam ids h.db)).ops)
  rw [drainS_ops, drainS_stored, hc, Index.ofOps, Index.ofOps, foldl_add_shared,
    foldl_add_shared fam _ ((purgeS fam ids h.db).stored.filterMap _)]
  congr 1
  symm
  apply filter_purged
  intro x hx o ho
  obtain ⟨_, p, hp, hr⟩ := mem_purgeSet_iff.1 hx
  rw [ho] at hp; cases hp
  rw [hr]; rfl

end

end Engine.Sync
