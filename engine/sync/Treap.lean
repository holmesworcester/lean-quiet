/-
Step two of the cost work (docs/BOUNDS.md): the canonical Merkle treap
kept as a value, so a range's fingerprint costs O(height) hashes instead
of a pass over the room. Its laws, of the treap built here:

- `label_canon`: the label of the canonical treap of a set is `lbl`'s,
  so `lbl_inj` and `exchange_complete` carry over unchanged, with no
  change on the wire.
- `split_canon`: splitting the canonical treap of S at a key gives the
  canonical treaps of S below the key and of the rest, given distinct
  priorities (`Prio`, as ids give). A range's fingerprint is then two
  splits and a label.
- `split_hashes`: a split hashes at most once per level it descends, so
  at most the treap's height (`height_canon`: the height of `canon S`
  is `height S`, the depth hypothesis's).
- `insert_canon`: inserting a new item into the canonical treap of S
  gives the canonical treap of S with it, given distinct priorities and
  keys; `insert_hashes`: in at most height + 1 hashes.

Not yet: the room index holding treaps, and an answer's pieces cut by
rank (the nodes keep sizes for it); until then the index is a sorted
list and this is not on the running path.
-/
import engine.sync.RoundLaws
import engine.core.Cost

namespace Engine.Sync

/-! ## The hash's door, and a list's treap height -/

section
variable {m : Type → Type} [Monad m] [Tick m]

/-- h, through its door: one call, charged with its input's size. -/
@[inline] def hashM (h : ByteArray → ByteArray) (x : ByteArray) : m ByteArray := do
  tick { hashes := 1, hashed := x.size }
  pure (h x)

end

@[simp] theorem val_hashM {m : Type → Type} [Monad m] [Tick m] [Valued m] (h : ByteArray → ByteArray)
    (x : ByteArray) : Valued.val (hashM (m := m) h x) = h x := by
  simp [hashM]

@[simp] theorem cost_hashM (h : ByteArray → ByteArray) (x : ByteArray) :
    Counted.cost (hashM (m := Counted) h x) = { hashes := 1, hashed := x.size } := by
  simp [hashM]

section
variable {α : Type} (key : α → Key)

/-- The height of the canonical treap of l's items. -/
def height (l : List α) : Nat :=
  match hm : top key l with
  | none => 0
  | some t =>
    have := below_lt key (top_mem key hm)
    have := above_lt key (top_mem key hm)
    max (height (below key l t)) (height (above key l t)) + 1
termination_by l.length

theorem height_eq (l : List α) : height key l = match top key l with
    | none => 0
    | some t => max (height key (below key l t)) (height key (above key l t)) + 1 := by
  rw [height]; split <;> rename_i hm <;> simp [hm]

end

/-- A treap node keeps its label and its size. -/
inductive Treap (α : Type) where
  | leaf
  | node (l : Treap α) (a : α) (r : Treap α) (lab : ByteArray) (size : Nat)
  deriving Inhabited

section
variable {α : Type} (key : α → Key) (ident : α → ByteArray) (h : ByteArray → ByteArray)

namespace Treap

def label : Treap α → ByteArray
  | .leaf => h .empty
  | .node _ _ _ lab _ => lab

def size : Treap α → Nat
  | .leaf => 0
  | .node _ _ _ _ n => n

def height : Treap α → Nat
  | .leaf => 0
  | .node l _ r _ _ => max l.height r.height + 1

/-- A node over its children: its label is one hash of theirs. -/
def mk (l : Treap α) (a : α) (r : Treap α) : Treap α :=
  .node l a r (h (Codec.encode (l.label h, ident a, r.label h))) (l.size + 1 + r.size)

end Treap

/-- The canonical treap of l's items, by the recursion `lbl` labels. -/
def canon (l : List α) : Treap α :=
  match hm : top key l with
  | none => .leaf
  | some t =>
    have := below_lt key (top_mem key hm)
    have := above_lt key (top_mem key hm)
    Treap.mk ident h (canon (below key l t)) t (canon (above key l t))
termination_by l.length

theorem canon_eq (l : List α) : canon key ident h l = match top key l with
    | none => .leaf
    | some t => Treap.mk ident h (canon key ident h (below key l t)) t (canon key ident h (above key l t)) := by
  rw [canon]; split <;> rename_i hm <;> simp [hm]

/-- **The canonical treap's label is `lbl`'s.** -/
theorem label_canon : ∀ (n : Nat) (l : List α), l.length ≤ n → (canon key ident h l).label h = lbl key ident h l := by
  intro n
  induction n with
  | zero =>
    intro l hl
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rw [canon_eq, lbl_eq]; simp [top, Treap.label]
  | succ n ih =>
    intro l hl
    rw [canon_eq, lbl_eq]
    cases ht : top key l with
    | none => rfl
    | some t =>
      have h1 := below_lt key (top_mem key ht)
      have h2 := above_lt key (top_mem key ht)
      show h (Codec.encode ((canon key ident h (below key l t)).label h, ident t,
        (canon key ident h (above key l t)).label h)) = _
      rw [ih _ (by omega), ih _ (by omega)]

/-- **The canonical treap's height is its items' treap height.** -/
theorem height_canon : ∀ (n : Nat) (l : List α), l.length ≤ n → (canon key ident h l).height = height key l := by
  intro n
  induction n with
  | zero =>
    intro l hl
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rw [canon_eq, height_eq]; simp [top, Treap.height]
  | succ n ih =>
    intro l hl
    rw [canon_eq, height_eq]
    cases ht : top key l with
    | none => rfl
    | some t =>
      have h1 := below_lt key (top_mem key ht)
      have h2 := above_lt key (top_mem key ht)
      simp only [Treap.mk, Treap.height]
      rw [ih _ (by omega), ih _ (by omega)]

/-- Distinct items have distinct priorities: two items tie in priority
only when their id numbers are equal (`Key.plt_tie`), so distinct id
numbers, as distinct ids give, are distinct priorities. -/
def Prio (l : List α) : Prop := ∀ a ∈ l, ∀ b ∈ l, (key a).n = (key b).n → a = b

/-- The top is the item of largest priority, and with distinct
priorities, the only one. -/
theorem top_of_max {l : List α} (hp : Prio key l) {t : α} (ht : t ∈ l)
    (hmax : ∀ a ∈ l, ¬ Key.plt (key t) (key a)) : top key l = some t := by
  cases hm : top key l with
  | none => rw [(top_none key).1 hm] at ht; cases ht
  | some m =>
    have hm1 := top_mem key hm
    have h1 := top_max key hm t ht
    have h2 := hmax m hm1
    rw [hp m hm1 t ht (Key.plt_tie h1 h2)]

/-- **The top survives a filter that keeps it.** -/
theorem top_filter {l : List α} (hp : Prio key l) {t : α} (ht : top key l = some t) {q : α → Bool}
    (hq : q t = true) : top key (l.filter q) = some t := by
  have hm := top_mem key ht
  apply top_of_max key (fun a ha b hb => hp a (List.mem_filter.1 ha).1 b (List.mem_filter.1 hb).1)
    (List.mem_filter.2 ⟨hm, hq⟩)
  intro a ha
  exact top_max key ht a (List.mem_filter.1 ha).1

theorem filter_congr' {l : List α} {p q : α → Bool} (h : ∀ a ∈ l, p a = q a) : l.filter p = l.filter q := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.filter_cons, h a (List.mem_cons_self ..), ih fun b hb => h b (List.mem_cons_of_mem _ hb)]

theorem filter_comm (l : List α) (p q : α → Bool) : (l.filter p).filter q = (l.filter q).filter p := by
  rw [List.filter_filter, List.filter_filter]
  congr 1; funext a; exact Bool.and_comm _ _

/-- Split a treap at k: the items below k, and the rest. -/
def Treap.split (k : Key) : Treap α → Treap α × Treap α
  | .leaf => (.leaf, .leaf)
  | .node l a r _ _ =>
    if key a < k then
      let p := r.split k
      (Treap.mk ident h l a p.1, p.2)
    else
      let p := l.split k
      (p.1, Treap.mk ident h p.2 a r)

/-- The items of l below k, and the rest. -/
def lows (k : Key) (l : List α) : List α := l.filter fun a => Decidable.decide (key a < k)
def highs (k : Key) (l : List α) : List α := l.filter fun a => !Decidable.decide (key a < k)

/-- **Splitting the canonical treap of a set at k gives the canonical
treaps of the set below k and of the rest.** -/
theorem split_canon (k : Key) : ∀ (n : Nat) (l : List α), l.length ≤ n → Prio key l →
    (canon key ident h l).split key ident h k = (canon key ident h (lows key k l), canon key ident h (highs key k l)) := by
  intro n
  induction n with
  | zero =>
    intro l hl _
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rw [canon_eq]; simp [top, lows, highs, Treap.split, canon_eq]
  | succ n ih =>
    intro l hl hp
    have hsub : ∀ q : α → Bool, Prio key (l.filter q) :=
      fun q a ha b hb => hp a (List.mem_filter.1 ha).1 b (List.mem_filter.1 hb).1
    rw [canon_eq]
    cases ht : top key l with
    | none =>
      rw [(top_none key).1 ht]
      simp [lows, highs, Treap.split, canon_eq, top]
    | some t =>
      have hm := top_mem key ht
      have h1 := below_lt key hm
      have h2 := above_lt key hm
      simp only [Treap.mk, Treap.split]
      by_cases hk : key t < k
      · simp only [hk, ↓reduceIte]
        have e := ih (above key l t) (by omega) (hsub _)
        rw [e]
        -- below k: the top stays, with all of its left and the low part of its right
        have tl : top key (lows key k l) = some t := top_filter key hp ht (by simp [hk])
        have eb : below key (lows key k l) t = below key l t := by
          unfold below lows
          rw [filter_comm, List.filter_filter]
          apply filter_congr'
          intro a _
          by_cases ha : key a < key t
          · simp [ha, Key.lt_trans ha hk]
          · simp [ha]
        have ea : above key (lows key k l) t = lows key k (above key l t) := by
          unfold above lows; exact filter_comm _ _ _
        have ehi : highs key k l = highs key k (above key l t) := by
          unfold highs above
          rw [List.filter_filter]
          apply filter_congr'
          intro a _
          by_cases ha : key a < k
          · simp [ha]
          · have : key t < key a := by
              rcases Key.not_lt.1 ha with h' | h'
              · exact Key.lt_trans hk h'
              · rw [h']; exact hk
            simp [ha, this]
        rw [canon_eq key ident h (lows key k l), tl]
        dsimp only
        rw [eb, ea, ehi]
        rfl
      · simp only [hk, ↓reduceIte]
        have e := ih (below key l t) (by omega) (hsub _)
        rw [e]
        have th : top key (highs key k l) = some t := top_filter key hp ht (by simp [hk])
        have elo : lows key k l = lows key k (below key l t) := by
          unfold lows below
          rw [List.filter_filter]
          apply filter_congr'
          intro a _
          by_cases ha : key a < k
          · have : key a < key t := by
              rcases Key.not_lt.1 hk with h' | h'
              · exact Key.lt_trans ha h'
              · rw [h']; exact ha
            simp [ha, this]
          · simp [ha]
        have eb : below key (highs key k l) t = highs key k (below key l t) := by
          unfold below highs; exact filter_comm _ _ _
        have ea : above key (highs key k l) t = above key l t := by
          unfold above highs
          rw [filter_comm, List.filter_filter]
          apply filter_congr'
          intro a _
          by_cases ha : key t < key a
          · have : ¬ key a < k := fun h' => hk (Key.lt_trans ha h')
            simp [ha, this]
          · simp [ha]
        rw [canon_eq key ident h (highs key k l), th]
        dsimp only
        rw [eb, ea, elo]
        rfl

/-! ## Insert -/

/-- Insert an item: down the path while it ranks below the nodes, then
split the subtree there under it. -/
def Treap.insert (a : α) : Treap α → Treap α
  | .leaf => Treap.mk ident h .leaf a .leaf
  | .node l b r lab sz =>
    if Key.plt (key b) (key a) then
      let p := (Treap.node l b r lab sz).split key ident h (key a)
      Treap.mk ident h p.1 a p.2
    else if key a < key b then Treap.mk ident h (l.insert a) b r
    else Treap.mk ident h l b (r.insert a)

/-- Items named by their keys. -/
def KeysApart (l : List α) : Prop := ∀ x ∈ l, ∀ y ∈ l, key x = key y → x = y

/-- **Inserting a new item into the canonical treap of S gives the
canonical treap of S with it**, given distinct priorities and keys. -/
theorem insert_canon (a : α) : ∀ (n : Nat) (l : List α), l.length ≤ n → a ∉ l → Prio key (a :: l) →
    KeysApart key (a :: l) → (canon key ident h l).insert key ident h a = canon key ident h (a :: l) := by
  intro n
  induction n with
  | zero =>
    intro l hl _ _ _
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rw [canon_eq, canon_eq key ident h [a]]
    simp [top, Treap.insert, below, above, canon_eq, Key.lt_irrefl]
  | succ n ih =>
    intro l hl hna hp hk
    have hkl : ∀ b ∈ l, key b ≠ key a := fun b hb e =>
      hna (hk b (List.mem_cons_of_mem _ hb) a (List.mem_cons_self ..) e ▸ hb)
    have hsub : ∀ q : α → Bool, Prio key (a :: l.filter q) ∧ KeysApart key (a :: l.filter q) := by
      intro q
      refine ⟨fun x hx y hy => hp x ?_ y ?_, fun x hx y hy => hk x ?_ y ?_⟩ <;>
      · first
        | (rcases List.mem_cons.1 hx with rfl | hx
           · exact List.mem_cons_self ..
           · exact List.mem_cons_of_mem _ (List.mem_filter.1 hx).1)
        | (rcases List.mem_cons.1 hy with rfl | hy
           · exact List.mem_cons_self ..
           · exact List.mem_cons_of_mem _ (List.mem_filter.1 hy).1)
    have hpl : Prio key l := fun x hx y hy => hp x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)
    rw [canon_eq key ident h l, canon_eq key ident h (a :: l)]
    cases ht : top key l with
    | none =>
      rw [(top_none key).1 ht]
      simp [top, Treap.insert, below, above, canon_eq, Key.lt_irrefl]
    | some t =>
      have hm := top_mem key ht
      have h1 := below_lt key hm
      have h2 := above_lt key hm
      have hta : t ≠ a := fun e => hna (e ▸ hm)
      simp only [top, ht]
      by_cases hpr : Key.plt (key t) (key a)
      · -- a is the new root: the old treap is split under it
        simp only [hpr, ↓reduceIte, Treap.mk, Treap.insert]
        have e := split_canon key ident h (key a) _ l (Nat.le_refl _) hpl
        rw [canon_eq key ident h l, ht] at e
        simp only [Treap.mk] at e
        rw [e]
        have eb : below key (a :: l) a = lows key (key a) l := by
          simp [below, lows, Key.lt_irrefl]
        have ea : above key (a :: l) a = highs key (key a) l := by
          simp only [above, highs, List.filter_cons, Key.lt_irrefl, decide_false, Bool.false_eq_true,
            ↓reduceIte]
          apply filter_congr'
          intro b hb
          rcases Key.lt_trichotomy (key a) (key b) with h' | h' | h'
          · simp [h', Key.lt_asymm h']
          · exact absurd h'.symm (hkl b hb)
          · simp [h', Key.lt_asymm h']
        rw [eb, ea]
      · -- a goes below the root, on its side
        simp only [hpr, ↓reduceIte, Treap.mk, Treap.insert]
        have hpa : Key.plt (key a) (key t) := by
          by_cases h' : Key.plt (key a) (key t)
          · exact h'
          · exact absurd (hp t (List.mem_cons_of_mem _ hm) a (List.mem_cons_self ..)
              (Key.plt_tie hpr h')) hta
        by_cases hlt : key a < key t
        · simp only [hlt, ↓reduceIte]
          have hb : below key (a :: l) t = a :: below key l t := by
            simp [below, hlt]
          have ha : above key (a :: l) t = above key l t := by
            simp [above, Key.lt_asymm hlt]
          have hs := hsub fun b => Decidable.decide (key b < key t)
          rw [hb, ha, ih (below key l t) (by omega) (fun hm' => hna (List.mem_filter.1 hm').1) hs.1 hs.2]
        · have hgt : key t < key a := by
            rcases Key.lt_trichotomy (key a) (key t) with h' | h' | h'
            · exact absurd h' hlt
            · exact absurd h'.symm (hkl t hm)
            · exact h'
          simp only [hlt, ↓reduceIte]
          have hb : below key (a :: l) t = below key l t := by
            simp [below, Key.lt_asymm hgt]
          have ha : above key (a :: l) t = a :: above key l t := by
            simp [above, hgt]
          have hs := hsub fun b => Decidable.decide (key t < key b)
          rw [hb, ha, ih (above key l t) (by omega) (fun hm' => hna (List.mem_filter.1 hm').1) hs.1 hs.2]

/-! ## What a split costs -/

section
variable {m : Type → Type} [Monad m] [Tick m]

/-- A node over its children, through the hash's door. -/
def Treap.mkM (l : Treap α) (a : α) (r : Treap α) : m (Treap α) := do
  let lab ← hashM h (Codec.encode (l.label h, ident a, r.label h))
  pure (.node l a r lab (l.size + 1 + r.size))

/-- `split`, as it would run: one node rebuilt, one hash, per level. -/
def Treap.splitM (k : Key) : Treap α → m (Treap α × Treap α)
  | .leaf => pure (.leaf, .leaf)
  | .node l a r _ _ =>
    if key a < k then do
      let p ← r.splitM k
      let n ← Treap.mkM ident h l a p.1
      pure (n, p.2)
    else do
      let p ← l.splitM k
      let n ← Treap.mkM ident h p.2 a r
      pure (p.1, n)

/-- `insert`, as it would run. -/
def Treap.insertM (a : α) : Treap α → m (Treap α)
  | .leaf => Treap.mkM ident h .leaf a .leaf
  | .node l b r lab sz =>
    if Key.plt (key b) (key a) then do
      let p ← (Treap.node l b r lab sz).splitM key ident h (key a)
      Treap.mkM ident h p.1 a p.2
    else if key a < key b then do
      let l' ← l.insertM a
      Treap.mkM ident h l' b r
    else do
      let r' ← r.insertM a
      Treap.mkM ident h l b r'

end

open Valued in
theorem val_splitM {m : Type → Type} [Monad m] [Tick m] [Valued m] (k : Key) : ∀ t : Treap α,
    val (Treap.splitM (m := m) key ident h k t) = t.split key ident h k
  | .leaf => by simp [Treap.splitM, Treap.split]
  | .node l a r _ _ => by
    unfold Treap.splitM Treap.split
    split
    · simp [val_splitM k r, Treap.mkM, Treap.mk]
    · simp [val_splitM k l, Treap.mkM, Treap.mk]

open Valued in
theorem val_insertM {m : Type → Type} [Monad m] [Tick m] [Valued m] (a : α) : ∀ t : Treap α,
    val (Treap.insertM (m := m) key ident h a t) = t.insert key ident h a
  | .leaf => by simp [Treap.insertM, Treap.insert, Treap.mkM, Treap.mk]
  | .node l b r lab sz => by
    unfold Treap.insertM Treap.insert
    split
    · simp [val_splitM, Treap.mkM, Treap.mk]
    · split
      · simp [val_insertM a l, Treap.mkM, Treap.mk]
      · simp [val_insertM a r, Treap.mkM, Treap.mk]

open Counted in
/-- **A split hashes at most once per level of the treap.** -/
theorem split_hashes (k : Key) : ∀ t : Treap α,
    (cost (Treap.splitM (m := Counted) key ident h k t)).hashes ≤ t.height
  | .leaf => by simp [Treap.splitM, Treap.height]
  | .node l a r _ _ => by
    unfold Treap.splitM
    split
    · have := split_hashes k r
      simp only [cost_bind, cost_pure, Treap.mkM, Meter.hashes_add, cost_hashM,
        Meter.add_zero, Treap.height]
      omega
    · have := split_hashes k l
      simp only [cost_bind, cost_pure, Treap.mkM, Meter.hashes_add, cost_hashM,
        Meter.add_zero, Treap.height]
      omega

open Counted in
/-- **An insert hashes at most once per level of the treap, and once
more.** -/
theorem insert_hashes (a : α) : ∀ t : Treap α,
    (cost (Treap.insertM (m := Counted) key ident h a t)).hashes ≤ t.height + 1
  | .leaf => by simp [Treap.insertM, Treap.mkM, Treap.height]
  | .node l b r lab sz => by
    unfold Treap.insertM
    split
    · have := split_hashes key ident h (key a) (.node l b r lab sz)
      simp only [cost_bind, cost_pure, Treap.mkM, Meter.hashes_add, cost_hashM, Meter.add_zero] at *
      omega
    · split
      · have := insert_hashes a l
        simp only [cost_bind, cost_pure, Treap.mkM, Meter.hashes_add, cost_hashM, Meter.add_zero,
          Treap.height]
        omega
      · have := insert_hashes a r
        simp only [cost_bind, cost_pure, Treap.mkM, Meter.hashes_add, cost_hashM, Meter.add_zero,
          Treap.height]
        omega

end

end Engine.Sync
