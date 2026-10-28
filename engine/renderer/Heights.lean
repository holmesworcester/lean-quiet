/-
The heights of the conversation's rows, in a tree whose nodes hold their
sums (docs/PERF.md: the frame's work).

The frame needs, every frame: the row at the scroll offset, the bottoms
of the rows from there to the top of the window, and the content's
height; and, when a row is laid out again or an older page loads, a
height changed or added. Over an array of heights the first two walk
every loaded row below the window (today's `bottoms`, `rowAt` and the
mount and paint loops: 4,981 rows walked per frame, scrolled back that
far). Here each costs a step per level of the tree, and the tree has
about log₂ n levels:

- `find t b`: the row whose span holds offset b (`find_spec`: the rows
  below it end at or under b, and it ends above b).
- `start t i`: where row i starts, the heights of the rows below it
  (`start_eq`).
- `set t i h`: row i's height becomes h (`set_toList`).
- `push`: a row more, at the top; the tree doubles when full, so it stays
  perfect of depth d with 2^(d-1) < rows ≤ 2^d (`push_ok`).

Each is written once over a monad with a tick per level (`findM`,
`startM`, `setM`): the code that runs at `Id`, counted at `Counted`,
where it costs at most the tree's depth (`findM_cost`, `startM_cost`,
`setM_cost`). The mutant control, the walk over every row below
(`bottomM`), costs a step per row (tests/engine/CostCheck.lean).
-/
import engine.core.Cost

namespace Heights
open Engine

/-- Heights at the leaves; a node holds its sum and its leaf count. -/
inductive T where
  | leaf (h : Nat)
  | node (l r : T) (s n : Nat)
  deriving Inhabited

namespace T

def sum : T → Nat
  | leaf h => h
  | node _ _ s _ => s

def size : T → Nat
  | leaf _ => 1
  | node _ _ _ n => n

@[simp] theorem sum_leaf (h : Nat) : (leaf h).sum = h := rfl
@[simp] theorem sum_node (l r : T) (s n : Nat) : (node l r s n).sum = s := rfl
@[simp] theorem size_leaf (h : Nat) : (leaf h).size = 1 := rfl
@[simp] theorem size_node (l r : T) (s n : Nat) : (node l r s n).size = n := rfl

/-- A node over l and r, its sum and count from theirs. -/
def mk (l r : T) : T := node l r (l.sum + r.sum) (l.size + r.size)

def toList : T → List Nat
  | leaf h => [h]
  | node l r _ _ => l.toList ++ r.toList

def depth : T → Nat
  | leaf _ => 0
  | node l r _ _ => max l.depth r.depth + 1

/-- Every node's sum and count are its children's. -/
def WF : T → Prop
  | leaf _ => True
  | node l r s n => WF l ∧ WF r ∧ s = l.sum + r.sum ∧ n = l.size + r.size

/-- A perfect tree of depth d. -/
def Perfect : Nat → T → Prop
  | 0, leaf _ => True
  | d + 1, node l r _ _ => Perfect d l ∧ Perfect d r
  | _, _ => False

/-- 2^d leaves of height 0, sharing one subtree per level: d nodes made. -/
def zeros : Nat → T
  | 0 => leaf 0
  | d + 1 => let z := zeros d; mk z z

section
variable {m : Type → Type} [Monad m] [Tick m]

/-- The row whose span holds offset b, from the bottom. -/
def findM : T → Nat → m Nat
  | leaf _, _ => pure 0
  | node l r _ _, b => do
    tick { work := 1 }
    if b < l.sum then findM l b else return l.size + (← findM r (b - l.sum))

/-- The heights of the first i rows. -/
def startM : T → Nat → m Nat
  | leaf h, i => pure (if i = 0 then 0 else h)
  | node l r _ _, i => do
    tick { work := 1 }
    if i ≤ l.size then startM l i else return l.sum + (← startM r (i - l.size))

/-- Row i's height set to h. -/
def setM : T → Nat → Nat → m T
  | leaf _, _, h => pure (leaf h)
  | node l r _ _, i, h => do
    tick { work := 1 }
    if i < l.size then return mk (← setM l i h) r else return mk l (← setM r (i - l.size) h)

end

/-- What runs: the same code, at `Id`. -/
def find (t : T) (b : Nat) : Nat := Id.run (findM t b)
def start (t : T) (i : Nat) : Nat := Id.run (startM t i)
def set (t : T) (i h : Nat) : T := Id.run (setM t i h)

/-! ## What they compute -/

@[simp] theorem find_leaf (h b : Nat) : find (leaf h) b = 0 := rfl
theorem find_node (l r : T) (s n b : Nat) :
    find (node l r s n) b = if b < l.sum then find l b else l.size + find r (b - l.sum) := by
  simp only [find, findM, tick]
  split <;> rfl

@[simp] theorem start_leaf (h i : Nat) : start (leaf h) i = if i = 0 then 0 else h := rfl
theorem start_node (l r : T) (s n i : Nat) :
    start (node l r s n) i = if i ≤ l.size then start l i else l.sum + start r (i - l.size) := by
  simp only [start, startM, tick]
  split <;> rfl

@[simp] theorem set_leaf (h i k : Nat) : set (leaf h) i k = leaf k := rfl
theorem set_node (l r : T) (s n i k : Nat) :
    set (node l r s n) i k = if i < l.size then mk (set l i k) r else mk l (set r (i - l.size) k) := by
  simp only [set, setM, tick]
  split <;> rfl

theorem wf_mk {l r : T} (hl : WF l) (hr : WF r) : WF (mk l r) := ⟨hl, hr, rfl, rfl⟩

theorem sum_eq : ∀ {t : T}, WF t → t.sum = t.toList.sum
  | leaf h, _ => by simp [sum, toList]
  | node l r s n, ⟨hl, hr, hs, _⟩ => by
    simp only [sum_node, toList, List.sum_append, hs, sum_eq hl, sum_eq hr]

theorem size_eq : ∀ {t : T}, WF t → t.size = t.toList.length
  | leaf _, _ => rfl
  | node l r s n, ⟨hl, hr, _, hn⟩ => by
    simp only [size_node, toList, List.length_append, hn, size_eq hl, size_eq hr]

theorem size_pos : ∀ {t : T}, WF t → 0 < t.size
  | leaf _, _ => Nat.one_pos
  | node l r _ _, ⟨hl, _, _, hn⟩ => by simp only [size_node, hn]; have := size_pos hl; omega

/-- **Where row i starts**: the heights of the rows below it. -/
theorem start_eq : ∀ {t : T}, WF t → ∀ i, start t i = (t.toList.take i).sum
  | leaf h, _, i => by
    cases i <;> simp [toList]
  | node l r s n, ⟨hl, hr, hs, hn⟩, i => by
    rw [start_node]
    simp only [toList, List.take_append, List.sum_append]
    split
    · rename_i hi
      rw [start_eq hl, Nat.sub_eq_zero_of_le (by rw [← size_eq hl]; exact hi)]
      simp
    · rename_i hi
      have hlen : l.toList.length ≤ i := by rw [← size_eq hl]; omega
      rw [start_eq hr, sum_eq hl, size_eq hl, List.take_of_length_le hlen]

theorem find_lt : ∀ {t : T}, WF t → ∀ {b}, b < t.sum → find t b < t.size
  | leaf _, _, _, _ => Nat.one_pos
  | node l r s n, ⟨hl, hr, hs, hn⟩, b, hb => by
    rw [find_node]
    simp only [size_node, hn]
    simp only [sum_node, hs] at hb
    split
    · rename_i h; have := find_lt hl h; omega
    · rename_i h; have := find_lt hr (b := b - l.sum) (by omega); omega

/-- **The row at offset b**: the rows below it end at or under b, and it
ends above b. -/
theorem find_spec : ∀ {t : T}, WF t → ∀ {b}, b < t.sum →
    start t (find t b) ≤ b ∧ b < start t (find t b + 1)
  | leaf h, _, b, hb => by simp at hb; simp [find, findM, start, startM]; omega
  | node l r s n, ⟨hl, hr, hs, hn⟩, b, hb => by
    simp only [sum_node, hs] at hb
    rw [find_node]
    split
    · rename_i h
      have hlt := find_lt hl h
      rw [start_node, start_node, ite_eq_left (Nat.le_of_lt hlt), ite_eq_left (show l.find b + 1 ≤ l.size from hlt)]
      exact find_spec hl h
    · rename_i h
      have ih := find_spec hr (b := b - l.sum) (by omega)
      have hp : ∀ j, start (node l r s n) (l.size + j) = l.sum + start r j := by
        intro j
        rw [start_node]
        split
        · rename_i hj
          have : j = 0 := by omega
          subst this
          rw [start_eq hl, start_eq hr, List.take_of_length_le (by rw [← size_eq hl]; omega),
            sum_eq hl]
          simp
        · rw [Nat.add_sub_cancel_left]
      rw [hp, Nat.add_assoc, hp]
      omega

/-- **A height set**: the list with row i's height h, the tree still
well formed, its size and depth unchanged. -/
theorem set_toList : ∀ {t : T}, WF t → ∀ {i}, i < t.size → ∀ k,
    (set t i k).toList = t.toList.set i k ∧ WF (set t i k) ∧ (set t i k).size = t.size ∧
      (set t i k).depth = t.depth
  | leaf h, _, i, hi, k => by
    simp only [size_leaf] at hi
    have : i = 0 := by omega
    subst this
    exact ⟨rfl, trivial, rfl, rfl⟩
  | node l r s n, ⟨hl, hr, hs, hn⟩, i, hi, k => by
    simp only [size_node, hn] at hi
    rw [set_node]
    split
    · rename_i h
      obtain ⟨e, w, z, d⟩ := set_toList hl h k
      refine ⟨?_, wf_mk w hr, ?_, ?_⟩
      · simp only [mk, toList, e, List.set_append, ← size_eq hl, h, ite_true]
      · simp only [mk, size_node, z, hn]
      · simp only [mk, depth, d]
    · rename_i h
      obtain ⟨e, w, z, d⟩ := set_toList hr (i := i - l.size) (by omega) k
      refine ⟨?_, wf_mk hl w, ?_, ?_⟩
      · simp only [mk, toList, e, List.set_append, ← size_eq hl, h, ite_false]
      · simp only [mk, size_node, z, hn]
      · simp only [mk, depth, d]

/-! ## Perfect trees: depth log₂ of the rows -/

theorem perfect_depth : ∀ {d : Nat} {t : T}, Perfect d t → t.depth = d
  | 0, leaf _, _ => rfl
  | d + 1, node l r _ _, ⟨hl, hr⟩ => by
    simp only [depth, perfect_depth hl, perfect_depth hr, Nat.max_self]
  | 0, node .., h => absurd h id
  | _ + 1, leaf _, h => absurd h id

theorem perfect_size : ∀ {d : Nat} {t : T}, WF t → Perfect d t → t.size = 2 ^ d
  | 0, leaf _, _, _ => rfl
  | d + 1, node l r _ _, ⟨wl, wr, _, hn⟩, ⟨hl, hr⟩ => by
    simp only [size_node, hn, perfect_size wl hl, perfect_size wr hr, Nat.pow_succ]; omega
  | 0, node .., _, h => absurd h id
  | _ + 1, leaf _, _, h => absurd h id

theorem zeros_ok : ∀ d, WF (zeros d) ∧ Perfect d (zeros d) ∧ (zeros d).sum = 0 ∧
    (zeros d).toList = List.replicate (2 ^ d) 0
  | 0 => ⟨trivial, trivial, rfl, rfl⟩
  | d + 1 => by
    obtain ⟨w, p, s, l⟩ := zeros_ok d
    refine ⟨wf_mk w w, ⟨p, p⟩, by simp [zeros, mk, s], ?_⟩
    simp only [zeros, mk, toList, l, Nat.pow_succ, Nat.mul_two, List.replicate_append_replicate]

theorem set_perfect : ∀ {d : Nat} {t : T}, WF t → Perfect d t → ∀ {i}, i < t.size → ∀ k,
    Perfect d (set t i k)
  | 0, leaf _, _, _, _, _, _ => trivial
  | d + 1, node l r s n, ⟨wl, wr, _, hn⟩, ⟨pl, pr⟩, i, hi, k => by
    simp only [size_node, hn] at hi
    rw [set_node]
    split
    · rename_i h; exact ⟨set_perfect wl pl h k, pr⟩
    · rename_i h; exact ⟨pl, set_perfect wr pr (i := i - l.size) (by omega) k⟩
  | 0, node .., _, h, _, _, _ => absurd h id
  | _ + 1, leaf _, _, h, _, _, _ => absurd h id

end T

/-! ## The rows: a perfect tree, the rows first, then zeros -/

/-- n rows' heights in a perfect tree of depth d, 2^(d-1) < n ≤ 2^d (or
d = 0), its leaves past the rows 0. -/
structure Rows where
  t : T := .leaf 0
  n : Nat := 0
  d : Nat := 0

namespace Rows

/-- What the tree must be. -/
def Ok (r : Rows) (hs : List Nat) : Prop :=
  r.t.WF ∧ r.t.Perfect r.d ∧ r.n = hs.length ∧ r.t.toList = hs ++ List.replicate (2 ^ r.d - r.n) 0 ∧
    (r.d = 0 ∨ 2 ^ (r.d - 1) < r.n)

theorem ok_empty : Ok {} [] := ⟨trivial, trivial, rfl, rfl, Or.inl rfl⟩

/-- A row more, at the top: in place while there is room, else in a tree
of twice the room. -/
def push (r : Rows) (h : Nat) : Rows :=
  if r.n < 2 ^ r.d then { r with t := r.t.set r.n h, n := r.n + 1 }
  else { t := (T.mk r.t (T.zeros r.d)).set r.n h, n := r.n + 1, d := r.d + 1 }

theorem replicate_set {k : Nat} (hk : 0 < k) (hs : List Nat) (h : Nat) :
    (hs ++ List.replicate k 0).set hs.length h = (hs ++ [h]) ++ List.replicate (k - 1) 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp [List.replicate_succ]

/-- **A push keeps the tree what it must be**: perfect, the rows then
zeros, and its depth the least that holds them. -/
theorem push_ok {r : Rows} {hs : List Nat} (ok : r.Ok hs) (h : Nat) : (r.push h).Ok (hs ++ [h]) := by
  obtain ⟨w, p, hn, hl, hd⟩ := ok
  have size := T.perfect_size w p
  have pos := Nat.two_pow_pos r.d
  have hle : r.n ≤ 2 ^ r.d := by
    have := T.size_eq w
    rw [size, hl, List.length_append, List.length_replicate, ← hn] at this
    omega
  unfold push
  split
  · rename_i room
    have hi : r.n < r.t.size := by rw [size]; exact room
    obtain ⟨e, w', _, _⟩ := T.set_toList w hi h
    refine ⟨w', T.set_perfect w p hi h, ?_, ?_, ?_⟩
    · show r.n + 1 = (hs ++ [h]).length
      simp [hn]
    · show (r.t.set r.n h).toList = (hs ++ [h]) ++ List.replicate (2 ^ r.d - (r.n + 1)) 0
      rw [e, hl, hn, replicate_set (by omega), Nat.sub_sub]
    · rcases hd with hd | hd
      · exact Or.inl hd
      · exact Or.inr (by show 2 ^ (r.d - 1) < r.n + 1; omega)
  · rename_i full
    have hfull : r.n = 2 ^ r.d := by omega
    obtain ⟨zw, zp, _, zl⟩ := T.zeros_ok r.d
    have wm := T.wf_mk w zw
    have pm : T.Perfect (r.d + 1) (T.mk r.t (T.zeros r.d)) := ⟨p, zp⟩
    have sm : (T.mk r.t (T.zeros r.d)).size = 2 ^ (r.d + 1) := T.perfect_size wm pm
    have hi : r.n < (T.mk r.t (T.zeros r.d)).size := by rw [sm, Nat.pow_succ]; omega
    obtain ⟨e, w', _, _⟩ := T.set_toList wm hi h
    refine ⟨w', T.set_perfect wm pm hi h, ?_, ?_, ?_⟩
    · show r.n + 1 = (hs ++ [h]).length
      simp [hn]
    · show ((T.mk r.t (T.zeros r.d)).set r.n h).toList =
        (hs ++ [h]) ++ List.replicate (2 ^ (r.d + 1) - (r.n + 1)) 0
      rw [e]
      show (r.t.toList ++ (T.zeros r.d).toList).set r.n h = _
      rw [hl, zl, show 2 ^ r.d - r.n = 0 by omega, List.replicate_zero, List.append_nil, hn,
        replicate_set pos]
      congr 2
      rw [Nat.pow_succ]; omega
    · right
      show 2 ^ (r.d + 1 - 1) < r.n + 1
      rw [Nat.add_sub_cancel]; omega

end Rows

/-! ## What they cost: a step per level -/

namespace T
open Engine.Counted

theorem findM_cost : ∀ (t : T) (b : Nat), cost (findM (m := Counted) t b) ≤ { work := t.depth }
  | leaf _, _ => by simp [findM]; meter_le
  | node l r _ _, b => by
    simp only [findM]
    have hl := findM_cost l b
    have hr := findM_cost r (b - l.sum)
    split
    · simp only [cost_bind, cost_tick]
      rw [Meter.le_iff] at hl ⊢
      simp only [Meter.work_add, Meter.reads_add, Meter.lists_add, Meter.writes_add, Meter.hashes_add,
        Meter.hashed_add, Meter.spawns_add, Meter.copied_add, Meter.seeks_add, Meter.rows_add, depth] at *
      omega
    · simp only [cost_bind, cost_tick, cost_map, bind_pure_comp]
      rw [Meter.le_iff] at hr ⊢
      simp only [Meter.work_add, Meter.reads_add, Meter.lists_add, Meter.writes_add, Meter.hashes_add,
        Meter.hashed_add, Meter.spawns_add, Meter.copied_add, Meter.seeks_add, Meter.rows_add, depth] at *
      omega

theorem startM_cost : ∀ (t : T) (i : Nat), cost (startM (m := Counted) t i) ≤ { work := t.depth }
  | leaf _, _ => by simp [startM]; meter_le
  | node l r _ _, i => by
    simp only [startM]
    have hl := startM_cost l i
    have hr := startM_cost r (i - l.size)
    split
    · simp only [cost_bind, cost_tick]
      rw [Meter.le_iff] at hl ⊢
      simp only [Meter.work_add, Meter.reads_add, Meter.lists_add, Meter.writes_add, Meter.hashes_add,
        Meter.hashed_add, Meter.spawns_add, Meter.copied_add, Meter.seeks_add, Meter.rows_add, depth] at *
      omega
    · simp only [cost_bind, cost_tick, cost_map, bind_pure_comp]
      rw [Meter.le_iff] at hr ⊢
      simp only [Meter.work_add, Meter.reads_add, Meter.lists_add, Meter.writes_add, Meter.hashes_add,
        Meter.hashed_add, Meter.spawns_add, Meter.copied_add, Meter.seeks_add, Meter.rows_add, depth] at *
      omega

theorem setM_cost : ∀ (t : T) (i k : Nat), cost (setM (m := Counted) t i k) ≤ { work := t.depth }
  | leaf _, _, _ => by simp [setM]; meter_le
  | node l r _ _, i, k => by
    simp only [setM]
    have hl := setM_cost l i k
    have hr := setM_cost r (i - l.size) k
    split
    · simp only [cost_bind, cost_tick, cost_map, bind_pure_comp]
      rw [Meter.le_iff] at hl ⊢
      simp only [Meter.work_add, Meter.reads_add, Meter.lists_add, Meter.writes_add, Meter.hashes_add,
        Meter.hashed_add, Meter.spawns_add, Meter.copied_add, Meter.seeks_add, Meter.rows_add, depth] at *
      omega
    · simp only [cost_bind, cost_tick, cost_map, bind_pure_comp]
      rw [Meter.le_iff] at hr ⊢
      simp only [Meter.work_add, Meter.reads_add, Meter.lists_add, Meter.writes_add, Meter.hashes_add,
        Meter.hashed_add, Meter.spawns_add, Meter.copied_add, Meter.seeks_add, Meter.rows_add, depth] at *
      omega

end T

/-- **On the rows' tree, finding the row at an offset, where a row
starts, and setting a height each cost at most d steps**, where
2^(d-1) < n for n rows: d ≤ log₂ n + 1, however far back the list is
scrolled. -/
theorem rows_cost {r : Rows} {hs : List Nat} (ok : r.Ok hs) (b i k : Nat) :
    Counted.cost (T.findM (m := Counted) r.t b) ≤ { work := r.d } ∧
    Counted.cost (T.startM (m := Counted) r.t i) ≤ { work := r.d } ∧
    Counted.cost (T.setM (m := Counted) r.t i k) ≤ { work := r.d } := by
  have := T.perfect_depth ok.2.1
  rw [← this]
  exact ⟨T.findM_cost _ _, T.startM_cost _ _, T.setM_cost _ _ _⟩

/-- The negative control: where row i starts, by walking the rows below
it, as `bottoms` does: a step per row. -/
def bottomM {m : Type → Type} [Monad m] [Tick m] : List Nat → Nat → m Nat
  | [], _ => pure 0
  | _, 0 => pure 0
  | h :: rest, i + 1 => do tick { work := 1 }; return h + (← bottomM rest i)

end Heights
