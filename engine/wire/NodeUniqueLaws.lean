import engine.wire.IOLaws
import engine.wire.Loop
import engine.wire.RetryOrderLaws
import engine.core.WindowIndex

namespace Engine.Sync.NodeUnique
attribute [local instance] Engine.lawfulBEqByteArray
set_option linter.unusedSectionVars false

/-- A refinement of the actual monadic action: it is the erasure of an action
whose returned value carries the invariant. Errors, divergence and native
implementation contracts are not asserted away by this returned-value law. -/
def Ensures {m : Type → Type} [Monad m] {α : Type} (p : m α) (P : α → Prop) : Prop :=
  ∃ checked : m {a // P a}, p = Subtype.val <$> checked

namespace Ensures
variable {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type}

theorem pure' {a : α} {P : α → Prop} (h : P a) : Ensures (pure a : m α) P :=
  ⟨pure ⟨a, h⟩, by simp⟩

theorem any (p : m α) : Ensures p (fun _ => True) :=
  ⟨(fun a => ⟨a, True.intro⟩) <$> p, by simp [Functor.map_map]⟩

theorem bind' {p : m α} {k : α → m β} {P : α → Prop} {Q : β → Prop}
    (hp : Ensures p P) (hk : ∀ a, P a → Ensures (k a) Q) : Ensures (p >>= k) Q := by
  classical
  obtain ⟨checked, eq⟩ := hp
  let next (a : {a // P a}) : m {b // Q b} := (hk a.val a.property).choose
  refine ⟨checked >>= next, ?_⟩
  rw [eq]
  simp only [map_bind, bind_map_left]
  apply bind_congr
  intro a
  exact (hk a.val a.property).choose_spec

theorem bind_any (p : m α) {k : α → m β} {Q : β → Prop}
    (hk : ∀ a, Ensures (k a) Q) : Ensures (p >>= k) Q :=
  bind' (any p) (fun a _ => hk a)

theorem mono {p : m α} {P Q : α → Prop} (hp : Ensures p P)
    (h : ∀ a, P a → Q a) : Ensures p Q := by
  obtain ⟨checked, eq⟩ := hp
  refine ⟨(fun a => ⟨a.val, h a.val a.property⟩) <$> checked, ?_⟩
  simpa only [Functor.map_map] using eq

theorem forIn' (xs : List α) (b : β) (I : β → Prop)
    {f : α → β → m (ForInStep β)} (initial : I b)
    (body : ∀ a, a ∈ xs → ∀ v, I v → Ensures (f a v) (fun r => I r.value)) :
    Ensures (forIn xs b f) I := by
  induction xs generalizing b with
  | nil => exact pure' initial
  | cons a tail ih =>
    rw [List.forIn_cons]
    apply bind' (body a (by simp) b initial)
    intro next hn
    cases next with
    | done v => exact pure' hn
    | yield v => exact ih v hn (fun a ha v hv => body a (by simp [ha]) v hv)

/-- The projected accumulator follows the actual loop's pure fold, even if
its other fields and the backing monad change arbitrarily. -/
theorem forIn_fold {γ : Type} (xs : List α) (b : β) (project : β → γ)
    (step : γ → α → γ) {f : α → β → m (ForInStep β)}
    (body : ∀ a v, Ensures (f a v)
      (fun r => ∃ next, r = .yield next ∧ project next = step (project v) a)) :
    Ensures (forIn xs b f) (fun v => project v = xs.foldl step (project b)) := by
  induction xs generalizing b with
  | nil => exact pure' rfl
  | cons a tail ih =>
    rw [List.forIn_cons]
    apply bind' (body a b)
    rintro _ ⟨next, rfl, eq⟩
    exact (ih next).mono (fun v h => by simpa only [List.foldl_cons, eq] using h)

theorem state {σ : Type} {p : StateM σ α} {P : α → Prop}
    (h : Ensures p P) (s : σ) : P (p s).1 := by
  obtain ⟨checked, eq⟩ := h
  rw [eq]
  exact (checked s).1.property

end Ensures
/-- The two identifiers used by the actual runtime admission scan. -/
def Shape (n : Node) : List Id × List Id := (n.conns.map Prod.fst, n.retryOrder)
def Valid (n : Node) : Prop := (Shape n).1.Nodup ∧ (Shape n).2.Nodup

theorem boot_valid {F : Type} (fam : Family F) (ops : List Op) (floor : Nat) :
    Valid (Node.boot fam ops floor) := by simp [Valid, Shape, Node.boot]

theorem close_valid (n : Node) (cid : Id) (h : Valid n) : Valid (n.close cid) := by
  refine ⟨?_, h.2⟩
  change ((n.conns.filter _).map Prod.fst).Nodup
  exact h.1.sublist (List.Sublist.map Prod.fst (List.filter_sublist))

theorem drop_valid (n : Node) (cid : Id) (h : Valid n) : Valid (n.drop cid) :=
  close_valid n cid h

theorem fold_drop_valid (ids : List Id) (n : Node) (h : Valid n) :
    Valid (ids.foldl Node.drop n) := by
  induction ids generalizing n with
  | nil => exact h
  | cons cid rest ih => exact ih _ (drop_valid n cid h)

theorem keys_map (conns : List (Id × Conn)) (cid : Id) (c : Conn) :
    (conns.map (fun p => if p.1 = cid then (cid, c) else p)).map Prod.fst =
      conns.map Prod.fst := by
  simp only [List.map_map]
  congr 1
  funext p
  dsimp only [Function.comp_def]
  split <;> simp_all

section
variable {F : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
  [Store F m] [Turn F m] (x : Sync F m)

/-- Successful storage changes no connection identifier or retry queue entry,
even when store implementations and hooks have arbitrary effects. -/
theorem write_shape (n : Node) (ops : List Op) :
    Ensures (n.write x ops) (fun r => Shape r.1 = Shape n) := by
  unfold Node.write
  apply Ensures.bind_any
  intro absent
  try dsimp only
  split
  · exact Ensures.pure' rfl
  · apply Ensures.bind_any
    intro _
    apply Ensures.bind_any
    intro _
    exact Ensures.pure' rfl

theorem put_shape (n : Node) (ops : List Op) (mine : Bool) :
    Ensures (n.put x ops mine) (fun r => Shape r.1 = Shape n) :=
  write_shape x n _

theorem recordGiven_shape (n : Node) (given : List (Id × Id)) :
    Ensures (n.recordGiven x given) (fun r => Shape r = Shape n) := by
  unfold Node.recordGiven
  apply Ensures.bind' (put_shape x n _ true)
  intro r hr
  exact Ensures.pure' hr

private theorem fold_keys (xs : List (Id × Conn)) (acc : List Id) :
    xs.foldl (fun acc p => p.1 :: acc) acc = (xs.map Prod.fst).reverse ++ acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons a xs ih => simp [List.foldl_cons, ih, List.reverse_cons, List.append_assoc]

theorem fanout_shape (n : Node) (ids : List Id) :
    Ensures (n.fanout x ids) (fun r => Shape r.1 = Shape n) := by
  unfold Node.fanout
  refine Ensures.bind' (Ensures.forIn_fold n.conns
    (([], {}, []) : List (Id × Conn) × Acts × List (Id × Id))
    (fun st => st.1.map Prod.fst) (fun acc p => p.1 :: acc) ?_) ?_
  · intro a st
    try dsimp only
    apply Ensures.bind_any
    intro c
    apply Ensures.bind_any
    intro next
    exact Ensures.pure' ⟨_, rfl, rfl⟩
  · intro st hst
    try dsimp only
    apply Ensures.bind' (recordGiven_shape x _ _)
    intro next hnext
    apply Ensures.pure'
    rw [hnext]
    apply Prod.ext
    · change (st.1.reverse.map Prod.fst) = n.conns.map Prod.fst
      rw [List.map_reverse]
      simpa only [fold_keys, List.map_nil, List.append_nil, List.reverse_reverse] using
        congrArg List.reverse hst
    · rfl

theorem store_valid (n : Node) (ops : List Op) (mine : Bool) (h : Valid n) :
    Ensures (n.store x ops mine) (fun r => Valid r.1) := by
  unfold Node.store
  apply Ensures.bind' (put_shape x n ops mine)
  intro first eq
  have hfirst : Valid first.1 := by simpa only [Valid, eq] using h
  try dsimp only
  split
  · exact Ensures.pure' hfirst
  · apply Ensures.bind' (fanout_shape x first.1 first.2)
    intro second eq2
    have hsecond : Valid second.1 := by simpa only [Valid, eq2] using hfirst
    try dsimp only
    simp only [Std.Legacy.Range.forIn_eq_forIn_range']
    refine Ensures.bind' (Ensures.forIn' _ _ (fun r : Node × Acts => Valid r.1) hsecond ?_) ?_
    · intro _ _ st hst
      try dsimp only
      apply Ensures.bind_any
      intro more
      try dsimp only
      split
      · exact Ensures.pure' hst
      · apply Ensures.bind' (put_shape x st.1 more true)
        intro next eq
        have hn : Valid next.1 := by simpa only [Valid, eq] using hst
        try dsimp only
        split
        · exact Ensures.pure' hst
        · apply Ensures.bind' (fanout_shape x next.1 next.2)
          intro last eq
          exact Ensures.pure' (by simpa only [ForInStep.value, Valid, eq] using hn)
    · intro last hlast
      exact Ensures.pure' hlast

theorem open_valid (n : Node) (cid : Id) (addr : ByteArray) (dialer : Bool) (now : Nat)
    (h : Valid n) : Ensures (n.open x cid addr dialer now) (fun r => Valid r.1) := by
  unfold Node.open
  apply Ensures.bind_any
  intro rooms
  apply Ensures.pure'
  refine ⟨List.nodup_cons.mpr ⟨?_, (close_valid n cid h).1⟩, h.2⟩
  simp [Node.setAddr, Node.close]


theorem follow_valid (n : Node) (now : Nat) (h : Valid n) :
    Ensures (n.follow x now) (fun r => Valid r.1) := by
  unfold Node.follow
  apply Ensures.bind_any
  intro est
  try dsimp only
  refine Ensures.bind' (Ensures.forIn' _ _ (fun r : Node × Acts => Valid r.1) h ?_) ?_
  · intro cid _ st hs
    try dsimp only
    split
    · exact Ensures.pure' (drop_valid st.1 cid hs)
    · exact Ensures.pure' hs
  · intro st hs
    try dsimp only
    refine Ensures.bind' (Ensures.forIn' _ _ (fun r : Node × Acts => Valid r.1) hs ?_) ?_
    · intro entry _ st hs
      try dsimp only
      split
      · apply Ensures.bind' (open_valid x st.1 entry.1 entry.2.1 entry.2.2 now hs)
        intro next hn
        exact Ensures.pure' hn
      · exact Ensures.pure' hs
    · intro last hl
      exact Ensures.pure' hl

theorem flush_shape (n : Node) (out : Acts) :
    Ensures (n.flush x out) (fun r => Shape r.1 = Shape n) := by
  unfold Node.flush
  apply Ensures.bind_any
  intro box
  apply Ensures.bind_any
  intro old
  try dsimp only
  split
  · exact Ensures.pure' rfl
  · apply Ensures.bind_any
    intro _
    exact Ensures.pure' rfl

theorem sent_shape (n : Node) (out : Acts) (now : Nat) : Shape (n.sent out now) = Shape n := by
  unfold Shape Node.sent
  simp [List.map_map, Function.comp_def]

theorem finish_valid (n : Node) (out : Acts) (now : Nat) (h : Valid n) :
    Ensures (n.finish x out now) (fun r => Valid r.1) := by
  unfold Node.finish
  apply Ensures.bind' (follow_valid x n now h)
  intro first hf
  try dsimp only
  apply Ensures.bind' (flush_shape x first.1 out)
  intro second eq
  have hs : Valid second.1 := by simpa only [Valid, eq] using hf
  try dsimp only
  apply Ensures.bind_any
  intro retired
  have hd := fold_drop_valid retired second.1 hs
  try dsimp only
  apply Ensures.bind_any
  intro sent
  try dsimp only
  apply Ensures.bind_any
  intro served
  apply Ensures.bind_any
  intro reserved
  try dsimp only
  apply Ensures.bind_any
  intro purged
  apply Ensures.pure'
  simpa only [Valid, Shape, Node.sent, List.map_map, Function.comp_def] using hd

theorem apply_valid (n : Node) (cid : Id) (step : Step) (now : Nat) (h : Valid n) :
    Ensures (n.apply x cid step now) (fun r => Valid r.1) := by
  unfold Node.apply
  split
  · exact Ensures.pure' (drop_valid n cid h)
  · try dsimp only
    apply Ensures.bind' (recordGiven_shape x _ _)
    intro next eq
    have hn : Valid next := by
      unfold Valid
      rw [eq]
      simpa only [Valid, Shape, keys_map] using h
    apply Ensures.bind' (store_valid x next step.take false hn)
    intro next hn
    try dsimp only
    apply Ensures.bind_any
    intro arrived
    try dsimp only
    apply Ensures.bind' (store_valid x next.1 arrived true hn)
    intro last hl
    exact Ensures.pure' hl

theorem serve_shape (n : Node) (cid : Id) (now : Nat) :
    Ensures (n.serveOwed x cid now) (fun r => Shape r.1 = Shape n) := by
  unfold Node.serveOwed
  split
  · exact Ensures.pure' rfl
  · split
    · exact Ensures.pure' rfl
    · apply Ensures.bind_any
      intro c
      try dsimp only
      apply Ensures.bind_any
      intro next
      apply Ensures.pure'
      simp only [Shape, keys_map]

theorem sweep_shape (n : Node) (cid : Id) :
    Ensures (n.sweep x cid) (fun r => Shape r.1 = Shape n) := by
  cases store : x.retryStore <;> simp only [Node.sweep, store]
  all_goals repeat' (first
    | exact Ensures.pure' rfl
    | dsimp only
    | simp only [pure_bind]
    | (apply Ensures.bind_any; intro value)
    | split)

/-- The actual sweep's final queue is unique. Both input facts are later
obtained from boot and actual handler preservation, not network assumptions. -/
theorem sweepAll_valid (n : Node) (ready : List Id) (out : Acts) (h : Valid n) :
    Ensures (n.sweepAll x ready out) (fun r => Valid r.1) := by
  unfold Node.sweepAll
  refine Ensures.bind' (Ensures.forIn' _ _
    (fun st : Node × Acts × List Id × List ByteArray => Shape st.1 = Shape n) rfl ?_) ?_
  · intro cid _ st hs
    try dsimp only
    split
    · exact Ensures.pure' hs
    · try dsimp only
      apply Ensures.bind' (sweep_shape _ st.1 cid)
      intro next hn
      have same : Shape next.1 = Shape n := hn.trans hs
      try dsimp only
      split
      all_goals
        try dsimp only
        split
        all_goals exact Ensures.pure' same
  · intro last hl
    apply Ensures.pure'
    refine ⟨?_, RetryOrder.offered_nodup _ _ (RetryOrder.reconcile_nodup _ _ h.1 h.2)⟩
    exact (congrArg Prod.fst hl) ▸ h.1

theorem onSealed_valid (n : Node) (addr : ByteArray) (opened : Option (Id × ByteArray))
    (now : Nat) (h : Valid n) :
    Ensures (n.onSealed x addr opened now) (fun r => Valid r.1) := by
  unfold Node.onSealed
  split
  · exact Ensures.pure' h
  · split
    · try dsimp only
      refine Ensures.bind' (Ensures.forIn' _ _ (fun st : Node × Acts => Valid st.1) h ?_) ?_
      · intro bytes _ st hs
        try dsimp only
        split
        · apply Ensures.bind_any
          intro c
          apply Ensures.bind_any
          intro step
          apply Ensures.bind' (apply_valid x st.1 _ step now hs)
          intro next hn
          exact Ensures.pure' hn
        · exact Ensures.pure' hs
      · intro next hn
        try dsimp only
        apply Ensures.bind' (serve_shape x next.1 _ now)
        intro served eq
        apply finish_valid
        simpa only [Valid, eq] using hn
    · exact Ensures.pure' h

theorem onFrame_valid (n : Node) (addr bytes : ByteArray) (now : Nat) (h : Valid n) :
    Ensures (n.onFrame x addr bytes now) (fun r => Valid r.1) := by
  unfold Node.onFrame
  split
  · dsimp only
    split
    · exact Ensures.pure' h
    · try dsimp only
      split
      · exact Ensures.pure' h
      · apply Ensures.bind' (write_shape x n _)
        intro next eq
        have hn : Valid next.1 := by simpa only [Valid, eq] using h
        apply Ensures.bind_any
        intro ops
        apply Ensures.bind' (store_valid x next.1 ops true hn)
        intro last hl
        exact finish_valid x last.1 last.2 now hl
  · apply Ensures.bind_any
    intro opened
    exact onSealed_valid x n addr opened now h
  · exact Ensures.pure' h

theorem onTickReserved_valid (n : Node) (now : Nat) (h : Valid n) :
    Ensures (n.onTickReserved x now) (fun r => Valid r.1) := by
  unfold Node.onTickReserved
  apply Ensures.bind_any
  intro ops
  apply Ensures.bind' (store_valid x n ops true h)
  intro first hf
  try dsimp only
  refine Ensures.bind' (Ensures.forIn' _ _ (fun st : Node × Acts × List Id => Valid st.1) hf ?_) ?_
  · intro entry _ st hs
    try dsimp only
    split
    · exact Ensures.pure' hs
    · apply Ensures.bind_any
      intro c
      try dsimp only
      split
      · exact Ensures.pure' hs
      · apply Ensures.bind_any
        intro step
        apply Ensures.bind' (apply_valid x st.1 entry.1 step now hs)
        intro next hn
        try dsimp only
        apply Ensures.bind' (serve_shape _ next.1 entry.1 now)
        intro served eq
        exact Ensures.pure' (by simpa only [ForInStep.value, Valid, eq] using hn)
  · intro next hn
    try dsimp only
    apply Ensures.bind' (sweepAll_valid x next.1 next.2.2 next.2.1 hn)
    intro swept hs
    exact finish_valid x swept.1 swept.2 now hs

theorem onTickDirect_valid (n : Node) (now : Nat) (h : Valid n) :
    Ensures (n.onTickDirect x now) (fun r => Valid r.1) := by
  unfold Node.onTickDirect
  apply Ensures.bind_any
  intro ops
  apply Ensures.bind' (store_valid x n ops true h)
  intro first hf
  try dsimp only
  refine Ensures.bind' (Ensures.forIn' _ _ (fun st : Node × Acts => Valid st.1) hf ?_) ?_
  · intro entry _ st hs
    try dsimp only
    split
    · exact Ensures.pure' hs
    · apply Ensures.bind_any
      intro c
      try dsimp only
      split
      · exact Ensures.pure' hs
      · apply Ensures.bind_any
        intro step
        apply Ensures.bind' (apply_valid x st.1 entry.1 step now hs)
        intro next hn
        try dsimp only
        apply Ensures.bind' (sweep_shape _ next.1 entry.1)
        intro swept eq
        have hs : Valid swept.1 := by simpa only [Valid, eq] using hn
        try dsimp only
        apply Ensures.bind' (serve_shape _ swept.1 entry.1 now)
        intro served eq
        exact Ensures.pure' (by simpa only [ForInStep.value, Valid, eq] using hs)
  · intro next hn
    exact finish_valid x next.1 next.2 now hn

theorem onTick_valid (n : Node) (now : Nat) (h : Valid n) :
    Ensures (n.onTick x now) (fun r => Valid r.1) := by
  unfold Node.onTick
  split
  · exact onTickReserved_valid x n now h
  · exact onTickDirect_valid x n now h

theorem onWrite_valid (n : Node) (ops : List Op) (now : Nat) (h : Valid n) :
    Ensures (n.onWrite x ops now) (fun r => Valid r.1) := by
  unfold Node.onWrite
  apply Ensures.bind' (store_valid x n ops true h)
  intro next hn
  exact finish_valid x _ _ now hn

theorem onClose_valid (n : Node) (addr : ByteArray) (now : Nat) (h : Valid n) :
    Ensures (n.onClose x addr now) (fun r => Valid r.1) :=
  finish_valid x _ _ now (fold_drop_valid _ n h)

/-- The actual dispatch preserves connection-ID and retry-order uniqueness
for every input, arbitrary effectful hooks and every lawful backing monad. -/
theorem step_valid (n : Node) (input : Node.Input) (now : Nat) (h : Valid n) :
    Ensures (n.step x input now) (fun r => Valid r.1) := by
  cases input with
  | write ops => exact onWrite_valid x n ops now h
  | frame addr bytes => exact onFrame_valid x n addr bytes now h
  | tick => exact onTick_valid x n now h
  | close addr => exact onClose_valid x n addr now h

end
/-- The actual SQLite-backed action called by TCP has the same checked-return
factorization. This does not assert that native SQLite/IO returns or succeeds. -/
theorem sql_step_valid {F : Type} [Codec F] [SortKey F] (x : Sync F (SqlM F))
    (db : Db) (n : Node) (input : Node.Input) (now : Nat) (h : Valid n) :
    Ensures ((n.step x input now).run db) (fun r => Valid r.1) := by
  letI : LawfulMonad IO := io_lawful
  letI : LawfulMonad (SqlM F) := inferInstanceAs (LawfulMonad (ReaderT Db IO))
  obtain ⟨checked, eq⟩ := step_valid x n input now h
  exact ⟨checked db, congrArg (fun p : SqlM F (Node × Effects) => p db) eq⟩

end Engine.Sync.NodeUnique
