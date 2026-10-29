/-
What a connection gives as a notice (docs/REMOVAL.md), proven of
`Conn`'s code run on the model store. A notice is (room r, op x): x and
its requirement closure in r, given once and never taken. The node runs
`notify` on a connection where it stores ops (`filedGive`) and on the
clock (`tickGive`).

- `closure`: the notice walk (`closureOps`) returns only stored ops of
  room r in x's requirement closure, and, when that closure has at most
  `fuel` ids, every one of them that is stored.
- `notice_sent`: a connection carrying a notice it has not given gives
  it on its next `filedGive`, and on a `tickGive` whose tick does not
  drop it: every op of x's closure in r that the peer is not known to
  hold goes out, x is reported given and recorded in `given`.
- `notice_send`: everything those steps send is a sync wire op or a
  stored op of the closure of a notice the connection carried and had
  not given, and they take nothing. `filed_send` and `tick_send` stand:
  `filed` and `tick` themselves send wire ops only.
- `notice_once`: once a connection has given all its notices, those
  steps send wire ops only again. `recv` never gives one (`recv_send`).
-/
import ops.sync.ConnLaws
import ops.sync.OfferLaws
import ops.sync.Notice

namespace Engine.Sync

section
variable {F : Type} (fam : Family F)

/-- y is x, or required (recursively) by an op of room r that x reaches:
x's requirement closure in r. An op of another room is not followed. -/
inductive ReachIn (ops : Id → Option Op) (r x : Id) : Id → Prop
  | refl : ReachIn ops r x x
  | step {y : Id} {o : Op} {z : Id} : ReachIn ops r x y → ops y = some o → fam.room o = some r →
      z ∈ o.reqs → ReachIn ops r x z

/-- x's closure in r has at most n ids. -/
def ClosureWithin (ops : Id → Option Op) (r x : Id) (n : Nat) : Prop :=
  ∃ L : List Id, L.length ≤ n ∧ ∀ y, ReachIn fam ops r x y → y ∈ L

/-- Ops are stored under their own ids (`Inv.key`). -/
def Keyed (s : DB F) : Prop := ∀ y o, s.ops y = some o → o.id = y

/-- What giving notice (r, x) in a step means: x is reported given and
recorded, and every stored op of x's closure in r the peer is not known
to hold goes out. -/
def Gives (s : DB F) (c : Conn) (r x : Id) (st : Step) : Prop :=
  x ∈ st.given ∧ has st.conn.given x = true ∧
    ∀ y o, ReachIn fam s.ops r x y → s.ops y = some o → fam.room o = some r →
      c.known.contains y = false → o ∈ st.send

/-- An op of a notice (r, x) the connection carries and has not given:
a stored op of x's closure in r. -/
def NoticeOp (s : DB F) (c : Conn) (o : Op) : Prop :=
  ∃ r x, (r, x) ∈ c.notices ∧ has c.given x = false ∧
    ∃ y, s.ops y = some o ∧ fam.room o = some r ∧ ReachIn fam s.ops r x y

end

section
variable {F : Type} (fam : Family F) (cfg : Config)

theorem has_cons_self (y : Id) (l : List Id) : has (y :: l) y = true :=
  (Engine.has_iff _ _).2 (List.mem_cons_self ..)

theorem has_cons_of (y : Id) {l : List Id} {z : Id} (h : has l z = true) : has (y :: l) z = true :=
  (Engine.has_iff _ _).2 (List.mem_cons_of_mem _ ((Engine.has_iff _ _).1 h))

theorem has_of_cons {y z : Id} {l : List Id} (h : has (y :: l) z = false) : has l z = false := by
  cases hl : has l z
  · rfl
  · rw [has_cons_of y hl] at h; cases h

/-! ## The walk -/

theorem closureOps_state (s : DB F) (r : Id) (fuel : Nat) : ∀ (todo seen : List Id),
    ((closureOps fam r fuel todo seen : Model F (List Op)).run s).2 = s := by
  induction fuel with
  | zero => intro todo seen; rw [closureOps]; rfl
  | succ n ih =>
    intro todo
    induction todo with
    | nil => intro seen; rw [closureOps_nil]; rfl
    | cons y rest ihr =>
      intro seen
      rw [closureOps]
      split
      · exact ihr seen
      · simp only [Model.run_bind, run_getOp]
        cases s.ops y with
        | none => exact ih _ _
        | some o =>
          dsimp only
          split
          · simp only [Model.run_bind, Model.run_pure]; exact ih _ _
          · exact ih _ _

/-- What the walk returns is stored, of room r, and reached from x. -/
theorem closureOps_sound (s : DB F) (r x : Id) (fuel : Nat) : ∀ (todo seen : List Id),
    (∀ y ∈ todo, ReachIn fam s.ops r x y) →
    ∀ o ∈ ((closureOps fam r fuel todo seen : Model F (List Op)).run s).1,
      ∃ y, s.ops y = some o ∧ fam.room o = some r ∧ ReachIn fam s.ops r x y := by
  induction fuel with
  | zero => intro todo seen _ o ho; rw [closureOps] at ho; cases ho
  | succ n ih =>
    intro todo
    induction todo with
    | nil => intro seen _ o ho; rw [closureOps_nil] at ho; cases ho
    | cons y rest ihr =>
      intro seen ht o ho
      have hrest : ∀ z ∈ rest, ReachIn fam s.ops r x z := fun z hz => ht z (List.mem_cons_of_mem _ hz)
      rw [closureOps] at ho
      split at ho
      · exact ihr seen hrest o ho
      · simp only [Model.run_bind, run_getOp] at ho
        cases hy : s.ops y with
        | none => rw [hy] at ho; exact ih _ _ hrest o ho
        | some p =>
          rw [hy] at ho
          dsimp only at ho
          split at ho
          · rename_i hroom
            simp only [Model.run_bind, Model.run_pure, List.mem_cons] at ho
            rcases ho with rfl | ho
            · exact ⟨y, hy, hroom, ht y (List.mem_cons_self ..)⟩
            · refine ih _ _ (fun z hz => ?_) o ho
              rcases List.mem_append.1 hz with hz | hz
              · exact .step (ht y (List.mem_cons_self ..)) hy hroom hz
              · exact hrest z hz
          · exact ih _ _ hrest o ho

/-- The walk's invariant: what it has seen is closed but for what it
still has to do; so, with fuel for every id of the closure, what it sees
in the end is closed, and it returns every stored op of room r it saw
there for the first time. -/
theorem closureOps_complete (s : DB F) (r x : Id) (L : List Id)
    (hL : ∀ y, ReachIn fam s.ops r x y → y ∈ L) (fuel : Nat) : ∀ (todo seen : List Id),
    seen.Nodup → (∀ y ∈ seen, ReachIn fam s.ops r x y) → (∀ y ∈ todo, ReachIn fam s.ops r x y) →
    L.length ≤ fuel + seen.length →
    (∀ z ∈ seen, ∀ o, s.ops z = some o → fam.room o = some r → ∀ w ∈ o.reqs, w ∈ seen ∨ w ∈ todo) →
    ∃ S : List Id, (∀ y ∈ seen, y ∈ S) ∧ (∀ y ∈ todo, y ∈ S) ∧
      (∀ z ∈ S, ∀ o, s.ops z = some o → fam.room o = some r → ∀ w ∈ o.reqs, w ∈ S) ∧
      (∀ y ∈ S, y ∉ seen → ∀ o, s.ops y = some o → fam.room o = some r →
        o ∈ ((closureOps fam r fuel todo seen : Model F (List Op)).run s).1) := by
  induction fuel with
  | zero =>
    intro todo seen hnd hs ht hlen hcl
    -- no fuel: everything to do was seen already
    have hsub : ∀ y ∈ todo, y ∈ seen := by
      intro y hy
      by_cases hin : y ∈ seen
      · exact hin
      · have h1 : (y :: seen).Nodup := List.nodup_cons.2 ⟨hin, hnd⟩
        have h2 : (y :: seen) ⊆ L := by
          intro z hz
          rcases List.mem_cons.1 hz with rfl | hz
          · exact hL _ (ht _ hy)
          · exact hL _ (hs _ hz)
        have := h1.length_le_of_subset h2
        simp at this; omega
    refine ⟨seen, fun y hy => hy, hsub, ?_, fun y hy hn => absurd hy hn⟩
    intro z hz o ho hr w hw
    rcases hcl z hz o ho hr w hw with h | h
    · exact h
    · exact hsub w h
  | succ n ih =>
    intro todo
    induction todo with
    | nil =>
      intro seen _ _ _ _ hcl
      refine ⟨seen, fun y hy => hy, ?_, ?_, fun y hy hn => absurd hy hn⟩
      · intro y hy; cases hy
      · intro z hz o ho hr w hw
        rcases hcl z hz o ho hr w hw with h | h
        · exact h
        · cases h
    | cons y rest ihr =>
      intro seen hnd hs ht hlen hcl
      have hy : ReachIn fam s.ops r x y := ht y (List.mem_cons_self ..)
      have hrest : ∀ z ∈ rest, ReachIn fam s.ops r x z := fun z hz => ht z (List.mem_cons_of_mem _ hz)
      by_cases hsy : has seen y = true
      · have hys : y ∈ seen := (Engine.has_iff _ _).1 hsy
        obtain ⟨S, h1, h2, h3, h4⟩ := ihr seen hnd hs hrest hlen (fun z hz o ho hr w hw => by
          rcases hcl z hz o ho hr w hw with h | h
          · exact Or.inl h
          · rcases List.mem_cons.1 h with rfl | h
            · exact Or.inl hys
            · exact Or.inr h)
        refine ⟨S, h1, fun z hz => ?_, h3, fun z hz hn o ho hr => ?_⟩
        · rcases List.mem_cons.1 hz with rfl | hz
          · exact h1 _ hys
          · exact h2 z hz
        · rw [closureOps, if_pos hsy]; exact h4 z hz hn o ho hr
      · have hyn : y ∉ seen := fun h => hsy ((Engine.has_iff _ _).2 h)
        have hnd' : (y :: seen).Nodup := List.nodup_cons.2 ⟨hyn, hnd⟩
        have hs' : ∀ z ∈ y :: seen, ReachIn fam s.ops r x z := by
          intro z hz
          rcases List.mem_cons.1 hz with rfl | hz
          · exact hy
          · exact hs z hz
        have hlen' : L.length ≤ n + (y :: seen).length := by simp; omega
        -- the old obligations: what pointed at y is now seen
        have hold : ∀ (todo' : List Id), (∀ z ∈ rest, z ∈ todo') →
            ∀ z ∈ seen, ∀ o, s.ops z = some o → fam.room o = some r → ∀ w ∈ o.reqs,
              w ∈ y :: seen ∨ w ∈ todo' := by
          intro todo' hsub z hz o ho hr w hw
          rcases hcl z hz o ho hr w hw with h | h
          · exact Or.inl (List.mem_cons_of_mem _ h)
          · rcases List.mem_cons.1 h with rfl | h
            · exact Or.inl (List.mem_cons_self ..)
            · exact Or.inr (hsub w h)
        have hrun : ((closureOps fam r (n + 1) (y :: rest) seen : Model F (List Op)).run s).1 =
            match s.ops y with
            | some o => if fam.room o = some r then
                o :: ((closureOps fam r n (o.reqs ++ rest) (y :: seen) : Model F (List Op)).run s).1
              else ((closureOps fam r n rest (y :: seen) : Model F (List Op)).run s).1
            | none => ((closureOps fam r n rest (y :: seen) : Model F (List Op)).run s).1 := by
          rw [closureOps, if_neg hsy]
          simp only [Model.run_bind, run_getOp]
          cases s.ops y with
          | none => rfl
          | some o => dsimp only; split <;> simp [Model.run_bind, Model.run_pure]
        -- y not stored, or of another room: it is seen, and nothing is followed
        have skip : (∀ o, s.ops y = some o → fam.room o ≠ some r) →
            ((closureOps fam r (n + 1) (y :: rest) seen : Model F (List Op)).run s).1 =
              ((closureOps fam r n rest (y :: seen) : Model F (List Op)).run s).1 →
            ∃ S : List Id, (∀ z ∈ seen, z ∈ S) ∧ (∀ z ∈ y :: rest, z ∈ S) ∧
              (∀ z ∈ S, ∀ o, s.ops z = some o → fam.room o = some r → ∀ w ∈ o.reqs, w ∈ S) ∧
              (∀ z ∈ S, z ∉ seen → ∀ o, s.ops z = some o → fam.room o = some r →
                o ∈ ((closureOps fam r (n + 1) (y :: rest) seen : Model F (List Op)).run s).1) := by
          intro hno he
          obtain ⟨S, h1, h2, h3, h4⟩ := ih rest (y :: seen) hnd' hs' hrest hlen' (by
            intro z hz o ho hr w hw
            rcases List.mem_cons.1 hz with rfl | hz
            · exact absurd hr (hno o ho)
            · exact hold rest (fun w hw => hw) z hz o ho hr w hw)
          refine ⟨S, fun z hz => h1 z (List.mem_cons_of_mem _ hz), fun z hz => ?_, h3,
            fun z hz hn o ho hr => ?_⟩
          · rcases List.mem_cons.1 hz with rfl | hz
            · exact h1 _ (List.mem_cons_self ..)
            · exact h2 z hz
          · rw [he]
            by_cases hzy : z = y
            · subst hzy; exact absurd hr (hno o ho)
            · exact h4 z hz (fun h => by
                rcases List.mem_cons.1 h with h | h
                · exact hzy h
                · exact hn h) o ho hr
        cases hop : s.ops y with
        | none => exact skip (fun o ho => by rw [hop] at ho; cases ho) (by rw [hrun, hop])
        | some p =>
          by_cases hroom : fam.room p = some r
          · obtain ⟨S, h1, h2, h3, h4⟩ := ih (p.reqs ++ rest) (y :: seen) hnd' hs'
              (fun z hz => by
                rcases List.mem_append.1 hz with hz | hz
                · exact .step hy hop hroom hz
                · exact hrest z hz)
              hlen' (by
                intro z hz o ho hr w hw
                rcases List.mem_cons.1 hz with rfl | hz
                · rw [hop] at ho; cases ho
                  exact Or.inr (List.mem_append_left _ hw)
                · exact hold (p.reqs ++ rest) (fun w hw => List.mem_append_right _ hw) z hz o ho hr w hw)
            refine ⟨S, fun z hz => h1 z (List.mem_cons_of_mem _ hz), fun z hz => ?_, h3,
              fun z hz hn o ho hr => ?_⟩
            · rcases List.mem_cons.1 hz with rfl | hz
              · exact h1 _ (List.mem_cons_self ..)
              · exact h2 z (List.mem_append_right _ hz)
            · rw [hrun, hop]
              simp only [hroom, ite_true, List.mem_cons]
              by_cases hzy : z = y
              · subst hzy; rw [hop] at ho; cases ho; exact Or.inl rfl
              · exact Or.inr (h4 z hz (fun h => by
                  rcases List.mem_cons.1 h with h | h
                  · exact hzy h
                  · exact hn h) o ho hr)
          · exact skip (fun o ho => by rw [hop] at ho; cases ho; exact hroom)
              (by rw [hrun, hop]; simp [hroom])

/-- **The notice walk (`closure`).** `closureOps r fuel [x] []`, run on
the model at s, returns stored ops of room r in x's closure; and every
one of them when the closure fits the fuel. -/
theorem closure (s : DB F) (r x : Id) (fuel : Nat) :
    (∀ o ∈ ((closureOps fam r fuel [x] [] : Model F (List Op)).run s).1,
      ∃ y, s.ops y = some o ∧ fam.room o = some r ∧ ReachIn fam s.ops r x y) ∧
    (ClosureWithin fam s.ops r x fuel →
      ∀ y o, ReachIn fam s.ops r x y → s.ops y = some o → fam.room o = some r →
        o ∈ ((closureOps fam r fuel [x] [] : Model F (List Op)).run s).1) := by
  refine ⟨closureOps_sound fam s r x fuel [x] [] (fun y hy => by
    rw [List.mem_singleton] at hy; subst hy; exact .refl), ?_⟩
  rintro ⟨L, hlen, hL⟩ y o hy ho hr
  obtain ⟨S, _, h2, h3, h4⟩ := closureOps_complete fam s r x L hL fuel [x] [] List.nodup_nil
    (fun _ h => by cases h) (fun z hz => by rw [List.mem_singleton] at hz; subst hz; exact .refl)
    (by simpa using hlen) (fun _ h => by cases h)
  have hS : ∀ z, ReachIn fam s.ops r x z → z ∈ S := by
    intro z hz
    induction hz with
    | refl => exact h2 x (List.mem_singleton_self _)
    | step _ hop hroom hw ih => exact h3 _ ih _ hop hroom _ hw
  exact h4 y (hS y hy) (fun h => by cases h) o ho hr

/-! ## Giving -/

theorem give_state (s : DB F) : ∀ (l : List (Id × Id)) (c : Conn),
    ((c.give fam cfg l : Model F Step).run s).2 = s
  | [], _ => rfl
  | (r, x) :: rest, c => by
    unfold Conn.give
    split
    · exact give_state s rest c
    · simp only [Model.run_bind, Model.run_pure]
      rw [closureOps_state]; exact give_state s rest _

/-- What `give` leaves of the connection: its `given` grown, nothing
else. -/
theorem give_conn (s : DB F) : ∀ (l : List (Id × Id)) (c : Conn),
    ∃ gs, ((c.give fam cfg l : Model F Step).run s).1.conn = { c with given := gs ++ c.given } ∧
      ((c.give fam cfg l : Model F Step).run s).1.take = [] ∧
      ((c.give fam cfg l : Model F Step).run s).1.drop = false
  | [], c => ⟨[], by simp [Conn.give], rfl, rfl⟩
  | (r, x) :: rest, c => by
    unfold Conn.give
    split
    · exact give_conn s rest c
    · simp only [Model.run_bind, Model.run_pure]
      rw [closureOps_state]
      obtain ⟨gs, h1, h2, h3⟩ := give_conn s rest { c with given := x :: c.given }
      exact ⟨gs ++ [x], by rw [h1]; simp, h2, h3⟩

/-- A notice recorded given stays recorded. -/
theorem give_given (s : DB F) (l : List (Id × Id)) (c : Conn) {x : Id} (h : has c.given x = true) :
    has ((c.give fam cfg l : Model F Step).run s).1.conn.given x = true := by
  obtain ⟨gs, h1, _⟩ := give_conn fam cfg s l c
  rw [h1]
  exact (Engine.has_iff _ _).2 (List.mem_append_right _ ((Engine.has_iff _ _).1 h))

/-- What `give` sends: stored ops of the closures of notices of l not
given before. -/
theorem give_send (s : DB F) : ∀ (l : List (Id × Id)) (c : Conn),
    ∀ o ∈ ((c.give fam cfg l : Model F Step).run s).1.send,
      ∃ r x, (r, x) ∈ l ∧ has c.given x = false ∧
        ∃ y, s.ops y = some o ∧ fam.room o = some r ∧ ReachIn fam s.ops r x y
  | [], c => by intro o ho; cases ho
  | (r, x) :: rest, c => by
    intro o ho
    unfold Conn.give at ho
    split at ho
    · obtain ⟨r', x', hm, hg, hy⟩ := give_send s rest c o ho
      exact ⟨r', x', List.mem_cons_of_mem _ hm, hg, hy⟩
    · rename_i hx
      simp only [Model.run_bind, Model.run_pure, List.mem_append, List.mem_reverse] at ho
      rw [closureOps_state] at ho
      rcases ho with ho | ho
      · exact ⟨r, x, List.mem_cons_self .., by simpa using hx,
          (closure fam s r x cfg.walk).1 o (List.mem_filter.1 ho).1⟩
      · obtain ⟨r', x', hm, hg, hy⟩ := give_send s rest _ o ho
        exact ⟨r', x', List.mem_cons_of_mem _ hm, has_of_cons hg, hy⟩

/-- `give` gives each notice of l not given before. -/
theorem give_gives (s : DB F) (hk : Keyed s) (r x : Id) : ∀ (l : List (Id × Id)) (c : Conn),
    (r, x) ∈ l → has c.given x = false → (∀ r', (r', x) ∈ l → r' = r) →
    ClosureWithin fam s.ops r x cfg.walk →
    Gives fam s c r x ((c.give fam cfg l : Model F Step).run s).1
  | [], _, hm => by cases hm
  | (r', x') :: rest, c, hm => by
    intro hg hu hw
    unfold Conn.give
    split
    · rename_i hx
      have hne : x' ≠ x := fun e => by subst e; rw [hx] at hg; cases hg
      have hm' : (r, x) ∈ rest := by
        rcases List.mem_cons.1 hm with h | h
        · cases h; exact absurd rfl hne
        · exact h
      exact give_gives s hk r x rest c hm' hg (fun r'' h => hu r'' (List.mem_cons_of_mem _ h)) hw
    · rename_i hx
      simp only [Model.run_bind, Model.run_pure]
      rw [closureOps_state]
      by_cases hxe : x' = x
      · subst hxe
        have hr : r' = r := hu r' (List.mem_cons_self ..)
        subst hr
        refine ⟨List.mem_cons_self .., give_given fam cfg s rest _ (has_cons_self _ _), ?_⟩
        intro y o hy ho hroom hkn
        apply List.mem_append_left
        rw [List.mem_reverse, List.mem_filter]
        refine ⟨(closure fam s r' x' cfg.walk).2 hw y o hy ho hroom, ?_⟩
        rw [hk y o ho, hkn]; rfl
      · have hm' : (r, x) ∈ rest := by
          rcases List.mem_cons.1 hm with h | h
          · cases h; exact absurd rfl hxe
          · exact h
        have hg' : has ({ c with given := x' :: c.given } : Conn).given x = false := by
          show has (x' :: c.given) x = false
          cases hh : has (x' :: c.given) x
          · rfl
          · exfalso
            rcases List.mem_cons.1 ((Engine.has_iff _ _).1 hh) with h | h
            · exact hxe h.symm
            · rw [(Engine.has_iff _ _).2 h] at hg; cases hg
        obtain ⟨h1, h2, h3⟩ := give_gives s hk r x rest _ hm' hg'
          (fun r'' h => hu r'' (List.mem_cons_of_mem _ h)) hw
        exact ⟨List.mem_cons_of_mem _ h1, h2, fun y o hy ho hroom hkn =>
          List.mem_append_right _ (h3 y o hy ho hroom hkn)⟩

/-- With every notice of l given, `give` sends nothing. -/
theorem give_quiet (s : DB F) : ∀ (l : List (Id × Id)) (c : Conn), (∀ p ∈ l, has c.given p.2 = true) →
    ((c.give fam cfg l : Model F Step).run s).1.send = []
  | [], _, _ => rfl
  | (r, x) :: rest, c, h => by
    unfold Conn.give
    rw [if_pos (h (r, x) (List.mem_cons_self ..))]
    exact give_quiet s rest c (fun p hp => h p (List.mem_cons_of_mem _ hp))

/-! ## Rooms -/

theorem mem_syncs {r : Id} : ∀ {rs : List Room}, r ∈ Room.syncs rs → Room.sync r ∈ rs
  | [], h => by cases h
  | .sync r' :: t, h => by
    simp only [Room.syncs, List.mem_cons] at h
    rcases h with rfl | h
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (mem_syncs h)
  | .notice .. :: t, h => List.mem_cons_of_mem _ (mem_syncs (by simpa [Room.syncs] using h))

theorem mem_notices {r x : Id} : ∀ {rs : List Room}, (r, x) ∈ Room.notices rs → Room.notice r x ∈ rs
  | [], h => by cases h
  | .sync _ :: t, h => List.mem_cons_of_mem _ (mem_notices (by simpa [Room.notices] using h))
  | .notice r' x' :: t, h => by
    simp only [Room.notices, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (mem_notices h)

/-- **A notice room answers no holds (`notice_no_holds`).** On a
connection carrying rooms rs, a have for a room rs does not sync (one it
carries only as a notice, or not at all) is ignored: the reply sends
nothing, takes nothing and reads nothing. So a removed member's node
learns nothing of what this node holds of the community it is told it
was removed from (`hold_reply_local` for the rooms it syncs). -/
theorem notice_no_holds (ix : Index) (c : Conn) (rs : List Room) (r : Id) (ids : List Id)
    (bytes : ByteArray) (now : Nat) (s : DB F) {o : Op} (hd : Op.decode bytes = some o)
    (hm : Msg.ofOp o = some (.hold r ids)) (hr : Room.sync r ∉ rs) :
    ((Conn.recv fam cfg ix (c.carry rs) bytes now : Model F Step).run s).1.send = [] ∧
    ((Conn.recv fam cfg ix (c.carry rs) bytes now : Model F Step).run s).1.take = [] ∧
    ((Conn.recv fam cfg ix (c.carry rs) bytes now : Model F Step).run s).2 = s := by
  have hn : has (c.carry rs).rooms r = false := by
    cases h : has (c.carry rs).rooms r
    · rfl
    · exact absurd (mem_syncs ((Engine.has_iff _ _).1 h)) hr
  unfold Conn.recv
  rw [hd]
  dsimp only
  rw [hm]
  dsimp only
  unfold Conn.onHold
  have hn' : has ({ c.carry rs with heard := now } : Conn).rooms r = false := hn
  simp [hn']

/-! ## The node's steps -/

theorem notify_state (c : Conn) (s : DB F) : ((c.notify fam cfg : Model F Step).run s).2 = s :=
  give_state fam cfg s _ c

theorem filedGive_run (c : Conn) (ids : List Id) (s : DB F) :
    ((c.filedGive fam cfg ids : Model F Step).run s).1 =
      Step.then ((c.notify fam cfg : Model F Step).run s).1
        ((((c.notify fam cfg : Model F Step).run s).1.conn.filed fam cfg ids : Model F Step).run s).1 := by
  simp only [Conn.filedGive, Model.run_bind, Model.run_pure]
  rw [notify_state]

theorem tickGive_run (ix : Index) (c : Conn) (now : Nat) (s : DB F) :
    ((c.tickGive fam cfg ix now : Model F Step).run s).1 =
      let g := ((c.notify fam cfg : Model F Step).run s).1
      let t := ((g.conn.tick fam cfg ix now : Model F Step).run s).1
      if t.drop then t else Step.then g t := by
  simp only [Conn.tickGive, Model.run_bind, Model.run_pure]
  rw [notify_state]

/-- A tick drops exactly on silence; giving notices never changes heard. -/
theorem tick_drop (ix : Index) (c : Conn) (now : Nat) (s : DB F) :
    ((c.tick fam cfg ix now : Model F Step).run s).1.drop =
      Decidable.decide (c.heard + cfg.live < now) := by
  unfold Conn.tick
  split
  · rename_i h; simp [h]
  · rename_i h
    simp only [Model.run_bind, Model.run_pure, Step.pulse_drop]
    unfold Conn.work
    simp only [Model.run_bind, Model.run_pure]
    split
    · unfold Conn.start; split <;> simp [h]
    · simp [h]

/-- A connection whose `given` alone differs ticks alike as to dropping. -/
theorem tick_drop_given (ix : Index) (c : Conn) (gs : List Id) (now : Nat) (s : DB F) :
    (((({ c with given := gs } : Conn)).tick fam cfg ix now : Model F Step).run s).1.drop =
      ((c.tick fam cfg ix now : Model F Step).run s).1.drop := by
  rw [tick_drop, tick_drop]

/-! What a step after `notify` keeps of it: its `given`, through `filed`
and `tick`. -/

theorem Model.forIn_reads {α β} (l : List α) (b : β) (f : α → β → Model F (ForInStep β))
    (g : β → α → β) (s : DB F) (hf : ∀ a b, (f a b).run s = (.yield (g b a), s)) :
    (forIn l b f).run s = (l.foldl g b, s) := by
  induction l generalizing b with
  | nil => rfl
  | cons a t ih => rw [List.forIn_cons, Model.run_bind, hf]; exact ih _

theorem filed_given (c : Conn) (ids : List Id) (s : DB F) :
    ((c.filed fam cfg ids : Model F Step).run s).1.conn.given = c.given := by
  unfold Conn.filed
  simp only [Model.run_bind]
  rw [Model.forIn_reads (g := fileOffer fam cfg s)]
  · have := foldl_inv (fun b : List (Id × Id) × Conn => b.2.given = c.given) (fileOffer fam cfg s) (by
      intro b i e
      unfold fileOffer
      split
      · split
        · split
          · exact e
          · exact e
        · exact e
      · exact e) ids ([], c) rfl
    exact this
  · intro a b
    unfold fileOffer
    by_cases h1 : (!b.2.known.contains a && !b.2.offered.contains a) = true
    · rw [ite_eq_left h1, ite_eq_left h1, Model.run_bind, run_getOp]
      dsimp only
      cases s.ops a with
      | none => rfl
      | some o =>
        dsimp only
        by_cases h2 : b.2.shows fam o = true
        · rw [ite_eq_left h2, ite_eq_left h2]; rfl
        · rw [ite_eq_right h2, ite_eq_right h2]; rfl
    · rw [ite_eq_right h1, ite_eq_right h1]; rfl

theorem walkN_given (s : DB F) : ∀ (k : Nat) (c : Conn) (offer : List (Id × Id)),
    ((c.walkN fam cfg offer k : Model F _).run s).1.1.given = c.given := by
  intro k
  induction k with
  | zero => intros; rfl
  | succ k ih =>
    intro c offer
    rw [Conn.walkN]
    cases c.frontier with
    | nil => rfl
    | cons x rest =>
      dsimp only
      split
      · exact ih _ _
      · rw [Model.run_bind, run_getOp]
        cases s.ops x with
        | none => exact ih _ _
        | some o => dsimp only; split <;> exact ih _ _

theorem tick_given (ix : Index) (c : Conn) (now : Nat) (s : DB F) :
    ((c.tick fam cfg ix now : Model F Step).run s).1.conn.given = c.given := by
  unfold Conn.tick
  split
  · rfl
  · simp only [Model.run_bind, Model.run_pure, Step.pulse_conn]
    unfold Conn.work
    simp only [Model.run_bind, Model.run_pure, Conn.walk]
    have hw := walkN_given fam cfg s cfg.walk c []
    generalize ((c.walkN fam cfg [] cfg.walk : Model F _).run s).1 = p at hw
    obtain ⟨c', offer⟩ := p
    dsimp only at hw ⊢
    split <;> simp_all [Conn.start, Conn.expireAsks, Conn.beginRound] <;>
      (try split) <;> simp_all

/-- **E1, the notice is given (`notice_sent`).** A connection carrying
notice (r, x) it has not given gives it on its next `filedGive` (the
node's step on every connection right after it stores ops, so right
after it decides a removal), and on a `tickGive` whose tick does not
drop it; given that x's closure fits `cfg.walk`, that the store keeps
ops under their ids, and that x is a notice of room r only. -/
theorem notice_sent (ix : Index) (s : DB F) (hk : Keyed s) (c : Conn) (ids : List Id) (now : Nat)
    (r x : Id) (hm : (r, x) ∈ c.notices) (hg : has c.given x = false)
    (hu : ∀ r', (r', x) ∈ c.notices → r' = r) (hw : ClosureWithin fam s.ops r x cfg.walk) :
    Gives fam s c r x ((c.filedGive fam cfg ids : Model F Step).run s).1 ∧
    (((c.tick fam cfg ix now : Model F Step).run s).1.drop = false →
      Gives fam s c r x ((c.tickGive fam cfg ix now : Model F Step).run s).1) := by
  obtain ⟨g1, g2, g3⟩ := give_gives fam cfg s hk r x c.notices c hm hg hu hw
  refine ⟨?_, fun hd => ?_⟩
  · rw [filedGive_run]
    refine ⟨List.mem_append_left _ g1, ?_, fun y o hy ho hroom hkn =>
      List.mem_append_left _ (g3 y o hy ho hroom hkn)⟩
    show has (((Conn.filed fam cfg _ ids : Model F Step).run s).1.conn.given) x = true
    rw [filed_given]; exact g2
  · rw [tickGive_run]
    obtain ⟨gs, hc, _, _⟩ := give_conn fam cfg s c.notices c
    have hd' : ((((c.notify fam cfg : Model F Step).run s).1.conn.tick fam cfg ix now :
        Model F Step).run s).1.drop = false := by
      show ((((c.give fam cfg c.notices : Model F Step).run s).1.conn.tick fam cfg ix now :
        Model F Step).run s).1.drop = false
      rw [hc, tick_drop_given]; exact hd
    dsimp only
    rw [if_neg (by rw [hd']; simp)]
    refine ⟨List.mem_append_left _ g1, ?_, fun y o hy ho hroom hkn =>
      List.mem_append_left _ (g3 y o hy ho hroom hkn)⟩
    show has (((Conn.tick fam cfg ix _ now : Model F Step).run s).1.conn.given) x = true
    rw [tick_given]; exact g2

/-- **A step gives nothing but notices (`notice_send`).** Everything
`filedGive` and `tickGive` send is a sync wire op, or a stored op of the
closure of a notice the connection carried and had not given; they take
nothing. -/
theorem notice_send (ix : Index) (s : DB F) (c : Conn) (ids : List Id) (now : Nat) :
    ∀ st ∈ [((c.filedGive fam cfg ids : Model F Step).run s).1,
        ((c.tickGive fam cfg ix now : Model F Step).run s).1],
      (∀ o ∈ st.send, isWire o.kind = true ∨ NoticeOp fam s c o) ∧ st.take = [] := by
  have hg : ∀ o ∈ ((c.notify fam cfg : Model F Step).run s).1.send, NoticeOp fam s c o := by
    intro o ho
    exact give_send fam cfg s c.notices c o ho
  obtain ⟨_, _, ht, _⟩ := give_conn fam cfg s c.notices c
  have ht' : ((c.notify fam cfg : Model F Step).run s).1.take = [] := ht
  intro st hst
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hst
  rcases hst with rfl | rfl
  · rw [filedGive_run]
    obtain ⟨f1, f2⟩ := filed_send fam cfg (((c.notify fam cfg : Model F Step).run s).1.conn) ids s
    refine ⟨fun o ho => ?_, by simp [Step.then, ht', f2]⟩
    rcases List.mem_append.1 ho with ho | ho
    · exact Or.inr (hg o ho)
    · exact Or.inl (f1 o ho)
  · rw [tickGive_run]
    obtain ⟨t1, t2⟩ := tick_send fam cfg ix (((c.notify fam cfg : Model F Step).run s).1.conn) now s
    dsimp only
    split
    · exact ⟨fun o ho => Or.inl (t1 o ho), t2⟩
    · refine ⟨fun o ho => ?_, by simp [Step.then, ht', t2]⟩
      rcases List.mem_append.1 ho with ho | ho
      · exact Or.inr (hg o ho)
      · exact Or.inl (t1 o ho)

/-- **Once (`notice_once`).** A connection that has given every notice
it carries sends only sync wire ops on `filedGive` and `tickGive`, as
`filed` and `tick` do: a notice is given once per connection. -/
theorem notice_once (ix : Index) (s : DB F) (c : Conn) (ids : List Id) (now : Nat)
    (h : ∀ p ∈ c.notices, has c.given p.2 = true) :
    (∀ o ∈ ((c.filedGive fam cfg ids : Model F Step).run s).1.send, isWire o.kind = true) ∧
    (∀ o ∈ ((c.tickGive fam cfg ix now : Model F Step).run s).1.send, isWire o.kind = true) := by
  have hq : ((c.notify fam cfg : Model F Step).run s).1.send = [] := give_quiet fam cfg s c.notices c h
  refine ⟨fun o ho => ?_, fun o ho => ?_⟩
  · rw [filedGive_run] at ho
    simp only [Step.then, hq, List.nil_append] at ho
    exact (filed_send fam cfg _ ids s).1 o ho
  · rw [tickGive_run] at ho
    dsimp only at ho
    split at ho
    · exact (tick_send fam cfg ix _ now s).1 o ho
    · simp only [Step.then, hq, List.nil_append] at ho
      exact (tick_send fam cfg ix _ now s).1 o ho

end

end Engine.Sync
