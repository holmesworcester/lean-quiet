/-
A row's "Duplicate" label, over the running code (Kinds.Profile.namesake,
read in ViewLaws' model, where a list read is the engine's `eval`):

- `others_iff`: the walk over the profiles filed under a look finds a
  user other than u whose newest name has that look, exactly when one
  is among the rows;
- `namesake_iff`: at rest, u's row is marked exactly when another user
  of the community has a Valid profile and their newest name looks as
  u's does (`nameLook`: invisible characters and kinds of space do not
  tell names apart). No namesake goes unmarked, and no row is marked
  without one;
- `row_marked`: so a shown message's row carries the mark exactly when
  its author has a namesake (with RowLaws.twin_shown: the row draws
  "⚠ Duplicate" exactly then).
-/
import ops.community.message.ViewLaws
import ops.community.Intents

namespace ViewLaws
open Engine Community Data Kinds

theorem others_iff (db : DB Fact) (c u k : Id) : ∀ (rows : List (Pos × Fact)) (deps : Array Q),
    ((Profile.others (m := Model) c u k rows deps).run db).1 = true ↔
      ∃ p c' u' n tm, (p, Fact.profile c' u' n tm) ∈ rows ∧ u' ≠ u ∧ nameLook (nameIn db c u') = k
  | [], deps => by simp [Profile.others, ReaderT.run, pure, ReaderT.pure]
  | (p, f) :: t, deps => by
    have ih := others_iff db c u k t
    cases f
    case profile c' u' n tm =>
      by_cases hu : u' = u
      · simp only [Profile.others, hu, ite_true]
        rw [ih]
        constructor
        · rintro ⟨p', c'', u'', n', tm', hm, hne, hl⟩
          exact ⟨p', c'', u'', n', tm', List.mem_cons_of_mem _ hm, hne, hl⟩
        · rintro ⟨p', c'', u'', n', tm', hm, hne, hl⟩
          rcases List.mem_cons.1 hm with he | hm
          · simp only [Prod.mk.injEq, Fact.profile.injEq] at he
            obtain ⟨-, -, rfl, -, -⟩ := he
            exact absurd rfl hne
          · exact ⟨p', c'', u'', n', tm', hm, hne, hl⟩
      · have hr := profile_read db c u' deps
        simp only [Profile.others, hu, ite_false, ReaderT.run, bind, ReaderT.bind, pure] at hr ⊢
        by_cases hk : nameLook ((Profile.read (m := Model) c u' deps) db).1.name = k
        · simp only [hk, ite_true]
          refine iff_of_true rfl ⟨p, c', u', n, tm, List.mem_cons_self .., hu, hr ▸ hk⟩
        · simp only [hk, ite_false]
          have := ih ((Profile.read (m := Model) c u' deps) db).2
          simp only [ReaderT.run] at this
          rw [this]
          constructor
          · rintro ⟨p', c'', u'', n', tm', hm, hne, hl⟩
            exact ⟨p', c'', u'', n', tm', List.mem_cons_of_mem _ hm, hne, hl⟩
          · rintro ⟨p', c'', u'', n', tm', hm, hne, hl⟩
            rcases List.mem_cons.1 hm with he | hm
            · simp only [Prod.mk.injEq, Fact.profile.injEq] at he
              obtain ⟨-, -, rfl, -, -⟩ := he
              exact absurd (hr ▸ hl) hk
            · exact ⟨p', c'', u'', n', tm', hm, hne, hl⟩
    all_goals
      simp only [Profile.others]
      rw [ih]
      constructor
      · rintro ⟨p', c'', u'', n', tm', hm, hne, hl⟩
        exact ⟨p', c'', u'', n', tm', List.mem_cons_of_mem _ hm, hne, hl⟩
      · rintro ⟨p', c'', u'', n', tm', hm, hne, hl⟩
        rcases List.mem_cons.1 hm with he | hm
        · simp at he
        · exact ⟨p', c'', u'', n', tm', hm, hne, hl⟩

variable {s : DB Fact} {C : Crypto}

theorem eval_one (r : Rel Fact) (as : List ByteArray) :
    (Engine.eval s (r.query as (some 1))).rows = (Engine.eval s (r.query as none)).rows.take 1 := by
  simp [Engine.eval, ListQ.cut, ListQ.inside, Rel.query, matching]

theorem byUser_args {c u : Id} {f : Fact} :
    profile.byUser.args f = some [c, u] ↔ ∃ n tm, f = .profile c u n tm := by
  cases f <;> simp [profile.byUser, eq_comm]

theorem byLook_args {c k : Id} {f : Fact} :
    profile.byLook.args f = some [c, k] ↔
      ∃ u n tm, f = .profile c u n tm ∧ nameLook ((String.fromUTF8? n).getD "?") = k := by
  cases f
  case profile c' u n tm =>
    simp only [profile.byLook, Option.some.injEq, List.cons.injEq, and_true, Fact.profile.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩; exact ⟨u, n, tm, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩
    · rintro ⟨_, _, _, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩; exact ⟨rfl, rfl⟩
  all_goals simp [profile.byLook]

/-- At rest, a user with a Valid profile has a newest one: their name is
a Valid profile's. -/
theorem newest (h : Inv (family C) s) (hq : s.queue = []) {c u : Id} {y : Id} {n : ByteArray} {tm : Nat}
    (hv : V C s.ops y (.profile c u n tm)) :
    ∃ (p : Pos) (n' : ByteArray) (tm' : Nat), V C s.ops p.2 (.profile c u n' tm') ∧ nameIn s c u = Profile.bytesStr n' := by
  have hm := at_row (C := C) (r := profile.byUser) (as := [c, u]) (desc := true) (by simp [rels]) h hq hv
    (by simp [profile.byUser])
  have hne : (Engine.eval s (profile.byUser.query [c, u] none)).rows ≠ [] := List.ne_nil_of_mem hm
  obtain ⟨x, t, ht⟩ := List.exists_cons_of_ne_nil hne
  have hx : x ∈ (Engine.eval s (profile.byUser.query [c, u] none)).rows := ht ▸ List.mem_cons_self ..
  obtain ⟨hvx, ha⟩ := row_filed (C := C) (by simp [rels]) h hq hx
  obtain ⟨n', tm', hf⟩ := byUser_args.1 ha
  refine ⟨x.1, n', tm', hf ▸ hvx, ?_⟩
  unfold nameIn
  rw [eval_one, ht]
  obtain ⟨px, fx⟩ := x
  dsimp only at hf
  subst hf
  rfl

/-- **A row is marked exactly when its name has a namesake.** At rest,
the running read marks user u of c (whose row shows `nameIn s c u`)
exactly when another user of c has a Valid profile and a newest name
that looks the same. -/
theorem namesake_iff (h : Inv (family C) s) (hq : s.queue = []) (c u : Id) (deps : Array Q) :
    ((Profile.namesake (m := Model) c u (nameIn s c u) deps).run s).1 = true ↔
      ∃ u', u' ≠ u ∧ (∃ y n tm, V C s.ops y (.profile c u' n tm)) ∧
        nameLook (nameIn s c u') = nameLook (nameIn s c u) := by
  simp only [Profile.namesake, readList, ReaderT.run, bind, ReaderT.bind, Reads.read, pure, ReaderT.pure]
  have := others_iff s c u (nameLook (nameIn s c u))
    (Engine.eval s (profile.byLook.query [c, nameLook (nameIn s c u)])).rows
  simp only [ReaderT.run] at this
  rw [this]
  constructor
  · rintro ⟨p, c', u', n, tm, hm, hne, hl⟩
    obtain ⟨hv, ha⟩ := row_filed (C := C) (by simp [rels]) h hq hm
    obtain ⟨_, _, _, hf, -⟩ := byLook_args.1 ha
    simp only [Fact.profile.injEq] at hf
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hf
    exact ⟨u', hne, ⟨p.2, n, tm, hv⟩, hl⟩
  · rintro ⟨u', hne, ⟨y, n, tm, hv⟩, hl⟩
    obtain ⟨p, n', tm', hv', hn⟩ := newest h hq hv
    have hm := at_row (C := C) (r := profile.byLook) (as := [c, nameLook (nameIn s c u)]) (desc := true)
      (by simp [rels]) h hq hv' (byLook_args.2 ⟨u', n', tm', rfl, by rw [← hl, hn]; rfl⟩)
    exact ⟨_, c, u', n', tm', hm, hne, hl⟩

/-- **A message row is marked Duplicate exactly when its author has a
namesake.** At rest, a shown message's row carries the mark exactly when
another user of the community has a Valid profile whose newest name
looks as its author's does. -/
theorem row_marked (h : Inv (family C) s) (hq : s.queue = []) {c me msg : Id} {d : Row.RowData}
    {deps : Array Q} (hr : (Message.read (m := Model) c me msg).run s = some (d, deps)) :
    ∃ c' u dev kid sealed n tm clump, factIn s msg = some (.message c' u dev kid sealed n tm clump) ∧
      (d.namesake = true ↔ ∃ u', u' ≠ u ∧ (∃ y n tm, V C s.ops y (.profile c u' n tm)) ∧
        nameLook (nameIn s c u') = nameLook (nameIn s c u)) := by
  obtain ⟨c', u, dev, kid, sealed, n, tm, clump, hf, hn, -, ⟨deps', hd⟩, -⟩ := message_read s c me msg d deps hr
  refine ⟨c', u, dev, kid, sealed, n, tm, clump, hf, ?_⟩
  rw [hd, hn]
  exact namesake_iff h hq c u deps'

end ViewLaws
