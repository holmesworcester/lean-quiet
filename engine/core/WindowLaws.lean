/-
The laws of windows (engine/core/Window.lean), over the engine's model.

**The journal is exact** (`run_exact`). A batch of changes (ops stored,
steps judged, purges, in any order: `Change`) writes a journal
(`Change.journal`: what the index triggers record; a decision files its
fact under each of its keys, a purge unfiles every filed op of its
closure). After the batch, a row is filed under k at p exactly when it
was before or the journal touched (k, p) an odd number of times, not
both. So the net filings (`net`) are exactly the rows that came or went.

**A filed op keeps its fact** (`fact_stable`): an op filed before and
after a batch was filed with one fact, if no two ops the batch saw
share an id (`OneOpPerId`, from SHA-256's collision freedom). Its
verdict is the spec's over its requirement closure, which is the same
ops in both.

**A window changes exactly when the net filings hit it**
(`window_ne_iff_flips`): a row whose position is in its range came or
went. Its rows are in position order and no two share a position (a
position holds the row's id), so the window is determined by which rows
it holds.

**Notices are exact** (`notice_iff`): matched against the index
(`Subs.notify`), the net filings reach a subscriber exactly when one of
its windows changed: never for a row outside them (precision), and
always for one inside (completeness).
-/
import engine.core.WindowIndex
import engine.core.Proofs
import engine.core.Locality
import engine.core.Order

namespace Engine

/-! ## Lists of keys, each once -/

/-- Each value once (its last occurrence). -/
def nubB : List ByteArray → List ByteArray
  | [] => []
  | k :: t => if has t k then nubB t else k :: nubB t

theorem mem_nubB {k : ByteArray} : ∀ {l : List ByteArray}, k ∈ nubB l ↔ k ∈ l
  | [] => by simp [nubB]
  | a :: t => by
    unfold nubB
    by_cases h : has t a = true
    · rw [if_pos h, mem_nubB, List.mem_cons]
      exact ⟨Or.inr, fun h' => h'.elim (fun e => e ▸ (has_iff _ _).1 h) id⟩
    · rw [if_neg h, List.mem_cons, List.mem_cons, mem_nubB]

theorem nodup_nubB : ∀ (l : List ByteArray), (nubB l).Nodup
  | [] => List.nodup_nil
  | a :: t => by
    unfold nubB
    by_cases h : has t a = true
    · rw [if_pos h]; exact nodup_nubB t
    · rw [if_neg h]
      exact List.nodup_cons.2 ⟨fun h' => h ((has_iff _ _).2 (mem_nubB.1 h')), nodup_nubB t⟩

/-- In a list of distinct values, k is counted once if it is there. -/
theorem countP_eq_nodup {k : ByteArray} :
    ∀ {l : List ByteArray}, l.Nodup → l.countP (fun a => Decidable.decide (a = k)) = if has l k then 1 else 0
  | [], _ => rfl
  | a :: t, h => by
    obtain ⟨ha, ht⟩ := List.nodup_cons.1 h
    rw [List.countP_cons, countP_eq_nodup ht]
    by_cases hk : a = k
    · subst hk
      rw [(has_false _ _).2 ha, if_pos ((has_iff _ _).2 (List.mem_cons_self ..))]
      simp
    · have : has (a :: t) k = has t k := by
        apply Bool.eq_iff_iff.2
        rw [has_iff, has_iff, List.mem_cons]
        exact ⟨fun h' => h'.elim (fun e => absurd e.symm hk) id, Or.inr⟩
      rw [this]
      simp [hk]

/-- A sum over distinct ids of a function that is 0 off one of them. -/
theorem sum_map_single {g : ByteArray → Nat} {y : ByteArray} :
    ∀ {l : List ByteArray}, l.Nodup → (∀ x ∈ l, x ≠ y → g x = 0) →
      (l.map g).sum = if has l y then g y else 0
  | [], _, _ => rfl
  | a :: t, h, hg => by
    obtain ⟨ha, ht⟩ := List.nodup_cons.1 h
    rw [List.map_cons, List.sum_cons, sum_map_single ht fun x hx => hg x (List.mem_cons_of_mem _ hx)]
    by_cases hy : a = y
    · subst hy
      rw [(has_false _ _).2 ha, if_pos ((has_iff _ _).2 (List.mem_cons_self ..))]
      simp
    · rw [hg a (List.mem_cons_self ..) hy]
      have : has (a :: t) y = has t y := by
        apply Bool.eq_iff_iff.2
        rw [has_iff, has_iff, List.mem_cons]
        exact ⟨fun h' => h'.elim (fun e => absurd e.symm hy) id, Or.inr⟩
      rw [this, Nat.zero_add]

/-! ## The model's journal -/

/-- One change to the tables, as commits make them: an op stored, a
queued op judged, or a purge (which unfiles its closure's ops, and
undecides its shared ones). -/
inductive Change where
  | ingest (o : Op)
  | step
  | purge (ids : List Id)

section
variable {F : Type} [SortKey F]

/-- The tables after a change. -/
def Change.apply (fam : Family F) : Change → DB F → DB F
  | .ingest o, s => ingestS o s
  | .step, s => stepS fam s
  | .purge ids, s => purgeS fam ids s

/-- The journal rows of op x filed (or unfiled) with fact f: one per
key, as the index holds one row per key and id (`INSERT OR IGNORE` and
the triggers' `AFTER INSERT` record nothing for a key already there). -/
def fileJ (fam : Family F) (x : Id) (f : F) (on : Bool) : List Filing :=
  (nubB (fam.fileKeys x f)).map fun k => ⟨k, (SortKey.sortOf f, x), on⟩

/-- What a step records: the filings of the op it decides Valid. -/
def stepJ (fam : Family F) (s : DB F) : List Filing :=
  match s.queue with
  | [] => []
  | x :: _ => match s.status x with
    | some _ => []
    | none => match s.ops x with
      | none => []
      | some o => match judge fam o (o.reqs.map s.status) with
        | some (.valid f) => fileJ fam x f true
        | _ => []

/-- What a purge records: the unfilings of every Valid op of its closure
(`purgeTx` deletes exactly these rows). -/
def purgeJ (fam : Family F) (ids : List Id) (s : DB F) : List Filing :=
  (nubB (closeUp s ids)).flatMap fun x => match s.status x with
    | some (.valid f) => fileJ fam x f false
    | _ => []

/-- What the index's triggers record for a change. -/
def Change.journal (fam : Family F) : Change → DB F → List Filing
  | .ingest _, _ => []
  | .step, s => stepJ fam s
  | .purge ids, s => purgeJ fam ids s

/-- A batch of changes: the tables after it, and its journal in order. -/
def runJ (fam : Family F) : List Change → DB F → DB F × List Filing
  | [], s => (s, [])
  | c :: cs, s => ((runJ fam cs (c.apply fam s)).1, c.journal fam s ++ (runJ fam cs (c.apply fam s)).2)

/-- The ops a batch stores. -/
def Change.ingests : List Change → List Op
  | [] => []
  | .ingest o :: cs => o :: Change.ingests cs
  | _ :: cs => Change.ingests cs

/-! ## Rows filed -/

/-- Whether a verdict is Valid with a fact of this sort key. -/
def sortIs : Option (Verdict F) → ByteArray → Bool
  | some (.valid f), sk => Decidable.decide (SortKey.sortOf f = sk)
  | _, _ => false

/-- Whether a row is filed under k at p (p names the row's op). -/
def filed (s : DB F) (k : ByteArray) (p : Pos) : Bool := has (s.idx k) p.2 && sortIs (s.status p.2) p.1

/-- Whether a journal touches (k, p) an odd number of times. -/
def flips (J : List Filing) (k : ByteArray) (p : Pos) : Bool :=
  J.countP (fun e => Decidable.decide (e.key = k ∧ e.pos = p)) % 2 == 1

theorem flips_nil (k : ByteArray) (p : Pos) : flips [] k p = false := rfl

theorem flips_append (J₁ J₂ : List Filing) (k : ByteArray) (p : Pos) :
    flips (J₁ ++ J₂) k p = (flips J₁ k p ^^ flips J₂ k p) := by
  simp only [flips, List.countP_append]
  generalize J₁.countP _ = a
  generalize J₂.countP _ = b
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
    simp [Nat.add_mod, ha, hb]

theorem filed_iff {s : DB F} {k : ByteArray} {p : Pos} :
    filed s k p = true ↔ ∃ f, p.2 ∈ s.idx k ∧ s.status p.2 = some (.valid f) ∧ SortKey.sortOf f = p.1 := by
  unfold filed
  rw [Bool.and_eq_true, has_iff]
  constructor
  · rintro ⟨h1, h2⟩
    cases hs : s.status p.2 with
    | none => rw [hs] at h2; cases h2
    | some v =>
      cases v with
      | invalid => rw [hs] at h2; cases h2
      | valid f => rw [hs] at h2; exact ⟨f, h1, rfl, of_decide_eq_true h2⟩
  · rintro ⟨f, h1, h2, h3⟩
    exact ⟨h1, by rw [h2]; exact decide_eq_true h3⟩

/-! ## Each change's journal is exact -/

theorem ingestS_idx (o : Op) (s : DB F) : (ingestS o s).idx = s.idx := by
  unfold ingestS; split <;> rfl

theorem ingest_exact (o : Op) (s : DB F) (k : ByteArray) (p : Pos) :
    filed (ingestS o s) k p = (filed s k p ^^ flips [] k p) := by
  rw [flips_nil, Bool.xor_false]
  unfold filed
  rw [ingestS_idx, ingestS_status]

/-- A journal row of a filing names its op. -/
theorem fileJ_pos {fam : Family F} {x : Id} {f : F} {on : Bool} {e : Filing}
    (he : e ∈ fileJ fam x f on) : e.pos = (SortKey.sortOf f, x) := by
  unfold fileJ at he
  obtain ⟨k, _, rfl⟩ := List.mem_map.1 he
  rfl

/-- The journal of x's filing touches (k, p) once if p is x's position
and k one of its keys, else not. -/
theorem flips_fileJ (fam : Family F) (x : Id) (f : F) (on : Bool) (k : ByteArray) (p : Pos) :
    flips (fileJ fam x f on) k p =
      (has (fam.fileKeys x f) k && Decidable.decide (p = (SortKey.sortOf f, x))) := by
  unfold flips fileJ
  rw [List.countP_map]
  by_cases hp : p = (SortKey.sortOf f, x)
  · subst hp
    have : ((fun e : Filing => Decidable.decide (e.key = k ∧ e.pos = (SortKey.sortOf f, x))) ∘
        fun k' => (⟨k', (SortKey.sortOf f, x), on⟩ : Filing)) = fun k' => Decidable.decide (k' = k) := by
      funext k'; simp
    rw [this, countP_eq_nodup (nodup_nubB _)]
    have hh : has (nubB (fam.fileKeys x f)) k = has (fam.fileKeys x f) k :=
      Bool.eq_iff_iff.2 (by rw [has_iff, has_iff, mem_nubB])
    rw [hh]
    cases has (fam.fileKeys x f) k <;> simp
  · have : ((fun e : Filing => Decidable.decide (e.key = k ∧ e.pos = p)) ∘
        fun k' => (⟨k', (SortKey.sortOf f, x), on⟩ : Filing)) = fun _ => false := by
      funext k'; simp only [Function.comp, decide_eq_false_iff_not, not_and]
      intro _ h; exact hp h.symm
    rw [this, List.countP_false]
    simp [hp]

theorem step_exact {fam : Family F} {s : DB F} (h : Inv fam s) (k : ByteArray) (p : Pos) :
    filed (stepS fam s) k p = (filed s k p ^^ flips (stepJ fam s) k p) := by
  unfold stepS stepJ
  cases hq : s.queue with
  | nil => simp [flips_nil]
  | cons x q =>
    simp only
    cases hs : s.status x with
    | some w => simp only [flips_nil, Bool.xor_false]; rfl
    | none =>
      simp only
      cases ho : s.ops x with
      | none => simp only [flips_nil, Bool.xor_false]; rfl
      | some o =>
        simp only
        cases hj : judge fam o (o.reqs.map s.status) with
        | none =>
          simp only [flips_nil, Bool.xor_false]
          unfold filed
          rw [waitOnS_idx, waitOnS_status]
        | some v =>
          simp only
          obtain ⟨_, hst, _, _, hidx⟩ := decideS_fields (fam := fam) x v { s with queue := q }
          -- x was filed nowhere: it was undecided
          have hx : ∀ k, x ∉ s.idx k := fun k hk => by
            obtain ⟨f, hf, _⟩ := (h.idx k x).1 hk
            rw [hs] at hf; cases hf
          cases v with
          | invalid =>
            simp only [flips_nil, Bool.xor_false]
            unfold filed
            have hi : (decideS fam x .invalid { s with queue := q }).idx k = s.idx k := rfl
            rw [hi, hst]
            dsimp only
            by_cases hy : p.2 = x
            · rw [if_pos hy, hy, (has_false _ _).2 (hx k)]; rfl
            · rw [if_neg hy]
          | valid f =>
            unfold filed
            rw [hst, flips_fileJ]
            dsimp only
            by_cases hy : p.2 = x
            · rw [if_pos hy, hy, (has_false _ _).2 (hx k), hs]
              have hh : has ((decideS fam x (.valid f) { s with queue := q }).idx k) x =
                  has (fam.fileKeys x f) k := by
                apply Bool.eq_iff_iff.2
                rw [has_iff, hidx k x, has_iff]
                constructor
                · rintro (h' | ⟨_, g, hg, hk⟩)
                  · exact absurd h' (hx k)
                  · cases hg; exact hk
                · intro hk; exact Or.inr ⟨rfl, f, rfl, hk⟩
              rw [hh]
              obtain ⟨sk, y⟩ := p
              simp only at hy; subst hy
              cases has (fam.fileKeys y f) k <;> by_cases hf : SortKey.sortOf f = sk <;>
                first
                | (simp [sortIs, hf, Prod.ext_iff]; done)
                | simp [sortIs, hf, Prod.ext_iff, Ne.symm hf]
            · rw [if_neg hy]
              have hh : has ((decideS fam x (.valid f) { s with queue := q }).idx k) p.2 = has (s.idx k) p.2 := by
                apply Bool.eq_iff_iff.2
                rw [has_iff, has_iff, hidx k p.2]
                constructor
                · rintro (h' | ⟨e, _⟩)
                  · exact h'
                  · exact absurd e hy
                · exact Or.inl
              rw [hh]
              have : Decidable.decide (p = (SortKey.sortOf f, x)) = false := by
                simp only [decide_eq_false_iff_not]
                intro hp; exact hy (by rw [hp])
              rw [this, Bool.and_false, Bool.xor_false]

/-- A filing's journal touches (k, p) at most once. -/
theorem countP_fileJ_le (fam : Family F) (x : Id) (f : F) (on : Bool) (k : ByteArray) (p : Pos) :
    (fileJ fam x f on).countP (fun e => Decidable.decide (e.key = k ∧ e.pos = p)) ≤ 1 := by
  unfold fileJ
  rw [List.countP_map]
  calc _ ≤ (nubB (fam.fileKeys x f)).countP (fun k' => Decidable.decide (k' = k)) := by
          apply List.countP_mono_left
          intro a _ ha
          simp only [Function.comp, decide_eq_true_eq] at ha ⊢
          exact ha.1
    _ ≤ 1 := by rw [countP_eq_nodup (nodup_nubB _)]; split <;> omega

/-- What a purge's journal holds of op y: its unfilings, if it is Valid. -/
def purgeBlock (fam : Family F) (s : DB F) (y : Id) : List Filing :=
  match s.status y with
  | some (.valid f) => fileJ fam y f false
  | _ => []

/-- A purge's journal touches (k, p) once if p's op is filed there and
in the closure. -/
theorem countP_purgeBlock {fam : Family F} {s : DB F} (h : Inv fam s) (k : ByteArray) (p : Pos) :
    (purgeBlock fam s p.2).countP (fun e => Decidable.decide (e.key = k ∧ e.pos = p)) =
      if filed s k p then 1 else 0 := by
  unfold purgeBlock
  cases hs : s.status p.2 with
  | none =>
    have : filed s k p = false := by unfold filed; rw [hs]; simp [sortIs]
    rw [this]; rfl
  | some v =>
    cases v with
    | invalid =>
      have : filed s k p = false := by unfold filed; rw [hs]; simp [sortIs]
      rw [this]; rfl
    | valid f =>
      simp only
      have hfl := flips_fileJ fam p.2 f false k p
      have hle := countP_fileJ_le fam p.2 f false k p
      have hf : filed s k p = (has (fam.fileKeys p.2 f) k && Decidable.decide (p = (SortKey.sortOf f, p.2))) := by
        apply Bool.eq_iff_iff.2
        rw [filed_iff, Bool.and_eq_true, has_iff, decide_eq_true_iff]
        constructor
        · rintro ⟨g, hg, hgs, hsk⟩
          rw [hs] at hgs; cases hgs
          obtain ⟨g', hg', hk'⟩ := (h.idx k p.2).1 hg
          rw [hs] at hg'; cases hg'
          exact ⟨hk', Prod.ext hsk.symm rfl⟩
        · rintro ⟨hk', hp⟩
          refine ⟨f, (h.idx k p.2).2 ⟨f, hs, hk'⟩, hs, ?_⟩
          rw [hp]
      unfold flips at hfl
      rw [hf, ← hfl]
      revert hle
      generalize List.countP _ _ = n
      intro hle
      rcases n with _ | _ | n
      · rfl
      · rfl
      · omega

theorem purge_exact {fam : Family F} {s : DB F} (h : Inv fam s) (ids : List Id) (k : ByteArray) (p : Pos) :
    filed (purgeS fam ids s) k p = (filed s k p ^^ flips (purgeJ fam ids s) k p) := by
  have hcount : (purgeJ fam ids s).countP (fun e => Decidable.decide (e.key = k ∧ e.pos = p)) =
      if has (closeUp s ids) p.2 then (if filed s k p then 1 else 0) else 0 := by
    show ((nubB (closeUp s ids)).flatMap (purgeBlock fam s)).countP _ = _
    rw [List.countP_flatMap, sum_map_single (y := p.2) (nodup_nubB _)]
    · have hh : has (nubB (closeUp s ids)) p.2 = has (closeUp s ids) p.2 :=
        Bool.eq_iff_iff.2 (by rw [has_iff, has_iff, mem_nubB])
      rw [hh, Function.comp, countP_purgeBlock h k p]
    · intro x _ hx
      simp only [Function.comp, purgeBlock]
      cases s.status x with
      | none => rfl
      | some v =>
        cases v with
        | invalid => rfl
        | valid f =>
          apply List.countP_eq_zero.2
          intro e he
          simp only [decide_eq_true_eq, not_and]
          intro _ hp
          rw [fileJ_pos he] at hp
          exact hx (by rw [← hp])
  have hidx : has ((purgeS fam ids s).idx k) p.2 = (has (s.idx k) p.2 && !has (closeUp s ids) p.2) := by
    apply Bool.eq_iff_iff.2
    rw [has_iff, mem_purgeS_idx, Bool.and_eq_true, has_iff, Bool.not_eq_true', has_false]
  have hf' : filed (purgeS fam ids s) k p = (filed s k p && !has (closeUp s ids) p.2) := by
    unfold filed
    rw [hidx]
    by_cases hc : has (closeUp s ids) p.2 = true
    · rw [purgeS_status_mem s ids ((has_iff _ _).1 hc), hc]; simp [sortIs]
    · rw [purgeS_status_not s ids ((has_false _ _).1 (by simpa using hc))]
      simp only [Bool.not_eq_true] at hc
      simp [hc]
  unfold flips
  rw [hcount, hf']
  by_cases hc : has (closeUp s ids) p.2 = true
  · rw [hc, if_pos rfl]; cases filed s k p <;> rfl
  · simp only [Bool.not_eq_true] at hc
    rw [hc]
    cases filed s k p <;> rfl

theorem change_inv {fam : Family F} {s : DB F} (h : Inv fam s) : ∀ c : Change, Inv fam (c.apply fam s)
  | .ingest o => inv_ingest h o
  | .step => inv_step h
  | .purge ids => purge_inv h ids

theorem change_exact {fam : Family F} {s : DB F} (h : Inv fam s) (c : Change) (k : ByteArray) (p : Pos) :
    filed (c.apply fam s) k p = (filed s k p ^^ flips (c.journal fam s) k p) := by
  cases c with
  | ingest o => exact ingest_exact o s k p
  | step => exact step_exact h k p
  | purge ids => exact purge_exact h ids k p

/-- **The journal is exact.** After any batch of changes, a row is filed
exactly when it was before or the journal touched it an odd number of
times, not both. -/
theorem run_exact {fam : Family F} :
    ∀ (cs : List Change) {s : DB F}, Inv fam s → ∀ k p,
      filed (runJ fam cs s).1 k p = (filed s k p ^^ flips (runJ fam cs s).2 k p)
  | [], s, _, k, p => by simp [runJ, flips_nil]
  | c :: cs, s, h, k, p => by
    simp only [runJ]
    rw [run_exact cs (change_inv h c) k p, change_exact h c k p, flips_append, Bool.xor_assoc]

theorem run_inv {fam : Family F} : ∀ (cs : List Change) {s : DB F}, Inv fam s → Inv fam (runJ fam cs s).1
  | [], _, h => h
  | c :: cs, _, h => run_inv cs (change_inv h c)

/-! ## A filed op keeps its fact -/

/-- One op per id across a batch: some naming of ids names every op the
tables hold and every op the batch stores. It holds when SHA-256 has no
collision among them (`oneOpPerId_of`). -/
def OneOpPerId (s : DB F) (cs : List Change) : Prop :=
  ∃ g : Id → Option Op, Extends s.ops g ∧ ∀ o ∈ Change.ingests cs, g o.id = some o

theorem ingest_extends {s : DB F} {g : Id → Option Op} (h : Extends s.ops g) {o : Op}
    (ho : g o.id = some o) : Extends (ingestS o s).ops g := by
  intro i p hp
  unfold ingestS at hp
  split at hp
  · exact h i p hp
  · change (if i = o.id then some o else s.ops i) = some p at hp
    by_cases hi : i = o.id
    · rw [if_pos hi] at hp; cases hp; rw [hi]; exact ho
    · rw [if_neg hi] at hp; exact h i p hp

theorem change_extends {fam : Family F} {s : DB F} {g : Id → Option Op} (h : Extends s.ops g) :
    ∀ (c : Change), (∀ o, c = .ingest o → g o.id = some o) → Extends (c.apply fam s).ops g
  | .ingest o, hc => ingest_extends h (hc o rfl)
  | .step, _ => by show Extends (stepS fam s).ops g; rw [stepS_ops]; exact h
  | .purge ids, _ => by
    intro i p hp
    show g i = some p
    by_cases hi : i ∈ purgeSet fam s ids
    · change (purgeS fam ids s).ops i = some p at hp
      rw [purgeS_ops_mem s ids hi] at hp; cases hp
    · change (purgeS fam ids s).ops i = some p at hp
      rw [purgeS_ops_not s ids hi] at hp; exact h i p hp

theorem run_extends {fam : Family F} {g : Id → Option Op} :
    ∀ (cs : List Change) {s : DB F}, Extends s.ops g → (∀ o ∈ Change.ingests cs, g o.id = some o) →
      Extends (runJ fam cs s).1.ops g
  | [], _, h, _ => h
  | c :: cs, s, h, hc => by
    have hc' : ∀ o ∈ Change.ingests cs, g o.id = some o := by
      intro o ho
      cases c with
      | ingest o' => exact hc o (List.mem_cons_of_mem _ ho)
      | step => exact hc o ho
      | purge _ => exact hc o ho
    have h1 : ∀ o, c = .ingest o → g o.id = some o := by
      rintro o rfl; exact hc o (List.mem_cons_self ..)
    exact run_extends cs (change_extends h c h1) hc'

theorem All2.mem_left {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {gs : List β}, All2 R l gs → ∀ {a}, a ∈ l → ∃ b, R a b
  | _, _, .nil, _, h => by cases h
  | _, _, .cons hr t, _, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨_, hr⟩
    · exact All2.mem_left t h

/-- Everything a Valid op requires, transitively, is Valid. -/
theorem spec_closure {fam : Family F} {ops : Id → Option Op} {x : Id} {f : F}
    (h : Spec fam ops x (.valid f)) {y : Id} (hr : Sync.Reach ops x y) : ∃ g, Spec fam ops y (.valid g) := by
  induction hr with
  | refl => exact ⟨f, h⟩
  | step _ hy hr' ih =>
    obtain ⟨g, hg⟩ := ih
    obtain ⟨o', fs, ho', hall, _⟩ := spec_valid_inv hg
    rw [hy] at ho'; cases ho'
    exact hall.mem_left hr'

/-- **A filed op keeps its fact.** Two states that hold one op per id
(both within one naming g) give an op Valid in both the same fact: its
requirement closure is the same ops in both, and the verdict reads only
that (`Sync.spec_local`). -/
theorem fact_stable {fam : Family F} {s t : DB F} (hs : Inv fam s) (ht : Inv fam t)
    {g : Id → Option Op} (es : Extends s.ops g) (et : Extends t.ops g) {x : Id} {f f' : F}
    (h1 : s.status x = some (.valid f)) (h2 : t.status x = some (.valid f')) : f = f' := by
  have sp := hs.sound x _ h1
  have tp := ht.sound x _ h2
  -- what x reaches in t, it reaches in s, through the same ops
  have reach : ∀ {y}, Sync.Reach t.ops x y → Sync.Reach s.ops x y := by
    intro y hr
    induction hr with
    | refl => exact .refl
    | @step y o r _ hy hr' ih =>
      obtain ⟨_, hyv⟩ := spec_closure sp ih
      obtain ⟨o', _, ho', _⟩ := spec_valid_inv hyv
      have := (es y o' ho').symm.trans (et y o hy)
      cases this
      exact .step ih ho' hr'
  have hold : ∀ y o, Sync.Reach t.ops x y → t.ops y = some o → s.ops y = some o := by
    intro y o hr hy
    obtain ⟨_, hyv⟩ := spec_closure sp (reach hr)
    obtain ⟨o', _, ho', _⟩ := spec_valid_inv hyv
    have := (es y o' ho').symm.trans (et y o hy)
    cases this
    exact ho'
  have := spec_det sp (Sync.spec_local fam tp hold)
  cases this; rfl

/-! ## Windows -/

/-- A window's rows: those filed under its key in its range, ascending. -/
def window (s : DB F) (w : Win) : List (Pos × F) :=
  (matching s { key := w.key }).filter fun r => w.inside r.1

theorem mem_window {s : DB F} {w : Win} {r : Pos × F} :
    r ∈ window s w ↔ w.inside r.1 = true ∧ filed s w.key r.1 = true ∧ s.status r.1.2 = some (.valid r.2) := by
  unfold window
  rw [List.mem_filter, mem_matching w.key (some 0), filed_iff]
  constructor
  · rintro ⟨⟨x, f, rfl, hx, hf⟩, hin⟩
    exact ⟨hin, ⟨f, hx, hf, rfl⟩, hf⟩
  · rintro ⟨hin, ⟨f, hx, hf, hsk⟩, hr⟩
    rw [hf] at hr; cases hr
    exact ⟨⟨r.1.2, r.2, by rw [hsk], hx, hf⟩, hin⟩

/-- A window's rows strictly ascend: sorted, and no two share a position. -/
theorem window_strict {fam : Family F} {s : DB F} (h : Inv fam s) (w : Win) :
    (window s w).Pairwise fun a b => a.1.cmp b.1 = .lt := by
  have hs := sortPos_sorted ((s.idx w.key).filterMap fun x =>
    if ([] : List ByteArray).all (fun k => has (s.idx k) x) then
      match s.status x with
      | some (.valid f) => some ((SortKey.sortOf f, x), f)
      | _ => none
    else none)
  have hn := matching_nodup h { key := w.key }
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map] at hn
  have both := (List.Pairwise.and hs hn)
  unfold window
  refine (both.filter _).imp fun ⟨h1, h2⟩ => strict_of h1 fun e => h2 (by rw [e])

/-- Two strictly ascending lists with the same rows are one list. -/
theorem eq_of_strict {α : Type} : ∀ {l₁ l₂ : List (Pos × α)},
    l₁.Pairwise (fun a b => a.1.cmp b.1 = .lt) → l₂.Pairwise (fun a b => a.1.cmp b.1 = .lt) →
      (∀ a, a ∈ l₁ ↔ a ∈ l₂) → l₁ = l₂
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).2 (List.mem_cons_self ..)) (by simp)
  | a :: _, [], _, _, h => absurd ((h a).1 (List.mem_cons_self ..)) (by simp)
  | a :: t₁, b :: t₂, h1, h2, h => by
    rw [List.pairwise_cons] at h1 h2
    have self : ∀ c : Pos × α, c.1.cmp c.1 ≠ .lt := fun c => by rw [(Pos.cmp_eq_iff _ _).2 rfl]; simp
    have hab : a = b := by
      rcases List.mem_cons.1 ((h a).1 (List.mem_cons_self ..)) with e | ha
      · exact e
      rcases List.mem_cons.1 ((h b).2 (List.mem_cons_self ..)) with e | hb
      · exact e.symm
      have x1 := h1.1 b hb
      have x2 := h2.1 a ha
      rw [Pos.cmp_swap, x2] at x1
      cases x1
    subst hab
    have ht : ∀ c, c ∈ t₁ ↔ c ∈ t₂ := by
      intro c
      constructor
      · intro hc
        rcases List.mem_cons.1 ((h c).1 (List.mem_cons_of_mem _ hc)) with rfl | hc'
        · exact absurd (h1.1 c hc) (self c)
        · exact hc'
      · intro hc
        rcases List.mem_cons.1 ((h c).2 (List.mem_cons_of_mem _ hc)) with rfl | hc'
        · exact absurd (h2.1 c hc) (self c)
        · exact hc'
    rw [eq_of_strict h1.2 h2.2 ht]

/-- **A window changes exactly when a row in its range came or went**,
between two states whose filed ops keep their facts. -/
theorem window_ne_iff {fam : Family F} {s t : DB F} (hs : Inv fam s) (ht : Inv fam t)
    (hst : ∀ x f f', s.status x = some (.valid f) → t.status x = some (.valid f') → f = f') (w : Win) :
    window s w ≠ window t w ↔ ∃ p, w.inside p = true ∧ filed s w.key p ≠ filed t w.key p := by
  constructor
  · intro hne
    apply Classical.byContradiction
    intro hno
    apply hne
    have same : ∀ p, w.inside p = true → filed s w.key p = filed t w.key p := by
      intro p hp
      apply Classical.byContradiction
      intro hd
      exact hno ⟨p, hp, hd⟩
    refine eq_of_strict (window_strict hs w) (window_strict ht w) fun r => ?_
    rw [mem_window, mem_window]
    constructor
    · rintro ⟨hin, hf, hv⟩
      have hf' := same r.1 hin ▸ hf
      obtain ⟨g, _, hg, _⟩ := filed_iff.1 hf'
      have := hst _ _ _ hv hg
      subst this
      exact ⟨hin, hf', hg⟩
    · rintro ⟨hin, hf, hv⟩
      have hf' := (same r.1 hin).symm ▸ hf
      obtain ⟨g, _, hg, _⟩ := filed_iff.1 hf'
      have := hst _ _ _ hg hv
      subst this
      exact ⟨hin, hf', hg⟩
  · rintro ⟨p, hin, hd⟩ heq
    cases e1 : filed s w.key p <;> cases e2 : filed t w.key p
    · exact hd (by rw [e1, e2])
    · obtain ⟨f, _, hf, _⟩ := filed_iff.1 e2
      have hr : (p, f) ∈ window t w := mem_window.2 ⟨hin, e2, hf⟩
      rw [← heq] at hr
      rw [(mem_window.1 hr).2.1] at e1; cases e1
    · obtain ⟨f, _, hf, _⟩ := filed_iff.1 e1
      have hr : (p, f) ∈ window s w := mem_window.2 ⟨hin, e1, hf⟩
      rw [heq] at hr
      rw [(mem_window.1 hr).2.1] at e2; cases e2
    · exact hd (by rw [e1, e2])

/-- **The net filings name exactly the windows a batch changed.** A
window changes over a batch exactly when the journal touched a row in
its range an odd number of times. -/
theorem window_ne_iff_flips {fam : Family F} {s : DB F} (hs : Inv fam s) {cs : List Change}
    (ho : OneOpPerId s cs) (w : Win) :
    window s w ≠ window (runJ fam cs s).1 w ↔
      ∃ p, w.inside p = true ∧ flips (runJ fam cs s).2 w.key p = true := by
  obtain ⟨g, es, eg⟩ := ho
  have ht := run_inv cs hs (fam := fam)
  have et := run_extends cs es eg (fam := fam)
  rw [window_ne_iff hs ht (fun x f f' h1 h2 => fact_stable hs ht es et h1 h2) w]
  constructor
  · rintro ⟨p, hin, hd⟩
    refine ⟨p, hin, ?_⟩
    rw [run_exact cs hs w.key p] at hd
    revert hd
    cases filed s w.key p <;> cases flips (runJ fam cs s).2 w.key p <;> simp
  · rintro ⟨p, hin, hf⟩
    refine ⟨p, hin, ?_⟩
    rw [run_exact cs hs w.key p, hf]
    cases filed s w.key p <;> simp

/-- **One op per id holds when SHA-256 has no collision** among the ops
the tables were built from and the ops the batch stores. -/
theorem oneOpPerId_of {fam : Family F} {L : List Op} {s : DB F} (hr : Reach fam L s) {cs : List Change}
    (hc : CollisionFree (L ++ Change.ingests cs)) : OneOpPerId s cs := by
  have hd := distinct_of_collisionFree hc
  let M := L ++ Change.ingests cs
  refine ⟨fun i => M.find? (fun o => Decidable.decide (o.id = i)), ?_, ?_⟩
  · intro i o ho
    obtain ⟨hL, hid⟩ := reach_stored hr i o ho
    have hm : o ∈ M := List.mem_append_left _ hL
    obtain ⟨o', ho'⟩ := Option.isSome_iff_exists.1
      ((List.find?_isSome (p := fun o' : Op => Decidable.decide (o'.id = i))).2 ⟨o, hm, decide_eq_true hid⟩)
    have h0 := List.find?_some (p := fun o' : Op => Decidable.decide (o'.id = i)) ho'
    have h1 : o'.id = i := of_decide_eq_true h0
    have h2 := List.mem_of_find?_eq_some ho'
    show M.find? _ = some o
    rw [ho', hd o' h2 o hm (h1.trans hid.symm)]
  · intro o ho
    have hm : o ∈ M := List.mem_append_right _ ho
    obtain ⟨o', ho'⟩ := Option.isSome_iff_exists.1
      ((List.find?_isSome (p := fun o' : Op => Decidable.decide (o'.id = o.id))).2 ⟨o, hm, decide_eq_true rfl⟩)
    have h0 := List.find?_some (p := fun o' : Op => Decidable.decide (o'.id = o.id)) ho'
    have h1 : o'.id = o.id := of_decide_eq_true h0
    have h2 := List.mem_of_find?_eq_some ho'
    show M.find? _ = some o
    rw [ho', hd o' h2 o hm h1]

/-! ## Notices are exact -/

/-- **Notices are exact.** Over any batch of changes (ops stored, steps
judged, purges, in any order), with one op per id: the index notifies a
subscriber of the batch's net filings exactly when one of its windows
changed. ⇐ is completeness: no window changes unnoticed. ⇒ is
precision: no notice for a row outside every window of the subscriber's,
nor for a row filed and unfiled within the batch. -/
theorem notice_iff {S : Type} {fam : Family F} {s : DB F} (hs : Inv fam s) {cs : List Change}
    (ho : OneOpPerId s cs) {I : Subs S} (hI : I.WF) (x : S) :
    x ∈ I.notify (runJ fam cs s).2.toArray ↔ ∃ w, I.Has x w ∧ window s w ≠ window (runJ fam cs s).1 w := by
  unfold Subs.notify
  rw [Subs.mem_notifyM hI]
  constructor
  · rintro ⟨e, he, w, hw, hh⟩
    simp only [Win.has, Bool.and_eq_true, decide_eq_true_eq] at hh
    rw [mem_net, List.toList_toArray] at he
    refine ⟨w, hw, (window_ne_iff_flips hs ho w).2 ⟨e.2, hh.2, ?_⟩⟩
    rw [← hh.1]; exact he
  · rintro ⟨w, hw, hne⟩
    obtain ⟨p, hin, hf⟩ := (window_ne_iff_flips hs ho w).1 hne
    refine ⟨(w.key, p), ?_, w, hw, by simp [Win.has, hin]⟩
    rw [mem_net, List.toList_toArray]; exact hf

end

end Engine
