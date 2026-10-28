/-
The epidemic step, proven: per-edge progress gives convergence over any
connected knows-graph, with the bound d · B for a node d edges away
(`hops`). With stores that only grow, an op reaches every node and
stays (`converge_of_edge`). From these, also proven:
- everyone knowing everyone is d = 1 (`converge_all_of`), two peers a
  case of it (`converge_two_of`);
- a chain of n has diameter n - 1 (`diam_chain`), so three peers who
  know each other transitively converge within two epochs
  (`converge_three_of`), and a chain within n - 1 (`chain_of`);
- a star has diameter 2 (`diam_star`, `star_of`), a web its source's
  eccentricity (`web_of`), and every path its length (`op_of`);
- a node back from offline catches up, and its outbox goes out, within
  d · B (`offline_of`).

None of this names node code: it is about the world's `Holds`, the
network's `Calm`, and an execution's times, so it applies to the running
nodes as soon as the per-edge bound (`edge_stmt`) and growth
(`grows_stmt`) are proven of them.
-/
import engine.world.Statements

namespace Engine.World
open Engine Engine.Sync

variable {F : Type} {M : Type → Type} {S : Type} [Monad M] [Store F M] [Turn F M]
variable {P : Setup F M S} {adv : World S P.n → ByteArray → Prop} {w₀ : World S P.n}

/-! ## Time only goes forward -/

/-- A legal step never sets the clock back. -/
theorem step_now (w : World S P.n) (a : Act P.n) (h : Legal P adv w a) : w.now ≤ (w.step P a).now := by
  cases a with
  | deliver k t =>
    simp only [Legal] at h
    simp only [World.step]
    split
    · exact Nat.le_refl _
    · split
      · exact h.2
      · simp only [World.enter]; exact h.2
  | dup k => simp only [World.step]; split <;> exact Nat.le_refl _
  | drop k => exact Nat.le_refl _
  | tick i t => exact h
  | write i ops t => exact h.1
  | restart i t => exact h
  | connect i j cid d t => exact h.2
  | inject i o b t => exact h.2

/-- Along an execution, time only goes forward. -/
theorem Exec.now_mono (E : Exec P adv w₀) {k k' : Nat} (h : k ≤ k') : (E.world k).now ≤ (E.world k').now := by
  induction k' with
  | zero => rw [Nat.le_zero.1 h]; exact Nat.le_refl _
  | succ k' ih =>
    rcases Nat.lt_or_ge k (k' + 1) with hl | hl
    · exact Nat.le_trans (ih (by omega)) (step_now _ _ (E.legal k'))
    · rw [show k = k' + 1 by omega]; exact Nat.le_refl _

/-! ## The network over shorter spans -/

theorem Net.Live.mono {n : Nat} {N : Net n} {i j : Fin n} {a b c d : Nat} (h : N.Live i j a b) (hc : a ≤ c)
    (hd : d ≤ b) : N.Live i j c d := fun t h1 h2 => h t (by omega) (by omega)

theorem Net.Calm.mono {n : Nat} {N : Net n} {a b c d : Nat} (h : N.Calm a b) (hc : a ≤ c) (hd : d ≤ b) :
    N.Calm c d :=
  ⟨fun i t h1 h2 => h.1 i t (by omega) (by omega), fun i j g => (h.2 i j g).mono hc hd⟩

/-! ## Hops -/

/-- **Hops.** Under the per-edge bound B, with every edge live: an op a
node holds at step k ≥ k₀, the node d edges away holds within d · B. -/
theorem hops (E : Exec P adv w₀) {N : Net P.n} {r : Id} {k₀ B : Nat} (hE : Edge E N r k₀ B) :
    ∀ {d : Nat} {i j : Fin P.n}, Path N.G d i j → ∀ k x, k₀ ≤ k → N.gst ≤ (E.world k).now →
      N.Calm (E.world k).now ((E.world k).now + d * B) → Holds P (E.world k) i r x →
        ∃ k', k ≤ k' ∧ (E.world k').now ≤ (E.world k).now + d * B ∧ Holds P (E.world k') j r x := by
  intro d i j hp
  induction hp with
  | refl i => intro k x _ _ _ hx; exact ⟨k, Nat.le_refl _, by omega, hx⟩
  | @step d i j l hij _ ih =>
    intro k x hk hg hc hx
    have hB : (E.world k).now + B ≤ (E.world k).now + (d + 1) * B := by
      rw [Nat.succ_mul]; omega
    obtain ⟨k₁, hk₁, ht₁, hx₁⟩ := hE k i j x hk hg hij ((hc.2 i j hij).mono (Nat.le_refl _) hB) hx
    have hm := Exec.now_mono E hk₁
    obtain ⟨k₂, hk₂, ht₂, hx₂⟩ := ih k₁ x (by omega) (by omega)
      (hc.mono hm (by rw [Nat.succ_mul]; omega)) hx₁
    refine ⟨k₂, by omega, ?_, hx₂⟩
    rw [Nat.succ_mul]; omega

/-- Growth along an execution: what a store holds at step k it holds at
every later step. -/
theorem held_on (E : Exec P adv w₀) {i : Fin P.n} {r x : Id}
    (hg : ∀ k, Holds P (E.world k) i r x → Holds P (E.world (k + 1)) i r x) :
    ∀ k k', k ≤ k' → Holds P (E.world k) i r x → Holds P (E.world k') i r x := by
  intro k k' hle hx
  induction k' with
  | zero => rw [Nat.le_zero.1 hle] at hx; exact hx
  | succ k' ih =>
    rcases Nat.lt_or_ge k (k' + 1) with h | h
    · exact hg k' (ih (by omega))
    · rw [show k = k' + 1 by omega] at hx; exact hx

/-! ## Graphs -/

theorem Path.mono {α : Type} {G G' : α → α → Prop} (hG : ∀ a b, G a b → G' a b) :
    ∀ {d : Nat} {i j : α}, Path G d i j → Path G' d i j
  | _, _, _, .refl i => .refl i
  | _, _, _, .step h p => .step (hG _ _ h) (Path.mono hG p)

theorem Diam.mono {α : Type} {G G' : α → α → Prop} {d : Nat} (h : Diam G d) (hG : ∀ a b, G a b → G' a b) :
    Diam G' d := fun i j => (h i j).imp fun _ ⟨he, hp⟩ => ⟨he, hp.mono hG⟩

/-- Everyone knowing everyone is diameter one. -/
theorem diam_allKnow {α : Type} {G : α → α → Prop} [DecidableEq α] (h : AllKnow G) : Diam G 1 := by
  intro i j
  by_cases e : i = j
  · subst e; exact ⟨0, by omega, .refl i⟩
  · exact ⟨1, Nat.le_refl _, .step (h i j e) (.refl j)⟩

/-- Up a chain, m steps. -/
theorem chain_up {n : Nat} : ∀ (m : Nat) (i j : Fin n), j.val = i.val + m → Path (chain n) m i j := by
  intro m
  induction m with
  | zero => intro i j h; rw [Fin.ext (by omega : i.val = j.val)]; exact .refl j
  | succ m ih =>
    intro i j h
    have hi : i.val + 1 < n := by have := j.isLt; omega
    exact .step (j := ⟨i.val + 1, hi⟩) (Or.inl rfl) (ih _ j (by simp; omega))

/-- Down a chain, m steps. -/
theorem chain_down {n : Nat} : ∀ (m : Nat) (i j : Fin n), i.val = j.val + m → Path (chain n) m i j := by
  intro m
  induction m with
  | zero => intro i j h; rw [Fin.ext (by omega : i.val = j.val)]; exact .refl j
  | succ m ih =>
    intro i j h
    have hi : i.val - 1 < n := by have := i.isLt; omega
    exact .step (j := ⟨i.val - 1, hi⟩) (Or.inr (by simp; omega)) (ih _ j (by simp; omega))

/-- **A chain of n has diameter n - 1.** -/
theorem diam_chain (n : Nat) : Diam (chain n) (n - 1) := by
  intro i j
  have := i.isLt; have := j.isLt
  rcases Nat.le_total i.val j.val with h | h
  · exact ⟨j.val - i.val, by omega, chain_up _ i j (by omega)⟩
  · exact ⟨i.val - j.val, by omega, chain_down _ i j (by omega)⟩

/-- **A star has diameter 2.** -/
theorem diam_star (n : Nat) : Diam (star n) 2 := by
  intro i j
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  let c : Fin n := ⟨0, hn⟩
  by_cases e : i = j
  · subst e; exact ⟨0, by omega, .refl i⟩
  by_cases hi : i.val = 0
  · exact ⟨1, by omega, .step ⟨e, Or.inl hi⟩ (.refl j)⟩
  by_cases hj : j.val = 0
  · exact ⟨1, by omega, .step ⟨e, Or.inr hj⟩ (.refl j)⟩
  have hic : i ≠ c := fun h => hi (by rw [h])
  have hcj : c ≠ j := fun h => hj (by rw [← h])
  exact ⟨2, Nat.le_refl _, .step (j := c) ⟨hic, Or.inr rfl⟩ (.step ⟨hcj, Or.inl rfl⟩ (.refl j))⟩

/-- Some node is the last to reach a bound: the largest of finitely many. -/
theorem fin_max {n : Nat} (f : Fin n → Nat) (hn : 0 < n) : ∃ l, ∀ l', f l' ≤ f l := by
  have : ∀ L : List (Fin n), L ≠ [] → ∃ l ∈ L, ∀ l' ∈ L, f l' ≤ f l := by
    intro L
    induction L with
    | nil => intro h; exact absurd rfl h
    | cons a t ih =>
      intro _
      cases t with
      | nil => exact ⟨a, List.mem_cons_self .., fun l' hl => by
          rw [List.mem_singleton.1 hl]; exact Nat.le_refl _⟩
      | cons b t' =>
        obtain ⟨m, hm, hmax⟩ := ih (List.cons_ne_nil _ _)
        by_cases hle : f a ≤ f m
        · exact ⟨m, List.mem_cons_of_mem _ hm, fun l' hl => by
            rcases List.mem_cons.1 hl with rfl | hl
            · exact hle
            · exact hmax l' hl⟩
        · exact ⟨a, List.mem_cons_self .., fun l' hl => by
            rcases List.mem_cons.1 hl with rfl | hl
            · exact Nat.le_refl _
            · exact Nat.le_trans (hmax l' hl) (by omega)⟩
  obtain ⟨l, -, h⟩ := this (List.finRange n) (by
    intro e; have := List.length_finRange (n := n); rw [e] at this; simp at this; omega)
  exact ⟨l, fun l' => h l' (List.mem_finRange l')⟩

/-! ## Convergence -/

/-- **The reduction, proven:** the per-edge bound and growth give
convergence over any connected knows-graph. -/
theorem converge_of_edge : converge_of_edge_stmt := by
  intro hedge hgrow F Q N E r k₀ W d hf hc hd k i j x hk hg hcalm hx
  obtain ⟨e, he, hp⟩ := hd i j
  have hb : e * Q.epochW N W ≤ d * Q.epochW N W := Nat.mul_le_mul_right _ he
  obtain ⟨k', hk', ht, hx'⟩ :=
    hops E (hedge F Q N E r k₀ W hf hc) hp k x hk hg (hcalm.mono (Nat.le_refl _) (by omega)) hx
  refine ⟨k', hk', by omega, fun k'' hk'' => held_on E (fun m hm => ?_) k' k'' hk'' hx'⟩
  exact hgrow F Q noAdv _ _ j r x (E.reachable m) (E.legal m) hm

/-- **When everyone knows everyone, one epoch.** -/
theorem converge_all_of (h : converge_stmt) : converge_all_stmt := by
  intro F Q N E r k₀ W hf hc hall k i j x hk hg hcalm hx
  obtain ⟨k', hk', ht, hx'⟩ := h F Q N E r k₀ W 1 hf hc (diam_allKnow hall) k i j x hk hg
    (by simpa using hcalm) hx
  exact ⟨k', hk', by simpa using ht, hx'⟩

/-- **Two peers.** -/
theorem converge_two_of (h : converge_stmt) : converge_two_stmt := by
  intro F Q N E r k₀ W _ hf hc hall
  exact converge_all_of h F Q N E r k₀ W hf hc hall

/-- **Three peers who know each other transitively.** -/
theorem converge_three_of (h : converge_stmt) : converge_three_stmt := by
  intro F Q N E r k₀ W hn hf hc hG k i j x hk hg hcalm hx
  have hd : Diam N.G 2 := by
    have e : Q.n - 1 = 2 := by omega
    have := (diam_chain Q.n).mono hG; rw [e] at this; exact this
  exact h F Q N E r k₀ W 2 hf hc hd k i j x hk hg hcalm hx

/-! ## Paths, chains, stars and webs, from the per-edge bound -/

/-- **T-op from the per-edge bound.** -/
theorem op_of (h : edge_stmt) : op_stmt := by
  intro F Q N E r k₀ W d i j hf hc hp k x hk hg hcalm hx
  exact hops E (h F Q N E r k₀ W hf hc) hp k x hk hg hcalm hx

/-- Within a diameter, from the per-edge bound. -/
theorem within_of (h : edge_stmt) {F : Type} {Q : Plain F} {N : Net Q.n} {E : Q.Run} {r : Id} {k₀ W d : Nat}
    (hf : Fair Q N E W) (hc : Carries E N.G r k₀) (hd : Diam N.G d) (k : Nat) (i j : Fin Q.n) (x : Id)
    (hk : k₀ ≤ k) (hg : N.gst ≤ (E.world k).now)
    (hcalm : N.Calm (E.world k).now ((E.world k).now + d * Q.epochW N W)) (hx : Q.Holds (E.world k) i r x) :
    ∃ k', k ≤ k' ∧ (E.world k').now ≤ (E.world k).now + d * Q.epochW N W ∧ Q.Holds (E.world k') j r x := by
  obtain ⟨e, he, hp⟩ := hd i j
  have hb : e * Q.epochW N W ≤ d * Q.epochW N W := Nat.mul_le_mul_right _ he
  obtain ⟨k', hk', ht, hx'⟩ :=
    hops E (h F Q N E r k₀ W hf hc) hp k x hk hg (hcalm.mono (Nat.le_refl _) (by omega)) hx
  exact ⟨k', hk', by omega, hx'⟩

/-- **A chain: n - 1 epochs.** -/
theorem chain_of (h : edge_stmt) : chain_stmt := by
  intro F Q N E r k₀ W hf hc hG k i j x hk hg hcalm hx
  exact within_of h hf hc ((diam_chain Q.n).mono hG) k i j x hk hg hcalm hx

/-- **A star: two epochs.** -/
theorem star_of (h : edge_stmt) : star_stmt := by
  intro F Q N E r k₀ W hf hc hG k i j x hk hg hcalm hx
  exact within_of h hf hc ((diam_star Q.n).mono hG) k i j x hk hg hcalm hx

/-- **A web: the source's eccentricity in epochs.** -/
theorem web_of (h : edge_stmt) : web_stmt := by
  intro F Q N E r k₀ W e s hf hc he k j x hk hg hcalm hx
  obtain ⟨d, hd, hp⟩ := he j
  have hb : d * Q.epochW N W ≤ e * Q.epochW N W := Nat.mul_le_mul_right _ hd
  obtain ⟨k', hk', ht, hx'⟩ :=
    hops E (h F Q N E r k₀ W hf hc) hp k x hk hg (hcalm.mono (Nat.le_refl _) (by omega)) hx
  exact ⟨k', hk', by omega, hx'⟩

/-- **T-offline from convergence:** everything held when a node comes
back, every node holds, at one step, within d · epoch. -/
theorem offline_of (h : converge_stmt) : offline_stmt := by
  intro F Q N E r k₀ W d hf hc hd k hk hg hcalm j x hx
  have each := fun l => h F Q N E r k₀ W d hf hc hd k j l x hk hg hcalm hx
  by_cases hn : 0 < Q.n
  · let f := fun l => Classical.choose (each l)
    have hs := fun l => Classical.choose_spec (each l)
    obtain ⟨l, hl⟩ := fin_max f hn
    exact ⟨f l, (hs l).1, (hs l).2.1, fun l' => (hs l').2.2 (f l) (hl l')⟩
  · exact ⟨k, Nat.le_refl _, by omega, fun l => absurd l.isLt (by omega)⟩

end Engine.World
