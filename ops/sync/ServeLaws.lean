/-
Read traces and byte bounds for the want reader used by Conn.onWant.
The trace is the running read program with a pure store lookup; its
interpreters below agree on both held stores and the engine's DB.
-/
import engine.wire.NodeLaws

namespace Engine.Sync

variable {F : Type}

theorem Read.run_held (p : Read α) (h : Held F) :
    (p.run (Store.getOp (F := F)) : HeldM F α) h = ((p.trace h.db.ops).1, h) := by
  induction p with
  | done a => rfl
  | get i next ih => simp [Read.run, Read.trace, ih]

theorem Read.run_model (p : Read α) (s : DB F) :
    (p.run (Store.getOp (F := F)) : Model F α).run s = ((p.trace s.ops).1, s) := by
  induction p with
  | done a => rfl
  | get i next ih => simp [Read.run, Read.trace, ih]

theorem serve_reads (shows : Op → Bool) (get : Id → Option Op) (ids : List Id) (budget : Nat) :
    ∀ i ∈ ((serve shows budget ids).trace get).2, i ∈ ids := by
  induction ids generalizing budget with
  | nil => simp [serve, Read.trace]
  | cons x xs ih =>
    simp only [serve]
    split
    · simp [Read.trace]
    · simp only [Read.trace]
      intro i hi
      rcases List.mem_cons.1 hi with rfl | hi
      · exact List.mem_cons_self ..
      · apply List.mem_cons_of_mem
        cases hg : get x <;> simp only [hg] at hi
        · exact ih _ i hi
        · split at hi
          · split at hi
            · cases hi
            · rw [Read.trace_map] at hi; exact ih _ i hi
          · exact ih _ i hi

theorem serve_shown (shows : Op → Bool) (get : Id → Option Op) (ids : List Id) (budget : Nat) :
    ∀ o ∈ ((serve shows budget ids).trace get).1,
      shows o = true ∧ ∃ i ∈ ids, get i = some o := by
  induction ids generalizing budget with
  | nil => simp [serve, Read.trace]
  | cons x xs ih =>
    simp only [serve]
    split
    · simp [Read.trace]
    · simp only [Read.trace]
      cases hg : get x with
      | none =>
        intro o ho
        obtain ⟨hs, i, hi, e⟩ := ih budget o ho
        exact ⟨hs, i, List.mem_cons_of_mem _ hi, e⟩
      | some y =>
        dsimp only
        split
        · rename_i hy
          split
          · intro o ho; obtain rfl := List.mem_singleton.1 ho
            exact ⟨hy, x, List.mem_cons_self .., hg⟩
          · rw [Read.trace_map]
            intro o ho
            rcases List.mem_cons.1 ho with rfl | ho
            · exact ⟨hy, x, List.mem_cons_self .., hg⟩
            · obtain ⟨hs, i, hi, e⟩ := ih _ o ho
              exact ⟨hs, i, List.mem_cons_of_mem _ hi, e⟩
        · intro o ho
          obtain ⟨hs, i, hi, e⟩ := ih budget o ho
          exact ⟨hs, i, List.mem_cons_of_mem _ hi, e⟩

theorem serve_blind (shows : Op → Bool) (a b : Id → Option Op) (ids : List Id) (budget : Nat)
    (agree : ∀ i ∈ ids, a i = b i) :
    (serve shows budget ids).trace a = (serve shows budget ids).trace b := by
  induction ids generalizing budget with
  | nil => rfl
  | cons x xs ih =>
    simp only [serve]
    split
    · rfl
    · simp only [Read.trace, agree x (List.mem_cons_self ..)]
      have ht := fun i hi => agree i (List.mem_cons_of_mem x hi)
      cases b x
      · simp [ih _ ht]
      · dsimp only; split
        · split
          · rfl
          · simp [Read.trace_map, ih _ ht]
        · simp [ih _ ht]

theorem serve_budget (shows : Op → Bool) (get : Id → Option Op) (ids : List Id) (budget : Nat) :
    let ops := ((serve shows budget ids).trace get).1
    replyBytes ops ≤ budget + largestOp ops := by
  induction ids generalizing budget with
  | nil => simp [serve, Read.trace, replyBytes, largestOp]
  | cons x xs ih =>
    simp only [serve]
    split
    · simp [Read.trace, replyBytes, largestOp]
    · simp only [Read.trace]
      cases get x with
      | none => exact ih budget
      | some o =>
        dsimp only; split
        · split
          · simp [Read.trace, replyBytes, largestOp]
          · rw [Read.trace_map]
            dsimp only
            simp only [replyBytes, largestOp, List.map_cons, List.sum_cons, List.foldr_cons]
            have := ih (budget - o.bytes.size)
            dsimp only [replyBytes, largestOp] at this
            omega
        · exact ih budget

theorem authorize_mem (ix : Index) (c : Conn) (ids : List Id) (i : Id) :
    i ∈ authorize ix c ids ↔ i ∈ ids ∧ ∃ r ∈ c.rooms, ∃ a ∈ ix.items r, a.2 = i := by
  simp only [authorize, List.mem_filter, List.any_eq_true, decide_eq_true_eq]

/-- The read plan used by onWant reads only ids indexed in shown rooms. -/
theorem want_reads_authorized (fam : Family F) (cfg : Config) (ix : Index) (c : Conn)
    (ids : List Id) (get : Id → Option Op) :
    ∀ i ∈ ((serve (c.shows fam) cfg.wantBytes (authorize ix c ids)).trace get).2,
      ∃ r ∈ c.rooms, ∃ a ∈ ix.items r, a.2 = i := by
  intro i hi
  exact ((authorize_mem ix c ids i).1 (serve_reads _ _ _ _ i hi)).2

/-- Stores agreeing on the authorized ids have exactly the same reads
and response. Nothing outside the shown index affects either. -/
theorem want_blind (fam : Family F) (cfg : Config) (ix : Index) (c : Conn) (ids : List Id)
    (a b : Id → Option Op)
    (agree : ∀ r ∈ c.rooms, ∀ item ∈ ix.items r, a item.2 = b item.2) :
    (serve (c.shows fam) cfg.wantBytes (authorize ix c ids)).trace a =
      (serve (c.shows fam) cfg.wantBytes (authorize ix c ids)).trace b := by
  apply serve_blind
  intro i hi
  obtain ⟨_, r, hr, item, hm, rfl⟩ := (authorize_mem ix c ids i).1 hi
  exact agree r hr item hm

/-- The same independence for the actual connection handler's result. -/
theorem want_blind_step (fam : Family F) (cfg : Config) (ix : Index) (c : Conn) (ids : List Id)
    (a b : Held F)
    (agree : ∀ r ∈ c.rooms, ∀ item ∈ ix.items r, a.db.ops item.2 = b.db.ops item.2) :
    ((c.onWant fam cfg ix ids : HeldM F Step) a).1 =
      ((c.onWant fam cfg ix ids : HeldM F Step) b).1 := by
  unfold Conn.onWant
  split
  · rfl
  · simp only [HeldM.bind_apply, Read.run_held, HeldM.pure_apply]
    rw [want_blind fam cfg ix c ids a.db.ops b.db.ops agree]

theorem onWant_one (fam : Family F) (cfg : Config) (ix : Index) (c : Conn) (o : Op) (h : Held F)
    (hm : 0 < cfg.maxIds) (hb : 0 < cfg.wantBytes)
    (ha : authorize ix c [o.id] = [o.id]) (hg : h.db.ops o.id = some o)
    (hs : c.shows fam o = true) :
    (c.onWant fam cfg ix [o.id] : HeldM F Step).run h =
      ({ conn := ({ c with
          known := remember cfg.maxKnown c.known o.id } : Conn).queue cfg o.reqs, send := [o] }, h) := by
  have hp : (serve (c.shows fam) cfg.wantBytes [o.id]).trace h.db.ops = ([o], [o.id]) := by
    simp only [serve, Nat.ne_of_gt hb, ite_false, Read.trace, hg, hs, ite_true]
    split <;> rfl
  unfold Conn.onWant
  rw [ite_eq_right (show ¬[o.id].length > cfg.maxIds by simp; omega)]
  change ((serve (c.shows fam) cfg.wantBytes (authorize ix c [o.id])).run (Store.getOp (F := F)) >>= _ : HeldM F Step) h = _
  rw [HeldM.bind_apply, Read.run_held, ha, hp]
  simp

/-- The actual onWant response contains at most wantBytes encoded op
bytes plus its largest op. Zero budget performs no reads. -/
theorem want_budget (fam : Family F) (cfg : Config) (ix : Index) (c : Conn) (ids : List Id) (h : Held F) :
    let s := ((c.onWant fam cfg ix ids : HeldM F Step) h).1
    replyBytes s.send ≤ cfg.wantBytes + largestOp s.send := by
  unfold Conn.onWant
  split
  · simp [replyBytes, largestOp]
  · rw [HeldM.bind_apply, Read.run_held]
    simpa only [HeldM.pure_apply] using serve_budget (c.shows fam) h.db.ops (authorize ix c ids) cfg.wantBytes

end Engine.Sync
