/-
Progress of the actual want reader, followed by delivery and validation of
an operation's finite requirement closure. Queue progress permits unbounded
tail arrivals and zero-budget stalls; service with positive room must recur.
The transport and store obligations are stated separately from the goal.
-/
import engine.sync.ClosureComplete
import engine.sync.ClosureStore

namespace Engine.Sync

local instance : LawfulBEq ByteArray where
  eq_of_beq {a b} h := ByteArray.ext (eq_of_beq (show a.data == b.data from h))
  rfl {a} := show a.data == a.data from beq_self_eq_true a.data

/-- Unless its stored, authorized operation is sent, a wanted id stays in
the queue and never moves back. Positive room moves it strictly forward.
This is about `serve`, the read program used by the running connection. -/
theorem serve_pending (shows : Op → Bool) (get : Id → Option Op)
    (ids : List Id) (budget : Nat) (i : Id) (o : Op)
    (hi : i ∈ ids) (hg : get i = some o) (hs : shows o = true)
    (hn : o ∉ ((serve shows budget ids).trace get).1.1) :
    i ∈ ((serve shows budget ids).trace get).1.2 ∧
    (((serve shows budget ids).trace get).1.2).idxOf i ≤ ids.idxOf i ∧
    (0 < budget → (((serve shows budget ids).trace get).1.2).idxOf i < ids.idxOf i) := by
  induction ids generalizing budget with
  | nil => cases hi
  | cons x xs ih =>
    rcases Nat.eq_zero_or_pos budget with rfl | hb
    · simp only [serve_zero] at *
      exact ⟨hi, Nat.le_refl _, by omega⟩
    have hxi : x ≠ i := by
      intro he
      subst x
      exact hn (serve_head shows get i xs budget hb o hg hs)
    have hit : i ∈ xs := (List.mem_cons.mp hi).resolve_left (Ne.symm hxi)
    rw [serve_cons shows get x xs budget hb] at hn ⊢
    cases hx : get x with
    | none =>
      simp only [hx] at hn ⊢
      obtain ⟨hm, hle, _⟩ := ih budget hit hn
      refine ⟨hm, ?_, ?_⟩ <;> simp [List.idxOf_cons, hxi] <;> omega
    | some p =>
      simp only [hx] at hn ⊢
      by_cases hp : shows p = true
      · simp only [hp, ite_true] at hn ⊢
        by_cases hbudget : budget ≤ p.bytes.size
        · simp only [hbudget, ite_true] at hn ⊢
          exact ⟨hit, by simp [List.idxOf_cons, hxi], by simp [List.idxOf_cons, hxi]⟩
        · simp only [hbudget, ite_false] at hn ⊢
          have hn' : o ∉ ((serve shows (budget - p.bytes.size) xs).trace get).1.1 :=
            fun ho => hn (List.mem_cons_of_mem _ ho)
          obtain ⟨hm, hle, _⟩ := ih (budget - p.bytes.size) hit hn'
          refine ⟨hm, ?_, ?_⟩ <;> simp [List.idxOf_cons, hxi] <;> omega
      · simp only [hp] at hn ⊢
        obtain ⟨hm, hle, _⟩ := ih budget hit hn
        refine ⟨hm, ?_, ?_⟩ <;> simp [List.idxOf_cons, hxi] <;> omega

/-- Removing other ids cannot increase a retained id's queue position. -/
theorem filter_idxOf_le (p : Id → Bool) (ids : List Id) (i : Id)
    (hi : i ∈ ids) (hp : p i = true) : (ids.filter p).idxOf i ≤ ids.idxOf i := by
  induction ids with
  | nil => cases hi
  | cons x xs ih =>
    by_cases hx : x = i
    · subst x
      simp [hp]
    · have hit := (List.mem_cons.mp hi).resolve_left (Ne.symm hx)
      have hle := ih hit
      by_cases hpx : p x = true
      · simpa [hpx, List.idxOf_cons, hx] using hle
      · simp [hpx, List.idxOf_cons, hx]
        omega

/-- Hot writes cannot starve the ordinary queue: a hot target is emitted
immediately; every other target survives hot filtering and advances under
the ordinary byte budget. This covers the actual `first` argument that
`Node.serveOwed` supplies, even when hot writes continue forever. -/
theorem serveOwed_pending {F : Type} (fam : Family F) (cfg : Config)
    (c : Conn) (h : Held F) (budget : Nat) (first : List Id) (i : Id) (o : Op)
    (hi : i ∈ c.owed) (hg : h.db.ops i = some o) (hs : c.shows fam o = true)
    (hn : o ∉ ((c.serveOwed fam cfg budget first : HeldM F _) h).1.2.1 ++
      ((c.serveOwed fam cfg budget first : HeldM F _) h).1.2.2) :
    i ∈ ((c.serveOwed fam cfg budget first : HeldM F _) h).1.1.owed ∧
    (((c.serveOwed fam cfg budget first : HeldM F _) h).1.1.owed).idxOf i ≤ c.owed.idxOf i ∧
    (0 < budget → (((c.serveOwed fam cfg budget first : HeldM F _) h).1.1.owed).idxOf i < c.owed.idxOf i) := by
  have run := serveOwed_run fam cfg c budget first h
  have hhot : i ∉ c.hotOf first := by
    intro hh
    have sent := fetch_all (c.shows fam) h.db.ops (c.hotOf first) i o hh hg hs
    apply hn
    rw [run.1]
    exact List.mem_append_left _ sent
  have hm : i ∈ c.owedAfter first := by
    unfold Conn.owedAfter
    split
    · exact hi
    · simp [hi, hhot]
  have hidx : (c.owedAfter first).idxOf i ≤ c.owed.idxOf i := by
    unfold Conn.owedAfter
    split
    · exact Nat.le_refl _
    · exact filter_idxOf_le _ _ i hi (by simpa using hhot)
  have hno : o ∉ ((serve (c.shows fam) budget (c.owedAfter first)).trace h.db.ops).1.1 := by
    intro ho
    apply hn
    rw [run.1]
    exact List.mem_append_right _ ho
  obtain ⟨hmem, hle, hlt⟩ := serve_pending _ _ _ _ i o hm hg hs hno
  rw [run.2.1]
  exact ⟨hmem, Nat.le_trans hle hidx, fun hb => Nat.lt_of_lt_of_le (hlt hb) hidx⟩

/-- A sequence of actual `serveOwed` calls. Between calls, fresh wants may
join at the tail. Source reads, connection rooms, and budgets may change;
the per-operation theorem states exactly the stability it needs. Hot-write
priorities may change arbitrarily without starving older ordinary requests. -/
structure ServiceRun {F : Type} (fam : Family F) (cfg : Config) where
  store : Nat → Held F
  conn : Nat → Conn
  room : Nat → Nat
  first : Nat → List Id := fun _ => []
  added : Nat → List Id
  next : ∀ n, (conn (n + 1)).owed =
    (((conn n).serveOwed fam cfg (room n) (first n) : HeldM F _) (store n)).1.1.owed ++ added n

namespace ServiceRun
variable {F : Type} {fam : Family F} {cfg : Config} (r : ServiceRun fam cfg)

def emitted (n : Nat) : List Op :=
  let sent := (((r.conn n).serveOwed fam cfg (r.room n) (r.first n) : HeldM F _) (r.store n)).1.2
  sent.1 ++ sent.2

theorem pending {n : Nat} {i : Id} {o : Op}
    (hi : i ∈ (r.conn n).owed) (hg : (r.store n).db.ops i = some o)
    (hs : (r.conn n).shows fam o = true) (hn : o ∉ r.emitted n) :
    i ∈ (r.conn (n + 1)).owed ∧
    (r.conn (n + 1)).owed.idxOf i ≤ (r.conn n).owed.idxOf i ∧
    (0 < r.room n → (r.conn (n + 1)).owed.idxOf i < (r.conn n).owed.idxOf i) := by
  obtain ⟨hm, hle, hlt⟩ := serveOwed_pending fam cfg (r.conn n) (r.store n)
    (r.room n) (r.first n) i o hi hg hs hn
  rw [r.next n]
  refine ⟨List.mem_append_left _ hm, ?_, ?_⟩
  · simpa [List.idxOf_append, hm] using hle
  · simpa [List.idxOf_append, hm] using hlt

/-- No matching emission over a finite interval means the wanted id
remains queued with a nonincreasing number of predecessors. -/
theorem pending_until {n k : Nat} {i : Id} {o : Op} (hnk : n ≤ k)
    (hi : i ∈ (r.conn n).owed)
    (available : ∀ j ≥ n, (r.store j).db.ops i = some o ∧ (r.conn j).shows fam o = true)
    (hn : ∀ j, n ≤ j → j < k → o ∉ r.emitted j) :
    i ∈ (r.conn k).owed ∧ (r.conn k).owed.idxOf i ≤ (r.conn n).owed.idxOf i := by
  induction hnk with
  | refl => exact ⟨hi, Nat.le_refl _⟩
  | @step k hnk ih =>
    have hp := ih (fun j hj hjk => hn j hj (by omega))
    have hs := r.pending hp.1 (available k hnk).1 (available k hnk).2 (hn k hnk (by omega))
    exact ⟨hs.1, Nat.le_trans hs.2.1 hp.2⟩

/-- **Every queued, persistently stored and authorized operation is
eventually emitted by actual `serveOwed`.** Arbitrary tail arrivals do not
delay an existing request indefinitely. The only service fairness premise
is recurring positive room; neither queue emptiness nor final delivery is
assumed. The result also holds after any finite prefix of the run. -/
theorem eventually_emitted
    (service : ∀ N, ∃ j ≥ N, 0 < r.room j)
    {n : Nat} {i : Id} {o : Op} (hi : i ∈ (r.conn n).owed)
    (available : ∀ j ≥ n, (r.store j).db.ops i = some o ∧ (r.conn j).shows fam o = true) :
    ∃ j ≥ n, o ∈ r.emitted j := by
  have progress : ∀ rank n, (r.conn n).owed.idxOf i = rank → i ∈ (r.conn n).owed →
      (∀ j ≥ n, (r.store j).db.ops i = some o ∧ (r.conn j).shows fam o = true) →
      ∃ j ≥ n, o ∈ r.emitted j := by
    intro rank
    induction rank using Nat.strongRecOn with
    | ind rank ih =>
      intro n hr hi available
      obtain ⟨k, hnk, hb⟩ := service n
      classical
      by_cases he : ∃ j, n ≤ j ∧ j < k ∧ o ∈ r.emitted j
      · obtain ⟨j, hnj, _, hj⟩ := he
        exact ⟨j, hnj, hj⟩
      · have hno : ∀ j, n ≤ j → j < k → o ∉ r.emitted j := by
          intro j hnj hjk hj
          exact he ⟨j, hnj, hjk, hj⟩
        have hp := r.pending_until hnk hi available hno
        by_cases hs : o ∈ r.emitted k
        · exact ⟨k, hnk, hs⟩
        · have ht := r.pending hp.1 (available k hnk).1 (available k hnk).2 hs
          have hlt := ht.2.2 hb
          have hrank : (r.conn (k + 1)).owed.idxOf i < rank := by omega
          obtain ⟨j, hj, he⟩ := ih _ hrank (k + 1) rfl ht.1
            (fun j hj => available j (by omega))
          exact ⟨j, by omega, he⟩
  exact progress _ n rfl hi available

end ServiceRun

/-- A finite set of eventually retained operations has a common point
after which the entire set is held. Different messages may arrive in any
order and at arbitrarily different finite times. -/
theorem finite_eventually_held {F : Type} {x : Sync F (HeldM F)} (r : ReceiverRun x)
    (whole : List Op) (start : Nat)
    (each : ∀ o ∈ whole, ∃ k ≥ start, (r.store k).db.ops o.id = some o) :
    ∃ k ≥ start, ∀ j ≥ k, ∀ o ∈ whole, (r.store j).db.ops o.id = some o := by
  induction whole with
  | nil => exact ⟨start, Nat.le_refl _, by simp⟩
  | cons o os ih =>
    obtain ⟨a, ha, hoa⟩ := each o (List.mem_cons_self ..)
    obtain ⟨b, hb, hob⟩ := ih (fun p hp => each p (List.mem_cons_of_mem _ hp))
    refine ⟨max a b, by omega, ?_⟩
    intro j hj p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact r.retains (by omega) hoa
    · exact hob j (by omega) p hp

/-- **A requested finite closure is eventually delivered and validated.**

`requested` concerns queue admission, `transport` concerns eventual input
of each emitted payload into the actual receiver write path. Neither
assumes possession of the final closure or its final verdict. Once every
required operation arrives, the running write turn's own drain budget
settles validation, and locality transfers the source's verdict. Ongoing
tail requests and out-of-order/duplicate input are permitted.

This is the post-discovery connection component: the round/walk/hold laws
must establish `requested`; session/transport refinement must establish
`transport`. Those obligations are not renamed fairness conclusions. -/
theorem closure_delivered {F : Type} {x : Sync F (HeldM F)} {cfg : Config}
    (send : ServiceRun x.fam cfg) (recv : ReceiverRun x)
    (whole : List Op) (source : Id → Option Op) (seed : Id) (v : Verdict F) (start : Nat)
    (spec : Spec x.fam source seed v)
    (closure : ∀ i o, Reach source seed i → source i = some o → o ∈ whole ∧ o.id = i)
    (service : ∀ N, ∃ j ≥ N, 0 < send.room j)
    (available : ∀ o ∈ whole, ∀ j ≥ start,
      (send.store j).db.ops o.id = some o ∧ (send.conn j).shows x.fam o = true)
    (requested : ∀ o ∈ whole, (recv.store start).db.ops o.id = some o ∨
      ∃ j ≥ start, o.id ∈ (send.conn j).owed)
    (transport : ∀ j ≥ start, ∀ o ∈ send.emitted j,
      ∃ k ≥ j, o ∈ recv.input k) :
    ∃ k ≥ start, ∀ j ≥ k,
      (∀ o ∈ whole, (recv.store j).db.ops o.id = some o) ∧
      (recv.store j).db.status seed = some v := by
  have each : ∀ o ∈ whole, ∃ k ≥ start, (recv.store k).db.ops o.id = some o := by
    intro o ho
    rcases requested o ho with held | ⟨n, hstart, queued⟩
    · exact ⟨start, Nat.le_refl _, held⟩
    · obtain ⟨j, hnj, emitted⟩ := send.eventually_emitted service queued
        (fun j hj => available o ho j (by omega))
      obtain ⟨k, hjk, received⟩ := transport j (by omega) o emitted
      have shown := (available o ho j (by omega)).2
      have shared : x.fam.shared o = true := by
        unfold Family.shared
        unfold Conn.shows at shown
        cases hr : x.fam.room o with
        | none => simp [hr] at shown
        | some r => rfl
      exact ⟨k + 1, by omega, recv.receives received shared⟩
  obtain ⟨k, hk, held⟩ := finite_eventually_held recv whole start each
  refine ⟨k, hk, ?_⟩
  intro j hj
  refine ⟨held j hj, ?_⟩
  apply (status_iff_spec (recv.invariant j) (recv.settled j) seed v).mpr
  apply spec_local x.fam spec
  intro i o reach sourceOp
  obtain ⟨ho, hid⟩ := closure i o reach sourceOp
  rw [← hid]
  exact held j hj o ho

end Engine.Sync
