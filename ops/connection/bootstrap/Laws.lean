/-
The laws of the bootstrap, over the real ops and validators (Net.Scene)
and the protocol's own handlers (Net.Node):

- **Safety, over a failing socket** (any interleaving of ticks, approval,
  delivery in any order, duplicates and loss): a request opens nothing
  and earns nothing; A's sessions are only with devices its own ops
  admit; B's only with a device it trusts by the two-clause rule.
- **Possible over an ideal socket**: a run with no loss that ends with
  B connected, admitted and in sync.
- **Inevitable over a failing socket**: every fair run gets there and
  stays there.
-/
import ops.connection.bootstrap.Steps

namespace Net
open Engine Community

namespace Scene
open Classical
variable {x : Scene} {C : Crypto} {s : Sys}

variable (x C) in
/-- Bootstrapped: both ends hold the session, hold the same ops, and
admit each other by those ops alone (`allowPeer`, with no exception: B
has forgotten its link). -/
def Goal (s : Sys) : Prop :=
  (x.c, x.B.pk) ∈ s.a.sessions ∧ (x.c, x.A.pk) ∈ s.b.sessions ∧
  (∀ o, o ∈ s.a.ops ↔ o ∈ s.b.ops) ∧
  Allowed C s.a.ops x.c x.B.pk ∧ Allowed C s.b.ops x.c x.A.pk ∧ Allowed C s.b.ops x.c x.B.pk ∧
  s.b.links = []

section
variable (g : x.Good C)
include g

/-! ## Safety -/

/-- **A request opens nothing.** Until A holds B's admission (A's user
has approved), however B's hellos are lost, duplicated or reordered: A
has no session with B and B none with A, no answer and no ops of A's are
in flight to B, and B holds nothing but its own request. -/
theorem no_connection_before_approval (h : Reachable C x.approval x.init s)
    (hna : x.adm ∉ s.a.ops) :
    (x.c, x.B.pk) ∉ s.a.sessions ∧ (x.c, x.A.pk) ∉ s.b.sessions ∧
    x.answer ∉ s.net ∧ (∀ os, Msg.push x.c x.A.pk x.B.pk os ∉ s.net) ∧ (∀ o ∈ s.b.ops, o = x.req) := by
  have hI := reachable_inv g h
  have ha : (x.c, x.B.pk) ∉ s.a.sessions := fun h => hna (hI.asess _ h).2
  refine ⟨ha, fun h => ha (hI.bsess _ h).2, fun h => ?_, fun os h => ?_, fun o ho => ?_⟩
  · rcases hI.net _ h with h | ⟨_, h⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩
    · cases h
    · exact ha h
    · cases h
    · cases h
  · rcases hI.net _ h with h | ⟨h, _⟩ | ⟨_, h, _, _, hs⟩ | ⟨_, h, _⟩
    · cases h
    · cases h
    · exact ha hs
    · injection h with _ h2; exact g.AB h2
  · apply Classical.byContradiction; intro hne
    exact ha (hI.bsess _ (hI.bmore ⟨o, ho, hne⟩).2).2

/-- **Sessions only with trusted peers.** Every session A holds is with
a device A's own ops admit, as `allowPeer` decides, with no exception;
every session B holds is with a device B trusts by the two-clause rule
(its link's inviter until its ops speak, its ops after). -/
theorem sessions_trusted (h : Reachable C x.approval x.init s) :
    (∀ p ∈ s.a.sessions, Allowed C s.a.ops p.1 p.2) ∧ (∀ p ∈ s.b.sessions, Trusts C s.b p.1 p.2) := by
  have hI := reachable_inv g h
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · obtain ⟨rfl, hadm⟩ := hI.asess p hp
    exact (allowedB g hI.aS hI.acov).2 hadm
  · obtain ⟨rfl, _⟩ := hI.bsess p hp
    exact hI.trustsB g

/-! ## What one step does -/

omit g in
theorem sent_mem {s : Sys} {act : Act} {m : Msg} (h : m ∈ sent C x.approval s act) :
    m ∈ (step C x.approval s act).net := by
  unfold sent at h; unfold step
  cases act with
  | tickA | tickB => exact List.mem_append_right _ h
  | approve | drop => cases h
  | deliver m' =>
    simp only [stepOut] at h ⊢
    split
    · rw [if_pos (by assumption)] at h; exact List.mem_append_right _ h
    · rw [if_neg (by assumption)] at h
      split
      · rw [if_pos (by assumption)] at h; exact List.mem_append_right _ h
      · rw [if_neg (by assumption)] at h; cases h

/-- Monotone across any step: what A and B hold, B's session, B's
forgotten link; and A's ops stop changing once A holds B's admission. -/
theorem step_mono (hI : x.Inv s) {act : Act} (he : Enabled s act) :
    (∀ o ∈ s.a.ops, o ∈ (step C x.approval s act).a.ops) ∧
    (∀ o ∈ s.b.ops, o ∈ (step C x.approval s act).b.ops) ∧
    ((x.c, x.A.pk) ∈ s.b.sessions → (x.c, x.A.pk) ∈ (step C x.approval s act).b.sessions) ∧
    (s.b.links = [] → (step C x.approval s act).b.links = []) ∧
    (x.adm ∈ s.a.ops → (step C x.approval s act).a.ops = s.a.ops) := by
  unfold step
  cases act with
  | tickA => rw [out_tickA g hI]; exact ⟨fun _ h => h, fun _ h => h, id, id, fun _ => rfl⟩
  | tickB =>
    rw [out_tickB g hI]
    refine ⟨fun _ h => h, fun _ h => h, id, fun h => ?_, fun _ => rfl⟩
    show (if x.adm ∈ s.b.ops then [] else s.b.links) = []
    split
    · rfl
    · exact h
  | drop m => rw [out_drop]; exact ⟨fun _ h => h, fun _ h => h, id, id, fun _ => rfl⟩
  | approve =>
    rw [out_approve, approval_eq g]
    split
    · rename_i hreq
      refine ⟨fun _ h => mem_add_of h, fun _ h => h, id, id, fun hadm => ?_⟩
      exact add_of_mem fun o ho => hI.acov hadm o (by simp at ho; rcases ho with rfl | rfl <;> simp [S])
    · exact ⟨fun _ h => h, fun _ h => h, id, id, fun _ => rfl⟩
  | deliver m =>
    rcases hI.net m he with rfl | ⟨rfl, _⟩ | ⟨os, rfl, hin, _, _⟩ | ⟨os, rfl, hin⟩
    · rw [out_hello g hI]
      split
      · rename_i hadm
        exact ⟨fun _ h => mem_add1_of h, fun _ h => h, id, id,
          fun _ => add1_of_mem (hI.acov hadm _ x.mem_S.2.2.1)⟩
      · rename_i hadm
        exact ⟨fun _ h => mem_add1_of h, fun _ h => h, id, id, fun h => absurd h hadm⟩
    · rw [out_answer g hI]
      split
      · exact ⟨fun _ h => h, fun _ h => h, fun h => mem_ins.2 (Or.inl h), id, fun _ => rfl⟩
      · exact ⟨fun _ h => h, fun _ h => h, id, id, fun _ => rfl⟩
    · rw [out_pushAB g hI hin]
      split
      · exact ⟨fun _ h => h, fun _ h => mem_add_of h, id, id, fun _ => rfl⟩
      · exact ⟨fun _ h => h, fun _ h => h, id, id, fun _ => rfl⟩
    · rw [out_pushBA g hI hin]; exact ⟨fun _ h => h, fun _ h => h, id, id, fun _ => rfl⟩

/-- B's tick re-sends its hello while its link is pending and no session
is open. -/
theorem hello_sent (hI : x.Inv s) (hns : (x.c, x.A.pk) ∉ s.b.sessions) :
    x.hello ∈ sent C x.approval s .tickB := by
  have hna : x.adm ∉ s.b.ops := fun h => hns (hI.bmore ⟨_, h, x.adm_ne.2.2⟩).2
  have hl : s.b.links = [x.link] := hI.blinks.resolve_left fun h => hna (hI.bdone h)
  unfold sent; rw [out_tickB g hI]
  show x.hello ∈ msgsB x s
  unfold msgsB; rw [if_pos ⟨hl, hna, hns⟩]; simp

/-- Delivering B's hello gives A the request. -/
theorem hello_gives_req (hI : x.Inv s) : x.req ∈ (step C x.approval s (.deliver x.hello)).a.ops := by
  unfold step; rw [out_hello g hI]
  have := self_add1 g.distinct hI.aS x.mem_S.2.2.1
  split <;> exact this

/-- Once A holds B's admission, every hello delivered is answered. -/
theorem hello_answered (hI : x.Inv s) (hadm : x.adm ∈ s.a.ops) :
    x.answer ∈ sent C x.approval s (.deliver x.hello) := by
  unfold sent; rw [out_hello g hI, if_pos hadm]; simp

/-- A's user approving, once A holds the request, gives A B's admission. -/
theorem approve_gives_adm (hI : x.Inv s) (hreq : x.req ∈ s.a.ops) :
    x.adm ∈ (step C x.approval s .approve).a.ops := by
  unfold step; rw [out_approve, approval_eq g, if_pos hreq]
  have hS2 : x.InS [x.appr, x.adm] := by
    intro o ho; simp at ho; rcases ho with rfl | rfl
    · exact x.mem_S.2.2.2.1
    · exact x.mem_S.2.2.2.2
  exact self_add g.distinct hI.aS hS2 (by simp)

/-- An answer delivered while B's link is pending opens B's session. -/
theorem answer_opens (hI : x.Inv s) (hl : s.b.links = [x.link]) :
    (x.c, x.A.pk) ∈ (step C x.approval s (.deliver x.answer)).b.sessions := by
  unfold step; rw [out_answer g hI, if_pos hl]
  exact mem_ins.2 (Or.inr rfl)

/-- A's tick pushes its ops over its session with B. -/
theorem push_sent (hI : x.Inv s) (hs : (x.c, x.B.pk) ∈ s.a.sessions) :
    Msg.push x.c x.A.pk x.B.pk s.a.ops ∈ sent C x.approval s .tickA := by
  unfold sent; rw [out_tickA g hI]
  exact List.mem_map.2 ⟨_, hs, rfl⟩

/-- A's ops delivered over B's session give B its admission. -/
theorem push_gives_adm (hI : x.Inv s) {os : List Op} (hin : x.InS os) (hcov : x.Covers os)
    (hs : (x.c, x.A.pk) ∈ s.b.sessions) :
    x.adm ∈ (step C x.approval s (.deliver (.push x.c x.A.pk x.B.pk os))).b.ops := by
  unfold step; rw [out_pushAB g hI hin, if_pos hs]
  exact self_add g.distinct hI.bS hin (hcov _ x.mem_S.2.2.2.2)

/-- B's tick forgets the link once B holds its admission. -/
theorem tick_forgets (hI : x.Inv s) (hadm : x.adm ∈ s.b.ops) :
    (step C x.approval s .tickB).b.links = [] := by
  unfold step; rw [out_tickB g hI]
  show (if x.adm ∈ s.b.ops then [] else s.b.links) = []
  rw [if_pos hadm]

theorem goal_of (hI : x.Inv s) (hs : (x.c, x.A.pk) ∈ s.b.sessions) (hadm : x.adm ∈ s.b.ops)
    (hl : s.b.links = []) : x.Goal C s := by
  have hab := (hI.bsess _ hs).2
  have hadmA := (hI.asess _ hab).2
  have hca := hI.acov hadmA
  have hcb := hI.bcov hadm
  refine ⟨hab, hs, fun o => ⟨fun h => hcb o (hI.aS o h), fun h => hca o (hI.bS o h)⟩,
    (allowedB g hI.aS hI.acov).2 hadmA, (allowedA g hI.bS).2 (hcb _ x.mem_S.1),
    (allowedB g hI.bS hI.bcov).2 hadm, hl⟩

/-! ## Possible over an ideal socket -/

/-- **Bootstrap is possible over an ideal socket.** From A having founded
c and invited B, and B having pasted the link: B ticks (its hello, with
its request), the hello arrives (A stores the request and does not
answer), A's user approves, B ticks again (the same hello), it arrives
(now A answers and opens its session), the answer arrives (B opens its
session on its link's word), A ticks (its ops), they arrive (B holds its
admission), B ticks (forgetting the link). No message is lost; each is
in flight when delivered; and then B is connected, admitted by both
ends' ops and in sync. -/
theorem bootstrap_possible :
    ∃ acts t, (∀ act ∈ acts, ∀ m, act ≠ .drop m) ∧ Path C x.approval x.init acts t ∧ x.Goal C t := by
  let st := step C x.approval
  have R0 : Reachable C x.approval x.init x.init := .init
  have I0 := inv_init g
  -- 1. B ticks: its hello is in flight.
  let s1 := st x.init .tickB
  have R1 : Reachable C x.approval x.init s1 := .step _ R0 trivial
  have I1 := reachable_inv g R1
  have h1 : x.hello ∈ s1.net := sent_mem (hello_sent g I0 (by simp [init, b0]))
  have b1 : s1.b = x.b0 := by
    show (stepOut C x.approval x.init .tickB).1.b = _
    rw [out_tickB g I0]; show x.bAfter x.init = x.b0
    unfold bAfter; rw [if_neg (by simp [init, b0]; exact x.adm_ne.2.2)]; rfl
  -- 2. The hello arrives: A stores the request, and answers nothing.
  let s2 := st s1 (.deliver x.hello)
  have R2 : Reachable C x.approval x.init s2 := .step _ R1 h1
  have I2 := reachable_inv g R2
  have h2 : x.req ∈ s2.a.ops := hello_gives_req g I1
  have b2 : s2.b = x.b0 := by
    show (stepOut C x.approval s1 (.deliver x.hello)).1.b = _
    rw [out_hello g I1]; split <;> exact b1
  -- 3. A's user approves.
  let s3 := st s2 .approve
  have R3 : Reachable C x.approval x.init s3 := .step _ R2 trivial
  have I3 := reachable_inv g R3
  have h3 : x.adm ∈ s3.a.ops := approve_gives_adm g I2 h2
  have b3 : s3.b = x.b0 := b2
  -- 4. B ticks: the same hello again.
  let s4 := st s3 .tickB
  have R4 : Reachable C x.approval x.init s4 := .step _ R3 trivial
  have I4 := reachable_inv g R4
  have h4 : x.hello ∈ s4.net := sent_mem (hello_sent g I3 (by rw [b3]; simp [b0]))
  have a4 : s4.a = s3.a := by
    show (stepOut C x.approval s3 .tickB).1.a = _
    rw [out_tickB g I3]
  have b4 : s4.b.links = [x.link] := by
    show (stepOut C x.approval s3 .tickB).1.b.links = _
    rw [out_tickB g I3]; show (if x.adm ∈ s3.b.ops then [] else s3.b.links) = _
    rw [b3, if_neg (by simp [b0]; exact x.adm_ne.2.2)]; rfl
  -- 5. It arrives: A, now holding B's admission, answers.
  let s5 := st s4 (.deliver x.hello)
  have R5 : Reachable C x.approval x.init s5 := .step _ R4 h4
  have I5 := reachable_inv g R5
  have h5 : x.answer ∈ s5.net := sent_mem (hello_answered g I4 (a4 ▸ h3))
  have b5 : s5.b = s4.b := by
    show (stepOut C x.approval s4 (.deliver x.hello)).1.b = _
    rw [out_hello g I4]; split <;> rfl
  -- 6. The answer arrives: B opens its session.
  let s6 := st s5 (.deliver x.answer)
  have R6 : Reachable C x.approval x.init s6 := .step _ R5 h5
  have I6 := reachable_inv g R6
  have h6 : (x.c, x.A.pk) ∈ s6.b.sessions := answer_opens g I5 (b5 ▸ b4)
  -- 7. A ticks: its ops, over its session.
  let s7 := st s6 .tickA
  have R7 : Reachable C x.approval x.init s7 := .step _ R6 trivial
  have I7 := reachable_inv g R7
  have hab : (x.c, x.B.pk) ∈ s6.a.sessions := (I6.bsess _ h6).2
  have h7 : Msg.push x.c x.A.pk x.B.pk s6.a.ops ∈ s7.net := sent_mem (push_sent g I6 hab)
  have b7 : s7.b = s6.b := by
    show (stepOut C x.approval s6 .tickA).1.b = _
    rw [out_tickA g I6]
  -- 8. They arrive: B holds its admission.
  let s8 := st s7 (.deliver (.push x.c x.A.pk x.B.pk s6.a.ops))
  have R8 : Reachable C x.approval x.init s8 := .step _ R7 h7
  have I8 := reachable_inv g R8
  have h8 : x.adm ∈ s8.b.ops :=
    push_gives_adm g I7 I6.aS (I6.acov (I6.asess _ hab).2) (by rw [b7]; exact h6)
  -- 9. B ticks: it forgets its link.
  let s9 := st s8 .tickB
  have R9 : Reachable C x.approval x.init s9 := .step _ R8 trivial
  have I9 := reachable_inv g R9
  have m8 := step_mono g I7 (act := .deliver (.push x.c x.A.pk x.B.pk s6.a.ops)) h7
  have m9 := step_mono g I8 (act := .tickB) trivial
  have h6' : (x.c, x.A.pk) ∈ s8.b.sessions := m8.2.2.1 (by rw [b7]; exact h6)
  refine ⟨[.tickB, .deliver x.hello, .approve, .tickB, .deliver x.hello, .deliver x.answer, .tickA,
    .deliver (.push x.c x.A.pk x.B.pk s6.a.ops), .tickB], s9, by simp, ?_, ?_⟩
  · exact .cons trivial (.cons h1 (.cons trivial (.cons trivial (.cons h4 (.cons h5 (.cons trivial
      (.cons h7 (.cons trivial (.nil s9)))))))))
  · exact goal_of g I9 (m9.2.2.1 h6') (m9.2.1 _ h8) (tick_forgets g I8 h8)

/-! ## Inevitable over a failing socket -/

theorem run_inv (r : Run C x.approval x.init) : ∀ i, x.Inv (r.st i)
  | 0 => by rw [r.zero]; exact inv_init g
  | i + 1 => by rw [(r.next i).2]; exact inv_step g (run_inv r i) (r.next i).1

theorem run_stable (r : Run C x.approval x.init) {P : Sys → Prop}
    (hP : ∀ s act, x.Inv s → Enabled s act → P s → P (step C x.approval s act))
    {i j : Nat} (hij : i ≤ j) (h : P (r.st i)) : P (r.st j) := by
  induction hij with
  | refl => exact h
  | step _ ih => rw [(r.next _).2]; exact hP _ _ (run_inv g r _) (r.next _).1 ih

omit g in
theorem run_step (r : Run C x.approval x.init) (i : Nat) :
    r.st (i + 1) = step C x.approval (r.st i) (r.act i) := (r.next i).2

variable {r : Run C x.approval x.init}

/-- B's hello is sent at infinitely many steps while B has no session. -/
theorem hellos_forever (hf : r.Fair) (hno : ∀ i, (x.c, x.A.pk) ∉ (r.st i).b.sessions) :
    ∀ N, ∃ i ≥ N, x.hello ∈ sent C x.approval (r.st i) (r.act i) := by
  intro N
  obtain ⟨i, hi, ha⟩ := hf.2.1 N
  exact ⟨i, hi, ha ▸ hello_sent g (run_inv g r i) (hno i)⟩

/-- Eventually A holds B's request: B keeps sending its hello, so one
gets through. -/
theorem ev_req (hf : r.Fair) : ∃ N, x.req ∈ (r.st N).a.ops := by
  apply Classical.byContradiction; intro hno
  have hno' : ∀ i, x.req ∉ (r.st i).a.ops := fun i h => hno ⟨i, h⟩
  have hns : ∀ i, (x.c, x.A.pk) ∉ (r.st i).b.sessions := fun i h => by
    have hI := run_inv g r i
    exact hno' i (hI.acov (hI.asess _ (hI.bsess _ h).2).2 _ x.mem_S.2.2.1)
  obtain ⟨i, _, ha⟩ := hf.2.2.2 _ (hellos_forever g hf hns) 0
  have := hello_gives_req g (run_inv g r i)
  rw [← ha, ← run_step] at this
  exact hno' (i + 1) this

/-- Eventually A holds B's admission: A's user approves. -/
theorem ev_approved (hf : r.Fair) : ∃ N, x.adm ∈ (r.st N).a.ops := by
  obtain ⟨N, hN⟩ := ev_req g hf
  obtain ⟨i, hi, ha⟩ := hf.2.2.1 N
  have hreq := run_stable g r (P := fun s => x.req ∈ s.a.ops)
    (fun _ _ hI he h => (step_mono g hI he).1 _ h) hi hN
  refine ⟨i + 1, ?_⟩
  rw [run_step, ha]
  exact approve_gives_adm g (run_inv g r i) hreq

theorem adm_stays (hf : r.Fair) : ∃ N, ∀ i ≥ N, x.adm ∈ (r.st i).a.ops := by
  obtain ⟨N, hN⟩ := ev_approved g hf
  exact ⟨N, fun i hi => run_stable g r (P := fun s => x.adm ∈ s.a.ops)
    (fun _ _ hI he h => (step_mono g hI he).1 _ h) hi hN⟩

/-- Eventually B's session opens: B keeps sending its hello, A answers
each one that arrives, and one answer gets through. -/
theorem ev_session (hf : r.Fair) : ∃ N, (x.c, x.A.pk) ∈ (r.st N).b.sessions := by
  obtain ⟨N2, h2⟩ := adm_stays g hf
  apply Classical.byContradiction; intro hno
  have hno' : ∀ i, (x.c, x.A.pk) ∉ (r.st i).b.sessions := fun i h => hno ⟨i, h⟩
  have hs : ∀ N, ∃ i ≥ N, x.answer ∈ sent C x.approval (r.st i) (r.act i) := by
    intro N
    obtain ⟨i, hi, ha⟩ := hf.2.2.2 _ (hellos_forever g hf hno') (max N N2)
    exact ⟨i, Nat.le_trans (Nat.le_max_left _ _) hi,
      ha ▸ hello_answered g (run_inv g r i) (h2 i (Nat.le_trans (Nat.le_max_right _ _) hi))⟩
  obtain ⟨i, _, ha⟩ := hf.2.2.2 _ hs 0
  have hI := run_inv g r i
  have hna : x.adm ∉ (r.st i).b.ops := fun h => hno' i (hI.bmore ⟨_, h, x.adm_ne.2.2⟩).2
  have hl : (r.st i).b.links = [x.link] := hI.blinks.resolve_left fun h => hna (hI.bdone h)
  have := answer_opens g hI hl
  rw [← ha, ← run_step] at this
  exact hno' (i + 1) this

/-- Eventually B holds its admission: A keeps pushing the same ops over
its session, and one push gets through. -/
theorem ev_admitted (hf : r.Fair) : ∃ N, x.adm ∈ (r.st N).b.ops := by
  obtain ⟨N2, h2⟩ := adm_stays g hf
  obtain ⟨N3, h3⟩ := ev_session g hf
  let M := max N2 N3
  have hs : ∀ i ≥ M, (x.c, x.A.pk) ∈ (r.st i).b.sessions := fun i hi =>
    run_stable g r (P := fun s => (x.c, x.A.pk) ∈ s.b.sessions)
      (fun _ _ hI he h => (step_mono g hI he).2.2.1 h) (Nat.le_trans (Nat.le_max_right _ _) hi) h3
  have hfix : ∀ i ≥ M, (r.st i).a.ops = (r.st M).a.ops := fun i hi =>
    run_stable g r (P := fun s => s.a.ops = (r.st M).a.ops)
      (fun _ _ hI he h => by
        rw [(step_mono g hI he).2.2.2.2 (h ▸ h2 M (Nat.le_max_left _ _))]; exact h) hi rfl
  let m := Msg.push x.c x.A.pk x.B.pk (r.st M).a.ops
  have hsent : ∀ N, ∃ i ≥ N, m ∈ sent C x.approval (r.st i) (r.act i) := by
    intro N
    obtain ⟨i, hi, ha⟩ := hf.1 (max N M)
    have hiM : i ≥ M := Nat.le_trans (Nat.le_max_right _ _) hi
    have hI := run_inv g r i
    refine ⟨i, Nat.le_trans (Nat.le_max_left _ _) hi, ?_⟩
    rw [ha, show m = Msg.push x.c x.A.pk x.B.pk (r.st i).a.ops by rw [hfix i hiM]]
    exact push_sent g hI (hI.bsess _ (hs i hiM)).2
  obtain ⟨i, hi, ha⟩ := hf.2.2.2 _ hsent M
  have hI := run_inv g r i
  have hIM := run_inv g r M
  have hadmM := h2 M (Nat.le_max_left _ _)
  have := push_gives_adm g hI hIM.aS (hIM.acov hadmM) (hs i hi)
  rw [← ha, ← run_step] at this
  exact ⟨_, this⟩

/-- **Bootstrap over a failing socket.** In every fair run, whatever the
socket loses, duplicates or reorders: eventually, and from then on, B is
connected to A, both hold the same ops, each admits the other by its
own ops alone, and B has forgotten its link. -/
theorem bootstrap (hf : r.Fair) : ∃ N, ∀ i ≥ N, x.Goal C (r.st i) := by
  obtain ⟨N4, h4⟩ := ev_admitted g hf
  obtain ⟨N3, h3⟩ := ev_session g hf
  obtain ⟨i, hi, ha⟩ := hf.2.1 (max N3 N4)
  have hadm : ∀ j ≥ N4, x.adm ∈ (r.st j).b.ops := fun j hj =>
    run_stable g r (P := fun s => x.adm ∈ s.b.ops) (fun _ _ hI he h => (step_mono g hI he).2.1 _ h) hj h4
  have hses : ∀ j ≥ N3, (x.c, x.A.pk) ∈ (r.st j).b.sessions := fun j hj =>
    run_stable g r (P := fun s => (x.c, x.A.pk) ∈ s.b.sessions)
      (fun _ _ hI he h => (step_mono g hI he).2.2.1 h) hj h3
  have hl : (r.st (i + 1)).b.links = [] := by
    rw [run_step, ha]
    exact tick_forgets g (run_inv g r i) (hadm i (Nat.le_trans (Nat.le_max_right _ _) hi))
  refine ⟨i + 1, fun j hj => goal_of g (run_inv g r j) (hses j ?_) (hadm j ?_) ?_⟩
  · exact Nat.le_trans (Nat.le_trans (Nat.le_max_left _ _) hi) (Nat.le_of_succ_le hj)
  · exact Nat.le_trans (Nat.le_trans (Nat.le_max_right _ _) hi) (Nat.le_of_succ_le hj)
  · exact run_stable g r (P := fun s => s.b.links = [])
      (fun _ _ hI he h => (step_mono g hI he).2.2.2.1 h) hj hl

/-- **And over an ideal socket**, every fair run without loss. -/
theorem bootstrap_ideal (hf : r.Fair) (_ : r.Ideal) : ∃ N, ∀ i ≥ N, x.Goal C (r.st i) :=
  bootstrap g hf

end

end Scene

end Net
