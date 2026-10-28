/-
What holds in every state of the scene reachable over a socket with
failure (drops, reordering, duplicates). In the scene, each decision a
node makes comes down to which of the five ops it holds (Net.Scene), so
each handler is worked out here under the invariant, and the invariant
is shown to survive every step.
-/
import Net.Scene

namespace Net
open Engine Community

/-! ## Lists of ops -/

theorem mem_add1 {L : List Op} {q o : Op} : o ∈ add1 L q → o ∈ L ∨ o = q := by
  unfold add1; split
  · exact Or.inl
  · intro h; rcases List.mem_append.1 h with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_singleton.1 h)

theorem mem_add1_of {L : List Op} {q o : Op} (h : o ∈ L) : o ∈ add1 L q := by
  unfold add1; split
  · exact h
  · exact List.mem_append_left _ h

theorem add1_of_mem {L : List Op} {q : Op} (h : q ∈ L) : add1 L q = L := by
  unfold add1; rw [if_pos]; exact List.any_eq_true.2 ⟨q, h, by simp⟩

theorem self_add1 {M L : List Op} {q : Op} (hd : Distinct M) (hL : ∀ o ∈ L, o ∈ M) (hq : q ∈ M) :
    q ∈ add1 L q := by
  unfold add1; split
  · rename_i h; obtain ⟨o, ho, he⟩ := List.any_eq_true.1 h
    have := hd o (hL o ho) q hq (of_decide_eq_true he); subst this; exact ho
  · exact List.mem_append_right _ (List.mem_singleton_self _)

theorem mem_add {L os : List Op} {o : Op} : o ∈ add L os → o ∈ L ∨ o ∈ os := by
  induction os generalizing L with
  | nil => exact Or.inl
  | cons q rest ih =>
    intro h
    rcases ih h with h | h
    · rcases mem_add1 h with h | rfl
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_self ..)
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem mem_add_of {L os : List Op} {o : Op} (h : o ∈ L) : o ∈ add L os := by
  induction os generalizing L with
  | nil => exact h
  | cons q rest ih => exact ih (mem_add1_of h)

theorem add_of_mem {L os : List Op} (h : ∀ o ∈ os, o ∈ L) : add L os = L := by
  induction os with
  | nil => rfl
  | cons q rest ih =>
    show add (add1 L q) rest = L
    rw [add1_of_mem (h q (List.mem_cons_self ..))]
    exact ih fun o ho => h o (List.mem_cons_of_mem _ ho)

theorem self_add {M L os : List Op} (hd : Distinct M) (hL : ∀ o ∈ L, o ∈ M) (hos : ∀ o ∈ os, o ∈ M)
    {o : Op} (h : o ∈ os) : o ∈ add L os := by
  induction os generalizing L with
  | nil => cases h
  | cons q rest ih =>
    show o ∈ add (add1 L q) rest
    have hL' : ∀ p ∈ add1 L q, p ∈ M := fun p hp => by
      rcases mem_add1 hp with hp | rfl
      · exact hL p hp
      · exact hos p (List.mem_cons_self ..)
    rcases List.mem_cons.1 h with rfl | h
    · exact mem_add_of (self_add1 hd hL (hos o (List.mem_cons_self ..)))
    · exact ih hL' (fun p hp => hos p (List.mem_cons_of_mem _ hp)) h

theorem mem_ins {l : List (Id × Key)} {s p : Id × Key} : p ∈ ins l s ↔ p ∈ l ∨ p = s := by
  unfold ins; split
  · rename_i h
    obtain ⟨t, ht, he⟩ := List.any_eq_true.1 h
    have := of_decide_eq_true he; subst this
    exact ⟨Or.inl, fun h => h.elim id (fun e => e ▸ ht)⟩
  · simp

theorem Node.ext' {n m : Node} (h1 : n.me = m.me) (h2 : n.ops = m.ops) (h3 : n.accepted = m.accepted)
    (h4 : n.links = m.links) (h5 : n.sessions = m.sessions) : n = m := by
  cases n; cases m; simp_all

namespace Scene
open Classical
variable (x : Scene) (C : Crypto)

theorem reqs_r : x.r.reqs = [] := rfl
theorem reqs_inv : x.inv.reqs = [x.c, x.c] := rfl
theorem reqs_req : x.req.reqs = [x.c, x.inv.id] := rfl
theorem reqs_appr : x.appr.reqs = [x.c, x.req.id, x.c] := rfl
theorem reqs_adm : x.adm.reqs = [x.c, x.req.id, x.appr.id] := rfl

theorem ofC_S {o : Op} (h : o ∈ x.S) : ofC x.c o = true := by
  simp only [S, List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;>
    simp [ofC, reqs_r, reqs_inv, reqs_req, reqs_appr, reqs_adm, c]

theorem filter_ofC {L : List Op} (hL : ∀ o ∈ L, o ∈ x.S) : L.filter (ofC x.c) = L :=
  List.filter_eq_self.2 fun o ho => x.ofC_S (hL o ho)

theorem kinds : x.r.kind = 0 ∧ x.inv.kind = 1 ∧ x.req.kind = 12 ∧ x.appr.kind = 10 ∧ x.adm.kind = 11 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem adm_ne : x.adm ≠ x.r ∧ x.adm ≠ x.inv ∧ x.adm ≠ x.req := by
  obtain ⟨h0, h1, h2, -, h4⟩ := x.kinds
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> have := congrArg Op.kind h <;> simp_all

theorem mem_S : x.r ∈ x.S ∧ x.inv ∈ x.S ∧ x.req ∈ x.S ∧ x.appr ∈ x.S ∧ x.adm ∈ x.S := by
  simp [S]

/-! ## The invariant -/

def InS (L : List Op) : Prop := ∀ o ∈ L, o ∈ x.S
def Covers (L : List Op) : Prop := ∀ o ∈ x.S, o ∈ L

def hello : Msg := .hello x.c x.B.pk x.A.pk (some x.req)
def answer : Msg := .answer x.c x.A.pk x.B.pk

/-- The messages that can be in flight: B's hello; A's answer and A's
ops (all five), both sent only over A's open session with B; B's ops. -/
def NetOk (s : Sys) (m : Msg) : Prop :=
  m = x.hello ∨ (m = x.answer ∧ (x.c, x.B.pk) ∈ s.a.sessions) ∨
  (∃ os, m = .push x.c x.A.pk x.B.pk os ∧ x.InS os ∧ x.Covers os ∧ (x.c, x.B.pk) ∈ s.a.sessions) ∨
  (∃ os, m = .push x.c x.B.pk x.A.pk os ∧ x.InS os)

structure Inv (s : Sys) : Prop where
  ame : s.a.me = x.A.pk
  bme : s.b.me = x.B.pk
  aacc : s.a.accepted = [x.c]
  bacc : s.b.accepted = [x.c]
  alinks : s.a.links = []
  blinks : s.b.links = [] ∨ s.b.links = [x.link]
  aS : x.InS s.a.ops
  bS : x.InS s.b.ops
  ar : x.r ∈ s.a.ops
  ai : x.inv ∈ s.a.ops
  breq : x.req ∈ s.b.ops
  acov : x.adm ∈ s.a.ops → x.Covers s.a.ops
  bmore : (∃ o ∈ s.b.ops, o ≠ x.req) → x.Covers s.b.ops ∧ (x.c, x.A.pk) ∈ s.b.sessions
  asess : ∀ p ∈ s.a.sessions, p = (x.c, x.B.pk) ∧ x.adm ∈ s.a.ops
  bsess : ∀ p ∈ s.b.sessions, p = (x.c, x.A.pk) ∧ (x.c, x.B.pk) ∈ s.a.sessions
  bdone : s.b.links = [] → x.adm ∈ s.b.ops
  net : ∀ m ∈ s.net, x.NetOk s m

variable {x C} {s : Sys}

theorem Inv.bcov (hI : x.Inv s) (h : x.adm ∈ s.b.ops) : x.Covers s.b.ops :=
  (hI.bmore ⟨_, h, x.adm_ne.2.2⟩).1

theorem inv_init (g : x.Good C) : x.Inv x.init := by
  have ne := x.adm_ne
  refine { ame := rfl, bme := rfl, aacc := rfl, bacc := rfl, alinks := rfl, blinks := Or.inr rfl,
           aS := ?_, bS := ?_, ar := by simp [init, a0], ai := by simp [init, a0],
           breq := by simp [init, b0], acov := ?_, bmore := ?_, asess := by simp [init, a0],
           bsess := by simp [init, b0], bdone := by simp [init, b0], net := by simp [init] }
  · intro o h; simp [init, a0] at h; rcases h with rfl | rfl <;> simp [S]
  · intro o h; simp [init, b0] at h; subst h; simp [S]
  · intro h; simp [init, a0] at h; rcases h with h | h
    · exact absurd h ne.1
    · exact absurd h ne.2.1
  · rintro ⟨o, h, hne⟩; simp [init, b0] at h; exact absurd h hne

/-! ## Trust, worked out -/

section
variable (g : x.Good C)
include g

/-- A trusts B for c exactly when A holds B's admission. -/
theorem trustsA {n : Node} (hacc : n.accepted = [x.c]) (hl : n.links = []) (hS : x.InS n.ops)
    (hcov : x.adm ∈ n.ops → x.Covers n.ops) : Trusts C n x.c x.B.pk ↔ x.adm ∈ n.ops := by
  constructor
  · rintro ⟨_, h | ⟨⟨l, hl', _⟩, _⟩⟩
    · exact (allowedB g hS hcov).1 h
    · rw [hl] at hl'; cases hl'
  · intro h; exact ⟨by rw [hacc]; simp, Or.inl ((allowedB g hS hcov).2 h)⟩

/-- B always trusts A: by its link until its ops speak about A, by its
ops after. -/
theorem trustsB {n : Node} (hme : n.me = x.B.pk) (hacc : n.accepted = [x.c])
    (hl : n.links = [] ∨ n.links = [x.link]) (hS : x.InS n.ops)
    (hcov : x.adm ∈ n.ops → x.Covers n.ops) (hdone : n.links = [] → x.adm ∈ n.ops) :
    Trusts C n x.c x.A.pk := by
  refine ⟨by rw [hacc]; simp, ?_⟩
  by_cases hr : x.r ∈ n.ops
  · exact Or.inl ((allowedA g hS).2 hr)
  · have hl' : n.links = [x.link] := by
      rcases hl with h | h
      · exact absurd (hcov (hdone h) _ x.mem_S.1) hr
      · exact h
    refine Or.inr ⟨⟨x.link, by rw [hl']; simp, rfl, rfl⟩, fun h => hr ((knownA g hS).1 h), ?_⟩
    rw [hme]; intro h
    exact hr (hcov ((allowedB g hS hcov).1 h) _ x.mem_S.1)

theorem Inv.trustsB (hI : x.Inv s) : Trusts C s.b x.c x.A.pk :=
  Net.Scene.trustsB g hI.bme hI.bacc hI.blinks hI.bS hI.bcov hI.bdone

/-! ## The handlers, worked out -/

theorem hello_A (hI : x.Inv s) :
    onHello C s.a x.c x.B.pk (some x.req) =
      if x.adm ∈ s.a.ops then
        ({ s.a with ops := add1 s.a.ops x.req, sessions := ins s.a.sessions (x.c, x.B.pk) },
          [x.answer])
      else ({ s.a with ops := add1 s.a.ops x.req }, []) := by
  have hS' : x.InS (add1 s.a.ops x.req) := fun o h => by
    rcases mem_add1 h with h | rfl
    · exact hI.aS o h
    · exact x.mem_S.2.2.1
  have hreq : x.req ∈ add1 s.a.ops x.req := self_add1 g.distinct hI.aS x.mem_S.2.2.1
  have hcov : x.adm ∈ add1 s.a.ops x.req → x.Covers (add1 s.a.ops x.req) := fun h o ho => by
    rcases mem_add1 h with h | h
    · exact mem_add1_of (hI.acov h o ho)
    · exact absurd h x.adm_ne.2.2
  have hi : IntroOk C s.a x.c x.req :=
    ⟨x.ofC_S x.mem_S.2.2.1, _, _, _, _, _,
      v_req g hS' (mem_add1_of hI.ar) (mem_add1_of hI.ai) hreq⟩
  have hadm : x.adm ∈ add1 s.a.ops x.req ↔ x.adm ∈ s.a.ops :=
    ⟨fun h => (mem_add1 h).resolve_right x.adm_ne.2.2, mem_add1_of⟩
  have ht := trustsA (n := { s.a with ops := add1 s.a.ops x.req }) g hI.aacc hI.alinks hS' hcov
  unfold onHello
  rw [if_pos (by rw [hI.aacc]; simp)]
  dsimp only
  refine ite_congr ?_ (fun _ => ?_) (fun _ => ?_)
  · apply propext
    simp only [if_pos hi]
    exact ⟨fun t => hadm.1 (ht.1 t), fun h => ht.2 (hadm.2 h)⟩
  · simp only [if_pos hi, hI.ame]; rfl
  · simp only [if_pos hi]

theorem answer_B (hI : x.Inv s) :
    onAnswer C s.b x.c x.A.pk =
      if s.b.links = [x.link] then { s.b with sessions := ins s.b.sessions (x.c, x.A.pk) }
      else s.b := by
  unfold onAnswer
  rcases hI.blinks with h | h
  · rw [if_neg, if_neg]
    · rw [h]; simp
    · rintro ⟨⟨l, hl, _⟩, _⟩; rw [h] at hl; cases hl
  · rw [if_pos ⟨⟨x.link, by rw [h]; simp, rfl, rfl⟩, hI.trustsB g⟩, if_pos h]

theorem push_B (hI : x.Inv s) {os : List Op} (hos : x.InS os) :
    onPush C s.b x.c x.A.pk os =
      if (x.c, x.A.pk) ∈ s.b.sessions then { s.b with ops := add s.b.ops os } else s.b := by
  unfold onPush
  rw [x.filter_ofC hos]
  by_cases h : (x.c, x.A.pk) ∈ s.b.sessions
  · rw [if_pos ⟨h, hI.trustsB g⟩, if_pos h]
  · rw [if_neg (fun t => h t.1), if_neg h]

theorem push_A (hI : x.Inv s) {os : List Op} (hos : x.InS os) :
    onPush C s.a x.c x.B.pk os = s.a := by
  unfold onPush
  split
  · rename_i h
    rw [x.filter_ofC hos, add_of_mem fun o ho => hI.acov (hI.asess _ h.1).2 o (hos o ho)]
  · rfl

theorem ticked_A (hI : x.Inv s) : ticked C s.a = s.a := by
  have hl : keptLinks C s.a = [] := by unfold keptLinks; rw [hI.alinks]; rfl
  refine Node.ext' (n := ticked C s.a) (m := s.a) rfl rfl rfl (hl.trans hI.alinks.symm) ?_
  show List.filter _ s.a.sessions = s.a.sessions
  refine List.filter_eq_self.2 fun p hp => ?_
  obtain ⟨rfl, hadm⟩ := hI.asess p hp
  exact decide_eq_true
    ((trustsA (n := { s.a with links := keptLinks C s.a }) g hI.aacc hl hI.aS hI.acov).2 hadm)

theorem tick_A (hI : x.Inv s) :
    tick C s.a = (s.a, s.a.sessions.map fun _ => Msg.push x.c x.A.pk x.B.pk s.a.ops) := by
  unfold tick; rw [ticked_A g hI]
  refine Prod.ext rfl ?_
  show sends s.a = _
  unfold sends; rw [hI.alinks]
  simp only [List.filter_nil, List.map_nil, List.nil_append]
  refine List.map_congr_left fun p hp => ?_
  obtain ⟨rfl, _⟩ := hI.asess p hp
  simp only [hI.ame, x.filter_ofC hI.aS]

theorem keptLinks_B (hI : x.Inv s) :
    keptLinks C s.b = if x.adm ∈ s.b.ops then [] else s.b.links := by
  have hall := allowedB (L := s.b.ops) g hI.bS hI.bcov
  unfold keptLinks
  rcases hI.blinks with h | h
  · rw [h]; split <;> rfl
  · rw [h]
    by_cases ha : x.adm ∈ s.b.ops
    · rw [if_pos ha]; simp [link, hI.bme, hall.2 ha]
    · rw [if_neg ha]; simp [link, hI.bme]; exact fun t => ha (hall.1 t)

theorem ticked_B (hI : x.Inv s) :
    ticked C s.b = { s.b with links := if x.adm ∈ s.b.ops then [] else s.b.links } := by
  have hl := keptLinks_B g hI
  have ht : Trusts C { s.b with links := keptLinks C s.b } x.c x.A.pk := by
    refine Net.Scene.trustsB g hI.bme hI.bacc ?_ hI.bS hI.bcov ?_
    · show keptLinks C s.b = [] ∨ keptLinks C s.b = [x.link]
      rw [hl]; split
      · exact Or.inl rfl
      · exact hI.blinks
    · show keptLinks C s.b = [] → _
      rw [hl]; split
      · intro _; assumption
      · exact hI.bdone
  refine Node.ext' (n := ticked C s.b) rfl rfl rfl hl ?_
  show List.filter _ s.b.sessions = s.b.sessions
  refine List.filter_eq_self.2 fun p hp => ?_
  obtain ⟨rfl, _⟩ := hI.bsess p hp
  exact decide_eq_true ht

theorem tick_B (hI : x.Inv s) :
    tick C s.b =
      ({ s.b with links := if x.adm ∈ s.b.ops then [] else s.b.links },
        (if s.b.links = [x.link] ∧ x.adm ∉ s.b.ops ∧ (x.c, x.A.pk) ∉ s.b.sessions then [x.hello]
          else []) ++ s.b.sessions.map fun _ => Msg.push x.c x.B.pk x.A.pk s.b.ops) := by
  unfold tick; rw [ticked_B g hI]
  refine Prod.ext rfl ?_
  show sends { s.b with links := if x.adm ∈ s.b.ops then [] else s.b.links } = _
  unfold sends
  dsimp only
  congr 1
  · by_cases ha : x.adm ∈ s.b.ops
    · rw [if_pos ha, if_neg (fun h => h.2.1 ha)]; rfl
    · rw [if_neg ha]
      rcases hI.blinks with h | h
      · rw [if_neg (fun t => by rw [h] at t; cases t.1), h]; rfl
      · rw [h]
        by_cases hs' : (x.c, x.A.pk) ∈ s.b.sessions
        · have hany : (s.b.sessions.any fun t => decide (t = (x.c, x.A.pk))) = true :=
            List.any_eq_true.2 ⟨_, hs', by simp⟩
          rw [if_neg (fun t => t.2.2 hs')]
          simp [link, List.filter_cons, hany]
        · have hany : (s.b.sessions.any fun t => decide (t = (x.c, x.A.pk))) = false := by
            rw [Bool.eq_false_iff]; intro h
            obtain ⟨t, ht, he⟩ := List.any_eq_true.1 h
            exact hs' ((of_decide_eq_true he) ▸ ht)
          rw [if_pos ⟨rfl, ha, hs'⟩]
          simp [link, List.filter_cons, hany, hello, hI.bme]
  · refine List.map_congr_left fun p hp => ?_
    obtain ⟨rfl, _⟩ := hI.bsess p hp
    simp only [hI.bme, x.filter_ofC hI.bS]

theorem approval_eq (n : Node) :
    x.approval n = if x.req ∈ n.ops then { n with ops := add n.ops [x.appr, x.adm] } else n := by
  unfold approval
  by_cases h : x.req ∈ n.ops
  · rw [if_pos (List.any_eq_true.2 ⟨_, h, by simp⟩), if_pos h]
  · rw [if_neg (fun t => h (by obtain ⟨o, ho, he⟩ := List.any_eq_true.1 t; simp at he; exact he ▸ ho)),
      if_neg h]

end

end Scene

end Net
