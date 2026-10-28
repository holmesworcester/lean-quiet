/-
Every step of the scene, worked out under the invariant, and the
invariant kept by every step: ticks, approval, delivery of any message
in flight in any order, and loss of any message.
-/
import ops.connection.bootstrap.Inv

namespace Net
open Engine Community

theorem NetOk.mono {x : Scene} {s s' : Sys} {m : Msg} (h : x.NetOk s m)
    (ha : (x.c, x.B.pk) ∈ s.a.sessions → (x.c, x.B.pk) ∈ s'.a.sessions) : x.NetOk s' m := by
  rcases h with h | ⟨h1, h2⟩ | ⟨os, h1, h2, h3, h4⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨h1, ha h2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨os, h1, h2, h3, ha h4⟩))
  · exact Or.inr (Or.inr (Or.inr h))

namespace Scene
open Classical
variable {x : Scene} {C : Crypto} {s : Sys}

variable (x) in
def pushA (s : Sys) : Msg := .push x.c x.A.pk x.B.pk s.a.ops
variable (x) in
def pushB (s : Sys) : Msg := .push x.c x.B.pk x.A.pk s.b.ops
variable (x) in
/-- What B's tick sends: its hello while its link is pending and no session is open; its ops
over its session. -/
noncomputable def msgsB (s : Sys) : List Msg :=
  (if s.b.links = [x.link] ∧ x.adm ∉ s.b.ops ∧ (x.c, x.A.pk) ∉ s.b.sessions then [x.hello] else []) ++
    s.b.sessions.map fun _ => x.pushB s
variable (x) in
/-- B after its tick: the link forgotten once B holds its admission. -/
def bAfter (s : Sys) : Node := { s.b with links := if x.adm ∈ s.b.ops then [] else s.b.links }

section
variable (g : x.Good C)
include g

theorem out_tickA (hI : x.Inv s) :
    stepOut C x.approval s .tickA =
      ({ s with net := s.net ++ s.a.sessions.map fun _ => x.pushA s },
        s.a.sessions.map fun _ => x.pushA s) := by
  simp only [stepOut, tick_A g hI]; rfl

theorem out_tickB (hI : x.Inv s) :
    stepOut C x.approval s .tickB = ({ s with b := x.bAfter s, net := s.net ++ x.msgsB s }, x.msgsB s) := by
  simp only [stepOut, tick_B g hI]; rfl

omit g in
theorem out_approve :
    stepOut C x.approval s .approve = ({ s with a := x.approval s.a }, []) := rfl

omit g in
theorem out_drop {m : Msg} : stepOut C x.approval s (.drop m) = ({ s with net := s.net.erase m }, []) :=
  rfl

theorem out_hello (hI : x.Inv s) :
    stepOut C x.approval s (.deliver x.hello) =
      if x.adm ∈ s.a.ops then
        ({ s with a := { s.a with ops := add1 s.a.ops x.req, sessions := ins s.a.sessions (x.c, x.B.pk) },
                  net := s.net.erase x.hello ++ [x.answer] }, [x.answer])
      else ({ s with a := { s.a with ops := add1 s.a.ops x.req }, net := s.net.erase x.hello }, []) := by
  have hd : x.hello.dst = s.a.me := by rw [hI.ame]; rfl
  simp only [stepOut, if_pos hd]
  rw [show recv C s.a x.hello = onHello C s.a x.c x.B.pk (some x.req) from rfl, hello_A g hI]
  split <;> simp

theorem out_answer (hI : x.Inv s) :
    stepOut C x.approval s (.deliver x.answer) =
      ({ s with b := if s.b.links = [x.link] then { s.b with sessions := ins s.b.sessions (x.c, x.A.pk) }
                     else s.b,
                net := s.net.erase x.answer }, []) := by
  have h1 : x.answer.dst ≠ s.a.me := by rw [hI.ame]; exact fun h => g.AB h.symm
  have h2 : x.answer.dst = s.b.me := by rw [hI.bme]; rfl
  simp only [stepOut, if_neg h1, if_pos h2]
  rw [show recv C s.b x.answer = (onAnswer C s.b x.c x.A.pk, []) from rfl, answer_B g hI]; simp

theorem out_pushAB (hI : x.Inv s) {os : List Op} (hos : x.InS os) :
    stepOut C x.approval s (.deliver (.push x.c x.A.pk x.B.pk os)) =
      ({ s with b := if (x.c, x.A.pk) ∈ s.b.sessions then { s.b with ops := add s.b.ops os } else s.b,
                net := s.net.erase (.push x.c x.A.pk x.B.pk os) }, []) := by
  have h1 : (Msg.push x.c x.A.pk x.B.pk os).dst ≠ s.a.me := by
    rw [hI.ame]; exact fun h => g.AB h.symm
  have h2 : (Msg.push x.c x.A.pk x.B.pk os).dst = s.b.me := by rw [hI.bme]; rfl
  simp only [stepOut, if_neg h1, if_pos h2]
  rw [show recv C s.b (.push x.c x.A.pk x.B.pk os) = (onPush C s.b x.c x.A.pk os, []) from rfl,
    push_B g hI hos]; simp

theorem out_pushBA (hI : x.Inv s) {os : List Op} (hos : x.InS os) :
    stepOut C x.approval s (.deliver (.push x.c x.B.pk x.A.pk os)) =
      ({ s with net := s.net.erase (.push x.c x.B.pk x.A.pk os) }, []) := by
  have h1 : (Msg.push x.c x.B.pk x.A.pk os).dst = s.a.me := by rw [hI.ame]; rfl
  simp only [stepOut, if_pos h1]
  rw [show recv C s.a (.push x.c x.B.pk x.A.pk os) = (onPush C s.a x.c x.B.pk os, []) from rfl,
    push_A g hI hos]; simp

/-! ## The invariant is kept -/

theorem covers_add {L os : List Op} (hL : x.InS L) (hos : x.InS os) (h : x.Covers os) :
    x.Covers (add L os) :=
  fun o ho => self_add g.distinct hL hos (h o ho)

theorem inv_step (hI : x.Inv s) {act : Act} (he : Enabled s act) :
    x.Inv (step C x.approval s act) := by
  unfold step
  cases act with
  | tickA =>
    rw [out_tickA g hI]
    refine { hI with net := fun m hm => ?_ }
    rcases List.mem_append.1 hm with hm | hm
    · exact NetOk.mono (hI.net m hm) id
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm
      have := hI.asess p hp
      exact Or.inr (Or.inr (Or.inl ⟨_, rfl, hI.aS, hI.acov this.2, this.1 ▸ hp⟩))
  | tickB =>
    rw [out_tickB g hI]
    refine { hI with blinks := ?_, bdone := ?_, net := fun m hm => ?_ }
    · show (if x.adm ∈ s.b.ops then [] else s.b.links) = [] ∨
        (if x.adm ∈ s.b.ops then [] else s.b.links) = [x.link]
      split
      · exact Or.inl rfl
      · exact hI.blinks
    · show (if x.adm ∈ s.b.ops then [] else s.b.links) = [] → _
      split
      · intro _; assumption
      · exact hI.bdone
    · rcases List.mem_append.1 hm with hm | hm
      · exact NetOk.mono (hI.net m hm) id
      · unfold msgsB at hm
        rcases List.mem_append.1 hm with hm | hm
        · split at hm
          · rw [List.mem_singleton.1 hm]; exact Or.inl rfl
          · cases hm
        · obtain ⟨p, _, rfl⟩ := List.mem_map.1 hm
          exact Or.inr (Or.inr (Or.inr ⟨_, rfl, hI.bS⟩))
  | approve =>
    rw [out_approve, approval_eq g]
    by_cases hreq : x.req ∈ s.a.ops
    · rw [if_pos hreq]
      have hS2 : x.InS [x.appr, x.adm] := by
        intro o ho; simp at ho; rcases ho with rfl | rfl
        · exact x.mem_S.2.2.2.1
        · exact x.mem_S.2.2.2.2
      have hadm : x.adm ∈ add s.a.ops [x.appr, x.adm] :=
        self_add g.distinct hI.aS hS2 (by simp)
      refine { hI with aS := ?_, ar := mem_add_of hI.ar, ai := mem_add_of hI.ai, acov := ?_,
                       asess := ?_, net := fun m hm => NetOk.mono (hI.net m hm) id }
      · intro o ho
        rcases mem_add ho with h | h
        · exact hI.aS o h
        · exact hS2 o h
      · intro _ o ho
        simp only [S, List.mem_cons, List.mem_nil_iff, or_false] at ho
        rcases ho with rfl | rfl | rfl | rfl | rfl
        · exact mem_add_of hI.ar
        · exact mem_add_of hI.ai
        · exact mem_add_of hreq
        · exact self_add g.distinct hI.aS hS2 (by simp)
        · exact hadm
      · intro p hp; exact ⟨(hI.asess p hp).1, hadm⟩
    · rw [if_neg hreq]; exact hI
  | drop m =>
    rw [out_drop]
    exact { hI with net := fun m' hm' => NetOk.mono (hI.net m' (List.mem_of_mem_erase hm')) id }
  | deliver m =>
    have hm : m ∈ s.net := he
    rcases hI.net m hm with rfl | ⟨rfl, hab⟩ | ⟨os, rfl, hin, hcov, _⟩ | ⟨os, rfl, hin⟩
    · rw [out_hello g hI]
      have hS' : x.InS (add1 s.a.ops x.req) := fun o h => by
        rcases mem_add1 h with h | rfl
        · exact hI.aS o h
        · exact x.mem_S.2.2.1
      have hadm' : x.adm ∈ add1 s.a.ops x.req → x.adm ∈ s.a.ops :=
        fun h => (mem_add1 h).resolve_right x.adm_ne.2.2
      split
      · rename_i hadm
        refine { hI with aS := hS', ar := mem_add1_of hI.ar, ai := mem_add1_of hI.ai,
                         acov := fun h o ho => mem_add1_of (hI.acov (hadm' h) o ho),
                         asess := ?_, bsess := ?_, net := ?_ }
        · intro p hp
          rcases mem_ins.1 hp with hp | rfl
          · exact ⟨(hI.asess p hp).1, mem_add1_of hadm⟩
          · exact ⟨rfl, mem_add1_of hadm⟩
        · intro p hp
          exact ⟨(hI.bsess p hp).1, mem_ins.2 (Or.inl (hI.bsess p hp).2)⟩
        · intro m' hm'
          rcases List.mem_append.1 hm' with hm' | hm'
          · exact NetOk.mono (hI.net m' (List.mem_of_mem_erase hm')) fun h => mem_ins.2 (Or.inl h)
          · rw [List.mem_singleton.1 hm']; exact Or.inr (Or.inl ⟨rfl, mem_ins.2 (Or.inr rfl)⟩)
      · rename_i hadm
        refine { hI with aS := hS', ar := mem_add1_of hI.ar, ai := mem_add1_of hI.ai,
                         acov := fun h => absurd (hadm' h) hadm,
                         asess := fun p hp => absurd (hI.asess p hp).2 hadm,
                         net := fun m' hm' => NetOk.mono (hI.net m' (List.mem_of_mem_erase hm')) id }
    · rw [out_answer g hI]
      split
      · refine { hI with bmore := ?_, bsess := ?_,
                         net := fun m' hm' => NetOk.mono (hI.net m' (List.mem_of_mem_erase hm')) id }
        · intro h; obtain ⟨h1, h2⟩ := hI.bmore h; exact ⟨h1, mem_ins.2 (Or.inl h2)⟩
        · intro p hp
          rcases mem_ins.1 hp with hp | rfl
          · exact hI.bsess p hp
          · exact ⟨rfl, hab⟩
      · exact { hI with net := fun m' hm' => NetOk.mono (hI.net m' (List.mem_of_mem_erase hm')) id }
    · rw [out_pushAB g hI hin]
      split
      · rename_i hses
        have hS' : x.InS (add s.b.ops os) := fun o h => by
          rcases mem_add h with h | h
          · exact hI.bS o h
          · exact hin o h
        refine { hI with bS := hS', breq := mem_add_of hI.breq,
                         bmore := fun _ => ⟨covers_add g hI.bS hin hcov, hses⟩,
                         bdone := fun h => mem_add_of (hI.bdone h),
                         net := fun m' hm' => NetOk.mono (hI.net m' (List.mem_of_mem_erase hm')) id }
      · exact { hI with net := fun m' hm' => NetOk.mono (hI.net m' (List.mem_of_mem_erase hm')) id }
    · rw [out_pushBA g hI hin]
      exact { hI with net := fun m' hm' => NetOk.mono (hI.net m' (List.mem_of_mem_erase hm')) id }

/-- **The invariant holds in every state reachable over a failing socket.** -/
theorem reachable_inv {t : Sys} (h : Reachable C x.approval x.init t) : x.Inv t := by
  induction h with
  | init => exact inv_init g
  | step act _ he ih => exact inv_step g ih he

end

end Scene

end Net
