/-
Every op the Community family's writers author cites at most `maxReqs`
requirements, so intake's cap (engine/core/Sync.lean) refuses no honest
write (docs/PERF.md; holmes-a3's check before landing the cap).

Per writer the count is a constant, and none grows with the community:
a root, a key, a secret, an acceptance and a pending join cite nothing;
a wrap, a receipt and an abandon one op; an invitation, a request, a
post and a profile two; an approval, a reaction and an attachment three;
a grant and a removal four; a chunk two; a name three and the name it
supersedes (`rename` cites at most one). The one that could grow is an
admission, which cites its threshold's approvals: an invitation's
validator now refuses a threshold over `maxReqs − 2`
(`check_invitation`), and `approveReq` composes no admission past it.

- Per writer: `*_reqs` (the requirements, as written).
- Per intent: `Authored` (every op within the cap) of `found`,
  `inviteTo`, `joinOps`, `stopWaiting`, `reactTo`; and of every answer of
  the view intents (`View.Always`): `join`, `introduce`, `approveReq`,
  `rename`, `removeMember`, `receiptFor`, `send`, `unwrap`.
-/
import ops.community.WrapLaws

namespace Community
open Engine Engine.View

/-- Every op of a write cites at most `maxReqs`. -/
def Authored (w : Write) : Prop := ∀ o ∈ w.ops, o.reqs.length ≤ maxReqs

/-! ## Each writer, its requirements -/

@[simp] theorem root_reqs (d : Device) : (root d).reqs = [] := rfl
@[simp] theorem invite_reqs (c a : Id) (d : Device) (b : Key) (l : Bool) (t : Nat) :
    (invite c a d b l t).reqs = [c, a] := rfl
@[simp] theorem request_reqs (c inv : Id) (d : Device) (bsk : ByteArray) :
    (request c inv d bsk).reqs = [c, inv] := rfl
@[simp] theorem approve_reqs (c req adm : Id) (d : Device) : (approve c req adm d).reqs = [c, req, adm] := rfl
@[simp] theorem admit_reqs (c req : Id) (aps : List Id) : (admit c req aps).reqs = c :: req :: aps := rfl
@[simp] theorem grant_reqs (c g a t : Id) (d : Device) : (grant c g a t d).reqs = [c, g, a, t] := rfl
@[simp] theorem remove_reqs (c r a t : Id) (d : Device) : (remove c r a t d).reqs = [c, r, a, t] := rfl
@[simp] theorem post_reqs (c adm : Id) (d : Device) (k t : ByteArray) (n tm : Nat) :
    (post c adm d k t n tm).reqs = [c, adm] := rfl
@[simp] theorem sealedPost_reqs (c adm : Id) (d : Device) (k nonce t : ByteArray) (n tm : Nat) :
    (sealedPost c adm d k nonce t n tm).reqs = [c, adm] := rfl
@[simp] theorem profile_reqs (c adm : Id) (d : Device) (nm : ByteArray) (tm : Nat) :
    (profile c adm d nm tm).reqs = [c, adm] := rfl
@[simp] theorem react_reqs (c adm t : Id) (d : Device) (e : ByteArray) (tm : Nat) :
    (react c adm t d e tm).reqs = [c, adm, t] := rfl
@[simp] theorem wrap_reqs (c : Id) (k r b : ByteArray) : (wrap c k r b).reqs = [c] := rfl
@[simp] theorem wrapKey_reqs (c : Id) (k esk to : ByteArray) : (wrapKey c k esk to).reqs = [c] := rfl
@[simp] theorem contentKey_reqs (c k : ByteArray) : (contentKey c k).reqs = [] := rfl
@[simp] theorem receipt_reqs (m : Id) (k : Nat) : (receipt m k).reqs = [m] := rfl
@[simp] theorem secret_reqs (seed : ByteArray) : (secret seed).reqs = [] := rfl
@[simp] theorem accept_reqs (c : Id) (d : Key) : (accept c d).reqs = [] := rfl
@[simp] theorem setName_reqs (c adm auth : Id) (prev : List Id) (n : Nat) (d : Device) (nm : ByteArray) :
    (setName c adm auth prev n d nm).reqs = [c, adm, auth] ++ prev := rfl
@[simp] theorem joining_reqs (i : Invite) (req : Id) (nm : ByteArray) (d : Key) (e : Nat) :
    (joining i req nm d e).reqs = [] := rfl
@[simp] theorem abandon_reqs (j : Id) : (abandon j).reqs = [j] := rfl

/-- An attachment cites three; each of its chunks two. -/
theorem attach_reqs (c adm msg : Id) (d : Device) (k : ByteArray) (f : NewFile) :
    (attach c adm msg d k f).1.reqs.length = 3 ∧ ∀ o ∈ (attach c adm msg d k f).2, o.reqs.length = 2 := by
  refine ⟨rfl, fun o ho => ?_⟩
  simp only [attach, List.mem_map] at ho
  obtain ⟨_, _, rfl⟩ := ho
  rfl

theorem maxReqs_eq : maxReqs = 64 := rfl

/-- **A Valid invitation's threshold is at most `maxReqs − 2`**, so the
admission completing it (the community, the request, and exactly
threshold approvals: `tally`) cites at most `maxReqs`. -/
theorem invite_threshold {C : Crypto} {o : Op} {b : Body} {fs : List Fact} {c i : Id} {k : Key}
    {l : Bool} {t : Nat} (h : check C o b fs = some (.invitation c i k l t)) : t + 2 ≤ maxReqs :=
  let ⟨_, _, _, _, _, _, _, _, _, ht, _, _⟩ := check_invitation h; ht

/-! ## Each intent, its writes -/

theorem found_authored (seed nm my : ByteArray) (tm : Nat) (k esk : ByteArray) :
    Authored (found seed nm my tm k esk) := by
  intro o ho
  simp only [found, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [maxReqs]

theorem inviteTo_authored (c a : Id) (d : Device) (b : ByteArray) (h : List ByteArray) (t : Nat) :
    Authored (inviteTo c a d b h t).1 := by
  intro o ho
  simp only [inviteTo, issue, List.mem_cons, List.not_mem_nil, or_false] at ho
  subst ho; simp [maxReqs]

theorem joinOps_authored (i : Invite) (seed nm : ByteArray) : Authored (joinOps i seed nm) := by
  intro o ho
  simp only [joinOps, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl <;> simp [maxReqs, Invite.request]

theorem stopWaiting_authored (j : Id) : Authored (stopWaiting j) := by
  intro o ho
  simp only [stopWaiting, List.mem_cons, List.not_mem_nil, or_false] at ho
  subst ho; simp [maxReqs]

theorem reactTo_authored (c a t : Id) (d : Device) (e : ByteArray) (tm : Nat) :
    Authored (reactTo c a t d e tm) := by
  intro o ho
  simp only [reactTo, List.mem_cons, List.not_mem_nil, or_false] at ho
  subst ho; simp [maxReqs]

/-- **An approval's admission stays within the cap**, whatever the store
answers: it cites the community, the request and at most `maxReqs − 2`
approvals. -/
theorem approveReq_authored (c req myAdm : Id) (d : Device) (esk : ByteArray) :
    Always Authored (approveReq c req myAdm d esk) := by
  unfold approveReq
  refine always_bind fun _ => always_bind fun _ => always_bind fun _ => always_bind fun ks => ?_
  dsimp only
  repeat' split
  all_goals (try simp only [Always, pure_eq])
  all_goals (repeat' split)
  all_goals (simp_all [Authored, maxReqs]; try omega)

theorem rename_authored (c a auth : Id) (d : Device) (nm : ByteArray) :
    Always Authored (rename c a auth d nm) := by
  unfold rename
  refine always_bind fun cur => ?_
  try simp only [Always]
  simp only [Always, pure_eq]
  intro o ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  subst ho
  split <;> simp [maxReqs]

theorem removeMember_authored (c t : Id) (d : Device) : Always Authored (removeMember c t d) := by
  unfold removeMember
  refine always_bind fun _ => always_bind fun _ => always_bind fun _ => ?_
  try simp only [Always]
  split
  · refine always_bind fun _ => ?_
    try simp only [Always]
    split
    · simp only [Always, pure_eq]
      split <;> simp_all [Authored, maxReqs]
    · simp [Always, pure_eq, Authored]
  · simp [Always, pure_eq, Authored]

theorem introduce_authored (c : Id) (d : Device) (tm : Nat) : Always Authored (introduce c d tm) := by
  unfold introduce
  refine always_bind fun _ => ?_
  try simp only [Always]
  split
  · refine always_bind fun _ => always_bind fun _ => ?_
    try simp only [Always]
    split
    · simp only [Always, pure_eq]
      split <;> simp_all [Authored, maxReqs]
    · simp [Always, pure_eq, Authored]
  · simp [Always, pure_eq, Authored]

theorem receiptFor_authored (o : Op) :
    Always (fun os : List Op => ∀ p ∈ os, p.reqs.length ≤ maxReqs) (receiptFor o) := by
  unfold receiptFor
  split
  · simp [Always, pure_eq]
  · split
    · split
      · simp [Always, pure_eq]
      · refine always_bind fun _ => ?_
        try simp only [Always]
        split
        · simp [Always, pure_eq]
        · refine always_bind fun _ => ?_
          simp only [Always, pure_eq]
          intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; subst hp; simp [maxReqs]
    · simp [Always, pure_eq]

/-- Whatever the first view answers. -/
theorem always_bind_all {α β : Type} {P : β → Prop} {f : α → View Fact β} (h : ∀ a, Always P (f a)) :
    ∀ v : View Fact α, Always P (v >>= f)
  | .pure a => h a
  | .list _ k => fun a => always_bind_all h (k a)

theorem always_mono {α : Type} {P Q : α → Prop} (h : ∀ a, P a → Q a) : ∀ {v : View Fact α}, Always P v → Always Q v
  | .pure a, hp => h a hp
  | .list _ k, hp => fun a => always_mono h (v := k a) (hp a)

theorem join_authored (i : Invite) (seed nm : ByteArray) : Always Authored (join i seed nm) := by
  unfold join
  refine always_bind_all (fun m => ?_) _
  split
  · simp [Always, pure_eq, Authored]
  · refine always_bind fun _ => ?_
    try simp only [Always]
    split
    · simp only [Always, pure_eq]; simp [Authored, maxReqs, mkOp]
    · simp only [Always, pure_eq]; exact joinOps_authored i seed nm

theorem send_authored (c a : Id) (d : Device) (k nonce t : ByteArray) (now : Nat) (files : List NewFile) :
    Always Authored (send c a d k nonce t now files) := by
  unfold send
  refine always_bind_all (fun n => ?_) _
  refine always_bind (always_mono (fun r (hr : ∀ p ∈ r, p.reqs.length ≤ maxReqs) => ?_) (receiptFor_authored _))
  simp only [Always, pure_eq]
  intro o ho
  simp only [List.mem_cons, List.mem_append, List.mem_flatMap] at ho
  rcases ho with (rfl | ho) | ⟨f, _, ho⟩
  · simp [maxReqs]
  · exact hr o ho
  · have := attach_reqs c a (sealedPost c a d k nonce t (min (n + 1) countCap) now).id d k f
    rcases ho with rfl | ho
    · rw [this.1]; decide
    · rw [this.2 o ho]; decide

end Community
