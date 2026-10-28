/-
What sync may send and take, as the laws a networked node relies on.

- **Offer.** A node offers a peer only ops it has stored, so never a
  write still in its outbox (a pending write travels once committed),
  and only ops of shared kinds (`offer_shared`, `offer_stored`).
- **Take.** A job of ops from a peer passes `intake` before it is
  received: ops of local kinds are dropped unless the job is this node's
  own (`intake_local`). So every local op a node stores is one of its own
  writes, whatever its peers send (`stored_local`): a peer can push no
  pending link, acceptance or session state into it.

`offer` runs where `Store` does: on SQLite, and on the model for proofs.
-/
import Engine.Run
import Engine.Proofs

namespace Engine

section
variable {F : Type} (fam : Family F)

/-- Whether ops of o's kind travel. -/
def Family.shared (o : Op) : Bool := (fam.room o).isSome

/-- What the writer receives from a job: all of it if the job is this
node's own; only shared ops if it came from a peer. -/
def intake (mine : Bool) (ops : List Op) : List Op :=
  if mine then ops else ops.filter fam.shared

/-- What the bare wire takes: conn ops only (a handshake's), never a
shared or a local op. -/
def intakeConn (ops : List Op) : List Op :=
  ops.filter fun o => Decidable.decide (fam.scope o = .conn)

theorem intakeConn_conn {ops : List Op} {o : Op} (h : o ∈ intakeConn fam ops) :
    fam.scope o = .conn ∧ o ∈ ops := by
  simp only [intakeConn, List.mem_filter, decide_eq_true_eq] at h
  exact ⟨h.2, h.1⟩

/-- **Nothing local is taken from a peer.** -/
theorem intake_local {mine : Bool} {ops : List Op} {o : Op} (h : o ∈ intake fam mine ops)
    (hl : fam.room o = none) : mine = true ∧ o ∈ ops := by
  unfold intake at h
  cases mine with
  | true => exact ⟨rfl, h⟩
  | false =>
    simp only [Bool.false_eq_true, ite_false, List.mem_filter, Family.shared] at h
    rw [hl] at h; cases h.2

variable {m : Type → Type} [Monad m] [Store F m]

/-- The stored ops among these ids that a peer may be sent. -/
def offer : List Id → m (List Op)
  | [] => pure []
  | x :: t => do
    let o ← Store.getOp (F := F) x
    let rest ← offer t
    pure (match o with
      | some o => if fam.shared o then o :: rest else rest
      | none => rest)

end

section
variable {F : Type} {fam : Family F}

def offerS (fam : Family F) (s : DB F) (ids : List Id) : List Op :=
  ids.filterMap fun x => match s.ops x with
    | some o => if fam.shared o then some o else none
    | none => none

theorem run_offer (ids : List Id) (s : DB F) :
    (offer fam ids : Model F (List Op)).run s = (offerS fam s ids, s) := by
  induction ids with
  | nil => rfl
  | cons x t ih =>
    simp only [offer, Model.run_bind, run_getOp, ih, Model.run_pure, offerS, List.filterMap_cons]
    cases s.ops x with
    | none => rfl
    | some o => by_cases h : fam.shared o = true <;> simp [h]

/-- **Sync offers only stored, shared ops.** -/
theorem offer_shared {s : DB F} {ids : List Id} {o : Op}
    (h : o ∈ ((offer fam ids : Model F (List Op)).run s).1) :
    (fam.room o).isSome = true ∧ ∃ x ∈ ids, s.ops x = some o := by
  rw [run_offer] at h
  simp only [offerS, List.mem_filterMap] at h
  obtain ⟨x, hx, hm⟩ := h
  split at hm
  · rename_i p hp
    split at hm
    · rename_i hs; cases hm
      exact ⟨hs, x, hx, hp⟩
    · cases hm
  · cases hm

/-- **Nothing pending is offered:** what is offered is in the store, and
an outbox write is not in the store until its commit. -/
theorem offer_stored {s : DB F} {ids : List Id} {o : Op}
    (h : o ∈ ((offer fam ids : Model F (List Op)).run s).1) : ∃ x, s.ops x = some o :=
  let ⟨_, x, _, hx⟩ := offer_shared h; ⟨x, hx⟩

/-- A node's tables after receiving jobs, each through `intake`, with
judging and purges anywhere in between. `M` collects the ops of its own
jobs. -/
inductive Fed (fam : Family F) : List Op → DB F → Prop
  | empty : Fed fam [] DB.empty
  | job {M : List Op} {s : DB F} (mine : Bool) (ops : List Op) : Fed fam M s →
      Fed fam (if mine then ops ++ M else M) ((intake fam mine ops).foldl (fun s o => ingestS o s) s)
  | step {M : List Op} {s : DB F} : Fed fam M s → Fed fam M (stepS fam s)
  | purge {M : List Op} {s : DB F} (ids : List Id) : Fed fam M s → Fed fam M (purgeS fam ids s)

theorem ingestS_ops {o : Op} {s : DB F} {x : Id} {p : Op} (h : (ingestS o s).ops x = some p) :
    s.ops x = some p ∨ p = o := by
  unfold ingestS at h
  split at h
  · exact Or.inl h
  · change (if x = o.id then some o else s.ops x) = some p at h
    split at h
    · cases h; exact Or.inr rfl
    · exact Or.inl h

theorem foldl_ingest_ops {ops : List Op} {s : DB F} {x : Id} {p : Op}
    (h : (ops.foldl (fun s o => ingestS o s) s).ops x = some p) : s.ops x = some p ∨ p ∈ ops := by
  induction ops generalizing s with
  | nil => exact Or.inl h
  | cons o t ih =>
    rcases ih h with h | h
    · rcases ingestS_ops h with h | rfl
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_self ..)
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem stepS_ops' (s : DB F) : (stepS fam s).ops = s.ops := stepS_ops (fam := fam) s

/-- **Every local op a node stores is its own write**, whatever its
peers send it, and whatever it has purged. -/
theorem stored_local {M : List Op} {s : DB F} (h : Fed fam M s) {x : Id} {o : Op}
    (hx : s.ops x = some o) (hl : fam.room o = none) : o ∈ M := by
  induction h with
  | empty => cases hx
  | job mine ops _ ih =>
    rcases foldl_ingest_ops hx with hx | ho
    · have := ih hx
      cases mine
      · exact this
      · exact List.mem_append_right _ this
    · obtain ⟨rfl, ho⟩ := intake_local fam ho hl
      exact List.mem_append_left _ ho
  | step _ ih => rw [stepS_ops'] at hx; exact ih hx
  | @purge M s ids _ ih =>
    by_cases hp : x ∈ purgeSet fam s ids
    · rw [purgeS_ops_mem s ids hp] at hx; cases hx
    · rw [purgeS_ops_not s ids hp] at hx; exact ih hx

end

end Engine
