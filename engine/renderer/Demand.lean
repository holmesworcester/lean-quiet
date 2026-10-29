/-
Demand shared by readers and render workers. A component owns requests,
not threads. Several component paths may hold the same key. Reconciliation
keeps its ticket until its last owner leaves; a later mount gets a new
ticket, so a completion from the previous mount cannot publish.

The queue is independent of the component tree and op family. It retains
pending work in arrival order, gives visible work priority over prefetch,
and rotates continuations. These are the decisions the running workers
call; no clock or native operation is claimed to have a proved duration.
-/
import Std

namespace Demand
set_option linter.unusedSectionVars false

/-- Paths name components, conventionally page / op type / op id / child.
They are identities, not addresses of UI objects. -/
abbrev Owner := List ByteArray

structure Need (K : Type) where
  owner : Owner := []
  key : K
  visible : Bool := true
  deriving BEq

structure Ticket (K : Type) where
  key : K
  serial : Nat
  deriving BEq, DecidableEq

structure Plan (K : Type) where
  needs : List (Need K) := []
  tickets : List (Ticket K) := []
  next : Nat := 0

variable {K : Type} [BEq K]

def Plan.ticket (p : Plan K) (key : K) : Option (Ticket K) :=
  p.tickets.find? (fun t => t.key == key)

/-- Work is shared by key. At least one visible owner makes it visible. -/
def Plan.visible (p : Plan K) (key : K) : Bool :=
  p.needs.any (fun n => n.key == key && n.visible)

def Plan.held (p : Plan K) (key : K) : Bool :=
  p.needs.any (fun n => n.key == key)

/-- Build once per reconciliation, then filter board entries in constant
expected lookup time rather than scanning the component tree per entry. -/
def Plan.heldIndex [Hashable K] (p : Plan K) : Std.HashSet K :=
  Std.HashSet.ofList (p.needs.map (·.key))

theorem heldIndex_agrees [Hashable K] [LawfulBEq K] (p : Plan K) (key : K) :
    p.heldIndex.contains key = p.held key := by
  apply Bool.eq_iff_iff.mpr
  simp [Plan.heldIndex, Plan.held, List.any_eq_true, List.mem_map]

/-- Preserve tickets for overlapping demand, including a change of owner.
Reserve fresh serials even when some keys reuse their old ticket. -/
def Plan.reconcile (p : Plan K) (needs : List (Need K)) : Plan K :=
  let keys := (needs.map (·.key)).eraseDups
  { needs, next := p.next + keys.length,
    tickets := keys.zipIdx.map fun (k, i) => (p.ticket k).getD ⟨k, p.next + i⟩ }

def Plan.current (p : Plan K) (t : Ticket K) : Bool :=
  p.ticket t.key == some t

/-- The publication gate, also used before every cooperative step. -/
def complete (p : Plan K) (t : Ticket K) (value : V) : Option V :=
  if p.current t then some value else none

/-- Remove retired requests without moving retained work behind newcomers. -/
def reconcile (wanted queued : List K) : List K :=
  queued.filter wanted.contains ++ wanted.filter (fun k => !queued.contains k)

/-- Visible work first, FIFO within a class. Background can be paused. -/
def next (visible : K → Bool) (background : Bool) (queued : List K) : Option K :=
  match queued.find? visible with
  | some k => some k
  | none => if background then queued.head? else none

theorem complete_retired (p : Plan K) (t : Ticket K) (value : V)
    (h : p.current t = false) : complete p t value = none := by
  simp [complete, h]

theorem complete_current (p : Plan K) (t : Ticket K) (value : V)
    (h : p.current t = true) : complete p t value = some value := by
  simp [complete, h]

theorem reconcile_empty (queued : List K) : reconcile [] queued = [] := by
  simp [reconcile]

theorem visible_first (visible : K → Bool) (background : Bool) (queued : List K) (k : K)
    (h : queued.find? visible = some k) : next visible background queued = some k := by
  simp [next, h]

theorem background_paused (visible : K → Bool) (queued : List K)
    (h : queued.find? visible = none) : next visible false queued = none := by
  simp [next, h]

theorem idle_fifo (queued : List K) : next (fun _ => false) true queued = queued.head? := by
  have h : queued.find? (fun _ => false) = none := by
    induction queued with
    | nil => rfl
    | cons x xs ih => simpa [List.find?] using ih
  simp [next, h]

theorem visible_owner_holds (p : Plan K) (key : K) (h : p.visible key = true) :
    p.held key = true := by
  simp only [Plan.visible, List.any_eq_true] at h
  obtain ⟨n, hn, hk⟩ := h
  simp only [Bool.and_eq_true] at hk
  exact List.any_eq_true.mpr ⟨n, hn, hk.1⟩

theorem unmounted (p : Plan K) (key : K) : (p.reconcile []).held key = false := by
  simp [Plan.reconcile, Plan.held]

theorem unmounted_ticket (p : Plan K) (t : Ticket K) : (p.reconcile []).current t = false := by
  simp [Plan.reconcile, Plan.current, Plan.ticket]

theorem serial_monotone (p : Plan K) (needs : List (Need K)) : p.next ≤ (p.reconcile needs).next := by
  simp [Plan.reconcile]

section
variable [LawfulBEq K]

deriving instance ReflBEq, LawfulBEq for Ticket

/-- Ownership is exact, including shared queries: a query is held iff
at least one of the mounted components declares it. -/
theorem owned_iff (p : Plan K) (needs : List (Need K)) (key : K) :
    (p.reconcile needs).held key = true ↔ ∃ n ∈ needs, n.key = key := by
  simp [Plan.reconcile, Plan.held]

theorem next_visible (visible : K → Bool) (background : Bool) (queued : List K) (k : K)
    (ready : ∃ x ∈ queued, visible x = true) (chosen : next visible background queued = some k) :
    visible k = true := by
  cases h : queued.find? visible with
  | none =>
    obtain ⟨x, hx, hv⟩ := ready
    exact False.elim ((List.find?_eq_none.mp h x hx) hv)
  | some x =>
    have e : x = k := by simpa [next, h] using chosen
    exact e ▸ List.find?_some h

theorem reconcile_members (wanted queued : List K) (k : K) :
    k ∈ reconcile wanted queued ↔ k ∈ wanted := by
  by_cases h : k ∈ queued <;> simp [reconcile, h]

/-- Reconciliation leaves the retained queue as an exact prefix. -/
theorem retained_prefix (wanted queued : List K) :
    (queued.filter wanted.contains).IsPrefix (reconcile wanted queued) := by
  exact ⟨_, rfl⟩

theorem ticket_key (p : Plan K) (k : K) (t : Ticket K) (h : p.ticket k = some t) : t.key = k := by
  have hk : (t.key == k) = true := List.find?_some (p := fun t : Ticket K => t.key == k) h
  exact eq_of_beq hk

theorem assigned_key (p : Plan K) (k : K) (i : Nat) :
    ((p.ticket k).getD ⟨k, p.next + i⟩).key = k := by
  cases h : p.ticket k with
  | none => simp
  | some t => simpa [h] using ticket_key p k t h

theorem reconcile_keys (p : Plan K) (needs : List (Need K)) :
    ((p.reconcile needs).tickets.map Ticket.key) = (needs.map (·.key)).eraseDups := by
  simp only [Plan.reconcile, List.map_map, Function.comp_def]
  have h : (fun x : K × Nat => ((p.ticket x.1).getD ⟨x.1, p.next + x.2⟩).key) = Prod.fst := by
    funext x
    exact assigned_key p x.1 x.2
  rw [h]
  exact List.zipIdx_map_fst 0 _

theorem ticket_none (p : Plan K) (k : K) :
    p.ticket k = none ↔ k ∉ p.tickets.map Ticket.key := by
  simp [Plan.ticket, List.find?_eq_none, List.mem_map]

theorem reconcile_ticket_none (p : Plan K) (needs : List (Need K)) (k : K) :
    (p.reconcile needs).ticket k = none ↔ (p.reconcile needs).held k = false := by
  rw [ticket_none, reconcile_keys]
  simp [Plan.reconcile, Plan.held]

theorem reconcile_ticket_origin (p : Plan K) (needs : List (Need K)) (k : K) (t : Ticket K)
    (h : (p.reconcile needs).ticket k = some t) :
    ∃ i, i < (needs.map (·.key)).eraseDups.length ∧ t = (p.ticket k).getD ⟨k, p.next + i⟩ := by
  have ht := List.mem_of_find?_eq_some h
  simp only [Plan.reconcile, List.mem_map] at ht
  obtain ⟨⟨key, i⟩, member, eq⟩ := ht
  have hk := ticket_key (p.reconcile needs) k t h
  have keyeq : key = k := by rw [← eq, assigned_key] at hk; exact hk
  subst key
  exact ⟨i, by simpa using List.snd_lt_of_mem_zipIdx member, eq.symm⟩

theorem retained_ticket (p : Plan K) (needs : List (Need K)) (k : K) (t : Ticket K)
    (held : (p.reconcile needs).held k = true) (old : p.ticket k = some t) :
    (p.reconcile needs).ticket k = some t := by
  cases h : (p.reconcile needs).ticket k with
  | none => have := (reconcile_ticket_none p needs k).mp h; simp [held] at this
  | some t' =>
    obtain ⟨i, _, hi⟩ := reconcile_ticket_origin p needs k t' h
    simpa [old] using hi

theorem fresh_ticket (p : Plan K) (needs : List (Need K)) (k : K) (t : Ticket K)
    (absent : p.ticket k = none) (found : (p.reconcile needs).ticket k = some t) :
    p.next ≤ t.serial := by
  obtain ⟨i, _, hi⟩ := reconcile_ticket_origin p needs k t found
  simp only [absent, Option.getD_none] at hi
  subst t
  simp
/-- Serial invariant established at creation and preserved by every reconciliation. -/
def Plan.BeforeNext (p : Plan K) : Prop :=
  ∀ k t, p.ticket k = some t → t.serial < p.next

theorem empty_before_next : ({} : Plan K).BeforeNext := by
  simp [Plan.BeforeNext, Plan.ticket]

theorem reconcile_before_next (p : Plan K) (needs : List (Need K)) (inv : p.BeforeNext) :
    (p.reconcile needs).BeforeNext := by
  intro k t found
  obtain ⟨i, hi, ht⟩ := reconcile_ticket_origin p needs k t found
  cases h : p.ticket k with
  | none =>
    simp only [h, Option.getD_none] at ht
    subst t
    simp only [Plan.reconcile]
    omega
  | some old =>
    have ho := inv k old h
    simp only [h, Option.getD_some] at ht
    subst t
    have hm := serial_monotone p needs
    omega

/-- Across an unmount and remount, the old ticket's serial cannot return. -/
theorem remount_fresh (p : Plan K) (off on : List (Need K)) (k : K) (old new : Ticket K)
    (inv : p.BeforeNext) (was : p.ticket k = some old)
    (absent : (p.reconcile off).held k = false)
    (found : ((p.reconcile off).reconcile on).ticket k = some new) :
    old.serial < new.serial := by
  have hn := (reconcile_ticket_none p off k).mpr absent
  have hf := fresh_ticket (p.reconcile off) on k new hn found
  have hm := serial_monotone p off
  have ho := inv k old was
  omega

theorem remount_rejects (p : Plan K) (off on : List (Need K)) (k : K) (old new : Ticket K)
    (inv : p.BeforeNext) (was : p.ticket k = some old)
    (absent : (p.reconcile off).held k = false)
    (found : ((p.reconcile off).reconcile on).ticket k = some new) :
    ((p.reconcile off).reconcile on).current old = false := by
  have lt := remount_fresh p off on k old new inv was absent found
  have key := ticket_key p k old was
  have different : new ≠ old := by intro e; subst new; omega
  simp [Plan.current, key, found, different]

end
end Demand
