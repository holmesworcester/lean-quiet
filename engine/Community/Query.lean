/-
What a node asks its tables when it connects and when it seals: is
this device a member's, and which device keys should a content key go
to. The queries read the persisted index and verdicts only, through
`Store`, so they run on SQLite as they run on the model.
-/
import Community.Facts

namespace Community
open Engine

section
variable {m : Type → Type} [Monad m] [Store Fact m]
open Store

/-- The facts of the Valid ops among ids. -/
def validOf : List Id → m (List Fact)
  | [] => pure []
  | x :: t => do
    let st ← getStatus x
    let r ← validOf t
    pure (match st with
      | some (.valid f) => f :: r
      | _ => r)

def isRemovalOf (c u : Id) : Fact → Bool
  | .removal c' u' _ => decide (c' = c ∧ u' = u)
  | _ => false

/-- Whether user u of c has been removed. -/
def removed (c u : Id) : m Bool := do
  let fs ← validOf (← lookup (key 2 c u))
  pure (fs.any (isRemovalOf c u))

/-- Whether any of these admits device d into a user of c not removed. -/
def liveUsers (c : Id) (d : Key) : List Fact → m Bool
  | [] => pure false
  | f :: t => do
    match f with
    | .admission c' u d' _ =>
      if c' = c ∧ d' = d then
        if !(← removed c u) then return true
      liveUsers c d t
    | _ => liveUsers c d t

/-- Whether to sync community c with device d. -/
def allowPeer (c : Id) (d : Key) : m Bool := do
  liveUsers c d (← validOf (← lookup (key 0 c d)))

/-- The encryption keys of these admissions into users of c not
removed. -/
def liveKeys (c : Id) : List Fact → m (List Key)
  | [] => pure []
  | f :: t => do
    let rest ← liveKeys c t
    match f with
    | .admission c' u _ e =>
      if c' = c then
        if !(← removed c u) then return e :: rest
      return rest
    | _ => return rest

/-- The device keys a new content key of c is wrapped to. -/
def recipients (c : Id) : m (List Key) := do
  liveKeys c (← validOf (← lookup (key 1 c c)))

end

/-! ## On the model: the queries as functions of the tables -/

section
variable (s : DB Fact)

def validOfP (l : List Id) : List Fact :=
  l.filterMap fun x => match s.status x with
    | some (.valid f) => some f
    | _ => none

def removedP (c u : Id) : Bool := (validOfP s (s.idx (key 2 c u))).any (isRemovalOf c u)

def liveP (c : Id) (d : Key) : Fact → Bool
  | .admission c' u d' _ => decide (c' = c ∧ d' = d) && !removedP s c u
  | _ => false

def allowP (c : Id) (d : Key) : Bool := (validOfP s (s.idx (key 0 c d))).any (liveP s c d)

def keyOfP (c : Id) : Fact → Option Key
  | .admission c' u _ e => if c' = c ∧ removedP s c u = false then some e else none
  | _ => none

def recipientsP (c : Id) : List Key := (validOfP s (s.idx (key 1 c c))).filterMap (keyOfP s c)

end

theorem run_validOf (l : List Id) (s : DB Fact) :
    (validOf l : Model Fact _).run s = (validOfP s l, s) := by
  induction l with
  | nil => rfl
  | cons x t ih =>
    simp only [validOf, Model.run_bind, run_getStatus, ih, Model.run_pure, validOfP,
      List.filterMap_cons]
    cases s.status x with
    | none => rfl
    | some v => cases v <;> rfl

theorem run_removed (c u : Id) (s : DB Fact) :
    (removed c u : Model Fact _).run s = (removedP s c u, s) := by
  simp only [removed, Model.run_bind, run_lookup, run_validOf, Model.run_pure]; rfl

theorem run_liveUsers (c : Id) (d : Key) (fs : List Fact) (s : DB Fact) :
    (liveUsers c d fs : Model Fact _).run s = (fs.any (liveP s c d), s) := by
  induction fs with
  | nil => rfl
  | cons f t ih =>
    cases f with
    | admission c' u d' e =>
      simp only [liveUsers, List.any_cons, liveP]
      by_cases h : c' = c ∧ d' = d
      · simp only [h, and_self, ite_true, Model.run_bind, run_removed]
        cases hr : removedP s c u
        · rfl
        · simpa using ih
      · simp only [h, ite_false, decide_false, Bool.false_and, Bool.false_or]; exact ih
    | _ => simp only [liveUsers, List.any_cons, liveP, Bool.false_or]; exact ih

theorem run_allowPeer (c : Id) (d : Key) (s : DB Fact) :
    (allowPeer c d : Model Fact _).run s = (allowP s c d, s) := by
  simp only [allowPeer, Model.run_bind, run_lookup, run_validOf, run_liveUsers]; rfl

theorem run_liveKeys (c : Id) (fs : List Fact) (s : DB Fact) :
    (liveKeys c fs : Model Fact _).run s = (fs.filterMap (keyOfP s c), s) := by
  induction fs with
  | nil => rfl
  | cons f t ih =>
    simp only [liveKeys, Model.run_bind, ih, List.filterMap_cons]
    cases f with
    | admission c' u d' e =>
      simp only [keyOfP]
      by_cases h : c' = c
      · simp only [h, ite_true, Model.run_bind, run_removed]
        cases hr : removedP s c u <;> rfl
      · simp only [h, ite_false, false_and]; rfl
    | _ => rfl

theorem run_recipients (c : Id) (s : DB Fact) :
    (recipients c : Model Fact _).run s = (recipientsP s c, s) := by
  simp only [recipients, Model.run_bind, run_lookup, run_validOf, run_liveKeys]; rfl

end Community
