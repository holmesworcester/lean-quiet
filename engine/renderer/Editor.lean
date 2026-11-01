/- The optional owned-editor seam. Android implements it with one immutable
semantic candidate; older shells explicitly return no metadata. -/
namespace Editor

structure Snapshot where
  ticket : UInt64
  owner : UInt64
  revision : UInt64
  content : UInt64
  text : String
  selection : Array UInt32
  deriving BEq, Repr

structure Latest where
  owner : UInt64
  revision : UInt64
  ready : Bool
  clearing : UInt64
  exhausted : Bool
  consumed : Bool
  installed : UInt64
  text : String
  selection : Array UInt32
  deriving BEq, Repr

/-- Commands never wait for the Java UI thread. Install/CAS publish a bounded
pending command; later reads report the state actually installed by Java. -/
structure Io where
  exchange : UInt32 → UInt64 → UInt64 → String → IO (String × Array UInt64) :=
    fun _ _ _ _ => pure ("", #[])
  action : UInt64 → UInt32 → IO (String × Array UInt64) :=
    fun _ _ => pure ("", #[])

def latest (p : String × Array UInt64) : Option Latest := do
  if p.2.size != 12 || p.2[0]! != 1 then none else
    some ⟨p.2[1]!, p.2[2]!, p.2[3]! == 1, p.2[4]!, p.2[5]! == 1, p.2[10]! == 1, p.2[11]!, p.1,
      (p.2.extract 6 10).map UInt64.toUInt32⟩

def snapshot (p : String × Array UInt64) : Option Snapshot := do
  if p.2.size != 8 || p.2[0]! == 0 then none else
    some ⟨p.2[0]!, p.2[1]!, p.2[2]!, p.2[3]!, p.1,
      (p.2.extract 4 8).map UInt64.toUInt32⟩

structure State where
  /-- Semantic epochs are separate from resize/IME geometry generations. -/
  owner : Nat := 0
  key : String := ""
  context : String := ""
  target : String := ""
  contentKey : String := ""
  content : Nat := 0
  handoff : Bool := false
  revision : UInt64 := 0
  enabled : Option Bool := none
  clear : Option (UInt64 × UInt64) := none
  deriving Repr

def State.next (s : State) : Option UInt64 :=
  if s.owner + 1 < 18446744073709551616 then some (s.owner + 1).toUInt64 else none

end Editor
