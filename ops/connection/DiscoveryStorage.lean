/- Extend the current Node storage theorem to the app's discovery hooks.
All durable changes still pass through the node's Turn, including retry clocks
and scan positions. No hook mutates the store behind the engine's back. -/
import ops.connection.DiscoveryLaws
import ops.connection.StorageEffects

namespace Connection.DiscoveryStorage
open Engine Engine.Sync Execution

private theorem plan_reads (c peer : B) (hs : List B) (now : Nat) :
    ReadsHeld (Discovery.plan c peer hs now : M _) := by
  unfold Discovery.plan; readsHeld [view_reads]

private theorem join_reads (K : Keys) (listen pk sk : B) (now : Nat) (f : Community.Fact) :
    ReadsHeld (Discovery.joinOne K listen pk sk now f : M _) := by
  cases f <;> simp only [Discovery.joinOne] <;>
    readsHeld [plan_reads, dialOne_reads ReadsHeld.fresh]

private theorem signer_reads (d : B) : ReadsHeld (Discovery.signer d : M _) := by
  unfold Discovery.signer; readsHeld [view_reads]

private theorem publish_reads (c adm d pk : B) (now : Nat) :
    ReadsHeld (Discovery.publish c adm d pk now : M _) := by
  unfold Discovery.publish; readsHeld [signer_reads, view_reads]

private theorem port_reads (cid : Id) : ReadsHeld (Discovery.remotePort cid : M _) := by
  unfold Discovery.remotePort; readsHeld [rows_reads]

private theorem observe_reads (c pk peer : B) (now : Nat) :
    ReadsHeld (Discovery.observe c pk peer now : M _) := by
  unfold Discovery.observe
  readsHeld [view_reads, signer_reads, list_reads, sessionOf_reads, port_reads]

private theorem member_reads (K : Keys) (listen pk sk : B) (now : Nat) (adm : Id) (f : Community.Fact) :
    ReadsHeld (Discovery.memberOne K listen pk sk now adm f : M _) := by
  cases f <;> simp only [Discovery.memberOne] <;>
    readsHeld [publish_reads, view_reads, connectedTo_reads, observe_reads, plan_reads,
      list_reads, helloOf_reads, ReadsHeld.fresh]

private theorem page_reads (r : Rel Community.Fact) (cursor : Option Pos) :
    ReadsHeld (Discovery.page r cursor : M _) := by
  unfold Discovery.page; readsHeld [view_reads]

/-- Discovery does not write around the node's write and validation path. -/
theorem dial_reads (K : Keys) (listen : B) (wall mono now : Nat) :
    ReadsHeld (Discovery.dial K listen wall mono now : M _) := by
  unfold Discovery.dial
  readsHeld [endpoints_reads, view_reads, page_reads, join_reads, member_reads]

theorem readOnly (fam : Family F) (K : Keys) (listen : B) (wall mono : Nat) (cfg : Config) :
    NodeTape.ReadOnly (Discovery.sync fam K listen wall mono cfg : Sync F M) := by
  obtain ⟨h1,h2,h3,h4,h5,h6,_,h8,h9,h10⟩ :=
    hooks_reads ReadsHeld.fresh fam K listen
  exact ⟨h1,h2,h3,h4,h5,h6,dial_reads K listen wall mono,h8,h9,h10⟩

/-- Every actual event with discovery enabled obeys the same primitive store
transition relation as Astra's existing full-node theorem. -/
theorem step_moves (listen : B) (wall mono : Nat) (cfg : Config)
    (n : Engine.Sync.Node) (input : Node.Input) (now : Nat) (s : Memory) :
    Moves Execution.family s.held
      ((n.step (Discovery.sync (m := M) Execution.family sodium listen wall mono cfg) input now) s).2.held :=
  NodeTape.step_goes _ (readOnly Execution.family sodium listen wall mono cfg) n input now s

theorem step_retains (listen : B) (wall mono : Nat) (cfg : Config)
    (n : Engine.Sync.Node) (input : Node.Input) (now : Nat) (s : Memory) {i : Id} {o : Op}
    (ho : s.held.db.ops i = some o) (hs : (Execution.family.room o).isSome) :
    ((n.step (Discovery.sync (m := M) Execution.family sodium listen wall mono cfg) input now) s).2.held.db.ops i = some o :=
  (step_moves listen wall mono cfg n input now s).shared_retained ho hs

theorem step_settled (listen : B) (wall mono : Nat) (cfg : Config)
    (n : Engine.Sync.Node) (input : Node.Input) (now : Nat) (s : Memory)
    (hr : s.held.Reachable Execution.family) (hq : s.held.db.queue = []) :
    ((n.step (Discovery.sync (m := M) Execution.family sodium listen wall mono cfg) input now) s).2.held.db.queue = [] :=
  (step_moves listen wall mono cfg n input now s).store_settled hr hq

end Connection.DiscoveryStorage
