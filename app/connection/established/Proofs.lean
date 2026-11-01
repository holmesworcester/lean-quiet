import app.connection.Family
import app.connection.established.Commands
import engine.sync.NoticeLaws

/-!
`connection.established`'s laws.
-/

namespace Connection
open Engine

/-- The family's validator judges an established by its op type's: the facts it
cites are these, typed. -/
theorem check_established {K : Keys} {o : Op} {fs : List F} {f : Fact} (h : check K o .established fs = some f) :
    ∃ cn rq ep en a, fs = [.inr (.ofConnection cn), .inr (.ofRequest rq), .inr (.ofEph ep), .inl (.ofEndpoint en)] ∧
      Established.check K o {} cn rq ep en = some a ∧ f = .ofEstablished a := by
  unfold check at h
  split at h <;> (try (simp_all; done))
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨_, _, _, _, a, rfl, ha, rfl⟩

end Connection

namespace Connection
open Engine Engine.Sync Codec

/-- The trust rule refuses, for c, every peer key connection cid names:
once the removal is held, a removed member's node. -/
def Refused (s : DB F) (cid c : B) : Prop :=
  ∀ peer ∈ peersOf (Engine.eval s (established.byConn.query [cid])), ((Community.allowPeer c peer).liftL : View F Bool).eval s = false

/-- Removal x of community c is owed to connection cid's peer: a removal
of a user admitted under the peer's key, read from the lists. -/
def Owed (s : DB F) (cid c x : B) : Prop :=
  ∃ peer ∈ peersOf (Engine.eval s (established.byConn.query [cid])), x ∈ ((Community.removalsAt c peer).liftL : View F (List Id)).eval s

end Connection
