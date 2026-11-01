import app.community.Family
import app.community.device.endpoint.Commands

namespace Community
open Engine

/-- What `nodeKeyOr` writes is local: at most the node's key. -/
theorem nodeKeyOr_local (C : Crypto) (s : DB Fact) (fresh : Key32) :
    ((nodeKeyOr fresh).eval s).2.filter (family C).shared = [] := by
  unfold nodeKeyOr
  rw [View.eval_bind']
  split <;> simp [View.eval, endpoint, shared_mkOp, Body.isLocal]
open Engine
variable {C : Crypto}

theorem check_endpoint {o : Op} {b : Body} {fs : List Fact} {pk sk : ByteArray}
    (h : check C o b fs = some (.endpoint pk sk)) : ∃ hs : sk.size = 32, pk = cryptoSeal.pub ⟨sk, hs⟩ := by
  unfold check at h
  split at h <;> (try (simp at h; done))
  rename_i b
  rcases b with ⟨sk'⟩
  simp only [Endpoint.check] at h
  split at h
  · rename_i hc
    simp only [Option.map_some, Option.some.injEq, Fact.ofEndpoint.injEq, Endpoint.Fact.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hc, rfl⟩
  · simp at h

/-- **A node's key is its secret's (`endpoint_derives`).** -/
theorem endpoint_derives {ops : Id → Option Op} {x : Id} {pk sk : ByteArray}
    (h : V C ops x (.endpoint pk sk)) : ∃ hs : sk.size = 32, pk = cryptoSeal.pub ⟨sk, hs⟩ := by
  obtain ⟨o, b, fs, _, _, _, hc⟩ := valid_inv h
  exact check_endpoint hc
open Engine
variable {C : Crypto}
section
variable {s : DB Fact}

theorem nodeKeyOr_held {fresh : Key32} {key : Key} {sk : Key32} (hk : nodeKey.eval s = some (key, sk)) :
    (nodeKeyOr fresh).eval s = (key, []) := by
  unfold nodeKeyOr
  rw [View.eval_bind', hk]; rfl

theorem body_endpoint (sk : ByteArray) : (Codec.decode (endpoint sk).body : Option Body) = some (.endpoint sk) :=
  body_mkOp _ _

end
end Community
