/-
Which rooms a connection carries: the laws of `roomsV`, the view the
`rooms` hook runs (Connection/Intents.lean), and so the rooms every
connection step uses (`Node.refresh`, Engine/Sync/Node.lean).

- `trusts_live`: for a node that is a live member of c, the trust rule
  is `allowPeer`: the link's inviter clause applies only before
  admission.
- `rooms_trusted`: a room is carried only if this node is a device in
  it whose secret it holds, and the trust rule takes the peer.
- `rooms_cut`: so a live member's connection carries no room whose
  peer `allowPeer` refuses.

With `recv_send` and `recv_take`, nothing of that room then goes out on
the connection or is taken from it. `Community.removal_cuts_off` says
`allowPeer` refuses a removed user's devices, over the Community
family's own store; `rooms_cut_node` (Connection/NodeLaws.lean) carries
it to the composed store the node runs, by `sum_project`.
-/
import Connection.Intents

namespace Connection
open Engine

section
variable {A B : Type} [SortKey (A ⊕ B)]

theorem eval_liftL_pure {α : Type} (s : DB (A ⊕ B)) (a : α) :
    ((Pure.pure a : View A α).liftL : View (A ⊕ B) α).eval s = a := rfl

theorem eval_liftL_bind {α β : Type} (s : DB (A ⊕ B)) (v : View A α) (f : α → View A β) :
    ((v >>= f).liftL : View (A ⊕ B) β).eval s =
      ((f ((v.liftL : View (A ⊕ B) α).eval s)).liftL : View (A ⊕ B) β).eval s := by
  induction v with
  | pure a => rfl
  | list q k ih => exact ih _

end

/-- **For a live member, the trust rule is `allowPeer`.** The link
clause (trust the inviter a pending join names) holds only before this
device is admitted. -/
theorem trusts_live (s : DB F) {c me peer : B}
    (h : ((Community.allowPeer c me).liftL : View F Bool).eval s = true) :
    ((trusts c me peer).liftL : View F Bool).eval s =
      ((Community.allowPeer c peer).liftL : View F Bool).eval s := by
  unfold trusts
  rw [eval_liftL_bind]
  cases hp : ((Community.allowPeer c peer).liftL : View F Bool).eval s
  · simp only [Bool.false_eq_true, ite_false]
    rw [eval_liftL_bind]
    split
    · rfl
    · rw [eval_liftL_bind, h, eval_liftL_bind]
      simp [eval_liftL_pure]
  · rfl

theorem eval_roomsOf (s : DB F) (ps : List (B × B)) :
    (roomsOf ps).eval s = ps.filterMap fun (c, peer) =>
      match (meV c).eval s with
      | some me => if ((trusts c me peer).liftL : View F Bool).eval s then some c else none
      | none => none := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨c, peer⟩ := p
    simp only [roomsOf, View.eval_bind, List.filterMap_cons]
    cases hm : (meV c).eval s with
    | none => simp [ih]
    | some me =>
      simp only []
      cases ht : ((trusts c me peer).liftL : View F Bool).eval s <;> simp [ih, ht]

/-- **A room is carried only if trusted.** If connection cid carries
room c, one of cid's established facts names c and a peer, this node is
a device in c whose secret it holds, and the trust rule takes the peer. -/
theorem rooms_trusted (s : DB F) {cid c : Id} (h : c ∈ (roomsV cid).eval s) :
    ∃ peer me, (c, peer) ∈ pairsOf (Engine.eval s (established.byConn.query [cid])) ∧
      (meV c).eval s = some me ∧ ((trusts c me peer).liftL : View F Bool).eval s = true := by
  simp only [roomsV, View.eval_bind, View.eval_read, View.eval_pure, List.mem_reverse,
    eval_roomsOf, List.mem_filterMap] at h
  obtain ⟨⟨c', peer⟩, hp, hc⟩ := h
  cases hm : (meV c').eval s with
  | none => simp [hm] at hc
  | some me =>
    rw [hm] at hc
    cases ht : ((trusts c' me peer).liftL : View F Bool).eval s
    · simp [ht] at hc
    · simp only [ht, ite_true, Option.some.injEq] at hc
      subst hc
      exact ⟨peer, me, hp, hm, ht⟩

/-- **A live member's connection carries no room whose peer
`allowPeer` refuses.** If this node is a live member of c, and
`allowPeer` refuses every peer cid's established facts name in c, then
cid carries no room c: no step of it sends an op of c or takes one
(`recv_send`, `recv_take`). -/
theorem rooms_cut (s : DB F) {cid c : Id}
    (hme : ∀ me, (meV c).eval s = some me →
      ((Community.allowPeer c me).liftL : View F Bool).eval s = true)
    (hpeer : ∀ peer, (c, peer) ∈ pairsOf (Engine.eval s (established.byConn.query [cid])) →
      ((Community.allowPeer c peer).liftL : View F Bool).eval s = false) :
    c ∉ (roomsV cid).eval s := by
  intro h
  obtain ⟨peer, me, hp, hm, ht⟩ := rooms_trusted s h
  rw [trusts_live s (hme me hm), hpeer peer hp] at ht
  cases ht

/-- The hook runs the view: on the model, `rooms` is `roomsV`. -/
theorem rooms_model (s : DB F) (cid : Id) :
    ((rooms cid : Model F (List Id))).run s = ((roomsV cid).eval s, s) :=
  View.run_model _ s

end Connection
